/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffTheta

/-!
# A TWISTING DATUM THAT DOES NOT CONFINE THE PIECES

`Picard/DivisorFamilyAffTheta.lean` builds the Θ-layer over a widened cover, and its own
`isEmpty_chartTyping_of_straddling` proves that every declaration in it is **vacuous on the
covers protection `I-0492` exists for**: the layer is indexed by a `ChartTyping`, whose field
`piece_le` puts each piece inside one of a FIXED PAIR of pinned `P¹` charts, and a piece
holding a point off `V₀` and a point off `V₁` admits no such assignment.

That is not a repairable detail of the Θ-layer; it is the fixed-pair typing re-entering
through an index, which `I-0492` clause 3 names as the pattern to avoid ("do not smuggle the
old typing back in by typing pieces INTO the charts").  This file removes it.

## The distinction the old index conflates

`relThetaSections` (`Picard/DivisorFamilyTheta.lean:59`) models `𝒪(Θᵃ)` as **pairs of
sections on `V₀`, `V₁` matching through the theta cocycle**.  That is a two-chart model of the
LINE BUNDLE, and it is not a constraint on any divisor: it is how this project spells the
sheaf, for every family, straddling or not.

`ChartTyping` is a different thing wearing the same clothes: it constrains **the divisor's own
pieces** to sit inside those charts.  Only the second is the refuted fixed-pair confinement
(ADDENDUM 3 §2, roadmap leaf `…joint-cover`, rejected).  The Θ-layer needs the first and was
given the second, and the second is what empties it.

## What the layer actually consumes

Four things, and none of them says where a piece lives:

* a per-piece **reading** `read j : H⁰(𝒪(Θᵃ)) → Γ(pieces j)` — a local trivialization of the
  twist over the piece, which is what `relThetaResSide` *is* when the piece happens to lie in
  a chart;
* a per-pair **comparison unit** `unit i j` on the overlap;
* the **matching law** relating the two through that unit — the only input of
  `thetaEval_mem`;
* a **germ law** tying the reading to the two chart components up to a unit of the stalk,
  which is what the kernel bridge runs on.

`ThetaTrivData` below packages exactly those.  It mentions `relPinnedChart` — the twist's own
model — and it says **nothing** about `pieces j ≤ anything`.

## What this buys, proved rather than asserted

* `ChartTyping.thetaTrivData` — the old index maps in, so nothing landed is lost and the
  chart-typed layer is the special case it always was.
* `thetaTrivData_zero` — **`ThetaTrivData D 0` is inhabited for EVERY widened cover**,
  straddling ones included, by gluing the two chart components over the piece (the sheaf
  axiom for `V₀ ⊔ V₁ = ⊤`, applied to the piece — not a confinement of the piece, which is
  covered by the two charts rather than contained in one).
* `nonempty_thetaTrivData_and_isEmpty_chartTyping` — **the separation**: on a straddling
  cover the new index is inhabited while `ChartTyping` is empty.  So this is a strictly wider
  index, on exactly the covers `I-0492` is about, and the exponent it is proved at is the one
  `DivisorAdaptation.divisorDatum` runs at (`thetaIdealUnit_zero`,
  `Picard/DivisorDatumInverse.lean:207`) — not a vacuous corner.

## What it does NOT buy, stated plainly

Inhabitation at `a > 0` needs `𝒪(Θᵃ)` to be trivial over each piece, which for an arbitrary
affine open is a condition on the bundle (a class in `Pic` of the piece), **not** free.  This
file makes that a hypothesis about the SHEAF that a producer may discharge per cover, in place
of an index that no straddling cover can inhabit at all.  The `a > 0` producer is not here and
is not claimed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

/-! ## The chart-free twisting datum -/

/-- **A twisting datum for a widened cover**, carrying what the Θ-layer consumes and no
containment of any piece in any chart.

Compare `ChartTyping` (`Picard/DivisorFamilyAffCover.lean:204`), whose `piece_le` field is the
fixed-pair confinement that `AffAdaptation.isEmpty_chartTyping_of_straddling` shows no
straddling cover can satisfy.  Nothing below is a statement about where `pieces j` lies. -/
structure ThetaTrivData (D : AffCoverData C R) (a : ℕ) where
  /-- The local reading of a global theta section on the piece: a trivialization of `𝒪(Θᵃ)`
  over `pieces j`, spelled through its effect on sections. -/
  read : ∀ j : D.index, relThetaSections C R π a →ₗ[R] Γ(relCurve C R, D.pieces j)
  /-- The comparison unit of two readings on the overlap of their pieces. -/
  unit : ∀ i j : D.index, Γ(relCurve C R, D.pieces i ⊓ D.pieces j)ˣ
  /-- **The matching law**: on the overlap the two readings differ by the comparison unit.
  This is the whole input of `thetaEval_mem`. -/
  matching : ∀ (i j : D.index) (x : relThetaSections C R π a),
    (relCurve C R).resHom (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (read i x)
      = ((unit i j : Γ(relCurve C R, D.pieces i ⊓ D.pieces j)ˣ) :
          Γ(relCurve C R, D.pieces i ⊓ D.pieces j))
        * (relCurve C R).resHom inf_le_right (read j x)
  /-- **The germ law**: where a point of the piece also lies in a pinned chart, the germ of
  the reading agrees with the germ of that chart's component of the section up to a unit of
  the stalk.  This is what the kernel bridge runs on, and it refers to the two-chart model of
  the SHEAF rather than to the location of the piece.

  Stated in the `relThetaResSide … inf_le_right` spelling rather than as `Bool.rec x.val.1
  x.val.2 b`, because that is the form `germ_val_mem_stalkIdeal_of_forall_side`
  (`Picard/DivisorFamilyAffTheta.lean:691`) consumes — the two differ by a self-restriction. -/
  germ_read : ∀ (j : D.index) (b : Bool) (z : relCurve C R) (hzj : z ∈ D.pieces j)
      (hzb : z ∈ relPinnedChart C R π b) (x : relThetaSections C R π a),
    ∃ u : ((relCurve C R).presheaf.stalk z)ˣ,
      ((relCurve C R).presheaf.germ (D.pieces j) z hzj).hom (read j x)
        = (u : (relCurve C R).presheaf.stalk z)
          * ((relCurve C R).presheaf.germ ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b)
              z ⟨trivial, hzb⟩).hom (relThetaResSide a b inf_le_right x)

/-! ## The old index maps in: nothing landed is lost -/

namespace ChartTyping

variable {D : AffCoverData C R} (τ : ChartTyping C R π D) (a : ℕ)

/-- **A chart typing gives a twisting datum.**  The reading is `relThetaResSide` at the
assigned side, the unit is `AffAdaptation.thetaOvlUnit`, the matching law is
`relThetaResSide_matching` — i.e. exactly the three ingredients
`Picard/DivisorFamilyAffTheta.lean` uses — and the germ law holds with `u = 1` on the assigned
side, comparing the two sides through the side matching unit otherwise.

So the widened Θ-layer's hypotheses are *implied* by the old index: this file weakens an
index, it does not replace one theory by another. -/
noncomputable def thetaTrivData : ThetaTrivData (π := π) D a where
  read j := relThetaResSide a (τ.side j)
    (AffAdaptation.piece_le_relPinnedChart (π := π) τ j)
  unit i j := relThetaSideUnit a (τ.side i) (τ.side j)
    (AffAdaptation.pieces_inf_le_relPinnedChart_inf (π := π) τ i j)
  matching i j x := by
    rw [resHom_relThetaResSide a (τ.side i)
        (AffAdaptation.piece_le_relPinnedChart (π := π) τ i),
      resHom_relThetaResSide a (τ.side j)
        (AffAdaptation.piece_le_relPinnedChart (π := π) τ j)]
    exact relThetaResSide_matching a (τ.side i) (τ.side j)
      (AffAdaptation.pieces_inf_le_relPinnedChart_inf (π := π) τ i j) x
  germ_read j b z hzj hzb x := by
    -- the two readings at `z` differ by the side matching unit, restricted to a germ
    have hzW : z ∈ D.pieces j ⊓ relPinnedChart C R π b := ⟨hzj, hzb⟩
    have hle : D.pieces j ⊓ relPinnedChart C R π b
        ≤ relPinnedChart C R π (τ.side j) ⊓ relPinnedChart C R π b :=
      inf_le_inf_right _ (AffAdaptation.piece_le_relPinnedChart (π := π) τ j)
    have hmatch := relThetaResSide_matching a (τ.side j) b hle x
    -- the comparison unit already lives on the piece-chart overlap, so its germ is a unit
    refine ⟨(((relThetaSideUnit a (τ.side j) b hle).isUnit).map
      ((relCurve C R).presheaf.germ (D.pieces j ⊓ relPinnedChart C R π b) z hzW).hom).unit, ?_⟩
    have hgerm := congrArg ((relCurve C R).presheaf.germ
      (D.pieces j ⊓ relPinnedChart C R π b) z hzW).hom hmatch
    rw [map_mul] at hgerm
    -- move the reading's germ down to the overlap, where `hmatch` lives
    rw [show ((relCurve C R).presheaf.germ (D.pieces j) z hzj).hom
          (relThetaResSide a (τ.side j)
            (AffAdaptation.piece_le_relPinnedChart (π := π) τ j) x)
        = ((relCurve C R).presheaf.germ (D.pieces j ⊓ relPinnedChart C R π b) z hzW).hom
            (relThetaResSide a (τ.side j) (hle.trans inf_le_left) x) from
      (AffAdaptation.germ_relThetaResSide_eq a x (τ.side j)
        (AffAdaptation.piece_le_relPinnedChart (π := π) τ j) inf_le_left hzW).symm,
      hgerm]
    -- and the `b`-component's germ up from the overlap to `⊤ ⊓ chart b`
    exact congrArg _ (AffAdaptation.germ_relThetaResSide_eq a x b
      (inf_le_right : (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b
        ≤ relPinnedChart C R π b)
      (le_inf le_top (hle.trans inf_le_right)) hzW)

end ChartTyping

/-! ## Inhabitation at exponent `0`, for EVERY widened cover

At `a = 0` the theta cocycle is trivial (`relThetaCocycle_zero`), so a global theta section is
a pair of sections of the STRUCTURE sheaf on `V₀`, `V₁` agreeing on the overlap — and the two
pinned charts cover the curve.  One gluing therefore produces a genuine global section, and the
reading on a piece is that section restricted.  Note where the covering is used: `V₀ ⊔ V₁ = ⊤`
is a statement about the CURVE, applied before any piece is mentioned.  No piece is required to
sit inside a chart, which is exactly the difference from `ChartTyping`. -/

section ZeroExponent

variable (C R π)

/-- **The two pinned charts cover the curve**, in the `⊤ ⊓ ·` spelling the theta components
live over. -/
lemma le_iSup_top_inf_relPinnedChart :
    (⊤ : (relCurve C R).Opens) ≤ ⨆ b : Bool, (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b :=
  fun z _ => by
    have hz : z ∈ (relCover C R (fiberTwoCover π)).V₀ ⊔ (relCover C R (fiberTwoCover π)).V₁ := by
      rw [relCover_sup]; trivial
    rcases Opens.mem_sup.mp hz with h | h
    · exact Opens.mem_iSup.mpr ⟨false, ⟨trivial, h⟩⟩
    · exact Opens.mem_iSup.mpr ⟨true, ⟨trivial, h⟩⟩

/-- **A global theta section at exponent `0` glues to a global section of `𝒪`.**  Its two
components agree on the chart overlap because the cocycle is `1` there, and the charts cover. -/
lemma existsUnique_glueThetaZero (x : relThetaSections C R π 0) :
    ∃! s : Γ(relCurve C R, ⊤), ∀ b : Bool,
      (relCurve C R).resHom
          (inf_le_left : (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b ≤ ⊤) s
        = relThetaResSide 0 b inf_le_right x := by
  refine (relCurve C R).sheaf.existsUnique_gluing'
    (fun b : Bool => (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b) ⊤
    (fun b => homOfLE inf_le_left) (le_iSup_top_inf_relPinnedChart C R π)
    (fun b => relThetaResSide 0 b inf_le_right x) ?_
  intro i j
  -- the matching law at exponent `0`, where the side unit is `1`
  have hle : ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π i)
        ⊓ ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π j)
      ≤ relPinnedChart C R π i ⊓ relPinnedChart C R π j :=
    inf_le_inf inf_le_right inf_le_right
  have hmatch := relThetaResSide_matching 0 i j hle x
  rw [AffAdaptation.relThetaSideUnit_zero (C := C) (R := R) (π := π) i j hle, Units.val_one,
    one_mul] at hmatch
  rw [show relThetaResSide 0 i (hle.trans inf_le_left) x
      = (relCurve C R).resHom (inf_le_left :
          ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π i)
            ⊓ ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π j)
          ≤ (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π i)
        (relThetaResSide 0 i inf_le_right x) from
    (resHom_relThetaResSide 0 i inf_le_right inf_le_left x).symm,
    show relThetaResSide 0 j (hle.trans inf_le_right) x
      = (relCurve C R).resHom (inf_le_right :
          ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π i)
            ⊓ ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π j)
          ≤ (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π j)
        (relThetaResSide 0 j inf_le_right x) from
    (resHom_relThetaResSide 0 j inf_le_right inf_le_right x).symm] at hmatch
  exact hmatch

/-- The glued global section of a theta section at exponent `0`. -/
noncomputable def glueThetaZero (x : relThetaSections C R π 0) : Γ(relCurve C R, ⊤) :=
  (existsUnique_glueThetaZero C R π x).choose

lemma resHom_glueThetaZero (x : relThetaSections C R π 0) (b : Bool) :
    (relCurve C R).resHom
        (inf_le_left : (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b ≤ ⊤)
        (glueThetaZero C R π x)
      = relThetaResSide 0 b inf_le_right x :=
  (existsUnique_glueThetaZero C R π x).choose_spec.1 b

/-- Uniqueness, in the form the linearity proofs consume. -/
lemma glueThetaZero_eq_of_forall {x : relThetaSections C R π 0} {s : Γ(relCurve C R, ⊤)}
    (h : ∀ b : Bool, (relCurve C R).resHom
        (inf_le_left : (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b ≤ ⊤) s
      = relThetaResSide 0 b inf_le_right x) :
    s = glueThetaZero C R π x :=
  (existsUnique_glueThetaZero C R π x).unique h
    ((existsUnique_glueThetaZero C R π x).choose_spec.1)

/-- **The gluing is `R`-linear**, as a map out of the theta sections at exponent `0`. -/
noncomputable def glueThetaZeroHom :
    relThetaSections C R π 0 →ₗ[R] Γ(relCurve C R, ⊤) where
  toFun := glueThetaZero C R π
  map_add' x y := by
    refine (glueThetaZero_eq_of_forall C R π (fun b => ?_)).symm
    rw [map_add, resHom_glueThetaZero, resHom_glueThetaZero, map_add]
  map_smul' r x := by
    refine (glueThetaZero_eq_of_forall C R π (fun b => ?_)).symm
    -- `resHom` commutes with the `overModule` scalar action; both spellings of that lemma in
    -- the tree are `private` (`Cohomology/TwistedSheaf.lean:122`, `GluedSheaf.lean:108`), so
    -- the two-line unfolding is inlined rather than re-exported (inbox `I-0712`).
    have hsmul : (relCurve C R).resHom
        (inf_le_left : (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b ≤ ⊤)
          (r • glueThetaZero C R π x)
        = r • (relCurve C R).resHom
            (inf_le_left : (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b ≤ ⊤)
            (glueThetaZero C R π x) := by
      rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
      congr 1
      exact (relCurve C R).overAlgebraMap_apply_res R (homOfLE inf_le_left).op r
    rw [RingHom.id_apply, hsmul, resHom_glueThetaZero, map_smul]

variable {C R π}

/-- **THE PRODUCER: every widened cover carries a twisting datum at exponent `0`.**  No
hypothesis on the pieces beyond `AffCoverData` itself — in particular a STRADDLING cover, on
which `ChartTyping` is empty (`AffAdaptation.isEmpty_chartTyping_of_straddling`), carries one.

The reading is the glued global section restricted to the piece; the comparison unit is `1`,
because at exponent `0` there is nothing to compare — the two chart components are two views of
one global section rather than two independent data.  The germ law holds with `u = 1` for the
same reason.

`0` is not a vacuous corner: it is the exponent `DivisorAdaptation.divisorDatum` runs at
(`thetaIdealUnit_zero`, `Picard/DivisorDatumInverse.lean:207`), i.e. the twist in which the
divisor's own class is read. -/
noncomputable def AffCoverData.thetaTrivDataZero (D : AffCoverData C R) :
    ThetaTrivData (π := π) D 0 where
  read j := (relResAlgHom C R (le_top : D.pieces j ≤ ⊤)).toLinearMap ∘ₗ glueThetaZeroHom C R π
  unit _ _ := 1
  matching i j x := by
    -- both sides restrict the SAME global section into the overlap
    simp only [Units.val_one, one_mul, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, relResAlgHom_apply]
    change (relCurve C R).resHom _ ((relCurve C R).resHom (le_top : D.pieces i ≤ ⊤) _)
      = (relCurve C R).resHom _ ((relCurve C R).resHom (le_top : D.pieces j ≤ ⊤) _)
    rw [Scheme.resHom_resHom, Scheme.resHom_resHom]
  germ_read j b z hzj hzb x := by
    refine ⟨1, ?_⟩
    rw [Units.val_one, one_mul]
    -- both germs are the germ of ONE global section: the glued one
    have hleft : ((relCurve C R).presheaf.germ (D.pieces j) z hzj).hom
        (relResAlgHom C R (le_top : D.pieces j ≤ ⊤) (glueThetaZero C R π x))
        = ((relCurve C R).presheaf.germ ⊤ z trivial).hom (glueThetaZero C R π x) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    have hright : ((relCurve C R).presheaf.germ
        ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b) z ⟨trivial, hzb⟩).hom
          (relThetaResSide 0 b inf_le_right x)
        = ((relCurve C R).presheaf.germ ⊤ z trivial).hom (glueThetaZero C R π x) := by
      rw [← resHom_glueThetaZero C R π x b]
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    -- `glueThetaZeroHom … x` is `glueThetaZero … x` by `rfl`, but `rw` is reducible-only
    -- against the folded bundled name, so the fold is discharged by `show` first.
    change ((relCurve C R).presheaf.germ (D.pieces j) z hzj).hom
        (relResAlgHom C R (le_top : D.pieces j ≤ ⊤) (glueThetaZero C R π x))
      = ((relCurve C R).presheaf.germ
          ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b) z ⟨trivial, hzb⟩).hom
        (relThetaResSide 0 b inf_le_right x)
    exact hleft.trans hright.symm

/-- **THE SEPARATION, which is the point of the file.**  On a cover with a straddling piece —
one holding a point off `V₀` and a point off `V₁` — the new twisting index is INHABITED while
`ChartTyping` is EMPTY.

So `ThetaTrivData` is strictly wider than `ChartTyping` on exactly the covers protection
`I-0492`'s widening exists for, and the widened Θ-layer's vacuity there
(`AffAdaptation.isEmpty_chartTyping_of_straddling`, reviewer item `I-0779`) is a defect of the
index rather than of the layer's mathematics. -/
theorem nonempty_thetaTrivData_and_isEmpty_chartTyping (D : AffCoverData C R) (j : D.index)
    {x y : relCurve C R} (hxj : x ∈ D.pieces j) (hyj : y ∈ D.pieces j)
    (hx₀ : x ∉ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R)))
    (hy₁ : y ∉ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R))) :
    Nonempty (ThetaTrivData (π := π) D 0) ∧ IsEmpty (ChartTyping C R π D) :=
  ⟨⟨D.thetaTrivDataZero⟩,
    AffAdaptation.isEmpty_chartTyping_of_straddling (π := π) D j hxj hyj hx₀ hy₁⟩

end ZeroExponent

/-! ## The Θ-layer, re-indexed on the chart-free datum

Everything here is the corresponding declaration of `Picard/DivisorFamilyAffTheta.lean` with
`τ : ChartTyping` replaced by `T : ThetaTrivData`, and it is a genuine re-indexing rather than
a copy: each proof below invokes exactly one field of `T` where the chart-typed version invoked
`relThetaResSide`/`relThetaResSide_matching` at `τ.side j`.  That correspondence is what
`ChartTyping.thetaTrivData` makes precise — the old layer is the special case.

The point of doing it here rather than editing that file: its declarations stay valid and
consumed, and a producer may now choose either index.  `AffCoverData.thetaTrivDataZero` gives
the widened one on every cover. -/

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d) {a : ℕ} (T : ThetaTrivData (π := π) D a)

/-- **The Θ-twisted right overlap arrow**, twisted by the datum's comparison unit. -/
noncomputable def trivDeltaRight : A.chartProd →ₗ[R] A.ovlProd :=
  LinearMap.pi (fun p : D.index × D.index =>
    LinearMap.mulLeft R (Ideal.Quotient.mk (A.ovlIdeal p.1 p.2)
        ((T.unit p.1 p.2 : Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2)ˣ) :
          Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2))) ∘ₗ
      (A.toOvlRight p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.2)

/-- **The Θ-twisted glued colength module `W(d)^{Θᵃ}` over a chart-free datum.** -/
noncomputable def trivGluedSubmodule : Submodule R A.chartProd :=
  LinearMap.ker (A.deltaLeft - trivDeltaRight A T)

lemma mem_trivGluedSubmodule_iff (s : A.chartProd) :
    s ∈ trivGluedSubmodule A T ↔ ∀ p : D.index × D.index,
      A.toOvlLeft p.1 p.2 (s p.1)
        = Ideal.Quotient.mk (A.ovlIdeal p.1 p.2)
            ((T.unit p.1 p.2 : Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2)ˣ) :
              Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2))
          * A.toOvlRight p.1 p.2 (s p.2) := by
  simp only [trivGluedSubmodule, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    funext_iff, deltaLeft, trivDeltaRight, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply,
    LinearMap.mulLeft_apply]

/-- The chart-free Θ-twisted glued colength module, as a type. -/
noncomputable abbrev TrivGlued : Type u := ↥(trivGluedSubmodule A T)

/-- The per-piece evaluation: the datum's reading, reduced mod `(f_j)`. -/
noncomputable def trivPieceEval (j : D.index) :
    relThetaSections C R π a →ₗ[R] A.colength j :=
  (Ideal.Quotient.mkₐ R (Ideal.span {A.eqn j})).toLinearMap ∘ₗ T.read j

/-- **The section evaluation into the widened chart product**, chart-free. -/
noncomputable def trivEval : relThetaSections C R π a →ₗ[R] A.chartProd :=
  LinearMap.pi (trivPieceEval A T)

@[simp]
lemma trivEval_apply (x : relThetaSections C R π a) (j : D.index) :
    trivEval A T x j
      = Ideal.Quotient.mk (Ideal.span {A.eqn j}) (T.read j x) := rfl

/-- **The evaluation lands in the twisted glued module.**  Where the chart-typed proof calls
`relThetaResSide_matching`, this calls the datum's `matching` field — the only input. -/
theorem trivEval_mem (x : relThetaSections C R π a) :
    trivEval A T x ∈ trivGluedSubmodule A T := by
  rw [mem_trivGluedSubmodule_iff]
  rintro ⟨i, j⟩
  rw [trivEval_apply, trivEval_apply, toOvlLeft_mk, toOvlRight_mk, ← map_mul]
  exact congrArg _ (T.matching i j x)

/-- **The evaluation `H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}` over a chart-free datum.** -/
noncomputable def trivGluedEval :
    relThetaSections C R π a →ₗ[R] TrivGlued A T :=
  LinearMap.codRestrict (trivGluedSubmodule A T) (trivEval A T) (trivEval_mem A T)

lemma ker_trivGluedEval_eq_ker :
    LinearMap.ker (trivGluedEval A T) = LinearMap.ker (trivEval A T) :=
  LinearMap.ker_codRestrict _ _ _

/-! ### The kernel bridge, chart-free

The one direction that needs the germ law.  Compare `ker_thetaGluedEval`
(`Picard/DivisorFamilyAffTheta.lean:813`): there the germ of the reading IS the germ of the
assigned chart component (the reading is a restriction), here it agrees with it up to a unit of
the stalk — and a stalk ideal is closed under multiplication by units, so the argument is
unchanged.  That unit is precisely the slack that buys chart-freedom. -/

/-- **The germ of the reading of a killed section lies in `d`'s stalk ideal**, at a point of the
piece, read against any pinned chart containing it.  The chart-free counterpart of
`germ_val_mem_stalkIdeal_of_thetaEval_eq_zero`. -/
lemma germ_read_mem_stalkIdeal_of_trivEval_eq_zero {x : relThetaSections C R π a}
    (hker : ∀ j, trivEval A T x j = 0) (b : Bool) (j : D.index)
    {z : relCurve C R} (hzj : z ∈ D.pieces j) (hzb : z ∈ relPinnedChart C R π b) :
    ((relCurve C R).presheaf.germ ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b)
        z ⟨trivial, hzb⟩).hom (relThetaResSide a b inf_le_right x) ∈ d.stalkIdeal z := by
  obtain ⟨u, hu⟩ := T.germ_read j b z hzj hzb x
  -- the reading's germ is in the stalk ideal: the evaluation vanishes on the piece
  have hgermread : ((relCurve C R).presheaf.germ (D.pieces j) z hzj).hom (T.read j x)
      ∈ d.stalkIdeal z := by
    have hmem : T.read j x ∈ Ideal.span {A.eqn j} := by
      have h := hker j
      rw [trivEval_apply, Ideal.Quotient.eq_zero_iff_mem] at h
      exact h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
    have hgerm := congrArg ((relCurve C R).presheaf.germ (D.pieces j) z hzj).hom hc
    rw [map_mul] at hgerm
    rw [← germ_eqn_span_eq_stalkIdeal A j hzj, hgerm]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  -- and the two differ by the unit `u`, which a stalk ideal absorbs
  rw [hu] at hgermread
  exact (Ideal.unit_mul_mem_iff_mem _ u.isUnit).mp hgermread

/-- **THE KERNEL BRIDGE, CHART-FREE**: the kernel of the chart-free Θ-twisted evaluation is the
cover-independent vanishing submodule of the family — the same right-hand side as the
chart-typed `ker_thetaGluedEval` and as `AffAdaptation.ker_thetaGluedEval`, so all three kernels
are the *same submodule* of `relThetaSections C R π a`.

This is what makes the new index usable rather than merely inhabited: `divisorWindow` is a
`Submodule.comap` of exactly this submodule, so `windowCarve`/`ker_windowCarve` transport
verbatim (below).

The forward direction picks a piece out of the JOINT cover (`AffCoverData.exists_mem_pieces`,
obligation `I-0492` 4(ii)); the reverse direction needs the germ law's unit in the other
direction, which is the same absorption. -/
theorem ker_trivGluedEval :
    LinearMap.ker (trivGluedEval A T)
      = d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
          (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) := by
  rw [ker_trivGluedEval_eq_ker]
  ext x
  rw [LinearMap.mem_ker, Scheme.LocalEquations.mem_vanishingSubmodule_iff, funext_iff]
  constructor
  · intro hker
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · obtain ⟨j, hj⟩ := D.exists_mem_pieces z
      have h := germ_read_mem_stalkIdeal_of_trivEval_eq_zero A T hker false j hj hz.2
      simpa using h
    · obtain ⟨j, hj⟩ := D.exists_mem_pieces z
      have h := germ_read_mem_stalkIdeal_of_trivEval_eq_zero A T hker true j hj hz.2
      simpa using h
  · intro h j
    rw [trivEval_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
    refine Scheme.mem_span_singleton_of_forall_germ
      (fun z hz => A.eqn_regular j z hz) (fun z hz => ?_)
    rw [germ_eqn_span_eq_stalkIdeal A j hz]
    -- the point lies in SOME pinned chart, and the germ law compares the reading there
    have hzc : ∃ b : Bool, z ∈ relPinnedChart C R π b := by
      have hz' : z ∈ (relCover C R (fiberTwoCover π)).V₀
          ⊔ (relCover C R (fiberTwoCover π)).V₁ := by
        rw [relCover_sup]; trivial
      rcases Opens.mem_sup.mp hz' with hb | hb
      · exact ⟨false, hb⟩
      · exact ⟨true, hb⟩
    obtain ⟨b, hzb⟩ := hzc
    obtain ⟨u, hu⟩ := T.germ_read j b z hz hzb x
    rw [hu]
    exact Ideal.mul_mem_left _ _
      (germ_val_mem_stalkIdeal_of_forall_side a x h b ⟨trivial, hzb⟩)

/-! ### The window carve, chart-free

`divisorWindow` is a `Submodule.comap` of the vanishing submodule and mentions no cover, so once
`ker_trivGluedEval` identifies the kernel these are `LinearMap.ker_comp` and nothing else — the
same three lines as the chart-typed versions (`Picard/DivisorFamilyAffTheta.lean:899`), now on an
index every widened cover inhabits at `a = 0`. -/

section WindowCarve

noncomputable local instance instOverCleftTrivWindow :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]

variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)

/-- **The chart-free window carve arrow** `R ⊗[k] H_a → W(d)^{Θᵃ}`. -/
noncomputable def trivWindowCarve :
    R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤) →ₗ[R] TrivGlued A T :=
  trivGluedEval A T ∘ₗ (relThetaWindowEquiv C R π a hH1).toLinearMap

/-- **The face, plugged in on the chart-free index**: the kernel of the carve arrow is the window
submodule `K_a(d)`. -/
theorem ker_trivWindowCarve :
    LinearMap.ker (trivWindowCarve A T hH1) = divisorWindow d hH1 := by
  rw [trivWindowCarve, LinearMap.ker_comp, ker_trivGluedEval, divisorWindow]

lemma trivWindowCarve_surjective (hsurj : Function.Surjective (trivGluedEval A T)) :
    Function.Surjective (trivWindowCarve A T hH1) := by
  rw [trivWindowCarve, LinearMap.coe_comp]
  exact hsurj.comp (relThetaWindowEquiv C R π a hH1).surjective

/-- **The chart-free corank identification**, conditional on the right-exactness heart exactly as
the chart-typed one is: `(R ⊗[k] H_a) ⧸ K_a(d) ≃ W(d)^{Θᵃ}`.  Surjectivity of the widened
evaluation is NOT proved here and remains the lane's open cohomological input. -/
noncomputable def trivWindowQuotEquiv (hsurj : Function.Surjective (trivGluedEval A T)) :
    ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d hH1) ≃ₗ[R] TrivGlued A T :=
  (Submodule.quotEquivOfEq _ _ (ker_trivWindowCarve A T hH1).symm).trans
    ((trivWindowCarve A T hH1).quotKerEquivOfSurjective
      (trivWindowCarve_surjective A T hH1 hsurj))

end WindowCarve

end AffAdaptation

end AlgebraicGeometry
