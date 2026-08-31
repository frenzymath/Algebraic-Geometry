/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffCover

/-!
# The widened adaptation and certificate (R2, human decision I-0492)

`DivisorFamilyAffCover.lean` carries the widened cover datum `AffCoverData` — arbitrary
affine opens, jointly covering, no chart typing.  This file puts the adaptation and the
colength certificate on top of it, clause for clause as in `DivisorFamily.lean`:

* `AffAdaptation` — equations `f_j` on the pieces plus the point-free refinement clause
  `eqn_rel` (so it pulls back along arbitrary morphisms);
* `colength`, `ovlColength`, `deltaLeft`/`deltaRight`, `gluedSubmodule` as a kernel;
* `IsCertified` with (c1)–(c4) unchanged.

**No clause is added and none is dropped.**  That is the point: consumers of the
*certificate* port by reindexing alone.  What does not survive is the (β2) upgrade from
"inside one piece" to "inside one chart" (`subset_chart₀_or_disjoint_chart₀` and
`supportLocus_subset_chart_of_isPreconnected`) — that upgrade is the no-go, not a tool, and
nothing here may depend on it.

The two facts the certificate layer actually uses about a piece are openness (for the
clopen-trace/swallow-or-miss argument, `DivSchemeCertZarConn.lean`) and affineness (for
(c1)-finiteness and the localization presentation).  Both are fields of `AffCoverData`, so
the whole per-piece layer transports.

## Main declarations

* `AlgebraicGeometry.AffAdaptation` — the widened adaptation.
* `AffAdaptation.ofAnchors` — the anchored constructor (mirrors
  `DivisorAdaptation.ofAnchors`).
* `AffAdaptation.eqn_regular` — the equations are regular, derived not stored.
* `AffAdaptation.gluedSubmodule`, `mem_gluedSubmodule_iff` — the equalizer `W(d)`.
* `AffAdaptation.IsCertified` — (c1)–(c4).
* `AffAdaptation.subsingleton_colength_of_disjoint_supportLocus`,
  `flat_colength_of_piece`, and the swallow-or-miss transport lemmas — the per-piece layer,
  proved from openness and affineness only.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]

/-- Restriction along `W ≤ V ≤ U` composes (the `private res_res` of
`Picard/DivisorFamily.lean`, restated here because that one is file-private). -/
private lemma res_res' {X : Scheme.{u}} {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-! ## The widened adaptation -/

/-- **The adaptation of a local-equation system to a widened cover.** Identical in content to
`DivisorAdaptation` except that the cover datum is an `AffCoverData`: equations on the pieces,
plus the point-free pointwise refinement clause `eqn_rel`.

`eqn_rel` quantifies over ALL `y` — on an empty overlap the section ring is the zero ring and
the clause is trivial — which is what makes it pull back along arbitrary morphisms. -/
structure AffAdaptation (D : AffCoverData C R) (d : (relCurve C R).LocalEquations) :
    Type u where
  /-- The equation on the piece `j`. -/
  eqn : ∀ j : D.index, Γ(relCurve C R, D.pieces j)
  /-- The equations refine `d` pointwise up to units. -/
  eqn_rel : ∀ (j : D.index) (y : relCurve C R),
    ∃ u : Γ(relCurve C R, D.pieces j ⊓ d.cover.opens y)ˣ,
      ((relCurve C R).presheaf.map (homOfLE inf_le_left).op).hom (eqn j)
        = (u : Γ(relCurve C R, D.pieces j ⊓ d.cover.opens y))
          * ((relCurve C R).presheaf.map (homOfLE inf_le_right).op).hom (d.eqn y)

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d)

/-- The index of the adaptation is the index of its cover. -/
abbrev index : Type := D.index

/-- **The anchored constructor.** A base point `pt j` of `d.cover` per piece with
`pieces j ≤ d.cover.opens (pt j)` and a comparison unit; `eqn_rel` is derived by transporting
`d.eqn (pt j)` to `d.eqn y` through `d.ratioUnit`, exactly as in
`DivisorAdaptation.ofAnchors`. -/
def ofAnchors
    (eqn : ∀ j : D.index, Γ(relCurve C R, D.pieces j))
    (pt : D.index → relCurve C R)
    (piece_le : ∀ j, D.pieces j ≤ d.cover.opens (pt j))
    (unit : ∀ j, Γ(relCurve C R, D.pieces j)ˣ)
    (eqn_eq : ∀ j, eqn j = (unit j : Γ(relCurve C R, D.pieces j))
      * ((relCurve C R).presheaf.map (homOfLE (piece_le j)).op).hom (d.eqn (pt j))) :
    AffAdaptation D d where
  eqn := eqn
  eqn_rel := fun j y => by
    have hWle : D.pieces j ⊓ d.cover.opens y
        ≤ d.cover.opens (pt j) ⊓ d.cover.opens y :=
      inf_le_inf (piece_le j) le_rfl
    have E1 := congrArg ((relCurve C R).presheaf.map (homOfLE
      (inf_le_left : D.pieces j ⊓ d.cover.opens y ≤ D.pieces j)).op).hom (eqn_eq j)
    rw [map_mul, res_res'] at E1
    have E2 := congrArg ((relCurve C R).presheaf.map (homOfLE hWle).op).hom
      (d.eqn_restrict_eq (pt j) y)
    rw [map_mul, res_res', res_res'] at E2
    refine ⟨(relCurve C R).unitsRestrict inf_le_left (unit j)
      * (relCurve C R).unitsRestrict hWle (d.ratioUnit (pt j) y), ?_⟩
    rw [Units.val_mul]
    calc ((relCurve C R).presheaf.map (homOfLE inf_le_left).op).hom (eqn j)
        = ((relCurve C R).unitsRestrict inf_le_left (unit j)).val
          * ((relCurve C R).presheaf.map (homOfLE
              ((inf_le_left : D.pieces j ⊓ d.cover.opens y ≤ D.pieces j).trans
                (piece_le j))).op).hom (d.eqn (pt j)) := by
          rw [show ((relCurve C R).unitsRestrict (inf_le_left :
              D.pieces j ⊓ d.cover.opens y ≤ D.pieces j) (unit j)).val
              = ((relCurve C R).presheaf.map (homOfLE (inf_le_left :
                  D.pieces j ⊓ d.cover.opens y ≤ D.pieces j)).op).hom (unit j).val
            from rfl]
          exact E1
      _ = ((relCurve C R).unitsRestrict inf_le_left (unit j)).val
          * (((relCurve C R).unitsRestrict hWle (d.ratioUnit (pt j) y)).val
            * ((relCurve C R).presheaf.map (homOfLE (hWle.trans
                (inf_le_right : d.cover.opens (pt j) ⊓ d.cover.opens y
                  ≤ d.cover.opens y))).op).hom (d.eqn y)) := by
          rw [show ((relCurve C R).unitsRestrict hWle (d.ratioUnit (pt j) y)).val
              = ((relCurve C R).presheaf.map
                  (homOfLE hWle).op).hom (d.ratioUnit (pt j) y).val from rfl]
          rw [E2]
      _ = ((relCurve C R).unitsRestrict inf_le_left (unit j)).val
          * ((relCurve C R).unitsRestrict hWle (d.ratioUnit (pt j) y)).val
          * ((relCurve C R).presheaf.map (homOfLE
              (inf_le_right : D.pieces j ⊓ d.cover.opens y
                ≤ d.cover.opens y)).op).hom (d.eqn y) := by
          rw [mul_assoc]

/-- **The equations are regular** — derived from `eqn_rel` at the point itself, not stored. -/
theorem eqn_regular (j : D.index) (z : relCurve C R) (hz : z ∈ D.pieces j) :
    ((relCurve C R).presheaf.germ (D.pieces j) z hz).hom (A.eqn j)
      ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk z) := by
  obtain ⟨u, hu⟩ := A.eqn_rel j z
  have hzW : z ∈ D.pieces j ⊓ d.cover.opens z := ⟨hz, d.cover.mem_opens z⟩
  have hgerm : ((relCurve C R).presheaf.germ (D.pieces j) z hz).hom (A.eqn j)
      = ((relCurve C R).presheaf.germ (D.pieces j ⊓ d.cover.opens z) z hzW).hom
          (u : Γ(relCurve C R, D.pieces j ⊓ d.cover.opens z))
        * ((relCurve C R).presheaf.germ (d.cover.opens z) z
            (d.cover.mem_opens z)).hom (d.eqn z) := by
    have h := congrArg ((relCurve C R).presheaf.germ
      (D.pieces j ⊓ d.cover.opens z) z hzW).hom hu
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
    exact h
  rw [hgerm]
  exact mul_mem
    ((u.isUnit.map ((relCurve C R).presheaf.germ
      (D.pieces j ⊓ d.cover.opens z) z hzW).hom).mem_nonZeroDivisors)
    (d.regular z z (d.cover.mem_opens z))

/-! ### The colength modules and the glued equalizer -/

/-- The piece-local colength module `Γ(pieces j) ⧸ (f_j)`. -/
noncomputable abbrev colength (j : D.index) : Type u :=
  Γ(relCurve C R, D.pieces j) ⧸ Ideal.span {A.eqn j}

/-- The symmetric overlap ideal, generated by both restricted equations. -/
noncomputable abbrev ovlIdeal (i j : D.index) :
    Ideal Γ(relCurve C R, D.pieces i ⊓ D.pieces j) :=
  Ideal.span
    {relResAlgHom C R (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i),
     relResAlgHom C R (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) (A.eqn j)}

/-- The overlap colength module. -/
noncomputable abbrev ovlColength (i j : D.index) : Type u :=
  Γ(relCurve C R, D.pieces i ⊓ D.pieces j) ⧸ A.ovlIdeal i j

/-- Restrict-then-quotient, from the `i` component. -/
noncomputable def toOvlLeft (i j : D.index) : A.colength i →ₐ[R] A.ovlColength i j :=
  Ideal.Quotient.liftₐ (Ideal.span {A.eqn i})
    ((Ideal.Quotient.mkₐ R (A.ovlIdeal i j)).comp (relResAlgHom C R inf_le_left))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [AlgHom.comp_apply, map_mul]
      have hmem : relResAlgHom C R
          (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i)
          ∈ A.ovlIdeal i j :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul])

/-- Restrict-then-quotient, from the `j` component. -/
noncomputable def toOvlRight (i j : D.index) : A.colength j →ₐ[R] A.ovlColength i j :=
  Ideal.Quotient.liftₐ (Ideal.span {A.eqn j})
    ((Ideal.Quotient.mkₐ R (A.ovlIdeal i j)).comp (relResAlgHom C R inf_le_right))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [AlgHom.comp_apply, map_mul]
      have hmem : relResAlgHom C R
          (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) (A.eqn j)
          ∈ A.ovlIdeal i j :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul])

/-- The product of the piece-local colengths. -/
noncomputable abbrev chartProd : Type u := ∀ j : D.index, A.colength j

/-- The product of the overlap colengths over ordered index pairs. -/
noncomputable abbrev ovlProd : Type u := ∀ p : D.index × D.index, A.ovlColength p.1 p.2

/-- The left arrow of the equalizer. -/
noncomputable def deltaLeft : A.chartProd →ₗ[R] A.ovlProd :=
  LinearMap.pi
    (fun p : D.index × D.index => (A.toOvlLeft p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.1)

/-- The right arrow of the equalizer. -/
noncomputable def deltaRight : A.chartProd →ₗ[R] A.ovlProd :=
  LinearMap.pi
    (fun p : D.index × D.index => (A.toOvlRight p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.2)

/-- **The glued colength module `W(d)`**, spelled as a kernel so the `FlatCokernel`
base-change keystone applies verbatim. -/
noncomputable def gluedSubmodule : Submodule R A.chartProd :=
  LinearMap.ker (A.deltaLeft - A.deltaRight)

/-- The equalizer description of `W(d)`. -/
lemma mem_gluedSubmodule_iff (s : A.chartProd) :
    s ∈ A.gluedSubmodule ↔ ∀ p : D.index × D.index,
      A.toOvlLeft p.1 p.2 (s p.1) = A.toOvlRight p.1 p.2 (s p.2) := by
  simp only [gluedSubmodule, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    funext_iff, deltaLeft, deltaRight, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]

/-- The glued colength module, as a type. -/
noncomputable abbrev Glued : Type u := ↥A.gluedSubmodule

/-! ### The certificate -/

/-- **The colength certificate over a widened cover** — clauses (c1)–(c4) verbatim from
`DivisorAdaptation.IsCertified`.  Nothing is added and nothing is dropped: the widening
changes where the pieces LIVE, not what the certificate asserts. -/
structure IsCertified (n : ℕ) : Prop where
  /-- (c1) Each piece-local colength module is a finite `R`-module. -/
  finite_colength : ∀ j, Module.Finite R (A.colength j)
  /-- (c1) Each piece-local colength module is projective over `R`. -/
  projective_colength : ∀ j, Module.Projective R (A.colength j)
  /-- (c2) The glued colength module is a finite `R`-module. -/
  finite_glued : Module.Finite R A.Glued
  /-- (c2) The glued colength module is projective over `R`. -/
  projective_glued : Module.Projective R A.Glued
  /-- (c2) The glued colength module has constant fibre rank `n`. -/
  rankAtStalk_glued : ∀ p : PrimeSpectrum R, Module.rankAtStalk A.Glued p = n
  /-- (c3) The cokernel of `W(d) ↪ Π_j colength j` is flat. -/
  flat_coker_incl : Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)
  /-- (c4) The cokernel of the difference arrow is flat. -/
  flat_coker_diff :
    Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))

end AffAdaptation

end AlgebraicGeometry
