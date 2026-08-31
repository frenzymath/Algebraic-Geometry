/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffAdaptation
import AlgebraicJacobian.Picard.DivSchemeFamilySide
import AlgebraicJacobian.Picard.DivisorFamilyThetaSections
import AlgebraicJacobian.Picard.DivisorDatumInverse
import AlgebraicJacobian.Picard.DivisorFamilyWindow

/-!
# The Θ-LAYER OVER A CHART-TYPED WIDENED COVER: a real absence, on an index that R2 empties

> **READ `isEmpty_chartTyping_of_straddling` (below) BEFORE THIS DOCSTRING'S ARGUMENT.**
> This module's original headline was "the widened carrier had no Θ-layer, and supplying it lets
> cert-r2's producer reach U2". **The first clause is true; the second is refuted, in Lean, in
> this file.** Every declaration here is indexed by a `ChartTyping C R π D`, and a cover with a
> straddling piece admits *none* — which is exactly the case protection `I-0492`'s widening
> exists to handle. So on those divisors every theorem below is vacuous, and the tree's only
> `ChartTyping` producer is the migration *from* the old chart-typed carrier. Refutation and its
> consequences: `isEmpty_chartTyping_of_straddling`; reviewer items `I-0779`/`I-0782`.
>
> What survives is worth keeping and is not the headline: the Θ-layer genuinely did not exist on
> `AffAdaptation` (measurements below, independently confirmed as `I-0780`), it ports cleanly, and
> it is now available for any cover that *does* carry a chart typing.

Protection `I-0492` widened the certificate carrier to arbitrary affine opens, and the
widened lane now produces a class from geometry
(`ThetaGeneratorSeed.divFamZarAff_of_swallowing_affineOpen`,
`Picard/DivisorFamilyAffSeedGate.lean`).  That producer still cannot feed U2, and the
reason recorded across five sessions — "U2 needs a certificate" — is **not** it.  The
argument below correctly identifies the *absence*; where it overreaches is in treating
supplying that absence as sufficient.

## The measurement that renames the seam

U2's consumer `DivRepChartFamily.IsChartClause` (`Picard/DivRepAffPullClause.lean:121`)
quantifies over `DivFamZar C (ChartRing i j) π g`, the *chart-typed* value.  There is no
map `DivFamZarAff → DivFamZar` and there cannot be (`informal/spec-dd-r.md` ADDENDUM 3 §2:
a straddling divisor has no chart-typed certificate).  So the only usable route is to
re-derive the ε-value facts on the widened carrier — and *that* is where the absence is:

> `divFamEps_eq_of_le` (`Picard/DivRepChartClassUnivQuot.lean`) needs projectivity and
> constant rank `g` of the **window quotient**.  On `DivFam` those are landed
> *unconditionally* (`Picard/DivSchemeFrameCover.lean:106`/`:117`) — but their only proof
> route is `windowQuotEquiv` (`Picard/DivisorFamilyWindow.lean:179`), whose target is
> `A.ThetaGlued a`, and `ThetaGlued` / `thetaGluedEval` / `thetaOvlUnit` /
> `thetaDeltaRight` / `ker_thetaGluedEval` are defined **only** on `DivisorAdaptation`
> (`Picard/DivisorFamilyTheta.lean`).

Cross-measured at HEAD: of the files mentioning `AffAdaptation`, **zero** define any theta
arrow.  `DivisorFamilyAffFraming.lean` is right that the ε-pair *statement* is
carrier-indifferent (both carriers have the same `eqns` field and `divisorWindow` reads
nothing else); the ε-pair **facts** are not, and statement was never separated from facts.

## Why this is a port and not new mathematics

The Θ-layer's chart-dependence is exactly **one `Bool` per piece**.  `FinCoverData`'s
version reads it off the `Sum` index (`pieces_inl_le` / `pieces_inr_le`), which is why it
looks chart-typed; but the side-uniform API it could have used already exists and is
consumed by some sixty files:

* `relThetaResSide` (`Picard/DivSchemeFamilySide.lean:155`) — the side component,
  restricted into any open below `relPinnedChart (side j)`;
* `relThetaSideUnit` (`:180`) — the matching unit of an ordered pair of sides, whose
  four-case split *is* `FinCoverData.thetaOvlUnit`'s;
* `relThetaResSide_matching` (`:194`) and `resHom_relThetaResSide` (`:172`).

Each needs only `piece ≤ relPinnedChart (side j)` — which is **verbatim** the field
`ChartTyping.piece_le` (`Picard/DivisorFamilyAffCover.lean:204`), the datum `I-0492`
clause 3 deliberately kept *separate* from the certificate clauses precisely so the
Θ-layer could have it without the certificate demanding it.

So this file is the missing face, built the way clause 3 intends: the twisting data is
indexed by a `ChartTyping`, and **no certificate clause and no locally-certified predicate
mentions it**.

## What this file does and does not claim

It builds the widened Θ-twisted glued module and its evaluation, and proves the kernel
bridge — left exactness, i.e. that the kernel is the *same* cover-independent vanishing
submodule the chart-typed layer produces.  That is the input `windowQuotEquiv`'s widened
analogue needs.

It does **not** prove surjectivity of the widened evaluation (the right-exactness heart,
`thetaGluedEval_surjective`'s analogue), and it does not produce a widened ε-value
identity: those consume the widened certificate's (c2) clause through a widened
`IsThetaPaired`, which is the next face and is *not* built here.  Read this as "the
ε-value facts are now *stateable* over the widened carrier", not as a gate cleared.

## Main declarations

* `AlgebraicGeometry.AffAdaptation.thetaOvlUnit` — the twisting unit of an ordered pair of
  widened pieces, read off a `ChartTyping` rather than a `Sum` index.
* `AlgebraicGeometry.AffAdaptation.thetaGluedSubmodule` / `ThetaGlued` — the Θ-twisted
  glued colength module over a widened cover, spelled as a kernel exactly as the
  chart-typed one.
* `AlgebraicGeometry.AffAdaptation.thetaGluedEval` — the evaluation
  `H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}`.
* `AlgebraicGeometry.AffAdaptation.ker_thetaGluedEval` — **the kernel bridge**: the widened
  kernel *is* the cover-independent vanishing submodule, hence literally the chart-typed
  layer's kernel.
* `AlgebraicGeometry.AffAdaptation.windowCarve` / `ker_windowCarve` / `windowQuotEquiv` — the
  bridge plugged in: the widened carve arrow's kernel is `divisorWindow d`, and (conditional on
  surjectivity, which is **not** proved here) the quotient of the free window by it is the
  widened `W(d)^{Θᵃ}`.  That last equivalence is the vehicle whose absence made the ε-value at a
  `DivFamZarAff` unstateable.

**A phrasing correction taken from a fresh-context review** (`I-0769`), because the wrong version
was in this docstring: `ker_thetaGluedEval` does **not** show "`divisorWindow` is the same on both
carriers" — `divisorWindow` takes only `d` and `hH1` and never mentioned a carrier, so that is
vacuous.  The content runs the other way: *the widened evaluation's kernel lands on that
already-fixed submodule.*
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
/- `ChartTyping` is stated with an `[IsAffineHom π]` binder, which `[IsFinite π]` already
supplies — the `overlappingInstances` linter reports the pair, so only `IsFinite` is taken
here and `IsAffineHom` is found by synthesis. -/
variable {π : C.left ⟶ P1 k} [IsFinite π]

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d) (τ : ChartTyping C R π D) (a : ℕ)

/-! ## The twisting unit, read off a chart typing

`FinCoverData.thetaOvlUnit` (`Picard/DivisorFamilyTheta.lean:149`) splits on the `Sum`
index and produces `1`, the cocycle, or its inverse.  That is `relThetaSideUnit` at the two
pieces' sides, and here the sides come from `τ` rather than from the index type — which is
the whole difference between the two layers. -/

/-- The pinned chart assigned to a widened piece agrees with `relPinnedChart` on the nose
(`pinnedChartOfSide` is `bif`, `relPinnedChart` is a match on the same `Bool`). -/
lemma pinnedChartOfSide_eq (b : Bool) :
    pinnedChartOfSide C R π b = relPinnedChart C R π b := by
  cases b <;> rfl

/-- The piece is contained in the pinned chart of its assigned side, in the
`relPinnedChart` spelling the side-uniform Θ API consumes. -/
lemma piece_le_relPinnedChart (j : D.index) :
    D.pieces j ≤ relPinnedChart C R π (τ.side j) :=
  (pinnedChartOfSide_eq (C := C) (R := R) (π := π) (τ.side j)) ▸ τ.piece_le j

/-- An overlap of two widened pieces sits below both assigned pinned charts. -/
lemma pieces_inf_le_relPinnedChart_inf (i j : D.index) :
    D.pieces i ⊓ D.pieces j
      ≤ relPinnedChart C R π (τ.side i) ⊓ relPinnedChart C R π (τ.side j) :=
  inf_le_inf (piece_le_relPinnedChart τ i) (piece_le_relPinnedChart τ j)

/-- **The Θ twisting unit of an ordered pair of widened pieces**: the side matching unit
of the two assigned sides, restricted to the overlap.  This replaces
`FinCoverData.thetaOvlUnit`'s four-case `Sum` split by one application of
`relThetaSideUnit` — the cases are the same cases, and the `Bool`s now come from the
separate `ChartTyping` datum rather than from the index type. -/
noncomputable def thetaOvlUnit (i j : D.index) :
    Γ(relCurve C R, D.pieces i ⊓ D.pieces j)ˣ :=
  relThetaSideUnit a (τ.side i) (τ.side j) (pieces_inf_le_relPinnedChart_inf τ i j)

/-- **The side matching unit at exponent `0` is trivial**, for any pair of sides.  The
side-uniform form of `FinCoverData.thetaOvlUnit_zero` (`Picard/DivisorDatumInverse.lean:155`),
whose four `Sum` cases are these four `Bool` cases.

The split is over *variable* `Bool`s here (not over `τ.side j` at a use site), which is what
keeps it out of the dependent-motive trap. -/
lemma relThetaSideUnit_zero (b b' : Bool) {W : (relCurve C R).Opens}
    (hW : W ≤ relPinnedChart C R π b ⊓ relPinnedChart C R π b') :
    relThetaSideUnit (C := C) (R := R) (π := π) 0 b b' hW = 1 := by
  cases b <;> cases b'
  · rfl
  · rw [show relThetaSideUnit (C := C) (R := R) (π := π) 0 false true hW
        = (relCurve C R).unitsRestrict hW (relThetaCocycle C R π 0) from rfl,
      relThetaCocycle_zero, map_one]
  · rw [show relThetaSideUnit (C := C) (R := R) (π := π) 0 true false hW
        = ((relCurve C R).unitsRestrict
            (le_inf (hW.trans inf_le_right) (hW.trans inf_le_left))
            (relThetaCocycle C R π 0))⁻¹ from rfl,
      relThetaCocycle_zero, map_one, inv_one]
  · rfl

/-- The widened twisting unit is trivial at exponent `0`. -/
lemma thetaOvlUnit_zero (i j : D.index) : thetaOvlUnit τ 0 i j = 1 :=
  relThetaSideUnit_zero (τ.side i) (τ.side j) (pieces_inf_le_relPinnedChart_inf τ i j)

/-! ## The Θ-twisted glued colength module -/

/-- **The Θ-twisted right overlap arrow** over a widened cover: restrict the `p.2`
component to each overlap and multiply by the twisting unit of the pair.  Verbatim
`DivisorAdaptation.thetaDeltaRight` (`Picard/DivisorFamilyTheta.lean:203`) with
`thetaOvlUnit` read off `τ`. -/
noncomputable def thetaDeltaRight : A.chartProd →ₗ[R] A.ovlProd :=
  LinearMap.pi (fun p : D.index × D.index =>
    LinearMap.mulLeft R (Ideal.Quotient.mk (A.ovlIdeal p.1 p.2)
        ((thetaOvlUnit τ a p.1 p.2 :
          Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2)ˣ) :
          Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2))) ∘ₗ
      (A.toOvlRight p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.2)

/-- **The Θ-twisted glued colength module `W(d)^{Θᵃ}` over a widened cover**, spelled as a
kernel so the `FlatCokernel` base-change shapes apply exactly as chart-typed. -/
noncomputable def thetaGluedSubmodule : Submodule R A.chartProd :=
  LinearMap.ker (A.deltaLeft - thetaDeltaRight A τ a)

/-- The twisted-equalizer description of the widened `W(d)^{Θᵃ}`. -/
lemma mem_thetaGluedSubmodule_iff (s : A.chartProd) :
    s ∈ thetaGluedSubmodule A τ a ↔ ∀ p : D.index × D.index,
      A.toOvlLeft p.1 p.2 (s p.1)
        = Ideal.Quotient.mk (A.ovlIdeal p.1 p.2)
            ((thetaOvlUnit τ a p.1 p.2 :
              Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2)ˣ) :
              Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2))
          * A.toOvlRight p.1 p.2 (s p.2) := by
  simp only [thetaGluedSubmodule, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    funext_iff, deltaLeft, thetaDeltaRight, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply,
    LinearMap.mulLeft_apply]

/-- The widened Θ-twisted glued colength module, as a type. -/
noncomputable abbrev ThetaGlued : Type u := ↥(thetaGluedSubmodule A τ a)

/-! ## The evaluation `H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}` -/

/-- **The germ of a widened equation spans the stalk ideal of the family.**  The widened
counterpart of `DivisorAdaptation.germ_eqn_span_eq_stalkIdeal`
(`Picard/DivisorFamilyTheta.lean:322`); its proof is the same one, and it ports because
`eqn_rel` is stated pointwise on both carriers. -/
theorem germ_eqn_span_eq_stalkIdeal (j : D.index) {z : relCurve C R}
    (hz : z ∈ D.pieces j) :
    Ideal.span {((relCurve C R).presheaf.germ (D.pieces j) z hz).hom (A.eqn j)}
      = d.stalkIdeal z := by
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
  rw [hgerm, Ideal.span_singleton_mul_left_unit (u.isUnit.map
    ((relCurve C R).presheaf.germ (D.pieces j ⊓ d.cover.opens z) z hzW).hom)]
  exact d.germ_eqn_span_eq z z (d.cover.mem_opens z)

/-- The per-piece evaluation of a global theta section: take the side component assigned to
the piece, restrict it, and reduce mod `(f_j)`.  Where the chart-typed version splits on the
`Sum` index (`DivisorAdaptation.thetaPieceEval`), this is one application of
`relThetaResSide` at `τ.side j`. -/
noncomputable def thetaPieceEval (j : D.index) :
    relThetaSections C R π a →ₗ[R] A.colength j :=
  (Ideal.Quotient.mkₐ R (Ideal.span {A.eqn j})).toLinearMap ∘ₗ
    relThetaResSide a (τ.side j) (piece_le_relPinnedChart τ j)

/-- **The section evaluation into the widened chart product.** -/
noncomputable def thetaEval : relThetaSections C R π a →ₗ[R] A.chartProd :=
  LinearMap.pi (thetaPieceEval A τ a)

@[simp]
lemma thetaEval_apply (x : relThetaSections C R π a) (j : D.index) :
    thetaEval A τ a x j
      = Ideal.Quotient.mk (Ideal.span {A.eqn j})
          (relThetaResSide a (τ.side j) (piece_le_relPinnedChart τ j) x) := rfl

/-- The left overlap arrow on a residue class: restrict into the overlap, then reduce.

Stated here because both widened forms exist only as `private` lemmas of
`Picard/DivisorFamilyAffCert.lean` (`toOvlLeft_mk'`/`toOvlRight_mk'`) — and both are `rfl`,
so this is a name, not a proof (inbox `I-0712`: `private` hides the name, not the argument).
The `resHom` spelling is the one the matching law below rewrites along. -/
lemma toOvlLeft_mk (i j : D.index) (s : Γ(relCurve C R, D.pieces i)) :
    A.toOvlLeft i j (Ideal.Quotient.mk (Ideal.span {A.eqn i}) s)
      = Ideal.Quotient.mk (A.ovlIdeal i j)
          ((relCurve C R).resHom inf_le_left s) :=
  rfl

/-- The right overlap arrow on a residue class. -/
lemma toOvlRight_mk (i j : D.index) (s : Γ(relCurve C R, D.pieces j)) :
    A.toOvlRight i j (Ideal.Quotient.mk (Ideal.span {A.eqn j}) s)
      = Ideal.Quotient.mk (A.ovlIdeal i j)
          ((relCurve C R).resHom inf_le_right s) :=
  rfl

/-- **The evaluation lands in the widened Θ-twisted glued module**: on each pairwise
overlap, the global matching of the two side components through the theta cocycle *is* the
Θ-twisted matching of the colengths.

Where the chart-typed proof (`DivisorAdaptation.thetaEval_mem`) runs a four-case `Sum`
split and calls `relThetaSections_matching` twice with hand-built containments, this is a
single application of `relThetaResSide_matching` — the side-uniform form of the same
matching law.  That collapse is the concrete payoff of taking the sides from a
`ChartTyping` rather than from the index type. -/
theorem thetaEval_mem (x : relThetaSections C R π a) :
    thetaEval A τ a x ∈ thetaGluedSubmodule A τ a := by
  rw [mem_thetaGluedSubmodule_iff]
  rintro ⟨i, j⟩
  rw [thetaEval_apply, thetaEval_apply, toOvlLeft_mk, toOvlRight_mk, ← map_mul]
  refine congrArg _ ?_
  -- both sides restrict the SAME section into the overlap; the side matching law compares
  -- the two assigned sides there, and `thetaOvlUnit` is by definition its unit
  rw [resHom_relThetaResSide (b := τ.side i), resHom_relThetaResSide (b := τ.side j)]
  exact relThetaResSide_matching a (τ.side i) (τ.side j)
    (pieces_inf_le_relPinnedChart_inf τ i j) x

/-- **The evaluation `H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}` over a widened cover.** -/
noncomputable def thetaGluedEval :
    relThetaSections C R π a →ₗ[R] ThetaGlued A τ a :=
  LinearMap.codRestrict (thetaGluedSubmodule A τ a) (thetaEval A τ a) (thetaEval_mem A τ a)

lemma thetaGluedEval_coe (x : relThetaSections C R π a) :
    (thetaGluedEval A τ a x : A.chartProd) = thetaEval A τ a x := rfl

/-- The kernel of the corestricted evaluation is the kernel of the evaluation. -/
lemma ker_thetaGluedEval_eq_ker :
    LinearMap.ker (thetaGluedEval A τ a) = LinearMap.ker (thetaEval A τ a) :=
  LinearMap.ker_codRestrict _ _ _

/-! ## The equalizer algebra and the unit-twisted glued modules

Everything in this section is **cover-generic**: it names `D.pieces`, `A.ovlIdeal`,
`A.toOvlLeft/Right` and nothing about a chart, so it ports from
`Picard/DivisorFamilyThetaRank.lean:77-231` with `AffAdaptation` in place of
`DivisorAdaptation` and no other change.  It is the substrate a widened `IsThetaPaired` —
the honest cohomological residue of the (c2)-transport — is stated over. -/

/-- **The equalizer algebra `A_D` over a widened cover**: the glued colength module is an
`R`-subalgebra of the piece product, because the overlap-restriction arrows are algebra
maps. -/
noncomputable def gluedSubalgebra : Subalgebra R A.chartProd where
  carrier := A.gluedSubmodule
  add_mem' := fun hx hy => A.gluedSubmodule.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    rw [SetLike.mem_coe, mem_gluedSubmodule_iff] at hx hy ⊢
    intro p
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, map_mul, hx p, hy p]
  one_mem' := by
    rw [SetLike.mem_coe, mem_gluedSubmodule_iff]
    intro p
    rw [Pi.one_apply, Pi.one_apply, map_one, map_one]
  algebraMap_mem' := by
    intro r
    rw [SetLike.mem_coe, mem_gluedSubmodule_iff]
    intro p
    rw [Pi.algebraMap_apply, Pi.algebraMap_apply, AlgHom.commutes, AlgHom.commutes]

lemma mem_gluedSubalgebra_iff {x : A.chartProd} :
    x ∈ gluedSubalgebra A ↔ x ∈ A.gluedSubmodule :=
  Iff.rfl

/-- The equalizer algebra and the glued module have the same carrier, `R`-linearly. -/
noncomputable def gluedSubalgebraEquiv : ↥(gluedSubalgebra A) ≃ₗ[R] A.Glued where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

section UnitTwist

variable (u v : ∀ i j : D.index, Γ(relCurve C R, D.pieces i ⊓ D.pieces j)ˣ)

/-- The `u`-twisted right overlap arrow for an arbitrary unit family on the piece
overlaps. -/
noncomputable def unitDeltaRight : A.chartProd →ₗ[R] A.ovlProd :=
  LinearMap.pi (fun p : D.index × D.index =>
    LinearMap.mulLeft R (Ideal.Quotient.mk (A.ovlIdeal p.1 p.2)
        ((u p.1 p.2 : Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2)ˣ) :
          Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2))) ∘ₗ
      (A.toOvlRight p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.2)

/-- The `u`-twisted glued colength module. -/
noncomputable def unitGluedSubmodule : Submodule R A.chartProd :=
  LinearMap.ker (A.deltaLeft - unitDeltaRight A u)

/-- The `u`-twisted equalizer description. -/
lemma mem_unitGluedSubmodule_iff (s : A.chartProd) :
    s ∈ unitGluedSubmodule A u ↔ ∀ p : D.index × D.index,
      A.toOvlLeft p.1 p.2 (s p.1)
        = Ideal.Quotient.mk (A.ovlIdeal p.1 p.2)
            ((u p.1 p.2 : Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2)ˣ) :
              Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2))
          * A.toOvlRight p.1 p.2 (s p.2) := by
  simp only [unitGluedSubmodule, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    funext_iff, deltaLeft, unitDeltaRight, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply,
    LinearMap.mulLeft_apply]

/-- At the trivial unit family, the twisted glued module is the glued module. -/
lemma unitGluedSubmodule_one : unitGluedSubmodule A 1 = A.gluedSubmodule := by
  ext s
  rw [mem_unitGluedSubmodule_iff, mem_gluedSubmodule_iff]
  refine forall_congr' fun p => ?_
  rw [Pi.one_apply, Pi.one_apply, Units.val_one, map_one, one_mul]

/-- At the Θ unit family, the twisted glued module is the widened `W(d)^{Θᵃ}` — by `rfl`,
exactly as chart-typed, which is what lets the pairing layer be stated over `thetaOvlUnit`
without a transport. -/
lemma unitGluedSubmodule_thetaOvlUnit :
    unitGluedSubmodule A (thetaOvlUnit τ a) = thetaGluedSubmodule A τ a :=
  rfl

variable {u v}

/-- **Twists multiply**: the componentwise product of a `u`-twisted and a `v`-twisted glued
family is `(u * v)`-twisted. -/
theorem mul_mem_unitGluedSubmodule {s t : A.chartProd}
    (hs : s ∈ unitGluedSubmodule A u) (ht : t ∈ unitGluedSubmodule A v) :
    s * t ∈ unitGluedSubmodule A (u * v) := by
  rw [mem_unitGluedSubmodule_iff] at hs ht ⊢
  intro p
  have h1 : (s * t) p.1 = s p.1 * t p.1 := rfl
  have h2 : (s * t) p.2 = s p.2 * t p.2 := rfl
  have h3 : (((u * v) p.1 p.2 : Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2)ˣ) :
      Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2))
      = ((u p.1 p.2 : Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2)ˣ) :
          Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2))
        * ((v p.1 p.2 : Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2)ˣ) :
          Γ(relCurve C R, D.pieces p.1 ⊓ D.pieces p.2)) := rfl
  rw [h1, h2, h3, map_mul, map_mul, map_mul, hs p, ht p]
  ring

variable (u) in
/-- The `u`-twisted glued module as a module over the equalizer algebra `A_D`. -/
noncomputable def unitGluedOver : Submodule ↥(gluedSubalgebra A) A.chartProd where
  carrier := unitGluedSubmodule A u
  add_mem' := fun hx hy => (unitGluedSubmodule A u).add_mem hx hy
  zero_mem' := (unitGluedSubmodule A u).zero_mem
  smul_mem' := by
    intro c x hx
    have hc : (c : A.chartProd) ∈ unitGluedSubmodule A 1 := by
      rw [unitGluedSubmodule_one]
      exact c.2
    have hmul := mul_mem_unitGluedSubmodule A hc hx
    rw [one_mul] at hmul
    have hsmul : c • x = (c : A.chartProd) * x := Algebra.smul_def c x
    rw [SetLike.mem_coe, hsmul]
    exact hmul

lemma mem_unitGluedOver_iff {x : A.chartProd} :
    x ∈ unitGluedOver A u ↔ x ∈ unitGluedSubmodule A u :=
  Iff.rfl

end UnitTwist

/-! ## The manufactured sections, side-uniformly

`DivisorAdaptation.thetaSectionFst/Snd` (`Picard/DivisorFamilyThetaSections.lean:271/:278`)
are the two sections `σ = (t₀ᵃ; 1)`, `τ = (1; t₁ᵃ)` whose pairing discharges
`IsThetaPaired` chart-typed.  They read the `Sum` index to decide *which side's coordinate
to use on this piece* — and that decision is again a `Bool`, so the side-uniform coordinate
below carries them to the widened cover. -/

section Sections

/-- **The side-uniform coordinate power** `t_bᵃ` on the pinned chart of side `b`: `t₀ᵃ` on
`false`, `t₁ᵃ` on `true`.  The `Bool`-indexed form of `relFiberCoordPow` /
`relFiberCoordOnePow`, which the widened sections need for the same reason
`relThetaResSide` was needed for the twisting unit. -/
noncomputable def relFiberCoordSidePow (n : ℕ) : ∀ b : Bool,
    Γ(relCurve C R, relPinnedChart C R π b)
  | false => relFiberCoordPow C R π n
  | true => relFiberCoordOnePow C R π n

@[simp]
lemma relFiberCoordSidePow_false (n : ℕ) :
    relFiberCoordSidePow (C := C) (R := R) (π := π) n false
      = relFiberCoordPow C R π n := rfl

@[simp]
lemma relFiberCoordSidePow_true (n : ℕ) :
    relFiberCoordSidePow (C := C) (R := R) (π := π) n true
      = relFiberCoordOnePow C R π n := rfl

/-- **The widened manufactured section at side `b`**: on each piece, the coordinate power of
its *assigned* side when that side is `b`, and `1` otherwise.

At `b = false` this is `thetaSectionFst` and at `b = true` it is `thetaSectionSnd`, with the
`Sum`-match replaced by a `Bool` comparison against `τ.side j`. -/
noncomputable def thetaSectionSide (b : Bool) : A.chartProd := fun j =>
  if h : τ.side j = b then
    Ideal.Quotient.mk (Ideal.span {A.eqn j})
      ((relCurve C R).resHom (piece_le_relPinnedChart τ j)
        (h ▸ relFiberCoordSidePow (C := C) (R := R) (π := π) a (τ.side j)))
  else 1

@[simp]
lemma thetaSectionSide_of_side_eq {b : Bool} {j : D.index} (h : τ.side j = b) :
    thetaSectionSide A τ a b j
      = Ideal.Quotient.mk (Ideal.span {A.eqn j})
          ((relCurve C R).resHom (piece_le_relPinnedChart τ j)
            (h ▸ relFiberCoordSidePow (C := C) (R := R) (π := π) a (τ.side j))) :=
  dif_pos h

@[simp]
lemma thetaSectionSide_of_side_ne {b : Bool} {j : D.index} (h : τ.side j ≠ b) :
    thetaSectionSide A τ a b j = 1 :=
  dif_neg h

end Sections

/-! ## The pairing input, widened

`IsThetaPaired` is the honest cohomological residue of the (c2)-transport: it is what
`finite/projective/rankAtStalk_thetaGlued` consume, and therefore what a widened
`divisorWindowGr` needs beyond the left-exactness bridge below.  The *statement* and its
automatic half port verbatim; the pairing itself is **not** proved here (chart-typed it is
discharged by manufactured sections through the pinned trivializations, which is where the
two charts genuinely enter). -/

section Pairing

/-- The widened `W(d)^{Θᵃ}` as an `A_D`-submodule. -/
noncomputable def thetaSpan : Submodule ↥(gluedSubalgebra A) A.chartProd :=
  unitGluedOver A (thetaOvlUnit τ a)

/-- The widened inverse-twisted glued module as an `A_D`-submodule. -/
noncomputable def thetaInvSpan : Submodule ↥(gluedSubalgebra A) A.chartProd :=
  unitGluedOver A (thetaOvlUnit τ a)⁻¹

lemma mem_thetaSpan_iff {x : A.chartProd} :
    x ∈ thetaSpan A τ a ↔ x ∈ thetaGluedSubmodule A τ a :=
  Iff.rfl

lemma mem_thetaInvSpan_iff {x : A.chartProd} :
    x ∈ thetaInvSpan A τ a ↔ x ∈ unitGluedSubmodule A (thetaOvlUnit τ a)⁻¹ :=
  Iff.rfl

/-- Products of `Θᵃ`- and `Θ⁻ᵃ`-sections are untwisted: the pairing lands in the equalizer
algebra.  This is the automatic half, and it ports verbatim. -/
theorem thetaSpan_mul_thetaInvSpan_le_one :
    thetaSpan A τ a * thetaInvSpan A τ a ≤ 1 := by
  rw [Submodule.mul_le]
  intro s hs t ht
  have hmul := mul_mem_unitGluedSubmodule A
    (mem_thetaSpan_iff A τ a |>.mp hs) (mem_thetaInvSpan_iff A τ a |>.mp ht)
  rw [mul_inv_cancel, unitGluedSubmodule_one] at hmul
  rw [Submodule.one_eq_range]
  exact ⟨⟨s * t, hmul⟩, rfl⟩

/-- **The widened pairing input**: the `Θᵃ`- and `Θ⁻ᵃ`-twisted glued modules pair onto the
full equalizer algebra.  Named so the remaining (c2)-transport obligation over the widened
carrier is a *statement in the tree* rather than a gap in prose.

**This is not proved here, and the reason is precise.** Chart-typed, it is discharged by
`isThetaPaired_of_sectionWitness` from two manufactured global sections `σ = (t₀ᵃ, 1)`,
`τ = (1, t₁ᵃ)` read through the **pinned chart trivializations** — that is where the fixed
pair genuinely enters the Θ-layer, and nothing above needed it.  A widened witness must
produce the analogous sections from the `ChartTyping` instead; whether the per-piece
coordinates suffice is the open question. -/
def IsThetaPaired : Prop :=
  thetaSpan A τ a * thetaInvSpan A τ a = 1

/-- The widened pairing input reduces to hitting `1`. -/
theorem isThetaPaired_of_one_mem
    (h : (1 : A.chartProd) ∈ thetaSpan A τ a * thetaInvSpan A τ a) :
    IsThetaPaired A τ a := by
  refine le_antisymm (thetaSpan_mul_thetaInvSpan_le_one A τ a) ?_
  rw [Submodule.one_eq_span]
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr h)

/-! ### The satisfiability probe on `IsThetaPaired`

`IsThetaPaired` is a `Prop` this file defines and does not prove, so per the standing
discipline it owes **two** probes.  "Not silently stronger" is discharged by
`thetaSpan_mul_thetaInvSpan_le_one`: the automatic half is landed, so the content is exactly
the reverse inclusion, the same content as chart-typed.

The mirror risk is **unsatisfiability** — a `Prop` no widened cover can ever satisfy would make
every consumer of it a vacuous theorem, which passes every `sorry` census and axiom probe.  The
probe below rules that out with an unconditional witness, so the residue is genuinely open
rather than false. -/

/-- **THE SATISFIABILITY PROBE, DISCHARGED at the trivial twist.**  At `a = 0` the theta
cocycle is `1`, so every `thetaOvlUnit` is `1`, both spans are the equalizer algebra itself, and
the pairing holds **unconditionally** — for every widened cover, every adaptation and every
chart typing.

This does not make the pairing easy at `a > 0`: the content there is the manufactured sections,
which is the open obligation. What it establishes is that `IsThetaPaired` is *satisfiable*, i.e.
that the widened statement is not a reduction to a false hypothesis. -/
theorem isThetaPaired_zero : IsThetaPaired A τ 0 := by
  refine isThetaPaired_of_one_mem A τ 0 ?_
  -- at the trivial twist both spans contain `1`
  have hone : (1 : A.chartProd) ∈ unitGluedSubmodule A (thetaOvlUnit τ 0) := by
    rw [mem_unitGluedSubmodule_iff]
    intro p
    rw [thetaOvlUnit_zero τ p.1 p.2]
    rw [Pi.one_apply, Pi.one_apply, map_one, map_one, Units.val_one, map_one, mul_one]
  have hinvunit : (thetaOvlUnit τ 0)⁻¹
      = (thetaOvlUnit τ 0 : ∀ i j : D.index,
          Γ(relCurve C R, D.pieces i ⊓ D.pieces j)ˣ) := by
    funext i j
    rw [Pi.inv_apply, Pi.inv_apply, thetaOvlUnit_zero τ i j, inv_one]
  have hinv : (1 : A.chartProd) ∈ unitGluedSubmodule A (thetaOvlUnit τ 0)⁻¹ := by
    rw [hinvunit]; exact hone
  have := Submodule.mul_mem_mul (mem_thetaSpan_iff A τ 0 |>.mpr hone)
    (mem_thetaInvSpan_iff A τ 0 |>.mpr hinv)
  rwa [one_mul] at this

end Pairing

/-! ## THE LIMIT OF THIS ENTIRE FILE, PROVED RATHER THAN CAVEATED

A fresh-context review (inbox `I-0779`) refuted this module's headline, and the refutation is
three lines, so it is landed here rather than left in prose.  **Every declaration in this file is
indexed by a `ChartTyping`, and a cover with a straddling piece admits none.** -/

section Emptiness

/-- **NO `ChartTyping` EXISTS ON A COVER WITH A STRADDLING PIECE.**  If one piece contains a
point outside `V₀` *and* a point outside `V₁`, then `ChartTyping C R π D` is empty: the piece is
assigned some side, `piece_le` puts the *whole* piece inside that pinned chart, and each witness
contradicts one of the two options.

**This is the honest limit of the whole module, and it cuts against the headline.**  The claim
this file was built on is that the widened carrier lacked a Θ-layer and that supplying it lets
cert-r2's producer reach U2.  The first half stands (see the module docstring's measurements,
independently confirmed as `I-0780`).  The second half does **not**: cert-r2's producer runs
through a cover in which the support sits inside **one** piece `W`
(`exists_affCoverData_swallowedBy`), while the straddling hypotheses of
`forall_not_isCertified_of_straddling` (`Picard/DivisorFamilyAffStrict.lean:127`) say precisely
that the support has a point outside `V₀` and a point outside `V₁` — and both then lie in `W`.
So on exactly the divisors protection `I-0492`'s widening exists to handle, this file's index
type is uninhabited and every theorem in it is vacuous.

**Compounding it** (`I-0782`): the tree's only producer of a `ChartTyping` is
`FinCoverData.toChartTyping` (`Picard/DivisorFamilyAffCover.lean:255`), the migration *from* the
old chart-typed carrier. So every instantiation available today factors through `FinCoverData`,
i.e. this layer currently computes on the covers the chart-typed layer already handled,
re-indexed.

**What the module docstring got wrong, and it is a real methodological error.** `I-0492` clause 3
keeps `ChartTyping` separate from the certificate clauses so that a certificate never *requires*
a chart typing. That is a statement about what is **permitted**, and I read it as evidence about
what is **inhabited**. Those are different questions, and only the second one decides whether a
layer indexed by that datum is usable. The recorded shape is `isolating-a-residue-as-a-class`:
check inhabitation of an index before pricing anything stated over it. -/
theorem isEmpty_chartTyping_of_straddling (D : AffCoverData C R) (j : D.index)
    {x y : relCurve C R} (hxj : x ∈ D.pieces j) (hyj : y ∈ D.pieces j)
    (hx₀ : x ∉ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R)))
    (hy₁ : y ∉ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R))) :
    IsEmpty (ChartTyping C R π D) := by
  refine ⟨fun τ => ?_⟩
  have h := piece_le_relPinnedChart (π := π) τ j
  cases hb : τ.side j with
  | false => rw [hb] at h; exact hx₀ (h hxj)
  | true => rw [hb] at h; exact hy₁ (h hyj)

end Emptiness

/-! ## The kernel bridge — left exactness, and the seam with the chart-typed layer -/

/-- The germ of a side component through a piece is the germ taken in the pinned chart:
`relThetaResSide` is a restriction, so `germ_res_apply` moves the germ up. -/
lemma germ_relThetaResSide_eq (x : relThetaSections C R π a) (b : Bool)
    {W W' : (relCurve C R).Opens} (hW : W ≤ relPinnedChart C R π b) (hW' : W' ≤ W)
    {z : relCurve C R} (hz : z ∈ W') :
    ((relCurve C R).presheaf.germ W' z hz).hom (relThetaResSide a b (hW'.trans hW) x)
      = ((relCurve C R).presheaf.germ W z (hW' hz)).hom (relThetaResSide a b hW x) := by
  rw [← resHom_relThetaResSide a b hW hW' x]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- **The two clauses of `vanishingSubmodule`, read side-uniformly.**  Its statement is a
conjunction over the two pinned charts; this packages it as one statement over an arbitrary
`Bool`, which is what a proof indexed by `τ.side j` needs.

Factored out because `cases` on `τ.side j` at the use site fails with *"result is not type
correct"*: the `Bool` occurs inside the germ's own open, so the motive is dependent and
`subst` does not rescue it either (memory `cases-on-a-bool-a-type-mentions`).  Splitting
over a *variable* `Bool` in a separate lemma is the fix. -/
lemma germ_val_mem_stalkIdeal_of_forall_side (x : relThetaSections C R π a)
    (h : (∀ (z : relCurve C R) (hz : z ∈ (⊤ : (relCurve C R).Opens) ⊓
          (relCover C R (fiberTwoCover π)).V₀),
        ((relCurve C R).presheaf.germ ((⊤ : (relCurve C R).Opens) ⊓
          (relCover C R (fiberTwoCover π)).V₀) z hz).hom x.val.1 ∈ d.stalkIdeal z) ∧
      ∀ (z : relCurve C R) (hz : z ∈ (⊤ : (relCurve C R).Opens) ⊓
          (relCover C R (fiberTwoCover π)).V₁),
        ((relCurve C R).presheaf.germ ((⊤ : (relCurve C R).Opens) ⊓
          (relCover C R (fiberTwoCover π)).V₁) z hz).hom x.val.2 ∈ d.stalkIdeal z)
    (b : Bool) {z : relCurve C R}
    (hz : z ∈ (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b) :
    ((relCurve C R).presheaf.germ ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b)
        z hz).hom (relThetaResSide a b inf_le_right x) ∈ d.stalkIdeal z := by
  -- `simpa` discharges the identity restriction `relThetaResSide b inf_le_right x = x.val.b`
  -- (`relThetaResSide_false`/`_true` plus `presheaf.map_id`), which is the only gap.
  cases b with
  | false => simpa using h.1 z hz
  | true => simpa using h.2 z hz

/-- **The germ of a side component of a killed section lies in `d`'s stalk ideal**, at a
point of the piece `j`, read on the overlap of that piece with the pinned chart `b`.

The proof follows `ThetaGeneratorSeed.le_vanishingSubmodule` (`Picard/DivSchemeFamily.lean:397`)
step for step — that is the template, and it is what makes this a port: it already works on
`D.piece z ⊓ relPinnedChart b` with the side taken from a `Bool`, so the only change is that
the piece comes from the joint cover and its side from `τ` rather than from the seed. -/
lemma germ_val_mem_stalkIdeal_of_thetaEval_eq_zero {x : relThetaSections C R π a}
    (hker : ∀ j, thetaEval A τ a x j = 0) (b : Bool) (j : D.index)
    {z : relCurve C R} (hzj : z ∈ D.pieces j)
    (hz : z ∈ (⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b) :
    ((relCurve C R).presheaf.germ ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b)
        z hz).hom (Bool.rec x.val.1 x.val.2 b) ∈ d.stalkIdeal z := by
  have hzW : z ∈ D.pieces j ⊓ relPinnedChart C R π b := ⟨hzj, hz.2⟩
  -- the matching law comparing the pinned side `b` with the piece's assigned side
  have hmatch := relThetaResSide_matching a b (τ.side j) (le_inf
    (inf_le_right : D.pieces j ⊓ relPinnedChart C R π b ≤ _)
    (inf_le_left.trans (piece_le_relPinnedChart τ j))) x
  -- the assigned-side germ lies in the stalk ideal: the evaluation vanishes on the piece
  have hgermside : ((relCurve C R).presheaf.germ
      (D.pieces j ⊓ relPinnedChart C R π b) z hzW).hom
        (relThetaResSide a (τ.side j)
          ((le_inf (inf_le_right : D.pieces j ⊓ relPinnedChart C R π b ≤ _)
            (inf_le_left.trans (piece_le_relPinnedChart τ j))).trans inf_le_right) x)
      ∈ d.stalkIdeal z := by
    rw [show relThetaResSide a (τ.side j)
        ((le_inf (inf_le_right : D.pieces j ⊓ relPinnedChart C R π b ≤ _)
          (inf_le_left.trans (piece_le_relPinnedChart τ j))).trans inf_le_right) x
        = (relCurve C R).resHom (inf_le_left : D.pieces j ⊓ relPinnedChart C R π b
            ≤ D.pieces j)
          (relThetaResSide a (τ.side j) (piece_le_relPinnedChart τ j) x) from
      (resHom_relThetaResSide a (τ.side j) (piece_le_relPinnedChart τ j) inf_le_left x).symm]
    rw [show ((relCurve C R).presheaf.germ
        (D.pieces j ⊓ relPinnedChart C R π b) z hzW).hom
          ((relCurve C R).resHom (inf_le_left : D.pieces j ⊓ relPinnedChart C R π b
            ≤ D.pieces j)
            (relThetaResSide a (τ.side j) (piece_le_relPinnedChart τ j) x))
        = ((relCurve C R).presheaf.germ (D.pieces j) z hzj).hom
          (relThetaResSide a (τ.side j) (piece_le_relPinnedChart τ j) x) from
      TopCat.Presheaf.germ_res_apply _ _ _ _ _]
    -- vanishing of the evaluation at `j`: the side component is a multiple of `A.eqn j`
    have hmem : relThetaResSide a (τ.side j) (piece_le_relPinnedChart τ j) x
        ∈ Ideal.span {A.eqn j} := by
      have h := hker j
      rw [thetaEval_apply, Ideal.Quotient.eq_zero_iff_mem] at h
      exact h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
    have hgerm := congrArg ((relCurve C R).presheaf.germ (D.pieces j) z hzj).hom hc
    rw [map_mul] at hgerm
    rw [← germ_eqn_span_eq_stalkIdeal A j hzj, hgerm]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  -- transport across the side unit
  have hkey := congrArg ((relCurve C R).presheaf.germ
    (D.pieces j ⊓ relPinnedChart C R π b) z hzW).hom hmatch
  rw [map_mul] at hkey
  have hgermb : ((relCurve C R).presheaf.germ
      (D.pieces j ⊓ relPinnedChart C R π b) z hzW).hom
        (relThetaResSide a b ((le_inf
          (inf_le_right : D.pieces j ⊓ relPinnedChart C R π b ≤ _)
          (inf_le_left.trans (piece_le_relPinnedChart τ j))).trans inf_le_left) x)
      = ((relCurve C R).presheaf.germ
          ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π b) z hz).hom
        (Bool.rec x.val.1 x.val.2 b) := by
    cases b with
    | false =>
        rw [relThetaResSide_false]
        exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    | true =>
        rw [relThetaResSide_true]
        exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [hgermb] at hkey
  rw [hkey]
  exact Ideal.mul_mem_left _ _ hgermside

/-- **THE KERNEL BRIDGE OVER THE WIDENED CARRIER** (left exactness of the Θ-twisted
section sequence): the kernel of the widened Θ-twisted colength evaluation is exactly the
**cover-independent** vanishing submodule of the family — the DD-4 spelling of
`H⁰(𝒪(Θᵃ − d)) = ker (H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ})`.

This is the statement that makes the widening *usable* rather than merely well-formed. Its
right-hand side is **literally the same term** as in the chart-typed
`DivisorAdaptation.ker_thetaGluedEval` (`Picard/DivisorFamilyTheta.lean:350`) — the
vanishing submodule mentions `d` and the two pinned charts and no cover at all — and both
kernels live in the same `relThetaSections C R π a`, so the widened kernel *equals* the
chart-typed one as a submodule.

**Stated in the honest direction** (a fresh-context review, `I-0769`, corrected an earlier
phrasing here): this is not "`divisorWindow` is carrier-independent" — that is vacuous, since
`divisorWindow` takes only `d` and `hH1`. The content is that **the widened evaluation's kernel
lands on that already-fixed submodule**, which is what `ker_windowCarve` below then turns into
the widened `windowQuotEquiv`.

Two places where the widened proof differs from the chart-typed one, both in R2's
direction:

* the forward direction picks a piece containing the point out of the **joint** cover
  (`AffCoverData.exists_mem_pieces`, `I-0492` clause 4(ii)) rather than out of one of the
  two per-chart covers `cover₀`/`cover₁` — which is precisely the datum the widening
  replaced the partitions of unity by;
* the case analysis on which pinned chart a point lies in is driven by `τ.side j` for the
  chosen piece, so the two directions never need the point's chart membership *a priori*.
  The chart-typed proof gets that membership from the `Sum` index for free and pays for it
  by being confined to a fixed pair. -/
theorem ker_thetaGluedEval :
    LinearMap.ker (thetaGluedEval A τ a)
      = d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
          (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) := by
  rw [ker_thetaGluedEval_eq_ker]
  ext x
  rw [LinearMap.mem_ker, Scheme.LocalEquations.mem_vanishingSubmodule_iff, funext_iff]
  constructor
  · intro hker
    -- pick a piece containing the point out of the JOINT cover, then compare sides
    exact ⟨fun z hz =>
        (D.exists_mem_pieces z).elim fun j hj =>
          germ_val_mem_stalkIdeal_of_thetaEval_eq_zero A τ a hker false j hj hz,
      fun z hz =>
        (D.exists_mem_pieces z).elim fun j hj =>
          germ_val_mem_stalkIdeal_of_thetaEval_eq_zero A τ a hker true j hj hz⟩
  · intro h j
    rw [thetaEval_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
    refine Scheme.mem_span_singleton_of_forall_germ
      (fun z hz => A.eqn_regular j z hz) (fun z hz => ?_)
    -- the germ through the piece is the germ in the assigned chart, where `h` applies
    rw [germ_eqn_span_eq_stalkIdeal A j hz]
    have key : ((relCurve C R).presheaf.germ (D.pieces j) z hz).hom
        (relThetaResSide a (τ.side j) (piece_le_relPinnedChart τ j) x)
        = ((relCurve C R).presheaf.germ
            ((⊤ : (relCurve C R).Opens) ⊓ relPinnedChart C R π (τ.side j)) z
            ⟨trivial, piece_le_relPinnedChart τ j hz⟩).hom
          (relThetaResSide a (τ.side j) inf_le_right x) :=
      germ_relThetaResSide_eq a x (τ.side j) inf_le_right
        (le_inf le_top (piece_le_relPinnedChart τ j)) hz
    rw [key]
    -- `cases` on `τ.side j` fails here with "result is not type correct": the Bool occurs
    -- in the germ's OPEN, so the motive is dependent (memory `cases-on-a-bool-a-type-mentions`).
    -- The split is therefore factored out over an arbitrary Bool.
    exact germ_val_mem_stalkIdeal_of_forall_side a x h (τ.side j)
      ⟨trivial, piece_le_relPinnedChart τ j hz⟩

/-! ## Plugging the bridge in: the widened window carve

A fresh-context review of the above (inbox `I-0769`) made two corrections, and both are taken
here rather than argued with.

**First, a phrasing correction.** Saying `ker_thetaGluedEval` shows "`divisorWindow` is the same
submodule on both carriers" is true but *empty*: `divisorWindow` takes only `d` and `hH1`
(`Picard/DivisorFamilyWindow.lean:103`) and never mentioned a carrier, so nothing had to be
proved to make it carrier-independent.  The honest content runs the other way — **the widened
evaluation's kernel lands on that already-fixed submodule.**

**Second, a real gap.** Nothing above connected `ker_thetaGluedEval` to `divisorWindow`: the
chart-typed layer does that through `windowCarve` / `ker_windowCarve`
(`Picard/DivisorFamilyWindow.lean:158/:166`), the composite with `relThetaWindowEquiv`, and no
widened analogue existed.  Without it the "face" is not plugged in.  It is three lines, and here
they are. -/

section WindowCarve

-- `divisorWindow` and `relThetaWindowEquiv` (`Picard/DivisorFamilyWindow.lean:103/:89`) are
-- stated over the curve-instance tower and the `Over` local instance; nothing above this
-- section needed them, which is itself the measurement that the Θ-layer proper is
-- instance-light.
noncomputable local instance instOverCleftAffWindow :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]

variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)

/-- **The widened window carve arrow** `R ⊗[k] H_a → W(d)^{Θᵃ}`: the widened Θ-twisted colength
evaluation read through the window identification. -/
noncomputable def windowCarve :
    R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤) →ₗ[R] ThetaGlued A τ a :=
  thetaGluedEval A τ a ∘ₗ (relThetaWindowEquiv C R π a hH1).toLinearMap

/-- **THE FACE, PLUGGED IN**: the kernel of the widened window carve arrow is exactly the window
submodule `K_a(d)`.

This is what `ker_thetaGluedEval` was for, and stating it is the step inbox `I-0769` correctly
observed was missing.  Together with surjectivity of the widened evaluation — **not** proved, see
the module docstring — it gives the widened analogue of `windowQuotEquiv`, i.e. the identification
`(R ⊗[k] H_a) ⧸ K_a(d) ≃ W(d)^{Θᵃ}` that the ε-value facts are transported along.

Note what carries it: `divisorWindow` is a `Submodule.comap` of the vanishing submodule, and
`ker_thetaGluedEval` says the widened kernel *is* that vanishing submodule, so this is
`LinearMap.ker_comp` and nothing else. -/
theorem ker_windowCarve :
    LinearMap.ker (windowCarve A τ a hH1) = divisorWindow d hH1 := by
  rw [windowCarve, LinearMap.ker_comp, ker_thetaGluedEval, divisorWindow]

/-- Surjectivity of the widened carve arrow follows from surjectivity of the widened
evaluation — the remaining input, and the one this file does not supply. -/
lemma windowCarve_surjective (hsurj : Function.Surjective (thetaGluedEval A τ a)) :
    Function.Surjective (windowCarve A τ a hH1) := by
  rw [windowCarve, LinearMap.coe_comp]
  exact hsurj.comp (relThetaWindowEquiv C R π a hH1).surjective

/-- **The widened corank identification**, conditional on the right-exactness heart: once the
widened evaluation is surjective, the quotient of the free window by `K_a(d)` *is* the widened
Θ-twisted colength module.  This is `windowQuotEquiv`'s widened analogue — the vehicle whose
absence made the ε-value at a `DivFamZarAff` unstateable. -/
noncomputable def windowQuotEquiv (hsurj : Function.Surjective (thetaGluedEval A τ a)) :
    ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d hH1) ≃ₗ[R] ThetaGlued A τ a :=
  (Submodule.quotEquivOfEq _ _ (ker_windowCarve A τ a hH1).symm).trans
    ((windowCarve A τ a hH1).quotKerEquivOfSurjective
      (windowCarve_surjective A τ a hH1 hsurj))

end WindowCarve

end AffAdaptation

end AlgebraicGeometry
