/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartRationalGraph
import AlgebraicJacobian.Picard.DivSchemeSeedUnivAssembleKappa
import AlgebraicJacobian.RiemannRoch.CoverageDrop

/-!
# B-5, the fibre step: the greedy drop RUN at the splitting field, as a `chartLocus` witness

**Title corrected (issue I-0615): this file is steps 4 and 5, not "4–6".**  Step 6 — feeding the
drop's output `Σ` back as the chart index — is NOT here and is not discharged anywhere; see the
DEFECT section of `Picard/Pic0ChartCoverageTest.lean`, which explains why the drop stage and the
index stage carry different `Z`.  The original "4–6" wording is what that retraction corrects.

`w4-datb` §1.2 steps 4–5 happen entirely on the curve over the splitting field `L`.  This file
runs them and hands the result to `Picard/Pic0ChartTwistSplit.lean`'s introduction rule, so
that what comes out is membership of `chartLocus`.

## The statement, and what is a hypothesis rather than a construction

`exists_isSplitWitness_of_drop` takes:

* the presentation of the *twisted* fibre class over `L` by a Čech class `M`
  (`hM` — supplied at step 1 by `picEtAffineEquiv_map_chartTwistFactor_eq_unit`);
* a divisor `W₀` in that class with vanishing `H¹` and degree `g + e`
  (`hdeg`/`h1` — supplied at step 4: the class's degree is computed by
  `Picard/Pic0ChartCoverageDegree.lean`, and the vanishing comes from the fibre's OWN
  vanishing bound, which is where step 3's per-fibre `m` is spent);
* the admissible point oracle at `L` (`hdense`/`hPcl`/`hPdeg` — supplied at step 5 by
  `Curve/SepPointsDense.lean`'s density keystone at the base-changed `K_s`-points).

and produces an `S ≥ 0` of degree `e`, supported in the oracle, with `h⁰(W₀ − S) = 1`,
`h¹ = 0`, together with `IsSplitWitness` at the twisted class.

**What is deliberately a hypothesis:** the *existence* of `W₀` of the right degree with
`h¹ = 0`.  That is DAT-0a at the fibre field, and per `w4-datb` §0.2.2 (the I-0204 discipline)
its bound `b_L` is a **per-fibre** constant that provably does not transport from `k` — so it
must be chosen at `L`, inside the coverage proof, against `L`'s own instance.  Threading it as
a hypothesis here keeps that choice visible instead of burying it: a caller who cannot produce
`W₀` has not yet done step 3.

**Why the `h⁰ = 1` conclusion is carried even though `IsSplitWitness` does not ask for it:**
the witness predicate asks only for vanishing `H¹` (documented at `IsSplitWitness`; the
worksheets' "effective degree-`g` witness with `h¹ = 0`" is stronger than what the tree's
predicates state).  But `h⁰ = 1` is what DAT-C's normalization and GAP-2's uniqueness need, and
it is free here — the drop produces it.  Dropping it from the conclusion would force a later
lane to re-run the induction.

## Main declarations

* `AlgebraicGeometry.exists_isSplitWitness_of_drop` — **the fibre step of B-5**: the greedy drop
  at `L`, packaged as `IsSplitWitness` of the twisted class plus the `h⁰ = 1` normalization.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The fibre step -/

variable (C) in
/-- **B-5's fibre step** (`w4-datb` §1.2 steps 4–5, run at the splitting field; **not** step 6 —
see the header correction and issue I-0615).

Given the twisted fibre class presented over `L` by `M`, a divisor `W₀` in `M` of degree
`g + e` with vanishing `H¹`, and an admissible point oracle `P` on the `L`-curve, the greedy
drop produces `S` of degree `e` supported in `P` with `h⁰(W₀ − S) = 1` and `h¹(W₀ − S) = 0`;
and the class of `W₀` itself already certifies `IsSplitWitness` of the twisted class.

The two conclusions serve different consumers, which is why both are returned: the
`IsSplitWitness` half is `chartLocus` membership (`w4-datb` §1.2's target), while the
`h⁰ = 1` half is what DAT-C's normalization and the GAP-2 uniqueness of the effective
representative consume.

**The `S`-becomes-the-chart-index sentence that stood here is RETRACTED** (issue I-0615, and this
was its last residual site — the file header at the top of this module already carried the
correction, and the worksheet's `w4-datb` §1.2 SECOND AMENDMENT retracts it harder).  Coverage does
not feed `S` back as the chart index, because it does not need the drop at all:
`IsSplitWitness` asks for `h¹ = 0` and for **neither** effectivity **nor** degree `g`
(`Picard/Pic0ChartCoverageNoDrop.lean`, `mem_chartLocus_of_witness_h1`).  What the drop's output
*is* needed for is DAT-C's canonical section and GAP-2's uniqueness, which do require `0 ≤ W` and
`h⁰ = 1` — i.e. the chart map's injectivity, not its coverage. -/
theorem exists_isSplitWitness_of_drop {K : Type u} [Field K] [Algebra k K]
    (μ : picEt C (overSpec k K)) (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {L : Type u} [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    (g e : ℕ) (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (M₀ : (relCurve C L).CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K μ)
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (W₀ : ((C ⊗ overSpec k L).left).CurveDivisor)
    (hW₀ : Scheme.CurveDivisor.picClass L W₀
      = M₀ * Scheme.CechPic.map (relCurveMap C k L) (chartTwistClass C m Z))
    (hdeg : Scheme.CurveDivisor.deg L W₀ = (g : ℤ) + e)
    (h1 : Subsingleton (Sheaf.HModule ((C ⊗ overSpec k L).left.divisorSheaf L W₀) 1))
    (P : Set ((C ⊗ overSpec k L).left))
    (hdense : ∀ U : ((C ⊗ overSpec k L).left).Opens,
      (U : Set ((C ⊗ overSpec k L).left)).Nonempty → (P ∩ U).Nonempty)
    (hPcl : ∀ x ∈ P, x ≠ genericPoint ((C ⊗ overSpec k L).left))
    (hPdeg : ∀ x ∈ P, ((C ⊗ overSpec k L).left).residueDeg L x = 1) :
    IsSplitWitness C (μ * thetaFamily C (chartTwistClass C m Z) (overSpec k K))
      ∧ ∃ S : ((C ⊗ overSpec k L).left).CurveDivisor, 0 ≤ S ∧
        Scheme.CurveDivisor.deg L S = (e : ℤ) ∧
        (∀ (x : ((C ⊗ overSpec k L).left))
          (hx : x ≠ genericPoint ((C ⊗ overSpec k L).left)),
          coeffAt hx S ≠ 0 → x ∈ P) ∧
        Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L (W₀ - S)) = 1 ∧
        Subsingleton (Sheaf.HModule
          ((C ⊗ overSpec k L).left.divisorSheaf L (W₀ - S)) 1) := by
  refine ⟨isSplitWitness_of_witness_twistClass C μ m Z M₀ hM₀ W₀ hW₀ h1, ?_⟩
  -- the χ-value at the fibre field, transported from `k` (genus is base-field invariant)
  -- The instance pack of `BaseChangeInstances` is keyed to the PRODUCT spelling
  -- `(C ⊗ overSpec k L).left`, not to the `relCurve` alias, so `chi_relCurve_baseField`'s
  -- `relCurve`-spelled binders do not synthesise without these three re-keyings.
  haveI : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L
  haveI : SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instSmoothOfRelativeDimensionBaseChange C L
  haveI : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instQuasiCompactBaseChange C L
  haveI : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
    instModuleFiniteHModuleZeroBaseChange C L
  haveI : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
    instModuleFiniteHModuleOneBaseChange C L
  have hχL : Sheaf.chi ((relCurve C L).moduleKSheaf L) = 1 - (g : ℤ) :=
    chi_relCurve_baseField C L g hχ
  exact exists_effective_sub_h0_eq_one (K := L) g hχL P hdense hPcl hPdeg W₀ e hdeg h1

end

end AlgebraicGeometry
