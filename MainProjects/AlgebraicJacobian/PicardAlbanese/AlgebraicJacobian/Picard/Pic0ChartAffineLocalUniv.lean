/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageAbel
import AlgebraicJacobian.Picard.Pic0ChartCoverageThreshold

/-!
# DAT-B B-4 discharged at the admissible parameter: `ChartLocusAffineLocal` is UNCONDITIONAL

`Picard/Pic0ChartCoverageAbel.lean` names the affine-local openness residue
`ChartLocusAffineLocal C m Z T lam` — "the *only* remaining input to CHART-U(b) at a general
test" (`Pic0ChartCoverageAbel.lean:127`) — and its only producers so far are **conditional**:
`chartLocusAffineLocal_of_presentation` (`Pic0ChartCoverageAbel.lean:182`) asks for a
`BasicOpenCocycleDatum` presentation per affine piece, and `chartLocusAffineLocal_of_plusFibre`
(`Pic0ChartLocusPlusFibre.lean:128`) asks for a plus-fibre datum.  The obligation was priced by
two roadmap rows and survived into the `chartLocusOpens` `haff` argument as an unexhibited cost.

**It is free at the admissible parameter, for degree-zero classes, and this file says so as a
theorem.**  `exists_uniform_admissibleCoverageChart_eq_univ`
(`Pic0ChartCoverageThreshold.lean:381`) proves that at the parameter
`m := admissibleCoverageParameter hπ g`, `Z := (…).choose`, the chart locus of **every**
`pic⁰` class over **every** test is all of `Set.univ` — a set that is open by
`isOpen_univ`.  `ChartLocusAffineLocal` asks for openness of the locus of the class *restricted*
to each affine piece; by `pic0Map_coe` that restricted class `picEtMap C (Over.fromSpecAffine T U)
lam.1` is the carrier of the degree-zero class `pic0Map C (Over.fromSpecAffine T U) lam`, to which
`_eq_univ` applies again.  So the residue holds with no presentation, no plus-fibre, no arithmetic,
and no `rep` — the numeric coverage result already contains the openness that CHART-U(b) needs.

## Why this is the right carrier and does not overclaim

`Pic0ChartAtlasCoupling.lean:52-55` warns that `chartLocus` (on the *test*) and the
open-immersion `V` (on the *divisor scheme*) do **not** meet, and that no tree declaration relates
them.  This file respects that: it discharges only the *test-side* openness residue `haff`, which
is exactly what `chartLocusOpens`/CHART-U(b) consumes; it does **not** touch antecedent 1
(`IsChartUniv`/`RestrictedChartFibre`), the pointwise-to-neighbourhood spreading-out that
`Pic0ChartCoverageSlice.lean` records as absent, or `rep`.  No antecedent of
`pic0RepresentableByOfCharts` is closed here — one of B-4's two named inputs to CHART-U(b) is.

## Main declarations

* `AlgebraicGeometry.chartLocusAffineLocal_admissible` — for the admissible parameter and any
  degree-zero class, `ChartLocusAffineLocal` holds unconditionally.
* `AlgebraicGeometry.chartLocusOpens_admissible_eq_top` — the open of the test that
  `chartLocusOpens` produces from that residue is all of `T.left` (the locus is `univ`).
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

noncomputable section

/-- **DAT-B B-4 at the admissible parameter, unconditionally.**

At the coverage chart index `(m, Z) := admissibleCoverageParameter hπ g` supplied by
`exists_uniform_admissibleCoverageChart_eq_univ`, the affine-local openness residue
`ChartLocusAffineLocal` holds for *every* degree-zero class `lam : pic0Subgroup C T` over *every*
test `T`, with no presentation, plus-fibre, or arithmetic hypothesis: the chart locus of the
restricted class is `Set.univ` and `univ` is open.

This retires the `haff` argument of `chartLocusOpens`/CHART-U(b) at the parameter coverage
actually uses.  The chart index `(m, Z)` is exactly the one `_eq_univ` produces (its `.choose`
/`choose_spec.choose`); its own degree constraint is `_eq_univ`'s first conjunct
`deg_k Z = m·d₁ − admissibleCoverageParameter` (note this subtracts `admissibleCoverageParameter
= (M·δ+g)·d₁`, which carries the `d₁ = classDeg (thetaCechClass C)` factor — it is *not* the
`(M·δ+g)`-without-`d₁` calibration some fixed-parameter chart data use, and neither theorem here
depends on identifying the two). -/
theorem chartLocusAffineLocal_admissible
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {T : Over (Spec (.of k))} (lam : pic0Subgroup C T) :
    ChartLocusAffineLocal C
      (exists_uniform_admissibleCoverageChart_eq_univ (C := C) hπ g hχ).choose
      (exists_uniform_admissibleCoverageChart_eq_univ (C := C) hπ g hχ).choose_spec.choose
      T lam.1 := by
  -- the locus of the class restricted to each affine piece (`pic0Map`, `pic0Map_coe`) is all of
  -- `Set.univ` by `_eq_univ`, and `Set.univ` is open.
  intro U
  rw [← pic0Map_coe (C := C) (Over.fromSpecAffine T U) lam,
    (exists_uniform_admissibleCoverageChart_eq_univ (C := C) hπ g hχ).choose_spec.choose_spec.2
      (pic0Map C (Over.fromSpecAffine T U) lam)]
  exact isOpen_univ

/-- The open of the test that `chartLocusOpens` produces from the residue above is all of
`T.left`: the underlying locus is `Set.univ`. -/
theorem chartLocusOpens_admissible_eq_top
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {T : Over (Spec (.of k))} (lam : pic0Subgroup C T) :
    chartLocusOpens C
        (exists_uniform_admissibleCoverageChart_eq_univ (C := C) hπ g hχ).choose
        (exists_uniform_admissibleCoverageChart_eq_univ (C := C) hπ g hχ).choose_spec.choose
        T lam.1 (chartLocusAffineLocal_admissible hπ g hχ lam)
      = ⊤ := by
  apply TopologicalSpace.Opens.ext
  change chartLocus C _ _ lam.1 = _
  rw [(exists_uniform_admissibleCoverageChart_eq_univ (C := C) hπ g hχ).choose_spec.choose_spec.2
    lam]
  rfl

end

end AlgebraicGeometry
