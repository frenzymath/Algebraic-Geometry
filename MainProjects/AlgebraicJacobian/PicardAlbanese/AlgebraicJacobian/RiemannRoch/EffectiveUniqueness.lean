/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorClassMeromorphic
import AlgebraicJacobian.RiemannRoch.MulEquiv
import AlgebraicJacobian.RiemannRoch.SectionSpaces

/-!
# DAT-C C3 — effective uniqueness at `h⁰ = 1`
(`informal/w4-datc-worksheet.md` GAP-2, Σ-UNIQ-fld)

The field-level uniqueness brick of the canonical-section normalization: on the curve
bundle `X` over a field `K`, an effective divisor `D` with `h⁰(𝒪(D)) = 1` is the
**unique** effective representative of its Čech Picard class.

Route (worksheet §0.3 GAP-2, verbatim): equal classes give a rational function `g`
with `div g = D' − D` (`CurveDivisor.exists_divOf_of_picClass_eq`); `g ∈ H⁰(𝒪(D))`
since `div g + D = D' ≥ 0` (`mem_divisorSections_top_iff`); `1 ∈ H⁰(𝒪(D))` since
`0 ≤ D`; `h⁰ = 1` forces `g = c · 1` (`finrank_eq_one_iff_of_nonzero'` through the
`h⁰` bridge `finrank_divisorSections_top`), and a nonzero constant has trivial
principal divisor, so `D' − D = div g = 0`.

* `AlgebraicGeometry.Scheme.ord_functionFieldOverAlgebraMap_eq_one` — a nonzero
  constant has trivial order valuation at every closed point.
* `Scheme.divOf_eq_zero_of_val_eq_functionFieldOverAlgebraMap` — a unit of `K(X)`
  whose value is a constant has trivial principal divisor.
* `Scheme.one_mem_divisorSections_top` — `1 ∈ H⁰(𝒪(D))` for effective `D`.
* `Scheme.CurveDivisor.eq_of_picClass_eq_of_finrank_one` — the worker, with the
  section-space hypothesis `dim_K H⁰(𝒪(D)) = 1`.
* `Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one` — **the keystone**: `0 ≤ D`,
  `0 ≤ D'`, equal classes, `h⁰(𝒪(D)) = 1` imply `D' = D`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

/-! ## Constants have trivial order and trivial principal divisor -/

/-- **A nonzero constant has trivial order valuation at every closed point**: both `c`
and `c⁻¹` are integral (`ord ≤ 1`), and their orders multiply to `ord 1 = 1`. -/
theorem ord_functionFieldOverAlgebraMap_eq_one {x : X} (hx : x ≠ genericPoint X)
    {c : K} (hc : c ≠ 0) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (functionFieldOverAlgebraMap K X c)
      = 1 := by
  have ha := ord_functionFieldOverAlgebraMap_le_one K hx c
  have hb := ord_functionFieldOverAlgebraMap_le_one K hx c⁻¹
  have hmul : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
        (functionFieldOverAlgebraMap K X c)
      * Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
        (functionFieldOverAlgebraMap K X c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  refine le_antisymm ha ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
          (functionFieldOverAlgebraMap K X c)
        * Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
          (functionFieldOverAlgebraMap K X c⁻¹) := hmul.symm
    _ ≤ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
          (functionFieldOverAlgebraMap K X c) * 1 := mul_le_mul_right hb _
    _ = Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
          (functionFieldOverAlgebraMap K X c) := mul_one _

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **A constant unit has trivial principal divisor**: `div (c · 1) = 0`. -/
theorem divOf_eq_zero_of_val_eq_functionFieldOverAlgebraMap {g : X.functionFieldˣ}
    {c : K} (hval : (g : X.functionField) = functionFieldOverAlgebraMap K X c) :
    Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g = 0 := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact g.ne_zero (by rw [hval, map_zero])
  refine CurveDivisor.ext_coeffAt fun x hx => ?_
  rw [CurveDivisor.coeffAt_divOf, CurveDivisor.coeffAt_zero]
  have hord : Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx g = 1 := by
    rw [Scheme.ordZ_eq_one_iff, hval]
    exact ord_functionFieldOverAlgebraMap_eq_one K hx hc
  rw [hord, toAdd_one]

/-! ## The two members of `H⁰(𝒪(D))` -/

/-- **The constant `1` is a global section of `𝒪(D)` for effective `D`.** -/
theorem one_mem_divisorSections_top {D : X.CurveDivisor} (hD : 0 ≤ D) :
    (1 : X.functionField) ∈ divisorSections K D ⊤ := by
  rw [mem_divisorSections_top_iff K one_ne_zero]
  have hone : Units.mk0 (1 : X.functionField) one_ne_zero = 1 := Units.ext rfl
  rw [hone, Scheme.divOf_one, add_zero]
  exact hD

/-! ## Effective uniqueness -/

/-- **Effective uniqueness at `dim H⁰ = 1` (worker form)**: if `0 ≤ D`, `0 ≤ D'`, the
classes agree, and the global sections of `𝒪(D)` are one-dimensional, then `D' = D`.
The extracted function realizing `D' − D` lies in `H⁰(𝒪(D))`, hence is a constant
multiple of `1 ∈ H⁰(𝒪(D))`, hence has trivial divisor. -/
theorem CurveDivisor.eq_of_picClass_eq_of_finrank_one {D D' : X.CurveDivisor}
    (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hcl : CurveDivisor.picClass K D = CurveDivisor.picClass K D')
    (hone : Module.finrank K ↥(divisorSections K D ⊤) = 1) :
    D' = D := by
  -- the rational function with divisor `D' − D`
  obtain ⟨g, hg⟩ := CurveDivisor.exists_divOf_of_picClass_eq K hcl.symm
  -- `g ∈ H⁰(𝒪(D))`: `div g + D = D' ≥ 0`
  have hmem : (g : X.functionField) ∈ divisorSections K D ⊤ := by
    rw [mem_divisorSections_top_iff K g.ne_zero]
    have hmk : Units.mk0 (g : X.functionField) g.ne_zero = g := Units.ext rfl
    rw [hmk, ← hg, add_sub_cancel]
    exact hD'
  -- `h⁰ = 1` forces `g = c · 1`
  have h1mem : (1 : X.functionField) ∈ divisorSections K D ⊤ :=
    one_mem_divisorSections_top K hD
  have h1ne : (⟨1, h1mem⟩ : ↥(divisorSections K D ⊤)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨1, h1mem⟩ :
    ↥(divisorSections K D ⊤)) h1ne).mp hone ⟨(g : X.functionField), hmem⟩
  have hval : (g : X.functionField) = functionFieldOverAlgebraMap K X c := by
    have h : c • (1 : X.functionField) = (g : X.functionField) :=
      congrArg Subtype.val hc
    rw [← h, functionFieldOverModule_smul_def, mul_one]
  -- the constant has trivial divisor, so `D' − D = 0`
  have hdiv0 : Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g = 0 :=
    divOf_eq_zero_of_val_eq_functionFieldOverAlgebraMap K hval
  rw [hdiv0] at hg
  exact sub_eq_zero.mp hg

/-- **Effective uniqueness at `h⁰ = 1`** (worksheet GAP-2, Σ-UNIQ-fld — THE keystone):
an effective divisor `D` with `h⁰(𝒪(D)) = 1` is the unique effective representative of
its Čech Picard class. -/
theorem CurveDivisor.eq_of_picClass_eq_of_h0_one {D D' : X.CurveDivisor}
    (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hcl : CurveDivisor.picClass K D = CurveDivisor.picClass K D')
    (hone : Sheaf.h0 (X.divisorSheaf K D) = 1) :
    D' = D :=
  CurveDivisor.eq_of_picClass_eq_of_finrank_one K hD hD' hcl
    ((finrank_divisorSections_top K D).trans hone)

end Scheme

end AlgebraicGeometry
