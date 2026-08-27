/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.FiberCoordinateDivisor

/-!
# Divisor-section lattices for source-side fiber coordinates

The three identities in this file are the part of the fiber-lattice argument that survives
arbitrary field base change without comparing two models of the projective line.  For source-side
coordinate data `Q`, its effective coordinate divisor is zero on `Q.V₁` and on the overlap, while
over `Q.V₀` twisting by `n` multiplies the section lattice by `Q.coordinateUnit⁻ⁿ`.

Unlike `Ledger/FiberLattice.lean`, no exhaustion or strict-positivity statement is needed here.
These local identities are the input for a base-change-compatible two-chart complex.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace FiberCoordinateData

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (Q : FiberCoordinateData Y)

/-! ## Coefficient bookkeeping -/

private lemma coeffAt_nsmul (n : ℕ) (A : Y.CurveDivisor) {x : Y}
    (hx : x ≠ genericPoint Y) : coeffAt hx (n • A) = (n : ℤ) * coeffAt hx A := by
  induction n with
  | zero => rw [zero_smul, CurveDivisor.coeffAt_zero, Nat.cast_zero, zero_mul]
  | succ m ih => rw [succ_nsmul, CurveDivisor.coeffAt_add, ih, Nat.cast_succ]; ring

private lemma divisorBound_congr {A B : Y.CurveDivisor} {x : Y}
    (hx : x ≠ genericPoint Y) (h : coeffAt hx A = coeffAt hx B) :
    Scheme.divisorBound A hx = Scheme.divisorBound B hx :=
  congrArg (fun m : Multiplicative ℤ => (m : WithZero (Multiplicative ℤ)))
    (congrArg Multiplicative.ofAdd h)

private lemma coeffAt_add_nsmul_of_mem_V1 (A : Y.CurveDivisor) (n : ℕ) {x : Y}
    (hx : x ≠ genericPoint Y) (hxV1 : x ∈ Q.V₁) :
    coeffAt hx (A + n • Q.coordinateWeilDivisor (K := K)) = coeffAt hx A := by
  rw [CurveDivisor.coeffAt_add, coeffAt_nsmul,
    Q.coordinateWeilDivisor_coeffAt_of_mem_V1 (K := K) hx hxV1, mul_zero, add_zero]

/-! ## The constant lattices -/

/-- Twisting by the coordinate divisor does not change sections over the inverse-coordinate
chart. -/
theorem divisorSections_add_nsmul_coordinateWeilDivisor_V1 (A : Y.CurveDivisor) (n : ℕ) :
    divisorSections K (A + n • Q.coordinateWeilDivisor (K := K)) Q.V₁ =
      divisorSections K A Q.V₁ := by
  have hne : (Q.V₁ : Set Y).Nonempty := ⟨genericPoint Y, (Q.genericPoint_mem_inf).2⟩
  rw [divisorSections_of_nonempty K hne, divisorSections_of_nonempty K hne]
  have hbound : ∀ (x : Y) (hx : x ≠ genericPoint Y), x ∈ Q.V₁ →
      Scheme.divisorBound (A + n • Q.coordinateWeilDivisor (K := K)) hx =
        Scheme.divisorBound A hx :=
    fun x hx hxV1 => divisorBound_congr hx (coeffAt_add_nsmul_of_mem_V1 Q A n hx hxV1)
  refine Submodule.ext (fun g => ?_)
  rw [mem_boundedSections, mem_boundedSections]
  constructor
  · intro h x hx hxU
    rw [← hbound x hx hxU]
    exact h x hx hxU
  · intro h x hx hxU
    rw [hbound x hx hxU]
    exact h x hx hxU

/-- Twisting by the coordinate divisor does not change sections over the chart overlap. -/
theorem divisorSections_add_nsmul_coordinateWeilDivisor_overlap
    (A : Y.CurveDivisor) (n : ℕ) :
    divisorSections K (A + n • Q.coordinateWeilDivisor (K := K)) (Q.V₀ ⊓ Q.V₁) =
      divisorSections K A (Q.V₀ ⊓ Q.V₁) := by
  have hne : ((Q.V₀ ⊓ Q.V₁ : Y.Opens) : Set Y).Nonempty := Q.inf_nonempty
  rw [divisorSections_of_nonempty K hne, divisorSections_of_nonempty K hne]
  have hbound : ∀ (x : Y) (hx : x ≠ genericPoint Y), x ∈ Q.V₀ ⊓ Q.V₁ →
      Scheme.divisorBound (A + n • Q.coordinateWeilDivisor (K := K)) hx =
        Scheme.divisorBound A hx :=
    fun x hx hxU => divisorBound_congr hx (coeffAt_add_nsmul_of_mem_V1 Q A n hx hxU.2)
  refine Submodule.ext (fun g => ?_)
  rw [mem_boundedSections, mem_boundedSections]
  constructor
  · intro h x hx hxU
    rw [← hbound x hx hxU]
    exact h x hx hxU
  · intro h x hx hxU
    rw [hbound x hx hxU]
    exact h x hx hxU

/-! ## The growing lattice -/

private lemma coeffAt_divOf_inv (v : Y.functionFieldˣ) {x : Y}
    (hx : x ≠ genericPoint Y) :
    coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) v⁻¹) =
      -coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) v) := by
  have h : Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) v⁻¹ +
      Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) v = 0 := by
    rw [← Scheme.divOf_mul (Y ↘ Spec (CommRingCat.of K)), inv_mul_cancel,
      Scheme.divOf_one (Y ↘ Spec (CommRingCat.of K))]
  have hc := congrArg (coeffAt hx) h
  rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_zero] at hc
  linarith

private lemma coeffAt_divOf_pow (v : Y.functionFieldˣ) (n : ℕ) {x : Y}
    (hx : x ≠ genericPoint Y) :
    coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (v ^ n)) =
      (n : ℤ) * coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) v) := by
  induction n with
  | zero => rw [pow_zero, Scheme.divOf_one, CurveDivisor.coeffAt_zero, Nat.cast_zero, zero_mul]
  | succ m ih =>
    rw [pow_succ, Scheme.divOf_mul, CurveDivisor.coeffAt_add, ih, Nat.cast_succ]
    ring

/-- Over the regular-coordinate chart, twisting by `n` multiplies the section lattice by the
inverse `n`th power of the coordinate unit. -/
theorem divisorSections_add_nsmul_coordinateWeilDivisor_V0
    (A : Y.CurveDivisor) (n : ℕ) :
    divisorSections K (A + n • Q.coordinateWeilDivisor (K := K)) Q.V₀ =
      Submodule.map (mulByUnit K (Q.coordinateUnit⁻¹ ^ n)).toLinearMap
        (divisorSections K A Q.V₀) := by
  have hne : (Q.V₀ : Set Y).Nonempty := ⟨genericPoint Y, (Q.genericPoint_mem_inf).1⟩
  set w : Y.functionFieldˣ := Q.coordinateUnit⁻¹ ^ n with hw
  have hcoeff : ∀ (x : Y) (hx : x ≠ genericPoint Y), x ∈ Q.V₀ →
      coeffAt hx (A + n • Q.coordinateWeilDivisor (K := K)) =
        coeffAt hx (A - Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) w) := by
    intro x hx hxV0
    rw [CurveDivisor.coeffAt_add, coeffAt_nsmul, CurveDivisor.coeffAt_sub, hw,
      coeffAt_divOf_pow, coeffAt_divOf_inv,
      Q.coordinateWeilDivisor_coeffAt_of_mem_V0 (K := K) hx hxV0]
    ring
  have hbdd : Scheme.boundedSections K
      (A + n • Q.coordinateWeilDivisor (K := K)) Q.V₀ =
      Scheme.boundedSections K
        (A - Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) w) Q.V₀ := by
    refine Submodule.ext (fun g => ?_)
    rw [Scheme.mem_boundedSections, Scheme.mem_boundedSections]
    refine forall_congr' (fun x => forall_congr' (fun hx => imp_congr_right (fun hxV0 => ?_)))
    rw [divisorBound_congr hx (hcoeff x hx hxV0)]
  rw [divisorSections_of_nonempty K hne, hbdd]
  refine Submodule.ext (fun y => ?_)
  rw [Submodule.mem_map]
  constructor
  · intro hy
    refine ⟨(↑w⁻¹ : Y.functionField) * y, ?_, ?_⟩
    · rw [divisorSections_of_nonempty K hne, ← Scheme.mem_boundedSections_mul_iff K w A,
        ← mul_assoc, Units.mul_inv, one_mul]
      exact hy
    · simp only [Scheme.mulByUnit_apply, LinearEquiv.coe_coe, ← mul_assoc, Units.mul_inv,
        one_mul]
  · rintro ⟨h, hh, rfl⟩
    rw [divisorSections_of_nonempty K hne] at hh
    simp only [Scheme.mulByUnit_apply, LinearEquiv.coe_coe]
    exact (Scheme.mem_boundedSections_mul_iff K w A (h : Y.functionField)).mpr hh

end FiberCoordinateData

end AlgebraicGeometry
