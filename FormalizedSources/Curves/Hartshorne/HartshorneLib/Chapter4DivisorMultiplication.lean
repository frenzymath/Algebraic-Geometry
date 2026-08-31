/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorSheaf

/-!
# Multiplication and divisor bounds

This file records the valuation identity that converts the classical order of a
nonzero rational function into the pole bound of its negative principal divisor.
It is the local bridge needed to construct multiplication isomorphisms between
divisor sheaves; the global degree-zero product formula remains separate.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-- The valuation of a rational-function unit is the divisor bound of its
negative principal divisor.  The sign records that `orderAt` is the adic
valuation while `orderZAt` uses the classical order convention. -/
theorem orderAt_eq_divisorBound_neg_principalDivisor
    (g : X.left.functionFieldˣ) {x : X.left} (hx : x ≠ genericPoint X.left) :
    orderAt X.hom hx (g : X.left.functionField) =
      divisorBound (-principalDivisor g) hx := by
  rw [divisorBound]
  change orderAt X.hom hx (g : X.left.functionField) =
    ↑(Multiplicative.ofAdd (-CurveDivisor.coeffAt hx (principalDivisor g)) :
      Multiplicative ℤ)
  rw [coeffAt_principalDivisor]
  rw [orderZAt]
  simp

omit [IsAlgClosed k] [IsProper X.hom] in
/-- The valuation of a rational-function unit is nonzero. -/
theorem orderAt_unit_ne_zero (g : X.left.functionFieldˣ) {x : X.left}
    (hx : x ≠ genericPoint X.left) :
    orderAt X.hom hx (g : X.left.functionField) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (Units.ne_zero g)

omit [IsAlgClosed k] [IsProper X.hom] in
/-- The valuation of a rational-function unit is positive in `WithZero`. -/
theorem orderAt_unit_pos (g : X.left.functionFieldˣ) {x : X.left}
    (hx : x ≠ genericPoint X.left) :
    0 < orderAt X.hom hx (g : X.left.functionField) :=
  zero_lt_iff.mpr (orderAt_unit_ne_zero g hx)

/-- Divisor addition becomes multiplication of the corresponding local bounds. -/
theorem divisorBound_add (D₁ D₂ : CurveDivisor k X) {x : X.left}
    (hx : x ≠ genericPoint X.left) :
    divisorBound (D₁ + D₂) hx = divisorBound D₁ hx * divisorBound D₂ hx := by
  simp only [divisorBound, ← WithZero.coe_mul, ← ofAdd_add]
  congr 2

/-- Subtracting a principal divisor shifts the local bound by the valuation of
the defining rational-function unit. -/
theorem divisorBound_sub_principalDivisor (g : X.left.functionFieldˣ)
    (D : CurveDivisor k X) {x : X.left} (hx : x ≠ genericPoint X.left) :
    divisorBound (D - principalDivisor g) hx =
      orderAt X.hom hx (g : X.left.functionField) * divisorBound D hx := by
  rw [sub_eq_add_neg, divisorBound_add, ← orderAt_eq_divisorBound_neg_principalDivisor,
    mul_comm]

/-- Multiplication by a rational-function unit transports the pole bound for
`D` to the pole bound for `D - div(g)`, with an exact converse. -/
theorem mem_boundedSections_mul_iff (g : X.left.functionFieldˣ)
    (D : CurveDivisor k X) {U : X.left.Opens} (h : X.left.functionField) :
    (g : X.left.functionField) * h ∈ boundedSections (D - principalDivisor g) U
      ↔ h ∈ boundedSections D U := by
  simp only [mem_boundedSections]
  refine ⟨fun H z hz hzU => ?_, fun H z hz hzU => ?_⟩
  · have key := H z hz hzU
    rw [map_mul, divisorBound_sub_principalDivisor] at key
    exact (mul_le_mul_iff_of_pos_left (orderAt_unit_pos g hz)).mp key
  · rw [map_mul, divisorBound_sub_principalDivisor]
    exact (mul_le_mul_iff_of_pos_left (orderAt_unit_pos g hz)).mpr (H z hz hzU)

/-- Products of sections satisfy the bound for the sum of two divisors. -/
theorem mul_mem_divisorSections_top {A B : CurveDivisor k X}
    {f h : X.left.functionField}
    (hfA : f ∈ divisorSections A ⊤) (hhB : h ∈ divisorSections B ⊤) :
    f * h ∈ divisorSections (A + B) ⊤ := by
  have htop : ((⊤ : X.left.Opens) : Set X.left).Nonempty :=
    ⟨genericPoint X.left, trivial⟩
  rw [mem_divisorSections_of_nonempty htop] at hfA hhB ⊢
  intro x hx hxU
  rw [map_mul, divisorBound_add]
  exact mul_le_mul' (hfA x hx hxU) (hhB x hx hxU)

end Hartshorne
