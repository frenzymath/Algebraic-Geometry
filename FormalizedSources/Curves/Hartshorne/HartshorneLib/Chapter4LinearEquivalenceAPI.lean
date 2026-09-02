/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorClass

/-!
# Hartshorne II.6: additive linear-equivalence API

The divisor class map is an additive quotient map.  This module exposes the
corresponding `+`, `-`, and negation laws, and transports them to
`LinearlyEquivalent`.  In particular, adding or subtracting a principal
divisor does not change a divisor class.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-! ## Additive laws for the quotient class map -/

@[simp]
theorem divisorClass_zero :
    divisorClass (k := k) (X := X) (0 : CurveDivisor k X) = 0 :=
  map_zero (divisorClass (k := k) (X := X))

@[simp]
theorem divisorClass_add (D E : CurveDivisor k X) :
    divisorClass (D + E) = divisorClass D + divisorClass E :=
  map_add (divisorClass (k := k) (X := X)) D E

@[simp]
theorem divisorClass_sub (D E : CurveDivisor k X) :
    divisorClass (D - E) = divisorClass D - divisorClass E :=
  map_sub (divisorClass (k := k) (X := X)) D E

@[simp]
theorem divisorClass_neg (D : CurveDivisor k X) :
    divisorClass (-D) = -divisorClass D :=
  map_neg (divisorClass (k := k) (X := X)) D

@[simp]
theorem divisorClass_add_principalDivisor (D : CurveDivisor k X)
    (g : X.left.functionFieldˣ) :
    divisorClass (D + principalDivisor g) = divisorClass D := by
  simp only [divisorClass_add, divisorClass_principalDivisor, add_zero]

@[simp]
theorem divisorClass_principalDivisor_add (D : CurveDivisor k X)
    (g : X.left.functionFieldˣ) :
    divisorClass (principalDivisor g + D) = divisorClass D := by
  simp only [divisorClass_add, divisorClass_principalDivisor, zero_add]

@[simp]
theorem divisorClass_sub_principalDivisor (D : CurveDivisor k X)
    (g : X.left.functionFieldˣ) :
    divisorClass (D - principalDivisor g) = divisorClass D := by
  simp only [divisorClass_sub, divisorClass_principalDivisor, sub_zero]

@[simp]
theorem divisorClass_principalDivisor_sub (D : CurveDivisor k X)
    (g : X.left.functionFieldˣ) :
    divisorClass (principalDivisor g - D) = -divisorClass D := by
  simp only [divisorClass_sub, divisorClass_principalDivisor, zero_sub]

/-! ## Transport of linear equivalence through the divisor group operations -/

/-- Adding linearly equivalent divisors preserves linear equivalence. -/
theorem linearlyEquivalent_add {D E F G : CurveDivisor k X}
    (hDE : LinearlyEquivalent D E) (hFG : LinearlyEquivalent F G) :
    LinearlyEquivalent (D + F) (E + G) := by
  apply (linearlyEquivalent_iff_divisorClass_eq _ _).mpr
  simp only [divisorClass_add]
  rw [((linearlyEquivalent_iff_divisorClass_eq D E).mp hDE),
    ((linearlyEquivalent_iff_divisorClass_eq F G).mp hFG)]

/-- Adding a fixed divisor on the left preserves linear equivalence. -/
theorem linearlyEquivalent_add_left {D E F : CurveDivisor k X}
    (hDE : LinearlyEquivalent D E) :
    LinearlyEquivalent (F + D) (F + E) := by
  exact linearlyEquivalent_add (linearlyEquivalent_refl F) hDE

/-- Adding a fixed divisor on the right preserves linear equivalence. -/
theorem linearlyEquivalent_add_right {D E F : CurveDivisor k X}
    (hDE : LinearlyEquivalent D E) :
    LinearlyEquivalent (D + F) (E + F) := by
  exact linearlyEquivalent_add hDE (linearlyEquivalent_refl F)

/-- Subtracting linearly equivalent divisors preserves linear equivalence. -/
theorem linearlyEquivalent_sub {D E F G : CurveDivisor k X}
    (hDE : LinearlyEquivalent D E) (hFG : LinearlyEquivalent F G) :
    LinearlyEquivalent (D - F) (E - G) := by
  apply (linearlyEquivalent_iff_divisorClass_eq _ _).mpr
  simp only [divisorClass_sub]
  rw [((linearlyEquivalent_iff_divisorClass_eq D E).mp hDE),
    ((linearlyEquivalent_iff_divisorClass_eq F G).mp hFG)]

/-- Subtracting a fixed divisor on the left preserves linear equivalence. -/
theorem linearlyEquivalent_sub_left {D E F : CurveDivisor k X}
    (hDE : LinearlyEquivalent D E) :
    LinearlyEquivalent (F - D) (F - E) := by
  exact linearlyEquivalent_sub (linearlyEquivalent_refl F) hDE

/-- Subtracting a fixed divisor on the right preserves linear equivalence. -/
theorem linearlyEquivalent_sub_right {D E F : CurveDivisor k X}
    (hDE : LinearlyEquivalent D E) :
    LinearlyEquivalent (D - F) (E - F) := by
  exact linearlyEquivalent_sub hDE (linearlyEquivalent_refl F)

/-- Negation preserves linear equivalence. -/
theorem linearlyEquivalent_neg {D E : CurveDivisor k X}
    (hDE : LinearlyEquivalent D E) :
    LinearlyEquivalent (-D) (-E) := by
  apply (linearlyEquivalent_iff_divisorClass_eq _ _).mpr
  simp only [divisorClass_neg]
  rw [((linearlyEquivalent_iff_divisorClass_eq D E).mp hDE)]

/-! ## Principal-divisor compatibility -/

/-- A divisor and its translate by a principal divisor are linearly equivalent. -/
theorem linearlyEquivalent_add_principalDivisor (D : CurveDivisor k X)
    (g : X.left.functionFieldˣ) :
    LinearlyEquivalent D (D + principalDivisor g) := by
  apply (linearlyEquivalent_iff_divisorClass_eq _ _).mpr
  simp only [divisorClass_add, divisorClass_principalDivisor, add_zero]

/-- The same principal-divisor translation with the principal term written first. -/
theorem linearlyEquivalent_principalDivisor_add (D : CurveDivisor k X)
    (g : X.left.functionFieldˣ) :
    LinearlyEquivalent D (principalDivisor g + D) := by
  apply (linearlyEquivalent_iff_divisorClass_eq _ _).mpr
  simp only [divisorClass_add, divisorClass_principalDivisor, zero_add]

/-- Subtracting a principal divisor leaves the linear-equivalence class unchanged. -/
theorem linearlyEquivalent_sub_principalDivisor (D : CurveDivisor k X)
    (g : X.left.functionFieldˣ) :
    LinearlyEquivalent D (D - principalDivisor g) := by
  apply (linearlyEquivalent_iff_divisorClass_eq _ _).mpr
  simp only [divisorClass_sub, divisorClass_principalDivisor, sub_zero]

/-! ## Direct class extraction -/

theorem divisorClass_eq_of_linearlyEquivalent
    {D E : CurveDivisor k X} (hDE : LinearlyEquivalent D E) :
    divisorClass D = divisorClass E :=
  (linearlyEquivalent_iff_divisorClass_eq D E).mp hDE

theorem linearlyEquivalent_of_divisorClass_eq
    {D E : CurveDivisor k X} (hDE : divisorClass D = divisorClass E) :
    LinearlyEquivalent D E :=
  (linearlyEquivalent_iff_divisorClass_eq D E).mpr hDE

end Hartshorne
