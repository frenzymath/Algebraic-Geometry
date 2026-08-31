/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4Curves

/-!
# Hartshorne IV.1: effective and negative parts of a divisor

The coefficient lattice on curve divisors gives canonical positive and negative
parts.  This is the finite-support form of the decomposition
`D = D⁺ - D⁻`, with disjoint parts, and is useful whenever an argument reduces
a divisor to effective pieces.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

namespace CurveDivisor

/-- The positive part of a divisor, obtained by taking the coefficientwise
maximum with zero. -/
noncomputable def positivePart (D : CurveDivisor k X) : CurveDivisor k X :=
  D ⊔ 0

/-- The negative part of a divisor, obtained by taking the coefficientwise
maximum of its negation with zero. -/
noncomputable def negativePart (D : CurveDivisor k X) : CurveDivisor k X :=
  (-D) ⊔ 0

/-- The positive part is effective. -/
theorem positivePart_nonneg (D : CurveDivisor k X) :
    0 ≤ positivePart D := by
  exact le_sup_right

/-- The negative part is effective. -/
theorem negativePart_nonneg (D : CurveDivisor k X) :
    0 ≤ negativePart D := by
  exact le_sup_right

/-- A divisor is the difference of its positive and negative parts. -/
theorem positivePart_sub_negativePart (D : CurveDivisor k X) :
    positivePart D - negativePart D = D := by
  apply ext_coeffAt
  intro x hx
  rw [positivePart, negativePart, coeffAt_sub, coeffAt_sup, coeffAt_sup,
    coeffAt_zero, coeffAt_neg]
  omega

/-- The positive and negative parts have no common coefficient. -/
theorem positivePart_inf_negativePart (D : CurveDivisor k X) :
    positivePart D ⊓ negativePart D = 0 := by
  apply ext_coeffAt
  intro x hx
  rw [positivePart, negativePart, coeffAt_inf, coeffAt_sup, coeffAt_sup,
    coeffAt_zero, coeffAt_neg]
  omega

/-- The positive part vanishes exactly for an everywhere nonpositive divisor. -/
theorem positivePart_eq_zero_iff {D : CurveDivisor k X} :
    positivePart D = 0 ↔ D ≤ 0 := by
  constructor
  · intro h
    rw [← h]
    exact le_sup_left
  · intro h
    exact sup_eq_right.mpr h

/-- The negative part vanishes exactly for an effective divisor. -/
theorem negativePart_eq_zero_iff {D : CurveDivisor k X} :
    negativePart D = 0 ↔ 0 ≤ D := by
  constructor
  · intro h
    have h' : -D ≤ (0 : CurveDivisor k X) := by
      rw [← h]
      exact le_sup_left
    rw [le_iff_coeffAt] at h'
    rw [le_iff_coeffAt]
    intro x hx
    have hx' := h' x hx
    rw [coeffAt_neg, coeffAt_zero] at hx'
    exact neg_nonpos.mp hx'
  · intro h
    apply sup_eq_right.mpr
    rw [le_iff_coeffAt]
    intro x hx
    rw [coeffAt_neg, coeffAt_zero]
    exact neg_nonpos.mpr (le_iff_coeffAt.mp h x hx)

/-- Degree decomposes as the degree of the positive part minus the degree of
the negative part. -/
theorem degree_positivePart_sub_negativePart (D : CurveDivisor k X) :
    degree (positivePart D) - degree (negativePart D) = degree D := by
  rw [← degree_sub, positivePart_sub_negativePart]

end CurveDivisor

end Hartshorne

