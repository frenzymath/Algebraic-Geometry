/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4Effective

/-!
# Degree bounds from the positive/negative divisor decomposition

The coefficientwise decomposition of a curve divisor into effective positive
and negative parts gives useful numerical tests for effectivity.  These are
purely algebraic consequences of the finite-support divisor model; the global
product formula is not used.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

namespace CurveDivisor

/-! ### Numerical effectivity tests -/

theorem degree_positivePart_nonneg (D : CurveDivisor k X) :
    0 ≤ degree (positivePart D) := by
  exact degree_nonneg (positivePart_nonneg D)

theorem degree_negativePart_nonneg (D : CurveDivisor k X) :
    0 ≤ degree (negativePart D) := by
  exact degree_nonneg (negativePart_nonneg D)

theorem nonneg_iff_degree_negativePart_eq_zero {D : CurveDivisor k X} :
    0 ≤ D ↔ degree (negativePart D) = 0 := by
  constructor
  · intro hD
    rw [negativePart_eq_zero_iff.mpr hD, degree_zero]
  · intro hdegree
    have hzero : negativePart D = 0 :=
      eq_zero_of_nonneg_of_degree_eq_zero (negativePart_nonneg D) hdegree
    exact negativePart_eq_zero_iff.mp hzero

theorem nonpos_iff_degree_positivePart_eq_zero {D : CurveDivisor k X} :
    D ≤ 0 ↔ degree (positivePart D) = 0 := by
  constructor
  · intro hD
    rw [positivePart_eq_zero_iff.mpr hD, degree_zero]
  · intro hdegree
    have hzero : positivePart D = 0 :=
      eq_zero_of_nonneg_of_degree_eq_zero (positivePart_nonneg D) hdegree
    exact positivePart_eq_zero_iff.mp hzero

/-! ### Degree of a sign part -/

theorem degree_positivePart_eq_degree_of_nonneg {D : CurveDivisor k X}
    (hD : 0 ≤ D) : degree (positivePart D) = degree D := by
  rw [positivePart, sup_eq_left.mpr hD]

theorem degree_negativePart_eq_zero_of_nonneg {D : CurveDivisor k X}
    (hD : 0 ≤ D) : degree (negativePart D) = 0 := by
  rw [negativePart_eq_zero_iff.mpr hD, degree_zero]

theorem degree_positivePart_eq_degree_iff {D : CurveDivisor k X} :
    degree (positivePart D) = degree D ↔ 0 ≤ D := by
  constructor
  · intro hdegree
    have hdecomp := degree_positivePart_sub_negativePart D
    have hneg : degree (negativePart D) = 0 := by
      omega
    exact nonneg_iff_degree_negativePart_eq_zero.mpr hneg
  · exact degree_positivePart_eq_degree_of_nonneg

theorem degree_negativePart_eq_neg_degree_iff {D : CurveDivisor k X} :
    degree (negativePart D) = -degree D ↔ D ≤ 0 := by
  constructor
  · intro hdegree
    have hdecomp := degree_positivePart_sub_negativePart D
    have hpos : degree (positivePart D) = 0 := by
      omega
    exact nonpos_iff_degree_positivePart_eq_zero.mpr hpos
  · intro hD
    have hzero : degree (positivePart D) = 0 :=
      (nonpos_iff_degree_positivePart_eq_zero.mp hD)
    have hdecomp := degree_positivePart_sub_negativePart D
    omega

/-! ### A uniform absolute-degree bound -/

theorem abs_degree_le_signPart_degrees (D : CurveDivisor k X) :
    |degree D| ≤ degree (positivePart D) + degree (negativePart D) := by
  have hp := degree_positivePart_nonneg D
  have hn := degree_negativePart_nonneg D
  have hdecomp := degree_positivePart_sub_negativePart D
  apply (abs_le).2
  constructor <;> omega

end CurveDivisor

end Hartshorne
