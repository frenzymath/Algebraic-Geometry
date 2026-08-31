/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4Effective
import HartshorneLib.Chapter4DegreeClass

/-!
# Hartshorne IV.1: effective representatives

An effective representative of a divisor class controls its degree.  The
degree-invariance input is kept explicit, as in `Chapter4DegreeClass`.
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

/-- A divisor admits an effective representative in its linear equivalence class. -/
def HasEffectiveRepresentative (D : CurveDivisor k X) : Prop :=
  ∃ E, 0 ≤ E ∧ LinearlyEquivalent D E

/-- An effective representative forces the represented divisor to have
nonnegative degree. -/
theorem degree_nonneg_of_hasEffectiveRepresentative
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    {D : CurveDivisor k X} (hrep : HasEffectiveRepresentative D) :
    0 ≤ CurveDivisor.degree D := by
  obtain ⟨E, hE, hEq⟩ := hrep
  have hdegE : 0 ≤ CurveDivisor.degree E := CurveDivisor.degree_nonneg hE
  have hdeg : CurveDivisor.degree D = CurveDivisor.degree E :=
    degree_eq_of_linearlyEquivalent hzero hEq
  omega

/-- If an effective representative has degree zero, the original divisor is
linearly equivalent to zero. -/
theorem linearlyEquivalent_zero_of_hasEffectiveRepresentative_of_degree_zero
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    {D : CurveDivisor k X} (hrep : HasEffectiveRepresentative D)
    (hD : CurveDivisor.degree D = 0) :
    LinearlyEquivalent D 0 := by
  obtain ⟨E, hE, hEq⟩ := hrep
  have hdegE : CurveDivisor.degree E = 0 := by
    have hdeg : CurveDivisor.degree D = CurveDivisor.degree E :=
      degree_eq_of_linearlyEquivalent hzero hEq
    omega
  have hEzero : E = 0 :=
    CurveDivisor.eq_zero_of_nonneg_of_degree_eq_zero hE hdegE
  rw [hEzero] at hEq
  exact hEq

end Hartshorne
