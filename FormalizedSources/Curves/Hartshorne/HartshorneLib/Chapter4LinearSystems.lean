/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4EffectiveRepresentative

/-!
# Hartshorne IV.1: rational sections of divisors

A nonzero rational section of a divisor `D` is a nonzero rational function
whose principal divisor becomes effective after adding `D`. This file proves
the divisor-theoretic content of Hartshorne IV.1.2: such a section exists
exactly when the linear equivalence class of `D` has an effective
representative. It then records the degree consequences.
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

/-- A nonzero rational section of `D`, expressed by its divisor inequality.
The unit type packages the requirement that the rational function be nonzero. -/
def HasNonzeroRationalSection (D : CurveDivisor k X) : Prop :=
  ∃ g : X.left.functionFieldˣ, 0 ≤ principalDivisor g + D

/-- A divisor has a nonzero rational section exactly when its linear
equivalence class contains an effective divisor. -/
theorem hasNonzeroRationalSection_iff_hasEffectiveRepresentative
    (D : CurveDivisor k X) :
    HasNonzeroRationalSection D ↔ HasEffectiveRepresentative D := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨principalDivisor g + D, hg, ?_⟩
    rw [linearlyEquivalent_iff_exists]
    refine ⟨g⁻¹, ?_⟩
    rw [principalDivisor_inv]
    abel
  · rintro ⟨E, hE, hDE⟩
    obtain ⟨g, hg⟩ := (linearlyEquivalent_iff_exists D E).mp hDE
    refine ⟨g⁻¹, ?_⟩
    rw [principalDivisor_inv, ← hg]
    have heq : -(D - E) + D = E := by abel
    rwa [heq]

/-- A divisor with a nonzero rational section has nonnegative degree. -/
theorem degree_nonneg_of_hasNonzeroRationalSection
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    {D : CurveDivisor k X} (hsec : HasNonzeroRationalSection D) :
    0 ≤ CurveDivisor.degree D :=
  degree_nonneg_of_hasEffectiveRepresentative hzero
    ((hasNonzeroRationalSection_iff_hasEffectiveRepresentative D).mp hsec)

/-- A divisor of negative degree has no nonzero rational section. -/
theorem not_hasNonzeroRationalSection_of_degree_neg
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    {D : CurveDivisor k X} (hD : CurveDivisor.degree D < 0) :
    ¬ HasNonzeroRationalSection D := by
  intro hsec
  exact (not_le_of_gt hD)
    (degree_nonneg_of_hasNonzeroRationalSection hzero hsec)

/-- A divisor linearly equivalent to zero has a nonzero rational section. -/
theorem hasNonzeroRationalSection_of_linearlyEquivalent_zero
    {D : CurveDivisor k X} (hD : LinearlyEquivalent D 0) :
    HasNonzeroRationalSection D :=
  (hasNonzeroRationalSection_iff_hasEffectiveRepresentative D).mpr
    ⟨0, le_rfl, hD⟩

/-- In degree zero, a nonzero rational section exists exactly for the trivial
divisor class. -/
theorem hasNonzeroRationalSection_iff_linearlyEquivalent_zero_of_degree_zero
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    {D : CurveDivisor k X} (hD : CurveDivisor.degree D = 0) :
    HasNonzeroRationalSection D ↔ LinearlyEquivalent D 0 := by
  constructor
  · exact fun hsec =>
      linearlyEquivalent_zero_of_hasEffectiveRepresentative_of_degree_zero
        hzero
        ((hasNonzeroRationalSection_iff_hasEffectiveRepresentative D).mp hsec)
        hD
  · exact hasNonzeroRationalSection_of_linearlyEquivalent_zero

/-- In degree zero, the existence of a nonzero rational section forces the
divisor class to vanish. -/
theorem divisorClass_eq_zero_of_hasNonzeroRationalSection_of_degree_zero
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    {D : CurveDivisor k X} (hsec : HasNonzeroRationalSection D)
    (hD : CurveDivisor.degree D = 0) :
    divisorClass D = 0 := by
  have hlin : LinearlyEquivalent D 0 :=
    (hasNonzeroRationalSection_iff_linearlyEquivalent_zero_of_degree_zero
      hzero hD).mp hsec
  simpa using (linearlyEquivalent_iff_divisorClass_eq D 0).mp hlin

end Hartshorne
