/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4LinearSystems
import HartshorneLib.Chapter4ProductFormulaBridge

/-!
# Unconditional consequences for smooth proper integral curves

The finite-map-to-`P1` producer supplies the finite cohomology input used by
the curve product-formula argument.  This file discharges that input once and
exposes the resulting degree and linear-system API without making callers
thread an auxiliary finiteness proof through every statement.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-- The finite-map-to-`P1` cohomology producer proves the degree-zero
assertion for every principal divisor on a smooth proper integral curve. -/
theorem principalDivisorsHaveDegreeZero_of_smoothProperIntegralCurve
    (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    PrincipalDivisorsHaveDegreeZero (k := k) (X := X) := by
  exact principalDivisorsHaveDegreeZero_of_residueWeightedProductFormula
    (residueWeightedProductFormula_of_smoothProperIntegralCurve X)

/-- The canonical degree map on the divisor class group of a smooth proper
integral curve. -/
noncomputable def smoothProperDegreeClass
    (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    DivisorClassGroup (k := k) (X := X) →+ ℤ :=
  degreeClass (principalDivisorsHaveDegreeZero_of_smoothProperIntegralCurve X)

@[simp]
theorem smoothProperDegreeClass_divisorClass
    (D : CurveDivisor k X) :
    smoothProperDegreeClass (k := k) X (divisorClass D) = CurveDivisor.degree D := by
  exact degreeClass_divisorClass
    (principalDivisorsHaveDegreeZero_of_smoothProperIntegralCurve X) D

/-- The cohomological Euler characteristic is affine-linear in divisor degree
on a smooth proper integral curve. -/
theorem chi_divisorSheaf_eq_base_add_degree_of_smoothProperIntegralCurve
    (D : CurveDivisor k X) :
    CategoryTheory.Sheaf.chi (divisorSheaf D) =
      CategoryTheory.Sheaf.chi
          (divisorSheaf (X := X) (0 : CurveDivisor k X)) +
        CurveDivisor.degree D := by
  exact chi_divisorSheaf_eq_base_add_degree
    (hasFiniteDivisorCohomology_of_smoothProperIntegralCurve X) D

/-- Degree is invariant under linear equivalence, with the product-formula
input discharged by the finite-map-to-`P1` construction. -/
theorem degree_eq_of_linearlyEquivalent_of_smoothProperIntegralCurve
    {D E : CurveDivisor k X} (h : LinearlyEquivalent D E) :
    CurveDivisor.degree D = CurveDivisor.degree E := by
  exact degree_eq_of_linearlyEquivalent
    (principalDivisorsHaveDegreeZero_of_smoothProperIntegralCurve X) h

/-- A nonzero rational section forces nonnegative degree on a smooth proper
integral curve. -/
theorem degree_nonneg_of_hasNonzeroRationalSection_of_smoothProperIntegralCurve
    {D : CurveDivisor k X} (hsec : HasNonzeroRationalSection D) :
    0 ≤ CurveDivisor.degree D := by
  exact degree_nonneg_of_hasNonzeroRationalSection
    (principalDivisorsHaveDegreeZero_of_smoothProperIntegralCurve X) hsec

/-- In degree zero, a nonzero rational section is equivalent to triviality of
the divisor class. -/
theorem hasNonzeroRationalSection_iff_linearlyEquivalent_zero_of_smoothProperIntegralCurve
    {D : CurveDivisor k X} (hD : CurveDivisor.degree D = 0) :
    HasNonzeroRationalSection D ↔ LinearlyEquivalent D 0 := by
  exact hasNonzeroRationalSection_iff_linearlyEquivalent_zero_of_degree_zero
    (principalDivisorsHaveDegreeZero_of_smoothProperIntegralCurve X) hD

end Hartshorne
