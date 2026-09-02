/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DegreeClass
import HartshorneLib.Chapter4FiniteMapP1Cohomology
import HartshorneLib.Chapter4ProductFormulaCohomology
import HartshorneLib.Chapter4WeightedDegree

/-!
# Product-formula bridge for curve divisors

The global product formula is naturally stated with residue-field weights over
an arbitrary field.  On the algebraically closed curves formalized here, those
weights are all one.  This file packages that reduction at the exact interface
consumed by the divisor-class construction.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-- A residue-weighted product formula on an algebraically closed curve gives
the degree-zero assertion used to descend divisor degree to divisor classes. -/
theorem principalDivisorsHaveDegreeZero_of_residueWeightedProductFormula
    (hformula : ∀ g : X.left.functionFieldˣ,
      CurveDivisor.residueWeightedDegree (principalDivisor g) = 0) :
    PrincipalDivisorsHaveDegreeZero (k := k) (X := X) := by
  intro g
  rw [← CurveDivisor.residueWeightedDegree_eq_degree]
  exact hformula g

/-- The cohomological product-formula argument also gives the standard
residue-weighted formulation. -/
theorem residueWeightedProductFormula_of_finiteDivisorCohomology
    (hfin : HasFiniteDivisorCohomology (k := k) (X := X)) :
    ∀ g : X.left.functionFieldˣ,
      CurveDivisor.residueWeightedDegree (principalDivisor g) = 0 := by
  intro g
  rw [CurveDivisor.residueWeightedDegree_eq_degree]
  exact principalDivisorsHaveDegreeZero_of_finiteDivisorCohomology hfin g

/-- Properness supplies the degree-zero finiteness needed by the cohomological
argument, so finite first cohomology alone yields the residue-weighted product
formula. -/
theorem residueWeightedProductFormula_of_moduleKSheaf_oneFinite
    (h1 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 1)) :
    ∀ g : X.left.functionFieldˣ,
      CurveDivisor.residueWeightedDegree (principalDivisor g) = 0 := by
  intro g
  rw [CurveDivisor.residueWeightedDegree_eq_degree]
  exact principalDivisorsHaveDegreeZero_of_moduleKSheaf_oneFinite h1 g

/-- Over an algebraically closed field, finite-map-to-`P1` existence supplies the
finite divisor-sheaf cohomology used by the product-formula argument. -/
theorem hasFiniteDivisorCohomology_of_smoothProperIntegralCurve
    (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    HasFiniteDivisorCohomology (k := k) (X := X) := by
  exact hasFiniteDivisorCohomology_of_moduleKSheaf_oneFinite
    (moduleFinite_moduleKSheaf_one_of_smoothProperIntegralCurve X)

/-- The finite-map-to-`P1` construction therefore yields the residue-weighted
product formula for principal divisors on an algebraically closed curve. -/
theorem residueWeightedProductFormula_of_smoothProperIntegralCurve
    (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    ∀ g : X.left.functionFieldˣ,
      CurveDivisor.residueWeightedDegree (principalDivisor g) = 0 := by
  exact residueWeightedProductFormula_of_moduleKSheaf_oneFinite
    (moduleFinite_moduleKSheaf_one_of_smoothProperIntegralCurve X)

end Hartshorne
