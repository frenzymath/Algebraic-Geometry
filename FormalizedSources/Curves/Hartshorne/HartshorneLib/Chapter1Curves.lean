/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Hartshorne Chapter I: valuation rings and one-dimensional local rings

This file records the commutative-algebra substrate used by the curve and
divisor chapters.  The valuation-ring statement is phrased through a chosen
fraction field, which is the form available in Mathlib and is equivalent to
the usual ``x or x⁻¹ lies in R`` formulation.
-/

set_option autoImplicit false

namespace Hartshorne

/-!
## Valuation rings
-/

/-- A domain is a valuation ring exactly when every element of its fraction
field, or its inverse, is integral over the base ring in the localization
sense.  This is the fraction-field form of the valuation-ring dichotomy. -/
theorem valuationRing_iff_fractionField_dichotomy
    (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    ValuationRing R ↔ ∀ x : K,
      IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ :=
  ValuationRing.iff_isInteger_or_isInteger R K

/-- The valuation-ring dichotomy for one specified fraction-field element. -/
theorem valuationRing_fractionField_dichotomy
    (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [ValuationRing R] (x : K) :
    IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ :=
  ValuationRing.isInteger_or_isInteger R x

/-!
## Normal local rings of dimension one
-/

/--
For a Noetherian local domain which is not a field, integral closedness is
equivalent to being a discrete valuation ring once the ring has dimension at
most one.  Together with the non-field hypothesis this is the
one-dimensional normal-local criterion used for curves.
-/
theorem isIntegrallyClosed_iff_isDiscreteValuationRing
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [Ring.DimensionLEOne R] (hfield : ¬ IsField R) :
    IsIntegrallyClosed R ↔ IsDiscreteValuationRing R := by
  have hpair :
      IsDiscreteValuationRing R ↔
        IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime :=
    (IsDiscreteValuationRing.TFAE R hfield).out 0 3
  constructor
  · intro hIC
    apply hpair.mpr
    refine ⟨hIC, ?_⟩
    refine ⟨IsLocalRing.maximalIdeal R, ?_, ?_⟩
    · exact ⟨IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hfield, inferInstance⟩
    · intro P hP
      apply IsLocalRing.isMaximal_iff R |>.mp
      exact Ring.DimensionLEOne.maximalOfPrime hP.1 hP.2
  · intro hDVR
    exact hpair.mp hDVR |>.1

end Hartshorne
