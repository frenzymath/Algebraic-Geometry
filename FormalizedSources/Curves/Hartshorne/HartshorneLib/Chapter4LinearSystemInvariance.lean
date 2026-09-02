/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4LinearSystemDimension
import HartshorneLib.Chapter4LinearEquivalenceCohomology
import HartshorneLib.Chapter4LinearEquivalenceAPI

/-!
# Linear-system predicates and linear equivalence

The complete linear system depends only on the divisor class.  This file makes
that transport explicit for the numerical base-point-free and very-ample
predicates, including the successive point-deletion terms used in their
definitions.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-- The complete linear-system dimension is invariant under linear equivalence. -/
theorem linearSystemDimension_eq_of_linearlyEquivalent
    {D E : CurveDivisor k X} (hDE : LinearlyEquivalent D E) :
    linearSystemDimension D = linearSystemDimension E := by
  rw [linearSystemDimension_eq_h0_sub_one, linearSystemDimension_eq_h0_sub_one,
    h0_divisorSheaf_eq_of_linearlyEquivalent hDE]

private theorem h0_devissage_eq_of_linearlyEquivalent
    {D E : CurveDivisor k X} (hDE : LinearlyEquivalent D E)
    {x : X.left} (hx : x ≠ genericPoint X.left) :
    CategoryTheory.Sheaf.h0
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) =
      CategoryTheory.Sheaf.h0
        (divisorSheaf (CurveDivisor.devissageDivisor hx E)) := by
  have hsub : LinearlyEquivalent
      (D - CurveDivisor.single hx 1) (E - CurveDivisor.single hx 1) :=
    linearlyEquivalent_sub_right hDE
  simpa only [CurveDivisor.devissageDivisor_eq_sub] using
    h0_divisorSheaf_eq_of_linearlyEquivalent hsub

/-- Numerical base-point-freeness is invariant under linear equivalence. -/
theorem basePointFreeLinearSystem_iff_of_linearlyEquivalent
    {D E : CurveDivisor k X} (hDE : LinearlyEquivalent D E) :
    BasePointFreeLinearSystem D ↔ BasePointFreeLinearSystem E := by
  constructor
  · intro h x hx
    rw [← h0_devissage_eq_of_linearlyEquivalent hDE hx,
      ← h0_divisorSheaf_eq_of_linearlyEquivalent hDE]
    exact h x hx
  · intro h x hx
    rw [h0_devissage_eq_of_linearlyEquivalent hDE hx,
      h0_divisorSheaf_eq_of_linearlyEquivalent hDE]
    exact h x hx

private theorem h0_two_devissage_eq_of_linearlyEquivalent
    {D E : CurveDivisor k X} (hDE : LinearlyEquivalent D E)
    {x y : X.left} (hx : x ≠ genericPoint X.left)
    (hy : y ≠ genericPoint X.left) :
    CategoryTheory.Sheaf.h0
        (divisorSheaf
          (CurveDivisor.devissageDivisor hy
            (CurveDivisor.devissageDivisor hx D))) =
      CategoryTheory.Sheaf.h0
        (divisorSheaf
          (CurveDivisor.devissageDivisor hy
            (CurveDivisor.devissageDivisor hx E))) := by
  have h₁ : LinearlyEquivalent
      (CurveDivisor.devissageDivisor hx D)
      (CurveDivisor.devissageDivisor hx E) := by
    simpa only [CurveDivisor.devissageDivisor_eq_sub] using
      (linearlyEquivalent_sub_right (F := CurveDivisor.single hx 1) hDE)
  have h₂ : LinearlyEquivalent
      (CurveDivisor.devissageDivisor hy
        (CurveDivisor.devissageDivisor hx D))
      (CurveDivisor.devissageDivisor hy
        (CurveDivisor.devissageDivisor hx E)) := by
    simpa only [CurveDivisor.devissageDivisor_eq_sub] using
      (linearlyEquivalent_sub_right (F := CurveDivisor.single hy 1) h₁)
  exact h0_divisorSheaf_eq_of_linearlyEquivalent h₂

/-- Numerical very-ampleness is invariant under linear equivalence. -/
theorem veryAmpleLinearSystem_iff_of_linearlyEquivalent
    {D E : CurveDivisor k X} (hDE : LinearlyEquivalent D E) :
    VeryAmpleLinearSystem D ↔ VeryAmpleLinearSystem E := by
  constructor
  · intro h x y hx hy
    rw [← h0_two_devissage_eq_of_linearlyEquivalent hDE hx hy,
      ← h0_divisorSheaf_eq_of_linearlyEquivalent hDE]
    exact h x y hx hy
  · intro h x y hx hy
    rw [h0_two_devissage_eq_of_linearlyEquivalent hDE hx hy,
      h0_divisorSheaf_eq_of_linearlyEquivalent hDE]
    exact h x y hx hy

end
end Hartshorne
