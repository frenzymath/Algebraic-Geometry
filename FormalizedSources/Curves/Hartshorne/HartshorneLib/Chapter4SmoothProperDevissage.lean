/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4ProductFormulaBridge
import HartshorneLib.Chapter4SectionDrop

/-!
# Unconditional one-point dévissage consequences

The finite-map-to-`P1` construction supplies the finiteness predicate required
by the cohomological dévissage theorem.  This file specializes that theorem to
smooth proper integral curves and exposes the corresponding numerical bounds.
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

/-- Removing one closed point raises the Euler characteristic by one. -/
theorem chi_divisorSheaf_devissage_of_smoothProperIntegralCurve
    {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X) :
    CategoryTheory.Sheaf.chi (divisorSheaf D) =
      CategoryTheory.Sheaf.chi
          (divisorSheaf (CurveDivisor.devissageDivisor hx D)) + 1 := by
  exact chi_divisorSheaf_devissage
    (hasFiniteDivisorCohomology_of_smoothProperIntegralCurve (k := k) X) hx D

/-- The one-point `h⁰` gain and `h¹` loss have total size one. -/
theorem h0_sub_h0_sub_point_add_h1_sub_h1_sub_point_of_smoothProperIntegralCurve
    {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X) :
    ((CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) -
        CategoryTheory.Sheaf.h0
          (divisorSheaf (CurveDivisor.devissageDivisor hx D))) +
      ((CategoryTheory.Sheaf.h1
          (divisorSheaf (CurveDivisor.devissageDivisor hx D)) : ℤ) -
        CategoryTheory.Sheaf.h1 (divisorSheaf D)) = 1 := by
  have hchi :=
    chi_divisorSheaf_devissage_of_smoothProperIntegralCurve hx D
  rw [CategoryTheory.Sheaf.chi, CategoryTheory.Sheaf.chi] at hchi
  omega

/-- The dimension of global sections can increase by at most one at a point. -/
theorem h0_le_h0_sub_point_add_one_of_smoothProperIntegralCurve
    {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X) :
    CategoryTheory.Sheaf.h0 (divisorSheaf D) ≤
      CategoryTheory.Sheaf.h0
          (divisorSheaf (CurveDivisor.devissageDivisor hx D)) + 1 := by
  have hbalance :=
    h0_sub_h0_sub_point_add_h1_sub_h1_sub_point_of_smoothProperIntegralCurve
      hx D
  have hmono :=
    h1_le_h1_sub_point hx D
      ((hasFiniteDivisorCohomology_of_smoothProperIntegralCurve (k := k) X
        (CurveDivisor.devissageDivisor hx D)).2)
  omega

end
end Hartshorne
