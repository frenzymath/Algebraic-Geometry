/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4Ampleness

/-!
# Hartshorne IV.3.1: dimensions of complete linear systems

The project stores section ranks as natural numbers.  This module supplies the
source convention `dim |D| = h0(D) - 1` in an integer-valued form and proves
that the rank-drop predicates used by the linear-system criteria are exactly
the corresponding dimension-drop statements.
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

/-- The integer dimension of the complete linear system `|D|`. -/
def linearSystemDimension (D : CurveDivisor k X) : ℤ :=
  (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) - 1

@[simp] theorem linearSystemDimension_eq_h0_sub_one (D : CurveDivisor k X) :
    linearSystemDimension D =
      (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) - 1 :=
  rfl

/-- A one-point rank drop is the usual one-dimensional drop of `|D|`. -/
theorem linearSystemDimension_sub_point_eq_sub_one_iff
    (D : CurveDivisor k X) {x : X.left} (hx : x ≠ genericPoint X.left) :
    linearSystemDimension (CurveDivisor.devissageDivisor hx D) =
        linearSystemDimension D - 1 ↔
      (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) -
          CategoryTheory.Sheaf.h0
            (divisorSheaf (CurveDivisor.devissageDivisor hx D)) = 1 := by
  dsimp [linearSystemDimension]
  omega

/-- A two-point rank drop is the usual two-dimensional drop of `|D|`. -/
theorem linearSystemDimension_sub_two_points_eq_sub_two_iff
    (D : CurveDivisor k X) {x y : X.left}
    (hx : x ≠ genericPoint X.left) (hy : y ≠ genericPoint X.left) :
    linearSystemDimension
          (CurveDivisor.devissageDivisor hy
            (CurveDivisor.devissageDivisor hx D)) =
        linearSystemDimension D - 2 ↔
      (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) -
          CategoryTheory.Sheaf.h0
            (divisorSheaf (CurveDivisor.devissageDivisor hy
              (CurveDivisor.devissageDivisor hx D))) = 2 := by
  dsimp [linearSystemDimension]
  omega

/-- The numerical base-point-free predicate is equivalent to the dimension
drop criterion for every closed point. -/
theorem basePointFreeLinearSystem_iff_linearSystemDimension_drop
    (D : CurveDivisor k X) :
    BasePointFreeLinearSystem D ↔
      ∀ (x : X.left) (hx : x ≠ genericPoint X.left),
        linearSystemDimension (CurveDivisor.devissageDivisor hx D) =
          linearSystemDimension D - 1 := by
  constructor
  · intro h x hx
    exact (linearSystemDimension_sub_point_eq_sub_one_iff D hx).mpr (h x hx)
  · intro h x hx
    exact (linearSystemDimension_sub_point_eq_sub_one_iff D hx).mp (h x hx)

/-- The numerical very-ample predicate is equivalent to the dimension-drop
criterion for every ordered pair of closed points, including equal points. -/
theorem veryAmpleLinearSystem_iff_linearSystemDimension_drop
    (D : CurveDivisor k X) :
    VeryAmpleLinearSystem D ↔
      ∀ (x y : X.left) (hx : x ≠ genericPoint X.left)
        (hy : y ≠ genericPoint X.left),
        linearSystemDimension
            (CurveDivisor.devissageDivisor hy
              (CurveDivisor.devissageDivisor hx D)) =
          linearSystemDimension D - 2 := by
  constructor
  · intro h x y hx hy
    exact (linearSystemDimension_sub_two_points_eq_sub_two_iff D hx hy).mpr
      (h x y hx hy)
  · intro h x y hx hy
    exact (linearSystemDimension_sub_two_points_eq_sub_two_iff D hx hy).mp
      (h x y hx hy)

/-- Above the nonspeciality threshold, the complete linear-system dimension is
`deg D - g`. -/
theorem linearSystemDimension_eq_degree_sub_genus_of_degree_ge
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X}
    (hD : 2 * (curveGenus (k := k) (X := X) : ℤ) - 1 ≤
      CurveDivisor.degree D) :
    linearSystemDimension D = CurveDivisor.degree D -
      (curveGenus (k := k) (X := X) : ℤ) := by
  dsimp [linearSystemDimension]
  have h0 :=
    h0_divisorSheaf_eq_degree_add_one_sub_genus_of_degree_ge_two_mul_genus_sub_one
      (k := k) (X := X) sd hD
  omega

end
end Hartshorne
