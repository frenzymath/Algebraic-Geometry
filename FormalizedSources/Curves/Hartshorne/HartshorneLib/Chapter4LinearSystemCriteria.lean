/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4Nonspecial

/-!
# Hartshorne IV.3.2: numerical linear-system criteria

The geometric notions of base-point-freeness and very ampleness are represented
here by their section-rank criteria.  This keeps the API available before a
scheme-theoretic morphism-to-projective-space layer is introduced.
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

/-- Numerical base-point-freeness: deleting any closed point lowers `h⁰` by one.

This is the section-dimension formulation of Hartshorne IV.3.1.
-/
def BasePointFreeLinearSystem (D : CurveDivisor k X) : Prop :=
  ∀ (x : X.left) (hx : x ≠ genericPoint X.left),
    (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) -
        CategoryTheory.Sheaf.h0
          (divisorSheaf (CurveDivisor.devissageDivisor hx D)) = 1

/-- Numerical very ampleness: deleting two (possibly equal) closed points lowers
`h⁰` by two.  This is the section-dimension formulation of Hartshorne IV.3.1.
-/
def VeryAmpleLinearSystem (D : CurveDivisor k X) : Prop :=
  ∀ (x y : X.left)
    (hx : x ≠ genericPoint X.left) (hy : y ≠ genericPoint X.left),
    (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) -
        CategoryTheory.Sheaf.h0
          (divisorSheaf
            (CurveDivisor.devissageDivisor hy
              (CurveDivisor.devissageDivisor hx D))) = 2

/-- Degree at least `2g` implies numerical base-point-freeness (IV.3.2). -/
theorem basePointFreeLinearSystem_of_degree_ge_two_mul_genus
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X}
    (hD : 2 * (curveGenus (k := k) (X := X) : ℤ) ≤
      CurveDivisor.degree D) :
    BasePointFreeLinearSystem D := by
  intro x hx
  exact h0_divisorSheaf_sub_point_sub_eq_one_of_degree_ge_two_mul_genus
    (k := k) (X := X) sd hD hx

/-- Degree at least `2g+1` implies numerical very ampleness (IV.3.2). -/
theorem veryAmpleLinearSystem_of_degree_ge_two_mul_genus_plus_one
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X}
    (hD : 2 * (curveGenus (k := k) (X := X) : ℤ) + 1 ≤
      CurveDivisor.degree D) :
    VeryAmpleLinearSystem D := by
  intro x y hx hy
  exact h0_divisorSheaf_sub_two_points_sub_eq_two_of_degree_ge_two_mul_genus_plus_one
    (k := k) (X := X) sd hD hx hy

end
end Hartshorne
