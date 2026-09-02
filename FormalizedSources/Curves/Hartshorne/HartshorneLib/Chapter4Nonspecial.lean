/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4CanonicalDegree
import HartshorneLib.Chapter4SectionBound
import HartshorneLib.Chapter4DivisorDegreeStep
import HartshorneLib.Chapter4RiemannInequality

/-!
# Nonspecial divisors and the numerical linear-system bounds

The explicit Serre-duality certificate identifies `H¹(𝒪(D))` with sections of
the complementary canonical divisor.  The negative-degree section obstruction
then gives the usual nonspeciality threshold.  The resulting exact `h⁰`
formula is packaged at the thresholds used for the base-point-free and
very-ample linear-system criteria.
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

/-- A divisor of degree strictly larger than the canonical degree is
nonspecial. -/
theorem h1_divisorSheaf_eq_zero_of_degree_gt_canonical
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X}
    (hD : CurveDivisor.degree sd.canonicalDivisor < CurveDivisor.degree D) :
    CategoryTheory.Sheaf.h1 (divisorSheaf D) = 0 := by
  have hcompdeg : CurveDivisor.degree (sd.canonicalDivisor - D) < 0 := by
    rw [CurveDivisor.degree_sub]
    omega
  have hcomp : CategoryTheory.Sheaf.h0
      (divisorSheaf (sd.canonicalDivisor - D)) = 0 := by
    by_contra hne
    have hnonneg := degree_nonneg_of_h0_ne_zero
      (k := k) (X := X) (D := sd.canonicalDivisor - D) hne
    omega
  rw [h1_divisorSheaf_eq_h0_complementary sd D, hcomp]

/-- The standard genus form of the nonspeciality threshold. -/
theorem h1_divisorSheaf_eq_zero_of_degree_ge_two_mul_genus_sub_one
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X}
    (hD : 2 * (curveGenus (k := k) (X := X) : ℤ) - 1 ≤
      CurveDivisor.degree D) :
    CategoryTheory.Sheaf.h1 (divisorSheaf D) = 0 := by
  apply h1_divisorSheaf_eq_zero_of_degree_gt_canonical sd
  have hK := degree_canonicalDivisor_eq_two_mul_h1_sub_two
    (k := k) (X := X) sd
  have hK' : CurveDivisor.degree sd.canonicalDivisor =
      2 * (curveGenus (k := k) (X := X) : ℤ) - 2 := by
    simpa only [curveGenus] using hK
  rw [hK']
  omega

/-- Above the nonspeciality threshold, Riemann--Roch is an exact formula for
the dimension of global sections. -/
theorem h0_divisorSheaf_eq_degree_add_one_sub_genus_of_degree_ge_two_mul_genus_sub_one
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X}
    (hD : 2 * (curveGenus (k := k) (X := X) : ℤ) - 1 ≤
      CurveDivisor.degree D) :
    (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) =
      CurveDivisor.degree D + 1 - (curveGenus (k := k) (X := X) : ℤ) := by
  have hχ := chi_divisorSheaf_eq_one_sub_curveGenus_add_degree
    (k := k) (X := X) D
  have h1zero := h1_divisorSheaf_eq_zero_of_degree_ge_two_mul_genus_sub_one
    (k := k) (X := X) sd hD
  rw [CategoryTheory.Sheaf.chi, h1zero, Nat.cast_zero, sub_zero] at hχ
  omega

/-- If `deg D ≥ 2g`, deleting one closed point drops `h⁰` by exactly one. -/
theorem h0_divisorSheaf_sub_point_sub_eq_one_of_degree_ge_two_mul_genus
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X}
    (hD : 2 * (curveGenus (k := k) (X := X) : ℤ) ≤
      CurveDivisor.degree D)
    {x : X.left} (hx : x ≠ genericPoint X.left) :
    (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) -
        CategoryTheory.Sheaf.h0
          (divisorSheaf (CurveDivisor.devissageDivisor hx D)) = 1 := by
  have hD0 := h0_divisorSheaf_eq_degree_add_one_sub_genus_of_degree_ge_two_mul_genus_sub_one
    (k := k) (X := X) sd (D := D) (by omega)
  have hdeg := CurveDivisor.degree_devissageDivisor (k := k) (X := X) hx D
  have hD1 := h0_divisorSheaf_eq_degree_add_one_sub_genus_of_degree_ge_two_mul_genus_sub_one
    (k := k) (X := X) sd
    (D := CurveDivisor.devissageDivisor hx D) (by omega)
  omega

/-- If `deg D ≥ 2g+1`, deleting two (possibly equal) closed points drops
`h⁰` by exactly two. -/
theorem h0_divisorSheaf_sub_two_points_sub_eq_two_of_degree_ge_two_mul_genus_plus_one
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X}
    (hD : 2 * (curveGenus (k := k) (X := X) : ℤ) + 1 ≤
      CurveDivisor.degree D)
    {x y : X.left} (hx : x ≠ genericPoint X.left)
    (hy : y ≠ genericPoint X.left) :
    (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) -
        CategoryTheory.Sheaf.h0 (divisorSheaf
          (CurveDivisor.devissageDivisor hy
            (CurveDivisor.devissageDivisor hx D))) = 2 := by
  have hD0 := h0_divisorSheaf_eq_degree_add_one_sub_genus_of_degree_ge_two_mul_genus_sub_one
    (k := k) (X := X) sd (D := D) (by omega)
  have hdeg₁ := CurveDivisor.degree_devissageDivisor (k := k) (X := X) hx D
  have hD1 := h0_divisorSheaf_eq_degree_add_one_sub_genus_of_degree_ge_two_mul_genus_sub_one
    (k := k) (X := X) sd
    (D := CurveDivisor.devissageDivisor hx D) (by omega)
  have hdeg₂ := CurveDivisor.degree_devissageDivisor (k := k) (X := X) hy
    (CurveDivisor.devissageDivisor hx D)
  have hD2 := h0_divisorSheaf_eq_degree_add_one_sub_genus_of_degree_ge_two_mul_genus_sub_one
    (k := k) (X := X) sd
    (D := CurveDivisor.devissageDivisor hy
      (CurveDivisor.devissageDivisor hx D)) (by omega)
  omega

end
end Hartshorne
