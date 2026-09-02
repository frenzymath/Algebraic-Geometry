/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4GenusBridge

/-!
# The genus-normalized Riemann inequality

The curve genus is the dimension of the first cohomology of the structure
sheaf.  Substituting this definition into the Euler-characteristic formula
gives the usual genus form of the curve ledger, and nonnegativity of first
cohomology yields the classical Riemann inequality.
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

/-- The Euler characteristic of a divisor sheaf in genus-normalized form. -/
theorem chi_divisorSheaf_eq_one_sub_curveGenus_add_degree
    (D : CurveDivisor k X) :
    CategoryTheory.Sheaf.chi (divisorSheaf D) =
      1 - (curveGenus (k := k) (X := X) : ℤ) +
        CurveDivisor.degree D := by
  simpa only [curveGenus] using
    (chi_divisorSheaf_eq_one_sub_h1_add_degree (k := k) (X := X) D)

/-- The classical Riemann inequality for a smooth proper integral curve. -/
theorem riemann_inequality_of_smoothProperIntegralCurve
    (D : CurveDivisor k X) :
    CurveDivisor.degree D + 1 -
          (curveGenus (k := k) (X := X) : ℤ) ≤
      (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) := by
  have hχ := chi_divisorSheaf_eq_one_sub_curveGenus_add_degree
    (k := k) (X := X) D
  have hnonneg :
      (0 : ℤ) ≤ (CategoryTheory.Sheaf.h1 (divisorSheaf D) : ℤ) := by
    exact_mod_cast Nat.zero_le (CategoryTheory.Sheaf.h1 (divisorSheaf D))
  simp only [CategoryTheory.Sheaf.chi] at hχ
  omega

end
end Hartshorne
