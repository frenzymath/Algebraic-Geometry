/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4SerreDuality

/-!
# The numerical degree of a canonical divisor

The canonical divisor is part of the explicit Serre-duality certificate.  This
file records the numerical consequence that is available from that certificate
and the already-proved curve Euler ledger: its degree is `2 h¹(𝒪_X) - 2`.
The statement is deliberately conditional on the certificate, so it does not
silently assert existence or identify a canonical sheaf with differentials.
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

/-- The zero divisor has the same degree-zero cohomology as the structure sheaf. -/
theorem h0_divisorSheaf_zero_eq_one :
    CategoryTheory.Sheaf.h0
        (divisorSheaf (X := X) (0 : CurveDivisor k X)) = 1 := by
  calc
    CategoryTheory.Sheaf.h0
        (divisorSheaf (X := X) (0 : CurveDivisor k X)) =
        CategoryTheory.Sheaf.h0 (X.left.moduleKSheaf k) :=
      CategoryTheory.Sheaf.h0_congr (divisorSheafZeroIso (X := X))
    _ = 1 := h0_moduleKSheaf_eq_one (k := k) (X := X)

/-- The degree-one cohomology of the zero divisor is the structure-sheaf `h¹`. -/
theorem h1_divisorSheaf_zero_eq_structure :
    CategoryTheory.Sheaf.h1
        (divisorSheaf (X := X) (0 : CurveDivisor k X)) =
      CategoryTheory.Sheaf.h1 (X.left.moduleKSheaf k) :=
  CategoryTheory.Sheaf.h1_congr (divisorSheafZeroIso (X := X))

/-- Serre duality identifies sections of the canonical divisor with `h¹(𝒪_X)`. -/
theorem h0_canonicalDivisor_eq_h1_structure
    (sd : CurveSerreDualityData (k := k) (X := X)) :
    CategoryTheory.Sheaf.h0 (divisorSheaf sd.canonicalDivisor) =
      CategoryTheory.Sheaf.h1 (X.left.moduleKSheaf k) := by
  have hdual := h1_divisorSheaf_eq_h0_complementary
    (k := k) (X := X) sd (0 : CurveDivisor k X)
  calc
    CategoryTheory.Sheaf.h0 (divisorSheaf sd.canonicalDivisor) =
        CategoryTheory.Sheaf.h1
          (divisorSheaf (X := X) (0 : CurveDivisor k X)) := by
      simpa only [sub_zero] using hdual.symm
    _ = CategoryTheory.Sheaf.h1 (X.left.moduleKSheaf k) :=
      h1_divisorSheaf_zero_eq_structure (k := k) (X := X)

/-- The canonical divisor has degree `2 h¹(𝒪_X) - 2`. -/
theorem degree_canonicalDivisor_eq_two_mul_h1_sub_two
    (sd : CurveSerreDualityData (k := k) (X := X)) :
    (CurveDivisor.degree sd.canonicalDivisor : ℤ) =
      2 * (CategoryTheory.Sheaf.h1 (X.left.moduleKSheaf k) : ℤ) - 2 := by
  have hrr := riemannRoch_of_curveSerreDuality
    (k := k) (X := X) sd sd.canonicalDivisor
  have hK := h0_canonicalDivisor_eq_h1_structure
    (k := k) (X := X) sd
  have hzero := h0_divisorSheaf_zero_eq_one (k := k) (X := X)
  rw [sub_self, hzero, hK] at hrr
  omega

/-- The numerical Riemann inequality obtained from the same duality certificate. -/
theorem riemann_inequality_of_curveSerreDuality
    (sd : CurveSerreDualityData (k := k) (X := X))
    (D : CurveDivisor k X) :
    CurveDivisor.degree D + 1 -
          (CategoryTheory.Sheaf.h1 (X.left.moduleKSheaf k) : ℤ) ≤
      (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) := by
  have hrr := riemannRoch_of_curveSerreDuality
    (k := k) (X := X) sd D
  have hnonneg :
      (0 : ℤ) ≤
        (CategoryTheory.Sheaf.h0
          (divisorSheaf (sd.canonicalDivisor - D)) : ℤ) := by
    exact_mod_cast
      (Nat.zero_le
        (CategoryTheory.Sheaf.h0
          (divisorSheaf (sd.canonicalDivisor - D))))
  omega

end
end Hartshorne
