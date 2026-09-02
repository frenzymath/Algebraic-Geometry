/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4LinearEquivalenceCohomology

/-!
# Hartshorne IV.1.2: degree-zero divisors

A divisor with a nonzero global section has nonnegative degree, and in degree
zero it is linearly equivalent to zero.  Consequently, a degree-zero divisor
has at most one independent global section, with equality exactly for the
trivial divisor class.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-- A degree-zero divisor has at most one independent global section. -/
theorem h0_divisorSheaf_le_one_of_degree_zero
    {D : CurveDivisor k X} (hD : CurveDivisor.degree D = 0) :
    CategoryTheory.Sheaf.h0 (divisorSheaf D) ≤ 1 := by
  by_cases h0 : CategoryTheory.Sheaf.h0 (divisorSheaf D) = 0
  · omega
  · have hlin : LinearlyEquivalent D 0 :=
      (h0_ne_zero_iff_linearlyEquivalent_zero_of_degree_zero hD).mp h0
    have hone : CategoryTheory.Sheaf.h0 (divisorSheaf D) = 1 :=
      (h0_divisorSheaf_eq_one_iff_linearlyEquivalent_zero_of_degree_zero hD).mpr hlin
    omega

/-- In degree zero, `h⁰ = 1` exactly for the trivial divisor class. -/
theorem h0_eq_one_iff_linearlyEquivalent_zero_of_degree_zero
    {D : CurveDivisor k X} (hD : CurveDivisor.degree D = 0) :
    CategoryTheory.Sheaf.h0 (divisorSheaf D) = 1 ↔ LinearlyEquivalent D 0 :=
  h0_divisorSheaf_eq_one_iff_linearlyEquivalent_zero_of_degree_zero hD

/-- The degree-zero part of Hartshorne IV.1.2: a divisor with a nonzero global
section represents the trivial divisor class. -/
theorem linearlyEquivalent_zero_of_h0_ne_zero_of_degree_zero
    {D : CurveDivisor k X}
    (h0 : CategoryTheory.Sheaf.h0 (divisorSheaf D) ≠ 0)
    (hD : CurveDivisor.degree D = 0) :
    LinearlyEquivalent D 0 :=
  (h0_ne_zero_iff_linearlyEquivalent_zero_of_degree_zero hD).mp h0

/-- Hartshorne IV.1.2 in bundled numerical and degree-zero form: a nonzero
global section forces nonnegative degree, and degree zero forces triviality of
the divisor class. -/
theorem degree_nonneg_and_linearlyEquivalent_zero_of_h0_ne_zero
    {D : CurveDivisor k X}
    (h0 : CategoryTheory.Sheaf.h0 (divisorSheaf D) ≠ 0) :
    0 ≤ CurveDivisor.degree D ∧
      (CurveDivisor.degree D = 0 → LinearlyEquivalent D 0) := by
  refine ⟨degree_nonneg_of_h0_ne_zero h0, ?_⟩
  intro hD
  exact linearlyEquivalent_zero_of_h0_ne_zero_of_degree_zero h0 hD

/-- The bundled statement specialized to a degree-zero divisor. -/
theorem degree_nonneg_and_linearlyEquivalent_zero_of_h0_ne_zero_of_degree_zero
    {D : CurveDivisor k X}
    (h0 : CategoryTheory.Sheaf.h0 (divisorSheaf D) ≠ 0)
    (hD : CurveDivisor.degree D = 0) :
    0 ≤ CurveDivisor.degree D ∧ LinearlyEquivalent D 0 :=
  ⟨degree_nonneg_of_h0_ne_zero h0,
    linearlyEquivalent_zero_of_h0_ne_zero_of_degree_zero h0 hD⟩

end
end Hartshorne
