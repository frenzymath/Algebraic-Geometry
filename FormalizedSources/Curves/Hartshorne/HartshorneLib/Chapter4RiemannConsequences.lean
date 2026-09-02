/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4RiemannInequality
import HartshorneLib.Chapter4SectionBound

/-!
# Consequences of the genus form of Riemann's inequality

The Riemann inequality immediately gives the first effective-representative
existence bounds for divisor classes.  These statements package the numerical
content needed by later linear-system arguments while leaving base-point and
separation notions to their own geometric interfaces.
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

/-- A divisor whose degree reaches the genus has an effective representative. -/
theorem hasEffectiveRepresentative_of_curveGenus_le_degree
    {D : CurveDivisor k X}
    (hD : (curveGenus (k := k) (X := X) : ℤ) ≤ CurveDivisor.degree D) :
    HasEffectiveRepresentative D := by
  have hri := riemann_inequality_of_smoothProperIntegralCurve (k := k) (X := X) D
  have hposZ : (0 : ℤ) < (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) := by
    omega
  have hne : CategoryTheory.Sheaf.h0 (divisorSheaf D) ≠ 0 := by
    exact_mod_cast (ne_of_gt hposZ)
  exact (hasNonzeroRationalSection_iff_hasEffectiveRepresentative D).mp
    ((h0_ne_zero_iff_hasNonzeroRationalSection D).mp hne)

/-- Strictly exceeding the genus forces at least two global sections. -/
theorem two_le_h0_of_curveGenus_lt_degree
    {D : CurveDivisor k X}
    (hD : (curveGenus (k := k) (X := X) : ℤ) < CurveDivisor.degree D) :
    2 ≤ CategoryTheory.Sheaf.h0 (divisorSheaf D) := by
  have hri := riemann_inequality_of_smoothProperIntegralCurve (k := k) (X := X) D
  have hboundZ : (2 : ℤ) ≤ (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) := by
    omega
  exact_mod_cast hboundZ

end
end Hartshorne
