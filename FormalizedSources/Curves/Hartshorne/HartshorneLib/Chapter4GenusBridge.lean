/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4FiniteMapP1Cohomology
import HartshorneLib.Chapter4SerreDuality

/-! # The genus bridge for smooth proper integral curves

The genus is represented here by the dimension of degree-one cohomology of the
structure sheaf.  This file only packages consequences of the existing finite
map and Serre-duality interfaces; it does not assert existence of a canonical
divisor or any additional geometric input.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

noncomputable section

variable {k : Type u} [Field k] [algClosed : IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [integral : IsIntegral X.left]
  [smooth : SmoothOfRelativeDimension 1 X.hom] [proper : IsProper X.hom]

attribute [local instance] Scheme.overModule

/-- The (cohomological) genus of a smooth proper integral curve. -/
-- Keep the geometric hypotheses in the public signature: the cohomology term
-- itself does not mention those typeclass instances syntactically.
noncomputable def curveGenus : ℕ :=
  let _ := algClosed
  let _ := integral
  let _ := smooth
  let _ := proper
  CategoryTheory.Sheaf.h1 (X.left.moduleKSheaf k)

/- The degree-one structure-sheaf cohomology carrying the genus is finite. -/
omit [IsAlgClosed k] in
lemma moduleFinite_curveGenus_carrier :
    Module.Finite k
      (Sheaf.HModule (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 1) :=
  moduleFinite_moduleKSheaf_one_of_smoothProperIntegralCurve (X := X)

/-- Riemann--Roch in terms of the cohomological genus. -/
theorem riemannRoch_of_curveSerreDuality_genus
    (sd : CurveSerreDualityData (k := k) (X := X))
    (D : CurveDivisor k X) :
    (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) -
        (CategoryTheory.Sheaf.h0
          (divisorSheaf (sd.canonicalDivisor - D)) : ℤ) =
      CurveDivisor.degree D + 1 - (curveGenus (k := k) (X := X) : ℤ) := by
  simpa only [curveGenus] using
    (riemannRoch_of_curveSerreDuality (k := k) (X := X) sd D)

/- Genus zero forces the degree-one structure-sheaf cohomology to be subsingleton. -/
theorem subsingleton_h1_of_curveGenus_eq_zero
    (hgen : curveGenus (k := k) (X := X) = 0) :
    Subsingleton
      (Sheaf.HModule (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 1) := by
  letI := moduleFinite_curveGenus_carrier (k := k) (X := X)
  have hfin : Module.finrank k
      (Sheaf.HModule (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 1) = 0 := by
    simpa only [curveGenus, CategoryTheory.Sheaf.h1] using hgen
  exact (Module.finrank_zero_iff).mp hfin

end
end Hartshorne
