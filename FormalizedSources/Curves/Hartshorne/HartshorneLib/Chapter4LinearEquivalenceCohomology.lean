/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorSheafMul
import HartshorneLib.Chapter4DivisorSheafZero
import HartshorneLib.Chapter4RiemannRochEuler
import HartshorneLib.Chapter4SectionBound

/-!
# Cohomology invariance under linear equivalence

Multiplication by a nonzero rational function identifies the sheaves attached
to linearly equivalent divisors.  This file exposes the resulting invariance
of `h⁰`, `h¹`, and the strong `Subsingleton` form of `H¹`, together with the
degree-zero `h⁰` characterization used in IV.1.2.

The statements are transport results: they do not add a finiteness or a
canonical-sheaf assumption, and the principal-divisor witness remains visible
in the proof.
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

private noncomputable def linearlyEquivalentDivisorSheafIso
    {D E : CurveDivisor k X} (h : LinearlyEquivalent D E) :
    divisorSheaf D ≅ divisorSheaf E := by
  let hex : ∃ g : X.left.functionFieldˣ, D - E = principalDivisor g :=
    (linearlyEquivalent_iff_exists D E).mp h
  let g : X.left.functionFieldˣ := hex.choose
  have hg : D - E = principalDivisor g := hex.choose_spec
  have heq : D - principalDivisor g = E := by
    rw [← hg]
    abel
  rw [← heq]
  exact mulEquivDivisorSheaf g D

/-- `h⁰` of a divisor sheaf depends only on its linear-equivalence class. -/
theorem h0_divisorSheaf_eq_of_linearlyEquivalent
    {D E : CurveDivisor k X} (h : LinearlyEquivalent D E) :
    CategoryTheory.Sheaf.h0 (divisorSheaf D) =
      CategoryTheory.Sheaf.h0 (divisorSheaf E) :=
  CategoryTheory.Sheaf.h0_congr (linearlyEquivalentDivisorSheafIso h)

/-- `h¹` of a divisor sheaf depends only on its linear-equivalence class. -/
theorem h1_divisorSheaf_eq_of_linearlyEquivalent
    {D E : CurveDivisor k X} (h : LinearlyEquivalent D E) :
    CategoryTheory.Sheaf.h1 (divisorSheaf D) =
      CategoryTheory.Sheaf.h1 (divisorSheaf E) :=
  CategoryTheory.Sheaf.h1_congr (linearlyEquivalentDivisorSheafIso h)

/-- Degree-one cohomology vanishing transports across linear equivalence. -/
theorem subsingleton_hModule_one_of_linearlyEquivalent
    {D E : CurveDivisor k X} (h : LinearlyEquivalent D E)
    (hD : Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 1)) :
    Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf E) 1) :=
  (CategoryTheory.Sheaf.HModule.mapEquiv
    (linearlyEquivalentDivisorSheafIso h) 1).toEquiv.subsingleton_congr.mp hD

/-- Finite-dimensional `H⁰` transports across linear equivalence. -/
theorem moduleFinite_hModule_zero_of_linearlyEquivalent
    {D E : CurveDivisor k X}
    [Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0)]
    (h : LinearlyEquivalent D E) :
    Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf E) 0) :=
  Module.Finite.equiv
    (CategoryTheory.Sheaf.HModule.mapEquiv
      (linearlyEquivalentDivisorSheafIso h) 0)

/-- Finite-dimensional `H¹` transports across linear equivalence. -/
theorem moduleFinite_hModule_one_of_linearlyEquivalent
    {D E : CurveDivisor k X}
    [Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 1)]
    (h : LinearlyEquivalent D E) :
    Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf E) 1) :=
  Module.Finite.equiv
    (CategoryTheory.Sheaf.HModule.mapEquiv
      (linearlyEquivalentDivisorSheafIso h) 1)

/-- On a degree-zero divisor, `h⁰ = 1` exactly when the divisor is principal. -/
theorem h0_divisorSheaf_eq_one_iff_linearlyEquivalent_zero_of_degree_zero
    {D : CurveDivisor k X} (hD : CurveDivisor.degree D = 0) :
    CategoryTheory.Sheaf.h0 (divisorSheaf D) = 1 ↔
      LinearlyEquivalent D 0 := by
  constructor
  · intro h
    apply (h0_ne_zero_iff_linearlyEquivalent_zero_of_degree_zero hD).mp
    rw [h]
    exact Nat.one_ne_zero
  · intro h
    rw [h0_divisorSheaf_eq_of_linearlyEquivalent h]
    calc
      CategoryTheory.Sheaf.h0 (divisorSheaf (0 : CurveDivisor k X)) =
          CategoryTheory.Sheaf.h0 (X.left.moduleKSheaf k) :=
        CategoryTheory.Sheaf.h0_congr (divisorSheafZeroIso (X := X))
      _ = 1 := h0_moduleKSheaf_eq_one (k := k) (X := X)

end
end Hartshorne
