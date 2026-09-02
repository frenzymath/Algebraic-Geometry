/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorDevissageExact
import HartshorneLib.Chapter4DivisorDegreeStep
import HartshorneLib.Chapter4SkyscraperCohomology
import HartshorneLib.Chapter2ChiSlice

/-!
# Section drop across the divisor dévissage sequence

This file records the degree-zero and degree-one consequences of the short exact
sequence `0 ⟶ 𝒪(D - x) ⟶ 𝒪(D) ⟶ sky_x J ⟶ 0`.
-/

set_option autoImplicit false
set_option linter.style.openClassical false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

section Slice

variable {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X)

/-- The degree-one cohomology of the skyscraper quotient is subsingleton. -/
private theorem subsingleton_devissage_X₃_one :
    Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₃ 1) := by
  change Subsingleton
    (CategoryTheory.Sheaf.HModule
      (Opens.grothendieckTopology (X.left : TopCat)) k
      (skyModule (X := X) x (jumpModule hx D)) 1)
  exact skyModule_subsingleton_hModule_one (X := X) x (jumpModule hx D)

/-- `H⁰(𝒪(D - x)) ↪ H⁰(𝒪(D))`, the injective left map of the slice. -/
theorem injective_hModule_zero_divisorSheafLE :
    Function.Injective
      (CategoryTheory.Sheaf.HModule.map (devissageSES hx D).f 0) := by
  exact CategoryTheory.Sheaf.HModule.injective_map_f_zero
    (devissageSES_shortExact hx D)

/-- `H¹(𝒪(D - x)) ↠ H¹(𝒪(D))`, since the skyscraper quotient has no `H¹`. -/
theorem surjective_hModule_one_divisorSheafLE :
    Function.Surjective
      (CategoryTheory.Sheaf.HModule.map (devissageSES hx D).f 1) := by
  letI : Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₃ 1) := subsingleton_devissage_X₃_one hx D
  exact CategoryTheory.Sheaf.HModule.surjective_map_f
    (devissageSES_shortExact hx D) 1

end Slice

section Step

variable {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X)

/-- A section with the smaller divisor bound injects into the larger section space. -/
theorem h0_sub_point_le
    (hD : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0)) :
    CategoryTheory.Sheaf.h0 (divisorSheaf (CurveDivisor.devissageDivisor hx D)) ≤
      CategoryTheory.Sheaf.h0 (divisorSheaf D) := by
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0) := hD
  have hinj := injective_hModule_zero_divisorSheafLE hx D
  change Module.finrank k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₁ 0) ≤
    Module.finrank k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₂ 0)
  haveI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₂ 0) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0)
    exact hD
  exact LinearMap.finrank_le_finrank_of_injective
    (f := CategoryTheory.Sheaf.HModule.map (devissageSES hx D).f 0) hinj

/-- The degree-one cohomology rank is antitone across one divisor-deletion step. -/
theorem h1_le_h1_sub_point
    (hD : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1)) :
    CategoryTheory.Sheaf.h1 (divisorSheaf D) ≤
      CategoryTheory.Sheaf.h1 (divisorSheaf (CurveDivisor.devissageDivisor hx D)) := by
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1) := hD
  have hsurj := surjective_hModule_one_divisorSheafLE hx D
  change Module.finrank k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₂ 1) ≤
    Module.finrank k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₁ 1)
  haveI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₁ 1) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1)
    exact hD
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := CategoryTheory.Sheaf.HModule.map (devissageSES hx D).f 1) hsurj

end Step

section ChiStep

variable {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X)

private theorem chi_skyModule_jump_eq_residueDeg :
    CategoryTheory.Sheaf.chi
        (skyModule (X := X) x (jumpModule hx D)) =
      (X.left.residueDeg k x : ℤ) := by
  rw [CategoryTheory.Sheaf.chi_eq_h0
    (skyModule_subsingleton_hModule_one (X := X) x (jumpModule hx D))]
  rw [h0_skyModule, finrank_jumpModule]

private theorem chi_devissage_step
    (hD0 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 0))
    (hD1 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1))
    (hD0' : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0))
    (hD1' : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 1)) :
    CategoryTheory.Sheaf.chi (divisorSheaf D) =
      CategoryTheory.Sheaf.chi
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) +
        (X.left.residueDeg k x : ℤ) := by
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 0) := hD0
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1) := hD1
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0) := hD0'
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 1) := hD1'
  letI : Module.Finite k (jumpModule hx D) := moduleFinite_jumpModule hx D
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₃ 0) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (skyModule (X := X) x (jumpModule hx D)) 0)
    exact Module.Finite.equiv
      (skyModuleGammaEquiv (X := X) x (jumpModule hx D)).symm
  letI : Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₃ 1) := subsingleton_devissage_X₃_one hx D
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₁ 0) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 0)
    exact hD0
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₁ 1) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1)
    exact hD1
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₂ 0) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0)
    exact hD0'
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₂ 1) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 1)
    exact hD1'
  have hchi := CategoryTheory.Sheaf.chi_eq_add_of_shortExact
    (devissageSES_shortExact hx D)
  change CategoryTheory.Sheaf.chi (divisorSheaf D) =
      CategoryTheory.Sheaf.chi
          (divisorSheaf (CurveDivisor.devissageDivisor hx D)) +
        CategoryTheory.Sheaf.chi
          (skyModule (X := X) x (jumpModule hx D)) at hchi
  rw [chi_skyModule_jump_eq_residueDeg hx D] at hchi
  exact hchi

end ChiStep

section Drop

variable {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X)

/-- The gain in `h0` at one point is bounded by the residue degree. -/
theorem h0_le_h0_sub_point_add_residueDeg
    (hD0 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 0))
    (hD1 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1))
    (hD0' : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0))
    (hD1' : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 1)) :
    CategoryTheory.Sheaf.h0 (divisorSheaf D) ≤
      CategoryTheory.Sheaf.h0
          (divisorSheaf (CurveDivisor.devissageDivisor hx D)) +
        X.left.residueDeg k x := by
  have hstep := chi_devissage_step hx D hD0 hD1 hD0' hD1'
  have hmono := h1_le_h1_sub_point hx D hD1
  rw [CategoryTheory.Sheaf.chi, CategoryTheory.Sheaf.chi] at hstep
  omega

/-- The `h0` gain and `h1` loss across one point add to its residue degree. -/
theorem h0_sub_h0_sub_point_add_h1_sub_h1_sub_point
    (hD0 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 0))
    (hD1 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1))
    (hD0' : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0))
    (hD1' : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 1)) :
    ((CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) -
        CategoryTheory.Sheaf.h0
          (divisorSheaf (CurveDivisor.devissageDivisor hx D))) +
      ((CategoryTheory.Sheaf.h1
          (divisorSheaf (CurveDivisor.devissageDivisor hx D)) : ℤ) -
        CategoryTheory.Sheaf.h1 (divisorSheaf D)) =
      (X.left.residueDeg k x : ℤ) := by
  have hstep := chi_devissage_step hx D hD0 hD1 hD0' hD1'
  rw [CategoryTheory.Sheaf.chi, CategoryTheory.Sheaf.chi] at hstep
  omega

end Drop

section Peel

variable {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X)

/-- `H¹`-vanishing propagates upward across one divisor-dévissage step. -/
theorem subsingleton_hModule_one_of_subsingleton_sub_point
    (h : Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1)) :
    Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 1) := by
  have hsurj := surjective_hModule_one_divisorSheafLE hx D
  haveI hsub : Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₁ 1) := by
    change Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1)
    exact h
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [Subsingleton.elim a' b']⟩

/-- The `h¹` numerical vanishing consequence of the one-step peel. -/
theorem h1_eq_zero_of_h1_sub_point_eq_zero
    (hD : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (CurveDivisor.devissageDivisor hx D)) 1))
    (h : CategoryTheory.Sheaf.h1
      (divisorSheaf (CurveDivisor.devissageDivisor hx D)) = 0) :
    CategoryTheory.Sheaf.h1 (divisorSheaf D) = 0 := by
  have hmono := h1_le_h1_sub_point hx D hD
  omega

end Peel

end
end Hartshorne
