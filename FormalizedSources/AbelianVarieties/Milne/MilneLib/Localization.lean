/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import MilneLib.LocalProperties

/-!
# Localization of residue-surjective maps

The residue-quotient criteria in `LocalProperties` transport to canonical
localizations at maximal ideals.
-/

open IsLocalizedModule

namespace MilneLib

/-- A residue-surjective map at a maximal ideal remains surjective after
localizing at the corresponding prime complement. -/
theorem LinearMap.surjective_localized_at_maximal_of_surjective_residue
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R N]
    (J : Ideal R) [J.IsMaximal]
    (f : M →ₗ[R] N)
    (h : Function.Surjective (((J • (⊤ : Submodule R N)).mkQ) ∘ₗ f)) :
    Function.Surjective (LocalizedModule.map J.primeCompl f) := by
  letI : Module.Finite (Localization J.primeCompl)
      (LocalizedModule J.primeCompl N) :=
    Module.Finite.of_isLocalizedModule J.primeCompl
      (LocalizedModule.mkLinearMap J.primeCompl N)
  apply LinearMap.surjective_of_surjective_residue
  change Function.Surjective
    (((IsLocalRing.maximalIdeal (Localization J.primeCompl) •
      (⊤ : Submodule (Localization J.primeCompl) (LocalizedModule J.primeCompl N))).mkQ) ∘ₗ
      LinearMap.extendScalarsOfIsLocalization J.primeCompl (Localization J.primeCompl)
        (IsLocalizedModule.map J.primeCompl
          (LocalizedModule.mkLinearMap J.primeCompl M)
          (LocalizedModule.mkLinearMap J.primeCompl N) f))
  have hrange : J • (⊤ : Submodule R N) ⊔ f.range = ⊤ := by
    rw [← Submodule.map_mkQ_eq_top, ← LinearMap.range_comp]
    exact LinearMap.range_eq_top.mpr h
  have hlocal := congrArg
    (Submodule.localized'FrameHom (Localization J.primeCompl) J.primeCompl
      (LocalizedModule.mkLinearMap J.primeCompl N)) hrange
  rw [map_sup] at hlocal
  simp only [Submodule.IsLocalizedModule.localized'FrameHom_apply] at hlocal
  rw [LinearMap.localized'_range_eq_range_localizedMap
    (Localization J.primeCompl) J.primeCompl
    (LocalizedModule.mkLinearMap J.primeCompl M)
    (LocalizedModule.mkLinearMap J.primeCompl N) f] at hlocal
  apply LinearMap.range_eq_top.mp
  rw [LinearMap.range_comp, Submodule.map_mkQ_eq_top]
  simpa only [Submodule.localized'_smul, Ideal.localized'_eq_map,
    Localization.AtPrime.map_eq_maximalIdeal, Submodule.localized'_top] using hlocal

/-- For a finite target, surjectivity is equivalent to surjectivity on every
maximal residue quotient. -/
theorem LinearMap.surjective_iff_surjective_residue_at_maximal
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) :
    Function.Surjective f ↔
      ∀ (J : Ideal R) [J.IsMaximal],
        Function.Surjective (((J • (⊤ : Submodule R N)).mkQ) ∘ₗ f) := by
  constructor
  · intro hf J hJ
    exact (Submodule.mkQ_surjective _).comp hf
  · exact LinearMap.surjective_of_surjective_residue_at_maximal f

end MilneLib
