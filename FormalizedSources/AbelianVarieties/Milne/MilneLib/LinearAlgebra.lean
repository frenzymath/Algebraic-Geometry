/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Rank-one module maps

The first algebraic lemma in Milne's chapter on line bundles is the fact that
a surjection between free modules of rank one is automatically an
isomorphism.  We package a chosen rank-one basis as a linear equivalence with
the base ring; this keeps the statement independent of a particular basis
implementation while exposing the exact algebra used in the proof.
-/

namespace MilneLib

theorem LinearMap.bijective_of_surjective_rank_one
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (eM : M ≃ₗ[R] R) (eN : N ≃ₗ[R] R)
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Bijective f := by
  let g : R →ₗ[R] R := eN.toLinearMap.comp (f.comp eM.symm.toLinearMap)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨n, hn⟩ := eN.surjective y
    obtain ⟨m, hm⟩ := hf n
    refine ⟨eM m, ?_⟩
    simpa [g, hm] using hn
  have hginj : Function.Injective g :=
    (Module.Invertible.bijective_of_surjective hg).injective
  exact ⟨by
    intro x y hxy
    apply eM.injective
    apply hginj
    simpa [g] using congrArg eN hxy, hf⟩

/-- The index of the image of an injective endomorphism of a finite free
integer module is the absolute value of its determinant. -/
theorem LinearMap.natCard_quotient_range_eq_natAbs_det
    {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : M →ₗ[ℤ] M) (hf : Function.Injective f) :
    Nat.card (M ⧸ LinearMap.range f) = (LinearMap.det f).natAbs := by
  have hcomp :
      (LinearMap.range f).subtype ∘ₗ
        (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext x
    rfl
  rw [← hcomp]
  exact (Submodule.natAbs_det_equiv (LinearMap.range f)
    (LinearEquiv.ofInjective f hf)).symm

/-- Milne's index--determinant formula under the source hypothesis that the
endomorphism becomes an isomorphism after extending scalars to `ℚ`. -/
theorem LinearMap.natCard_quotient_range_eq_natAbs_det_of_baseChange_bijective
    {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : M →ₗ[ℤ] M)
    (hf : Function.Bijective (LinearMap.baseChange ℚ f)) :
    Nat.card (M ⧸ LinearMap.range f) = (LinearMap.det f).natAbs := by
  have hdetQ : LinearMap.det (LinearMap.baseChange ℚ f) ≠ 0 := by
    intro h
    have hker : (LinearMap.baseChange ℚ f).ker ≠ ⊥ :=
      LinearMap.det_eq_zero_iff_ker_ne_bot.mp h
    exact hker (LinearMap.ker_eq_bot.mpr hf.1)
  have hdetZ : LinearMap.det f ≠ 0 := by
    intro h
    apply hdetQ
    rw [LinearMap.det_baseChange, h, map_zero]
  apply LinearMap.natCard_quotient_range_eq_natAbs_det f
  rw [← LinearMap.ker_eq_bot]
  exact not_ne_iff.mp
    (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hdetZ)

end MilneLib
