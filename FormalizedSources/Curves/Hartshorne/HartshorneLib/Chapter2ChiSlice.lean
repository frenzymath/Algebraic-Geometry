/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HartshorneLib.Chapter2Chi
import Mathlib

/-! The degree-`≤ 1` cohomology slice of a short exact sequence, together with
the finiteness and Euler-characteristic bookkeeping needed by the curve files. -/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open Module (finrank)

section FiniteDimensional

variable {K V₁ V₂ V₃ : Type*} [DivisionRing K]
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/-- The middle term of an exact pair is finite-dimensional when both outer terms are. -/
theorem FiniteDimensional.of_exact (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (h : Function.Exact f g) [FiniteDimensional K V₁] [FiniteDimensional K V₃] :
    FiniteDimensional K V₂ := by
  have hexact : Function.Exact f g.rangeRestrict := fun y => by
    rw [← h y]
    exact ⟨fun hy => congrArg Subtype.val hy, fun hy => Subtype.ext hy⟩
  exact Module.Finite.of_exact hexact g.surjective_rangeRestrict

end FiniteDimensional

namespace AlgebraicGeometry

/-- The alternating finrank sum vanishes along a five-term exact sequence.

This is the linear-algebra bookkeeping used by the degree-zero cohomology slice;
the geometric input is kept separate from this purely algebraic lemma. -/
theorem finrank_alt_sum_eq_zero_of_exact₅
    {k V₁ V₂ V₃ V₄ V₅ : Type*} [Field k]
    [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    [AddCommGroup V₃] [Module k V₃] [AddCommGroup V₄] [Module k V₄]
    [AddCommGroup V₅] [Module k V₅]
    [Module.Finite k V₁] [Module.Finite k V₂] [Module.Finite k V₃]
    [Module.Finite k V₄] [Module.Finite k V₅]
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃)
    (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (h₁ : Function.Injective f₁) (e₁ : Function.Exact f₁ f₂)
    (e₂ : Function.Exact f₂ f₃) (e₃ : Function.Exact f₃ f₄)
    (h₄ : Function.Surjective f₄) :
    (finrank k V₁ : ℤ) - finrank k V₂ + finrank k V₃ - finrank k V₄
        + finrank k V₅ = 0 := by
  have rn₁ := LinearMap.finrank_range_add_finrank_ker f₁
  have rn₂ := LinearMap.finrank_range_add_finrank_ker f₂
  have rn₃ := LinearMap.finrank_range_add_finrank_ker f₃
  have rn₄ := LinearMap.finrank_range_add_finrank_ker f₄
  have hk₁ : finrank k (LinearMap.ker f₁) = 0 := by
    rw [LinearMap.ker_eq_bot.2 h₁, finrank_bot]
  have ke₁ : finrank k (LinearMap.ker f₂) = finrank k (LinearMap.range f₁) := by
    rw [e₁.linearMap_ker_eq]
  have ke₂ : finrank k (LinearMap.ker f₃) = finrank k (LinearMap.range f₂) := by
    rw [e₂.linearMap_ker_eq]
  have ke₃ : finrank k (LinearMap.ker f₄) = finrank k (LinearMap.range f₃) := by
    rw [e₃.linearMap_ker_eq]
  have hr₄ : finrank k (LinearMap.range f₄) = finrank k V₅ := by
    rw [LinearMap.range_eq_top.2 h₄, finrank_top]
  omega

end AlgebraicGeometry

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

namespace HModule

section Exactness

variable {R : Type u} [CommRing R] [HasSheafify J (ModuleCat.{u} R)]
  {S : ShortComplex (Sheaf J (ModuleCat.{u} R))}

noncomputable def delta (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    HModule J R S.X₃ n₀ →ₗ[R] HModule J R S.X₁ n₁ :=
  hS.extClass.postcompOfLinear R (constModuleSheaf J R) h

theorem exact_map_f_map_g (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (map S.f n) (map S.g n) := by
  have h := Abelian.Ext.covariant_sequence_exact₂' (constModuleSheaf J R) hS n
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

theorem exact_map_g_delta (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    Function.Exact (map S.g n₀) (delta hS h) := by
  have h' := Abelian.Ext.covariant_sequence_exact₃' (constModuleSheaf J R) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at h'
  exact h'

theorem exact_delta_map_f (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    Function.Exact (delta hS h) (map S.f n₁) := by
  have h' := Abelian.Ext.covariant_sequence_exact₁' (constModuleSheaf J R) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at h'
  exact h'

theorem injective_map_f_zero (hS : S.ShortExact) :
    Function.Injective (map S.f 0) := by
  letI := hS.mono_f
  exact Abelian.Ext.postcomp_mk₀_injective_of_mono (constModuleSheaf J R) S.f

theorem surjective_map_f (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (HModule J R S.X₃ n)] :
    Function.Surjective (map S.f n) := fun y =>
  (exact_map_f_map_g hS n y).mp (Subsingleton.elim _ 0)

end Exactness

section FinitenessTransfer

variable {R : Type u} [Field R] [HasSheafify J (ModuleCat.{u} R)]
  {S : ShortComplex (Sheaf J (ModuleCat.{u} R))}

theorem moduleFinite_middle (hS : S.ShortExact) (n : ℕ)
    [Module.Finite R (HModule J R S.X₁ n)] [Module.Finite R (HModule J R S.X₃ n)] :
    Module.Finite R (HModule J R S.X₂ n) :=
  FiniteDimensional.of_exact (map S.f n) (map S.g n) (exact_map_f_map_g hS n)

theorem moduleFinite_left_zero (hS : S.ShortExact)
    [Module.Finite R (HModule J R S.X₂ 0)] :
    Module.Finite R (HModule J R S.X₁ 0) :=
  FiniteDimensional.of_injective (map S.f 0) (injective_map_f_zero hS)

theorem moduleFinite_left_succ (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    [Module.Finite R (HModule J R S.X₃ n₀)] [Module.Finite R (HModule J R S.X₂ n₁)] :
    Module.Finite R (HModule J R S.X₁ n₁) :=
  FiniteDimensional.of_exact (delta hS h) (map S.f n₁) (exact_delta_map_f hS h)

end FinitenessTransfer
end HModule

section ChiAdditivity

variable {R : Type u} [Field R] [HasSheafify J (ModuleCat.{u} R)]
  {S : ShortComplex (Sheaf J (ModuleCat.{u} R))}

theorem chi_eq_add_of_shortExact (hS : S.ShortExact)
    [Module.Finite R (HModule J R S.X₁ 0)] [Module.Finite R (HModule J R S.X₂ 0)]
    [Module.Finite R (HModule J R S.X₃ 0)] [Module.Finite R (HModule J R S.X₁ 1)]
    [Module.Finite R (HModule J R S.X₂ 1)] [Subsingleton (HModule J R S.X₃ 1)] :
    chi S.X₂ = chi S.X₁ + chi S.X₃ := by
  have hone : (0 : ℕ) + 1 = 1 := rfl
  have halt := AlgebraicGeometry.finrank_alt_sum_eq_zero_of_exact₅
    (HModule.map S.f 0) (HModule.map S.g 0) (HModule.delta hS hone) (HModule.map S.f 1)
    (HModule.injective_map_f_zero hS) (HModule.exact_map_f_map_g hS 0)
    (HModule.exact_map_g_delta hS hone) (HModule.exact_delta_map_f hS hone)
    (HModule.surjective_map_f hS 1)
  have h3 : h1 S.X₃ = 0 := h1_eq_zero inferInstance
  rw [chi, chi, chi, h3]
  unfold h0 h1
  omega

end ChiAdditivity
end CategoryTheory.Sheaf
