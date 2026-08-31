/-
Copyright (c) 2026 The StacksPart03Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart03Lib Contributors
-/

import StacksPart03Lib.PeriodicLength

/-!
# Euler characteristic of an exact six-cycle

An exact cycle splits at every vertex into the image entering that vertex and
the image leaving it.  Additivity of finite length for those six short exact
sequences makes the image lengths cancel in the alternating sum.
-/

namespace StacksPart03

namespace TwoPeriodicComplex

variable {R V₀ V₁ V₂ V₃ V₄ V₅ : Type*} [Ring R]
  [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup V₂]
  [AddCommGroup V₃] [AddCommGroup V₄] [AddCommGroup V₅]
  [Module R V₀] [Module R V₁] [Module R V₂]
  [Module R V₃] [Module R V₄] [Module R V₅]

/-- The alternating sum of finite lengths in an exact cyclic six-term sequence
is zero.

The exactness hypothesis `exactᵢ` is exactness at `Vᵢ`; for example,
`exact₀` says that the image of `f₅ : V₅ → V₀` is the kernel of
`f₀ : V₀ → V₁`.
-/
theorem finiteLengthInt_alternating_sum_eq_zero_of_six_cycle
    (f₀ : V₀ →ₗ[R] V₁) (f₁ : V₁ →ₗ[R] V₂) (f₂ : V₂ →ₗ[R] V₃)
    (f₃ : V₃ →ₗ[R] V₄) (f₄ : V₄ →ₗ[R] V₅) (f₅ : V₅ →ₗ[R] V₀)
    (exact₀ : Function.Exact f₅ f₀) (exact₁ : Function.Exact f₀ f₁)
    (exact₂ : Function.Exact f₁ f₂) (exact₃ : Function.Exact f₂ f₃)
    (exact₄ : Function.Exact f₃ f₄) (exact₅ : Function.Exact f₄ f₅)
    (h₀ : IsFiniteLength R V₀) (h₁ : IsFiniteLength R V₁)
    (h₂ : IsFiniteLength R V₂) (h₃ : IsFiniteLength R V₃)
    (h₄ : IsFiniteLength R V₄) (h₅ : IsFiniteLength R V₅) :
    finiteLengthInt R V₀ h₀ - finiteLengthInt R V₁ h₁ +
      finiteLengthInt R V₂ h₂ - finiteLengthInt R V₃ h₃ +
      finiteLengthInt R V₄ h₄ - finiteLengthInt R V₅ h₅ = 0 := by
  have hr₀ : IsFiniteLength R (LinearMap.range f₀) :=
    IsFiniteLength.of_surjective h₀ f₀.surjective_rangeRestrict
  have hr₁ : IsFiniteLength R (LinearMap.range f₁) :=
    IsFiniteLength.of_surjective h₁ f₁.surjective_rangeRestrict
  have hr₂ : IsFiniteLength R (LinearMap.range f₂) :=
    IsFiniteLength.of_surjective h₂ f₂.surjective_rangeRestrict
  have hr₃ : IsFiniteLength R (LinearMap.range f₃) :=
    IsFiniteLength.of_surjective h₃ f₃.surjective_rangeRestrict
  have hr₄ : IsFiniteLength R (LinearMap.range f₄) :=
    IsFiniteLength.of_surjective h₄ f₄.surjective_rangeRestrict
  have hr₅ : IsFiniteLength R (LinearMap.range f₅) :=
    IsFiniteLength.of_surjective h₅ f₅.surjective_rangeRestrict
  have e₀ : finiteLengthInt R V₀ h₀ =
      finiteLengthInt R (LinearMap.range f₅) hr₅ +
        finiteLengthInt R (LinearMap.range f₀) hr₀ :=
    finiteLengthInt_eq_add_of_exact (LinearMap.range f₅).subtype f₀.rangeRestrict
      (Submodule.subtype_injective _) f₀.surjective_rangeRestrict
      exact₀.linearMap_rangeRestrict hr₅ h₀ hr₀
  have e₁ : finiteLengthInt R V₁ h₁ =
      finiteLengthInt R (LinearMap.range f₀) hr₀ +
        finiteLengthInt R (LinearMap.range f₁) hr₁ :=
    finiteLengthInt_eq_add_of_exact (LinearMap.range f₀).subtype f₁.rangeRestrict
      (Submodule.subtype_injective _) f₁.surjective_rangeRestrict
      exact₁.linearMap_rangeRestrict hr₀ h₁ hr₁
  have e₂ : finiteLengthInt R V₂ h₂ =
      finiteLengthInt R (LinearMap.range f₁) hr₁ +
        finiteLengthInt R (LinearMap.range f₂) hr₂ :=
    finiteLengthInt_eq_add_of_exact (LinearMap.range f₁).subtype f₂.rangeRestrict
      (Submodule.subtype_injective _) f₂.surjective_rangeRestrict
      exact₂.linearMap_rangeRestrict hr₁ h₂ hr₂
  have e₃ : finiteLengthInt R V₃ h₃ =
      finiteLengthInt R (LinearMap.range f₂) hr₂ +
        finiteLengthInt R (LinearMap.range f₃) hr₃ :=
    finiteLengthInt_eq_add_of_exact (LinearMap.range f₂).subtype f₃.rangeRestrict
      (Submodule.subtype_injective _) f₃.surjective_rangeRestrict
      exact₃.linearMap_rangeRestrict hr₂ h₃ hr₃
  have e₄ : finiteLengthInt R V₄ h₄ =
      finiteLengthInt R (LinearMap.range f₃) hr₃ +
        finiteLengthInt R (LinearMap.range f₄) hr₄ :=
    finiteLengthInt_eq_add_of_exact (LinearMap.range f₃).subtype f₄.rangeRestrict
      (Submodule.subtype_injective _) f₄.surjective_rangeRestrict
      exact₄.linearMap_rangeRestrict hr₃ h₄ hr₄
  have e₅ : finiteLengthInt R V₅ h₅ =
      finiteLengthInt R (LinearMap.range f₄) hr₄ +
        finiteLengthInt R (LinearMap.range f₅) hr₅ :=
    finiteLengthInt_eq_add_of_exact (LinearMap.range f₄).subtype f₅.rangeRestrict
      (Submodule.subtype_injective _) f₅.surjective_rangeRestrict
      exact₅.linearMap_rangeRestrict hr₄ h₅ hr₅
  linarith

end TwoPeriodicComplex

end StacksPart03
