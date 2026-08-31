/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Trivializations of base-changed modules and their transition units

Let `A` be a commutative ring and `N` an `A`-module.  A **trivialization** of `N` over an
`A`-algebra `C` is a `C`-linear isomorphism `t : C ⊗[A] N ≃ₗ[C] C`.  This file develops
the elementary calculus of such trivializations that drives the surjectivity half of the
Čech–Picard dictionary (`AlgebraicJacobian.Picard.CechPicSurjective`):

* `Module.trivialization_ext`: a trivialization is determined by its values on the
  tensors `1 ⊗ₜ n` (they `C`-span the base change).
* `Module.trivializationPush h t`: the pushforward of a trivialization along an
  `A`-algebra map `h : C →ₐ[A] C'`, with `trivializationPush_one_tmul` computing it on
  `1 ⊗ₜ n` as `h (t (1 ⊗ₜ n))`, and strict compositionality
  (`trivializationPush_trivializationPush`).
* `Module.transitionUnit t₁ t₂ : Cˣ`: the unit comparing two trivializations, uniquely
  characterized by `transitionUnit_mul_apply : transitionUnit t₁ t₂ * t₁ x = t₂ x`
  (uniqueness: `transitionUnit_eq_of`).  The cocycle calculus is immediate from the
  characterization: `transitionUnit_self`, the telescoping identity
  `transitionUnit_mul_transitionUnit`, and compatibility with pushforward
  (`map_transitionUnit`).

On a finite localization cover these transition units become a Čech 1-cocycle presenting
the class of an invertible module; see
`AlgebraicJacobian.Algebra.LocalizationTrivialization`.

Everything is pinned to a single universe `u`, matching the descent development in
`AlgebraicJacobian.Descent.ModuleDescent`.
-/

universe u

open TensorProduct

namespace Module

variable {A : Type u} [CommRing A] {N : Type u} [AddCommGroup N] [Module A N]
variable {C : Type u} [CommRing C] [Algebra A C]
variable {C' : Type u} [CommRing C'] [Algebra A C']
variable {C'' : Type u} [CommRing C''] [Algebra A C'']

/-! ## Extensionality on the tensors `1 ⊗ₜ n` -/

/-- Two `C`-linear maps out of `C ⊗[A] N` valued in `C` that agree on the tensors
`1 ⊗ₜ n` are equal: these tensors `C`-span the base change. -/
theorem trivialization_hom_ext {t₁ t₂ : C ⊗[A] N →ₗ[C] C}
    (h : ∀ n : N, t₁ (1 ⊗ₜ n) = t₂ (1 ⊗ₜ n)) : t₁ = t₂ := by
  apply LinearMap.restrictScalars_injective A
  apply TensorProduct.ext'
  intro c n
  have hc : (c ⊗ₜ[A] n : C ⊗[A] N) = c • (1 ⊗ₜ[A] n : C ⊗[A] N) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [LinearMap.coe_restrictScalars, hc, map_smul, h]

/-- Two trivializations agreeing on the tensors `1 ⊗ₜ n` are equal. -/
theorem trivialization_ext {t₁ t₂ : C ⊗[A] N ≃ₗ[C] C}
    (h : ∀ n : N, t₁ (1 ⊗ₜ n) = t₂ (1 ⊗ₜ n)) : t₁ = t₂ :=
  LinearEquiv.toLinearMap_injective (trivialization_hom_ext h)

/-! ## Pushforward along an algebra map -/

/-- The pushforward of a trivialization `t : C ⊗[A] N ≃ₗ[C] C` along an `A`-algebra map
`h : C →ₐ[A] C'`: the composite
`C' ⊗[A] N ≃ C' ⊗[C] (C ⊗[A] N) ≃ C' ⊗[C] C ≃ C'` (with `C'` a `C`-algebra via `h`),
which on the tensors `1 ⊗ₜ n` is `h (t (1 ⊗ₜ n))` (`trivializationPush_one_tmul`). -/
noncomputable def trivializationPush (h : C →ₐ[A] C') (t : C ⊗[A] N ≃ₗ[C] C) :
    C' ⊗[A] N ≃ₗ[C'] C' :=
  letI : Algebra C C' := h.toRingHom.toAlgebra
  haveI : IsScalarTower A C C' :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (h.commutes a).symm
  ((AlgebraTensorModule.cancelBaseChange A C C' C' N).symm.trans
    (LinearEquiv.baseChange C C' _ _ t)).trans (AlgebraTensorModule.rid C C' C')

@[simp]
lemma trivializationPush_one_tmul (h : C →ₐ[A] C') (t : C ⊗[A] N ≃ₗ[C] C) (n : N) :
    trivializationPush h t (1 ⊗ₜ n) = h (t (1 ⊗ₜ n)) := by
  letI : Algebra C C' := h.toRingHom.toAlgebra
  haveI : IsScalarTower A C C' :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (h.commutes a).symm
  show (AlgebraTensorModule.rid C C' C')
      (LinearEquiv.baseChange C C' _ _ t
        ((AlgebraTensorModule.cancelBaseChange A C C' C' N).symm ((1 : C') ⊗ₜ n))) = _
  rw [AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
    AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
  rfl

/-- Pushforward of trivializations is strictly compositional. -/
lemma trivializationPush_trivializationPush (h' : C' →ₐ[A] C'') (h : C →ₐ[A] C')
    (t : C ⊗[A] N ≃ₗ[C] C) :
    trivializationPush h' (trivializationPush h t) = trivializationPush (h'.comp h) t :=
  trivialization_ext fun n ↦ by
    rw [trivializationPush_one_tmul, trivializationPush_one_tmul,
      trivializationPush_one_tmul, AlgHom.comp_apply]

/-! ## Transition units

The transition unit compares two `C`-linear identifications of a module with `C`; it is
defined for an arbitrary source module (`M ≃ₗ[C] C`), so that it also serves the
base-changed trivializations of `AlgebraicJacobian.Algebra.TrivializationBaseChange`. -/

section transitionUnit

variable {M : Type u} [AddCommGroup M] [Module C M]
variable (t t₁ t₂ t₃ : M ≃ₗ[C] C)

/-- The **transition unit** between two `C`-linear identifications of a module with `C`:
the unit of `C` by which they differ, `transitionUnit t₁ t₂ * t₁ x = t₂ x`
(`transitionUnit_mul_apply`). -/
noncomputable def transitionUnit : Cˣ where
  val := t₂ (t₁.symm 1)
  inv := t₁ (t₂.symm 1)
  val_inv := by
    have h1 : t₂ (t₁.symm 1) • t₂.symm (1 : C) = t₁.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, t₂.symm_apply_apply]
    rw [← smul_eq_mul, ← map_smul, h1, t₁.apply_symm_apply]
  inv_val := by
    have h1 : t₁ (t₂.symm 1) • t₁.symm (1 : C) = t₂.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, t₁.symm_apply_apply]
    rw [← smul_eq_mul, ← map_smul, h1, t₂.apply_symm_apply]

lemma transitionUnit_val : (transitionUnit t₁ t₂).val = t₂ (t₁.symm 1) :=
  rfl

/-- The defining property of the transition unit. -/
lemma transitionUnit_mul_apply (x : M) :
    (transitionUnit t₁ t₂).val * t₁ x = t₂ x := by
  rw [transitionUnit_val, mul_comm]
  have h1 : t₁ x • t₁.symm (1 : C) = x := by
    rw [← map_smul, smul_eq_mul, mul_one, t₁.symm_apply_apply]
  rw [← smul_eq_mul, ← map_smul, h1]

@[simp]
lemma transitionUnit_self : transitionUnit t t = 1 :=
  Units.ext (by rw [transitionUnit_val, t.apply_symm_apply, Units.val_one])

/-- The telescoping identity for transition units: the Čech 1-cocycle relation. -/
lemma transitionUnit_mul_transitionUnit :
    transitionUnit t₂ t₃ * transitionUnit t₁ t₂ = transitionUnit t₁ t₃ :=
  Units.ext (transitionUnit_mul_apply t₂ t₃ (t₁.symm 1))

/-- Precomposition with a common identification does not change the transition unit. -/
@[simp]
lemma transitionUnit_trans {M' : Type u} [AddCommGroup M'] [Module C M']
    (φ : M' ≃ₗ[C] M) :
    transitionUnit (φ ≪≫ₗ t₁) (φ ≪≫ₗ t₂) = transitionUnit t₁ t₂ :=
  Units.ext (by
    rw [transitionUnit_val, transitionUnit_val, LinearEquiv.trans_symm,
      LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply])

end transitionUnit

section transitionUnitTensor

variable (t t₁ t₂ t₃ : C ⊗[A] N ≃ₗ[C] C)

/-- The transition unit is the unique unit conjugating the values of `t₁` on the tensors
`1 ⊗ₜ n` into those of `t₂`. -/
lemma transitionUnit_eq_of {u : Cˣ}
    (h : ∀ n : N, u.val * t₁ (1 ⊗ₜ n) = t₂ (1 ⊗ₜ n)) : transitionUnit t₁ t₂ = u := by
  have key : ∀ x : C ⊗[A] N, u.val * t₁ x = t₂ x := by
    intro x
    induction x with
    | zero => simp
    | tmul c n =>
        have hc : (c ⊗ₜ[A] n : C ⊗[A] N) = c • (1 ⊗ₜ[A] n : C ⊗[A] N) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hc, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm, h]
    | add x y hx hy => rw [map_add, map_add, mul_add, hx, hy]
  have h1 := key (t₁.symm 1)
  rw [t₁.apply_symm_apply, mul_one] at h1
  exact Units.ext ((transitionUnit_val t₁ t₂).trans h1.symm)

/-- Transition units are compatible with pushforward of trivializations along an
`A`-algebra map. -/
lemma map_transitionUnit (h : C →ₐ[A] C') :
    transitionUnit (trivializationPush h t₁) (trivializationPush h t₂)
      = Units.map h.toRingHom.toMonoidHom (transitionUnit t₁ t₂) :=
  transitionUnit_eq_of _ _ fun n ↦ by
    have := congrArg h (transitionUnit_mul_apply t₁ t₂ (1 ⊗ₜ n))
    rw [map_mul] at this
    rw [trivializationPush_one_tmul, trivializationPush_one_tmul]
    exact this

end transitionUnitTensor

end Module
