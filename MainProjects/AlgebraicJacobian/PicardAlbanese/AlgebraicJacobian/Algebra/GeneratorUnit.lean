/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Units from evaluated trivialization generators

For a trivialization `t : R ⊗[A] M ≃ₗ[R] R` of a base-changed module, the generator
`t.symm 1` generates `R ⊗[A] M` as an `R`-module.  This file proves the abstract
unit-production lemma of the ζ3 kernel-lemma construction: pushing the generator along
a ring map `φ : R → R'` (as `rTensor` of an `A`-linear avatar of `φ`) and applying any
surjective `R'`-linear evaluation `F : R' ⊗[A] M →ₗ[R'] R'` yields a **unit** of `R'`
(`Module.isUnit_map_rTensor_generator`).

It also packages the multiplication evaluation `Module.descentMulEval`: for a tower
`A → B' → R'` and a descent equivalence `dE : B' ⊗[A] M ≃ₗ[B'] B'`, the base-changed
`R'`-linear equivalence `R' ⊗[A] M ≃ₗ[R'] R'` with `r' ⊗ m ↦ r' * algebraMap _ _ (dE
(1 ⊗ m))` — the concrete surjective evaluation fed to the unit-production lemma.

Everything is stated over abstract commutative rings so that the kernel checks small
types; the composite section-ring instance stacks appear only at the single
instantiation site in `AlgebraicJacobian.Picard.DescentClassRepBuild`.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Module

variable {A R R' M : Type u} [CommRing A] [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R'] [AddCommGroup M] [Module A M]

/-- The generator property of a trivialization: every element is the `t`-value scalar
multiple of the generator `t.symm 1`. -/
lemma trivialization_smul_symm_one {M₀ : Type u} [AddCommGroup M₀] [Module R M₀]
    (t : M₀ ≃ₗ[R] R) (x : M₀) :
    t x • t.symm 1 = x := by
  apply t.injective
  rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

/-- `rTensor` of an `A`-linear avatar of a ring map is `φ`-semilinear for the
module-side scalars. -/
lemma rTensor_smul_of_ringHom (φ : R →+* R') (φₗ : R →ₗ[A] R')
    (hφ : ∀ r, φₗ r = φ r) (c : R) (x : R ⊗[A] M) :
    LinearMap.rTensor M φₗ (c • x) = φ c • LinearMap.rTensor M φₗ x := by
  induction x with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul r m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul, hφ, hφ, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **Unit production from an evaluated generator**: pushing the (collapsed) generator
of a trivialization `t : M' ≃ₗ[R] R` along `φ : R → R'` (through a collapse
`cN : M' ≃ₗ[R] R ⊗[A] M`) and evaluating by any surjective `R'`-linear map
`R' ⊗[A] M → R'` produces a unit of `R'`. 


 * Provenance: CUSTOM.
-/
theorem isUnit_map_rTensor_generator (φ : R →+* R') (φₗ : R →ₗ[A] R')
    (hφ : ∀ r, φₗ r = φ r) {M' : Type u} [AddCommGroup M'] [Module R M']
    (t : M' ≃ₗ[R] R) (cN : M' ≃ₗ[R] R ⊗[A] M)
    (F : R' ⊗[A] M →ₗ[R'] R') (hF : Function.Surjective F) :
    IsUnit (F (LinearMap.rTensor M φₗ (cN (t.symm 1)))) := by
  -- every element of `R ⊗[A] M` is an `R`-multiple of the collapsed generator
  have hgen₀ : ∀ x : R ⊗[A] M, x = t (cN.symm x) • cN (t.symm 1) := by
    intro x
    rw [← map_smul, trivialization_smul_symm_one, LinearEquiv.apply_symm_apply]
  -- every element of `R' ⊗[A] M` is an `R'`-multiple of the pushed generator
  have hgen : ∀ z : R' ⊗[A] M,
      ∃ c : R', z = c • LinearMap.rTensor M φₗ (cN (t.symm 1)) := by
    intro z
    induction z with
    | zero => exact ⟨0, (zero_smul _ _).symm⟩
    | tmul r' m =>
        refine ⟨r' * φ (t (cN.symm ((1 : R) ⊗ₜ[A] m))), ?_⟩
        have h1 : LinearMap.rTensor M φₗ ((1 : R) ⊗ₜ[A] m) = (1 : R') ⊗ₜ[A] m := by
          rw [LinearMap.rTensor_tmul, hφ, map_one]
        calc r' ⊗ₜ[A] m
            = r' • ((1 : R') ⊗ₜ[A] m) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          _ = r' • LinearMap.rTensor M φₗ ((1 : R) ⊗ₜ[A] m) := by rw [h1]
          _ = r' • LinearMap.rTensor M φₗ
                (t (cN.symm ((1 : R) ⊗ₜ[A] m)) • cN (t.symm 1)) := by
              rw [← hgen₀]
          _ = r' • (φ (t (cN.symm ((1 : R) ⊗ₜ[A] m)))
                • LinearMap.rTensor M φₗ (cN (t.symm 1))) := by
              rw [rTensor_smul_of_ringHom φ φₗ hφ]
          _ = (r' * φ (t (cN.symm ((1 : R) ⊗ₜ[A] m))))
                • LinearMap.rTensor M φₗ (cN (t.symm 1)) := by
              rw [smul_smul]
    | add x y hx hy =>
        obtain ⟨c₁, hc₁⟩ := hx
        obtain ⟨c₂, hc₂⟩ := hy
        exact ⟨c₁ + c₂, by rw [hc₁, hc₂, add_smul]⟩
  -- pull `1` back through `F` and rewrite via the generator property
  obtain ⟨y, hy⟩ := hF 1
  obtain ⟨c, hc⟩ := hgen y
  refine IsUnit.of_mul_eq_one c ?_
  rw [mul_comm, ← smul_eq_mul, ← map_smul, ← hc, hy]

/-! ## The multiplication evaluation of a descent equivalence -/

variable (A M) in
/-- The base change of a descent equivalence `B' ⊗[A] M ≃ₗ[B'] B'` along `B' → R'`,
collapsed to an `R'`-linear equivalence `R' ⊗[A] M ≃ₗ[R'] R'`. 


 * Provenance: CUSTOM.
-/
noncomputable def descentMulEval {B' : Type u} [CommRing B'] [Algebra A B']
    [Algebra B' R'] [IsScalarTower A B' R'] (dE : B' ⊗[A] M ≃ₗ[B'] B') :
    (R' ⊗[A] M) ≃ₗ[R'] R' :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A B' R' R' M).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') dE ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid B' R' R'

lemma descentMulEval_tmul {B' : Type u} [CommRing B'] [Algebra A B']
    [Algebra B' R'] [IsScalarTower A B' R'] (dE : B' ⊗[A] M ≃ₗ[B'] B')
    (r' : R') (m : M) :
    descentMulEval A M dE (r' ⊗ₜ[A] m) = dE ((1 : B') ⊗ₜ[A] m) • r' := by
  have h1 : (TensorProduct.AlgebraTensorModule.cancelBaseChange A B' R' R' M).symm
      (r' ⊗ₜ[A] m) = r' ⊗ₜ[B'] ((1 : B') ⊗ₜ[A] m) := by
    rw [LinearEquiv.symm_apply_eq,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  rw [descentMulEval, LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul]

end Module
