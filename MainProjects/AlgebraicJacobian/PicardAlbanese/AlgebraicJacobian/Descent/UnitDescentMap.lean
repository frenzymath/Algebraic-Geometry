/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.UnitDescent

/-!
# Base change of descent 1-cocycles along maps of algebras

Continuation of `AlgebraicJacobian.Descent.UnitDescent`: the base change of a descent
1-cocycle along a map `h : B →ₐ[A] B'` of `A`-algebras is a descent 1-cocycle
(`Module.IsDescentCocycle.map`), and for faithfully flat `B, B'` the descended module —
hence the Picard class — does not change (`Module.descendedMapEquiv`,
`Module.IsDescentCocycle.picClass_map`).
-/

universe u

open TensorProduct

namespace Module

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {u : (B ⊗[A] B)ˣ}

/-! ## Base change of cocycles along maps of algebras -/

section map

variable {B' : Type u} [CommRing B'] [Algebra A B'] (h : B →ₐ[A] B')

/-- The base change of a descent cocycle along a map of `A`-algebras is a descent
cocycle. -/
theorem IsDescentCocycle.map {u : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u) :
    IsDescentCocycle (Units.map (Algebra.TensorProduct.map h h).toRingHom.toMonoidHom u) := by
  -- Naturality: `lmul' ∘ (map h h) = h ∘ lmul'` and
  -- `descentFaceᵢⱼ ∘ (map h h) = (map h (map h h)) ∘ descentFaceᵢⱼ` (check on pure
  -- tensors by `Algebra.TensorProduct.ext` or by `TensorProduct.induction_on`); apply `h`
  -- to the two conditions of `hu`.
  have hlmul : ∀ w : B ⊗[A] B,
      Algebra.TensorProduct.lmul' A (S := B') (Algebra.TensorProduct.map h h w)
        = h (Algebra.TensorProduct.lmul' A (S := B) w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.lmul'_apply_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hface₁₂ : ∀ w : B ⊗[A] B,
      descentFace₁₂ A B' (Algebra.TensorProduct.map h h w)
        = Algebra.TensorProduct.map h (Algebra.TensorProduct.map h h)
            (descentFace₁₂ A B w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hface₁₃ : ∀ w : B ⊗[A] B,
      descentFace₁₃ A B' (Algebra.TensorProduct.map h h w)
        = Algebra.TensorProduct.map h (Algebra.TensorProduct.map h h)
            (descentFace₁₃ A B w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hface₂₃ : ∀ w : B ⊗[A] B,
      descentFace₂₃ A B' (Algebra.TensorProduct.map h h w)
        = Algebra.TensorProduct.map h (Algebra.TensorProduct.map h h)
            (descentFace₂₃ A B w) := by
    intro w
    simp
  constructor
  · change Algebra.TensorProduct.lmul' A (S := B') (Algebra.TensorProduct.map h h u.val) = 1
    rw [hlmul, hu.lmul'_eq_one, map_one]
  · change descentFace₂₃ A B' (Algebra.TensorProduct.map h h u.val)
        * descentFace₁₂ A B' (Algebra.TensorProduct.map h h u.val)
      = descentFace₁₃ A B' (Algebra.TensorProduct.map h h u.val)
    rw [hface₂₃, hface₁₂, hface₁₃, ← map_mul, hu.cocycle]

/-- Base change of the descended module along a map of faithfully flat `A`-algebras:
the descended module does not change. -/
noncomputable def descendedMapEquiv [Module.FaithfullyFlat A B] [Module.FaithfullyFlat A B']
    {u : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u) :
    hu.descended ≃ₗ[A] (hu.map h).descended := by
  -- Route: `equivDescended (DescentDatum.ofUnit _ (hu.map h)) e' he'` where
  -- `e' : B' ⊗[A] descended u ≃ₗ[B'] B'` is `liftBaseChange` of `h ∘ subtype`, bijective
  -- because it factors as
  -- `B' ⊗[A] M ≃ B' ⊗[B] (B ⊗[A] M) ≃ B' ⊗[B] B ≃ B'`
  -- (`AlgebraTensorModule.cancelBaseChange` and the descent equivalence of `u`), and the
  -- compatibility `he'` reduces on pure tensors to applying `map h h` to
  -- `u * (m ⊗ₜ 1) = 1 ⊗ₜ m`.
  have hbij : Function.Bijective
      ⇑((h.toLinearMap ∘ₗ hu.descended.subtype).liftBaseChange B') := by
    letI : Algebra B B' := h.toRingHom.toAlgebra
    haveI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun a => (h.commutes a).symm
    have hpt : ∀ x : B' ⊗[A] hu.descended,
        ((h.toLinearMap ∘ₗ hu.descended.subtype).liftBaseChange B') x
          = (((AlgebraTensorModule.cancelBaseChange A B B' B' hu.descended).symm.trans
              (LinearEquiv.baseChange B B' (B ⊗[A] hu.descended) B
                (DescentDatum.ofUnit u hu).descentEquiv)).trans
              (AlgebraTensorModule.rid B B' B')) x := by
      intro x
      induction x with
      | zero => simp
      | tmul b' m =>
          change b' * h (m : B) = ((1 : B) • ((m : B))) • b'
          rw [one_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
          exact mul_comm _ _
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [show ⇑((h.toLinearMap ∘ₗ hu.descended.subtype).liftBaseChange B')
        = ⇑(((AlgebraTensorModule.cancelBaseChange A B B' B' hu.descended).symm.trans
              (LinearEquiv.baseChange B B' (B ⊗[A] hu.descended) B
                (DescentDatum.ofUnit u hu).descentEquiv)).trans
              (AlgebraTensorModule.rid B B' B'))
      from funext hpt]
    exact (((AlgebraTensorModule.cancelBaseChange A B B' B' hu.descended).symm.trans
      (LinearEquiv.baseChange B B' (B ⊗[A] hu.descended) B
        (DescentDatum.ofUnit u hu).descentEquiv)).trans
      (AlgebraTensorModule.rid B B' B')).bijective
  refine (DescentDatum.ofUnit _ (hu.map h)).equivDescended
    (LinearEquiv.ofBijective ((h.toLinearMap ∘ₗ hu.descended.subtype).liftBaseChange B') hbij)
    fun x => ?_
  induction x with
  | zero => simp
  | tmul b' m =>
      have hm : u.val * ((m : B) ⊗ₜ[A] (1 : B)) = 1 ⊗ₜ (m : B) := hu.mem_descended.mp m.2
      have hm' : Algebra.TensorProduct.map h h u.val * (h (m : B) ⊗ₜ[A] (1 : B'))
          = 1 ⊗ₜ h (m : B) := by
        have := congrArg (Algebra.TensorProduct.map h h) hm
        simpa using this
      simp only [ofUnit_coaction, unitCoaction_apply, DescentDatum.baseChange_coaction,
        LinearMap.baseChange_tmul, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
        TensorProduct.mk_apply]
      change Algebra.TensorProduct.map h h u.val * ((b' * h (m : B)) ⊗ₜ[A] (1 : B'))
        = b' ⊗ₜ[A] ((1 : B') * h (m : B))
      rw [one_mul,
        show (b' * h (m : B)) ⊗ₜ[A] (1 : B')
            = (b' ⊗ₜ[A] (1 : B')) * (h (m : B) ⊗ₜ[A] (1 : B')) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
        show b' ⊗ₜ[A] h (m : B) = (b' ⊗ₜ[A] (1 : B')) * ((1 : B') ⊗ₜ[A] h (m : B)) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      linear_combination (b' ⊗ₜ[A] (1 : B')) * hm'
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp]
theorem IsDescentCocycle.picClass_map [Module.FaithfullyFlat A B]
    [Module.FaithfullyFlat A B'] {u : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u) :
    (hu.map h).picClass = hu.picClass :=
  (CommRing.Pic.mk_eq_mk_iff.mpr ⟨(descendedMapEquiv h hu).symm⟩)

end map
end Module
