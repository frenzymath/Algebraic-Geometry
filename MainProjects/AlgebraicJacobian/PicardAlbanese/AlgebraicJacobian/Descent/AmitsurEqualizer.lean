/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.ModuleDescent
import AlgebraicJacobian.Descent.UnitDescent

/-!
# The degree-`0` Amitsur equalizer for a faithfully flat base change

For a faithfully flat `A → B` and an `A`-algebra `S₀`, an element of `S₀ ⊗[A] B` on
which the two coprojection faces into `S₀ ⊗[A] (B ⊗[A] B)` agree is `s ⊗ₜ 1` for a
unique `s : S₀` (`Module.FaithfullyFlat.existsUnique_tmul_one_eq`) — the right-tensor
form of degree-`0` Amitsur exactness, by transport from the coaction encoding of
`Module.DescentDatum.exact_mk_coactionSub`.

This is the algebra input to the fppf descent of sections along the curve-side base
change in `AlgebraicJacobian.Picard.SectionsDescent` (ζ3 brick D).
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Module

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **The degree-`0` Amitsur equalizer** (right-tensor form): for a faithfully flat
`A → B` and an `A`-algebra `S₀`, an element of `S₀ ⊗[A] B` on which the two coprojection
faces into `S₀ ⊗[A] (B ⊗[A] B)` agree is `s ⊗ₜ 1` for a unique `s : S₀`.  Transport of
`Module.DescentDatum.exact_mk_coactionSub` through `TensorProduct.comm`/`assoc`.
 * Provenance: CUSTOM. -/
theorem FaithfullyFlat.existsUnique_tmul_one_eq [Module.FaithfullyFlat A B]
    {S₀ : Type u} [CommRing S₀] [Algebra A S₀] (x : S₀ ⊗[A] B)
    (hx : Algebra.TensorProduct.map (AlgHom.id A S₀) (Module.descentIncl₁ A B) x
        = Algebra.TensorProduct.map (AlgHom.id A S₀) (Module.descentIncl₂ A B) x) :
    ∃! s : S₀, s ⊗ₜ[A] (1 : B) = x := by
  classical
  -- the two faces, in the coaction encoding of `DescentDatum.baseChange`
  have h₁ : ∀ y : S₀ ⊗[A] B,
      ((TensorProduct.comm A S₀ (B ⊗[A] B)).trans
          (TensorProduct.assoc A B B S₀))
        (Algebra.TensorProduct.map (AlgHom.id A S₀) (Module.descentIncl₁ A B) y)
      = (Module.DescentDatum.baseChange A B S₀).coaction (TensorProduct.comm A S₀ B y) := by
    intro y
    induction y with
    | zero => simp
    | tmul s b => rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  have h₂ : ∀ y : S₀ ⊗[A] B,
      ((TensorProduct.comm A S₀ (B ⊗[A] B)).trans
          (TensorProduct.assoc A B B S₀))
        (Algebra.TensorProduct.map (AlgHom.id A S₀) (Module.descentIncl₂ A B) y)
      = (1 : B) ⊗ₜ[A] (TensorProduct.comm A S₀ B y) := by
    intro y
    induction y with
    | zero => simp
    | tmul s b => rfl
    | add y z hy hz =>
        simp only [map_add, hy, hz, TensorProduct.tmul_add]
  -- the coaction difference vanishes on `comm x`
  have h0 : (Module.DescentDatum.baseChange A B S₀).coactionSub
      (TensorProduct.comm A S₀ B x) = 0 := by
    rw [Module.DescentDatum.coactionSub_apply, ← h₁ x, ← h₂ x, hx, sub_self]
  -- Amitsur exactness in degree `0`
  obtain ⟨s, hs⟩ := (Module.DescentDatum.exact_mk_coactionSub (A := A) (B := B) S₀
    (TensorProduct.comm A S₀ B x)).mp h0
  have hs' : (1 : B) ⊗ₜ[A] s = TensorProduct.comm A S₀ B x := hs
  refine ⟨s, ?_, ?_⟩
  · -- `s ⊗ₜ 1 = x`: apply `comm.symm` to `1 ⊗ₜ s = comm x`
    change s ⊗ₜ[A] (1 : B) = x
    have h := congrArg (TensorProduct.comm A S₀ B).symm hs'
    rwa [LinearEquiv.symm_apply_apply, TensorProduct.comm_symm_tmul] at h
  · -- uniqueness: `TensorProduct.mk` is injective for faithfully flat `B`
    intro s' hs''
    have h1 : (1 : B) ⊗ₜ[A] s' = (1 : B) ⊗ₜ[A] s := by
      have h := congrArg (TensorProduct.comm A S₀ B) hs''
      rw [TensorProduct.comm_tmul] at h
      rw [h, hs']
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) S₀ h1

end Module
