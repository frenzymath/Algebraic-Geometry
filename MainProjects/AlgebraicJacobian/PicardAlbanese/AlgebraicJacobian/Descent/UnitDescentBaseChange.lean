/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.UnitDescentMap

/-!
# Base change of descent 1-cocycles along a change of the base ring

Continuation of `AlgebraicJacobian.Descent.UnitDescent` and
`AlgebraicJacobian.Descent.UnitDescentMap`, which treat maps of covers `B →ₐ[A] B'` over a
*fixed* base `A`.  Here the **base ring changes**: for a ring map `A → A'` and a descent
1-cocycle `u : (B ⊗[A] B)ˣ`, the image of `u` in `(B'' ⊗[A'] B'')ˣ` for the base-changed
cover `B'' := A' ⊗[A] B` is a descent 1-cocycle over `A'`
(`Module.IsDescentCocycle.baseChange`), the descended module base-changes accordingly
(`Module.descendedBaseChangeEquiv : A' ⊗[A] descended u ≃ₗ[A'] descended (baseChange u)`),
and hence the Picard class of the descended module is natural in the base:
`(hu.baseChange A').picClass = CommRing.Pic.mapAlgebra A A' hu.picClass`
(`Module.IsDescentCocycle.picClass_baseChange`).

This is the algebra face of the naturality of the Čech–Picard dictionary
(`AlgebraicJacobian.Picard.CechPicToPic`) in the scheme, consumed by the étale
separatedness theorem of the relative Picard functor (Kleiman, *The Picard Scheme*,
Theorem 2.5(1)).

The proofs mirror `Module.descendedMapEquiv`: the descended module of the base-changed
cocycle is recognized by `Module.DescentDatum.equivDescended`, fed with the composite of
`AlgebraTensorModule.cancelBaseChange` and the base change along `B → A' ⊗[A] B` of the
descent equivalence of `u`.
-/

universe u

open TensorProduct

namespace Module

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

/-! ## The base-change map on tensor squares -/

variable (A A' B) in
/-- The canonical `A`-algebra map `B ⊗[A] B → (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)`,
`x ⊗ y ↦ (1 ⊗ x) ⊗ (1 ⊗ y)`: base change of the tensor square of a cover along
`A → A'`. -/
noncomputable def tensorSqBaseChange :
    B ⊗[A] B →ₐ[A] (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft :
        (A' ⊗[A] B) →ₐ[A'] (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)).restrictScalars A).comp
      Algebra.TensorProduct.includeRight)
    (((Algebra.TensorProduct.includeRight :
        (A' ⊗[A] B) →ₐ[A'] (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)).restrictScalars A).comp
      Algebra.TensorProduct.includeRight)
    fun _ _ => Commute.all _ _

@[simp]
lemma tensorSqBaseChange_tmul (x y : B) :
    tensorSqBaseChange A A' B (x ⊗ₜ y)
      = ((1 : A') ⊗ₜ[A] x) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] y) := by
  simp [tensorSqBaseChange]

variable (A A' B) in
/-- The canonical `A`-algebra map on tensor cubes,
`x ⊗ (y ⊗ z) ↦ (1 ⊗ x) ⊗ ((1 ⊗ y) ⊗ (1 ⊗ z))`: base change of the triple product of a
cover along `A → A'`. -/
noncomputable def tensorCubeBaseChange :
    B ⊗[A] (B ⊗[A] B) →ₐ[A]
      (A' ⊗[A] B) ⊗[A'] ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft :
        (A' ⊗[A] B) →ₐ[A'] (A' ⊗[A] B) ⊗[A'] ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B))).restrictScalars
          A).comp
      Algebra.TensorProduct.includeRight)
    (((Algebra.TensorProduct.includeRight :
        ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)) →ₐ[A']
          (A' ⊗[A] B) ⊗[A'] ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B))).restrictScalars A).comp
      (tensorSqBaseChange A A' B))
    fun _ _ => Commute.all _ _

@[simp]
lemma tensorCubeBaseChange_tmul (x y z : B) :
    tensorCubeBaseChange A A' B (x ⊗ₜ (y ⊗ₜ z))
      = ((1 : A') ⊗ₜ[A] x) ⊗ₜ[A'] (((1 : A') ⊗ₜ[A] y) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] z)) := by
  simp [tensorCubeBaseChange]

/-! ## Base change of cocycles -/

section cocycle

variable {u : (B ⊗[A] B)ˣ}

/-- Base change of a descent 1-cocycle along `A → A'` is a descent 1-cocycle for the
base-changed cover `A' ⊗[A] B` over `A'`. -/
theorem IsDescentCocycle.baseChange (hu : IsDescentCocycle u) :
    IsDescentCocycle
      (Units.map (tensorSqBaseChange A A' B).toRingHom.toMonoidHom u) := by
  have hlmul : ∀ w : B ⊗[A] B,
      Algebra.TensorProduct.lmul' A' (S := A' ⊗[A] B) (tensorSqBaseChange A A' B w)
        = Algebra.TensorProduct.includeRight (Algebra.TensorProduct.lmul' A (S := B) w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.lmul'_apply_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hface₁₂ : ∀ w : B ⊗[A] B,
      descentFace₁₂ A' (A' ⊗[A] B) (tensorSqBaseChange A A' B w)
        = tensorCubeBaseChange A A' B (descentFace₁₂ A B w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.one_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hface₁₃ : ∀ w : B ⊗[A] B,
      descentFace₁₃ A' (A' ⊗[A] B) (tensorSqBaseChange A A' B w)
        = tensorCubeBaseChange A A' B (descentFace₁₃ A B w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.one_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hface₂₃ : ∀ w : B ⊗[A] B,
      descentFace₂₃ A' (A' ⊗[A] B) (tensorSqBaseChange A A' B w)
        = tensorCubeBaseChange A A' B (descentFace₂₃ A B w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.one_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  · change Algebra.TensorProduct.lmul' A' (S := A' ⊗[A] B)
        (tensorSqBaseChange A A' B u.val) = 1
    rw [hlmul, hu.lmul'_eq_one, map_one]
  · change descentFace₂₃ A' (A' ⊗[A] B) (tensorSqBaseChange A A' B u.val)
        * descentFace₁₂ A' (A' ⊗[A] B) (tensorSqBaseChange A A' B u.val)
      = descentFace₁₃ A' (A' ⊗[A] B) (tensorSqBaseChange A A' B u.val)
    rw [hface₂₃, hface₁₂, hface₁₃, ← map_mul, hu.cocycle]

end cocycle

/-! ## Base change of the descended module -/

section descended

variable {u : (B ⊗[A] B)ˣ}

/-- Base change of the descended module along `A → A'`: the descended module of the
base-changed cocycle is the base change of the descended module.  Needs flatness of the
cover only on the `A`-side (`Module.FaithfullyFlat A B`), through the descent equivalence
of `u`. -/
noncomputable def descendedBaseChangeEquiv [Module.FaithfullyFlat A B]
    (hu : IsDescentCocycle u) :
    (A' ⊗[A] hu.descended) ≃ₗ[A'] (hu.baseChange (A' := A')).descended := by
  letI : Algebra B (A' ⊗[A] B) :=
    (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom.toAlgebra
  haveI : IsScalarTower A B (A' ⊗[A] B) := IsScalarTower.of_algebraMap_eq
    fun b => ((Algebra.TensorProduct.includeRight :
      B →ₐ[A] A' ⊗[A] B).commutes b).symm
  have hbij : Function.Bijective
      ⇑((((Algebra.TensorProduct.includeRight :
            B →ₐ[A] A' ⊗[A] B).toLinearMap ∘ₗ hu.descended.subtype).liftBaseChange
          (A' ⊗[A] B)) ∘ₗ
        (AlgebraTensorModule.cancelBaseChange A A' (A' ⊗[A] B) (A' ⊗[A] B)
          hu.descended).toLinearMap) := by
    have hpt : ∀ x : (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] hu.descended),
        ((((Algebra.TensorProduct.includeRight :
            B →ₐ[A] A' ⊗[A] B).toLinearMap ∘ₗ hu.descended.subtype).liftBaseChange
          (A' ⊗[A] B)) ∘ₗ
          (AlgebraTensorModule.cancelBaseChange A A' (A' ⊗[A] B) (A' ⊗[A] B)
            hu.descended).toLinearMap) x
          = (AlgebraTensorModule.cancelBaseChange A A' (A' ⊗[A] B) (A' ⊗[A] B)
                hu.descended ≪≫ₗ
              (AlgebraTensorModule.cancelBaseChange A B (A' ⊗[A] B) (A' ⊗[A] B)
                hu.descended).symm ≪≫ₗ
              LinearEquiv.baseChange B (A' ⊗[A] B) (B ⊗[A] hu.descended) B
                (DescentDatum.ofUnit u hu).descentEquiv ≪≫ₗ
              AlgebraTensorModule.rid B (A' ⊗[A] B) (A' ⊗[A] B)) x := by
      intro x
      induction x with
      | zero => simp
      | tmul b' m =>
          induction m with
          | zero => simp
          | tmul a' n =>
              change ((a' • b') : A' ⊗[A] B) * Algebra.TensorProduct.includeRight (n : B)
                = Algebra.TensorProduct.includeRight (((1 : B) • (n : B) : B)) * (a' • b')
              rw [one_smul]
              exact mul_comm _ _
          | add x y hx hy =>
              simp only [tmul_add, map_add] at hx hy ⊢
              rw [hx, hy]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [funext hpt]
    exact (AlgebraTensorModule.cancelBaseChange A A' (A' ⊗[A] B) (A' ⊗[A] B)
        hu.descended ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange A B (A' ⊗[A] B) (A' ⊗[A] B)
        hu.descended).symm ≪≫ₗ
      LinearEquiv.baseChange B (A' ⊗[A] B) (B ⊗[A] hu.descended) B
        (DescentDatum.ofUnit u hu).descentEquiv ≪≫ₗ
      AlgebraTensorModule.rid B (A' ⊗[A] B) (A' ⊗[A] B)).bijective
  refine (DescentDatum.ofUnit _ (hu.baseChange (A' := A'))).equivDescended
    (LinearEquiv.ofBijective _ hbij) fun x => ?_
  induction x with
  | zero => simp
  | tmul b' m =>
      induction m with
      | zero => simp
      | tmul a' n =>
          simp only [LinearEquiv.ofBijective_apply, LinearMap.coe_comp,
            LinearEquiv.coe_coe, Function.comp_apply,
            AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.liftBaseChange_tmul,
            Submodule.coe_subtype, AlgHom.toLinearMap_apply, ofUnit_coaction,
            unitCoaction_apply, DescentDatum.baseChange_coaction,
            LinearMap.baseChange_tmul, LinearMap.coe_restrictScalars,
            TensorProduct.mk_apply, Algebra.TensorProduct.includeRight_apply]
          have hn' : (Units.map (tensorSqBaseChange A A' B).toRingHom.toMonoidHom u).val
              * (((1 : A') ⊗ₜ[A] (n : B)) ⊗ₜ[A'] (1 : A' ⊗[A] B))
              = 1 ⊗ₜ ((1 : A') ⊗ₜ[A] (n : B)) := by
            have h := congrArg (tensorSqBaseChange A A' B) (hu.mem_descended.mp n.2)
            rw [map_mul, tensorSqBaseChange_tmul] at h
            simpa [Algebra.TensorProduct.one_def] using h
          rw [← smul_tmul', mul_smul_comm, hn', smul_tmul', smul_eq_mul, mul_one,
            smul_tmul, smul_assoc, one_smul]
      | add x y hx hy =>
          simp only [tmul_add, map_add] at hx hy ⊢
          rw [hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Naturality of the Picard class of a descent cocycle in the base ring**: the class
of the base-changed cocycle along `A → A'` is the image of the class under
`CommRing.Pic.mapAlgebra`.  Faithful flatness of the base-changed cover `A' ⊗[A] B` over
`A'` is a hypothesis (automatic for the covers in use, e.g. products of localizations
along a covering family). -/
theorem IsDescentCocycle.picClass_baseChange [Module.FaithfullyFlat A B]
    [Module.FaithfullyFlat A' (A' ⊗[A] B)] {u : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u) :
    (hu.baseChange (A' := A')).picClass = CommRing.Pic.mapAlgebra A A' hu.picClass := by
  rw [IsDescentCocycle.picClass, IsDescentCocycle.picClass,
    CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_mk_iff]
  exact ⟨(descendedBaseChangeEquiv hu).symm.trans
    (AlgebraTensorModule.congr (LinearEquiv.refl A' A')
      (CommRing.Pic.mk.linearEquiv A hu.descended).symm)⟩

end descended

end Module
