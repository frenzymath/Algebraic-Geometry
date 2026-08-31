/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.PicardGroup

/-!
# Invertible modules over finite product rings

This file proves that a finite product of invertible modules is invertible over the
corresponding product ring.  The main algebraic input is the coordinatewise equivalence

`(forall i, N i) tensor[(forall i, R i)] (forall i, M i) ~=
  (forall i, N i tensor[R i] M i)`.

The rings and modules are allowed to vary with the finite index.  This is distinct from
`TensorProduct.piRight`, where all factors are modules over one fixed base ring.
-/

set_option autoImplicit false

universe u v

open TensorProduct

namespace Module

section TensorPi

variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable (R : ι -> Type u) [forall i, CommSemiring (R i)]
variable (M N : ι -> Type u)
variable [forall i, AddCommMonoid (M i)] [forall i, AddCommMonoid (N i)]
variable [forall i, Module (R i) (M i)] [forall i, Module (R i) (N i)]

/-- Tensor products of dependent products over a finite product ring are computed
coordinatewise. -/
noncomputable def tensorPiEquiv :
    letI : Module (forall i, R i) (forall i, M i) := Pi.module'
    letI : Module (forall i, R i) (forall i, N i) := Pi.module'
    letI : Module (forall i, R i) (forall i, N i ⊗[R i] M i) := Pi.module'
    (forall i, N i) ⊗[(forall i, R i)] (forall i, M i) ≃ₗ[(forall i, R i)]
      (forall i, N i ⊗[R i] M i) := by
  let P := forall i, R i
  letI : Module P (forall i, M i) := Pi.module'
  letI : Module P (forall i, N i) := Pi.module'
  letI : Module P (forall i, N i ⊗[R i] M i) := Pi.module'
  letI : forall i, Algebra P (R i) := fun i => (Pi.evalRingHom R i).toAlgebra
  letI : forall i, Module P (M i) := fun i => Module.compHom _ (Pi.evalRingHom R i)
  letI : forall i, Module P (N i) := fun i => Module.compHom _ (Pi.evalRingHom R i)
  letI : forall i, Module P (N i ⊗[R i] M i) :=
    fun i => Module.compHom _ (Pi.evalRingHom R i)
  letI : forall i, IsScalarTower P (R i) (M i) := fun i => ⟨fun p r m => by
    change (p i * r) • m = (p i) • (r • m)
    rw [mul_smul]⟩
  letI : forall i, IsScalarTower P (R i) (N i) := fun i => ⟨fun p r n => by
    change (p i * r) • n = (p i) • (r • n)
    rw [mul_smul]⟩
  letI : forall i, Module (R i) (N i ⊗[P] M i) := fun i => TensorProduct.leftModule
  let scalarInv (i : ι) : N i ⊗[R i] M i →ₗ[P] N i ⊗[P] M i := by
    let gRi : N i ⊗[R i] M i →ₗ[R i] N i ⊗[P] M i :=
      TensorProduct.lift <| LinearMap.mk₂ (R i) (fun n m => n ⊗ₜ[P] m)
        (fun _ _ _ => add_tmul _ _ _)
        (fun _ _ _ => rfl)
        (fun _ _ _ => tmul_add _ _ _)
        (fun r n m => by
          let e : P := Pi.single i r
          calc
            n ⊗ₜ[P] (r • m) = n ⊗ₜ[P] (e • m) := by
              congr 1
              change r • m = (e i) • m
              simp [e]
            _ = (e • n) ⊗ₜ[P] m := (TensorProduct.smul_tmul e n m).symm
            _ = (r • n) ⊗ₜ[P] m := by
              congr 1
              change (e i) • n = r • n
              simp [e]
            _ = r • (n ⊗ₜ[P] m) := rfl)
    exact
      { toFun := gRi
        map_add' := gRi.map_add
        map_smul' := fun p x => by
          change gRi ((p i) • x) = (p i) • gRi x
          exact gRi.map_smul (p i) x }
  let singleM (i : ι) : M i →ₗ[P] (forall j, M j) :=
    { toFun := Pi.single i
      map_add' := Pi.single_add i
      map_smul' := fun p m => by
        ext j
        change Pi.single i ((p i) • m) j = p j • Pi.single i m j
        by_cases h : j = i
        · subst h
          simp
        · simp [Pi.single_eq_of_ne h] }
  let singleN (i : ι) : N i →ₗ[P] (forall j, N j) :=
    { toFun := Pi.single i
      map_add' := Pi.single_add i
      map_smul' := fun p n => by
        ext j
        change Pi.single i ((p i) • n) j = p j • Pi.single i n j
        by_cases h : j = i
        · subst h
          simp
        · simp [Pi.single_eq_of_ne h] }
  let embed (i : ι) : N i ⊗[R i] M i →ₗ[P]
      (forall j, N j) ⊗[P] (forall j, M j) :=
    (TensorProduct.map (singleN i) (singleM i)).comp (scalarInv i)
  let proj (i : ι) : (forall j, N j ⊗[R j] M j) →ₗ[P] N i ⊗[R i] M i :=
    { toFun := fun x => x i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let bil : (forall i, N i) →ₗ[P]
      (forall i, M i) →ₗ[P] (forall i, N i ⊗[R i] M i) :=
    { toFun := fun n =>
        { toFun := fun m i => n i ⊗ₜ[R i] m i
          map_add' := fun _ _ => by
            funext i
            exact tmul_add _ _ _
          map_smul' := fun p m => by
            funext i
            change n i ⊗ₜ[R i] (p i • m i) = p i • (n i ⊗ₜ[R i] m i)
            rw [TensorProduct.tmul_smul] }
      map_add' := fun n n' => by
        ext m i
        exact add_tmul _ _ _
      map_smul' := fun p n => by
        ext m i
        rfl }
  let f : (forall i, N i) ⊗[P] (forall i, M i) →ₗ[P]
      (forall i, N i ⊗[R i] M i) := TensorProduct.lift bil
  let g : (forall i, N i ⊗[R i] M i) →ₗ[P]
      (forall i, N i) ⊗[P] (forall i, M i) :=
    ∑ i, (embed i).comp (proj i)
  have hEmbed (i : ι) (x : N i ⊗[R i] M i) : f (embed i x) = Pi.single i x := by
    induction x using TensorProduct.induction_on with
    | zero => simp [f, embed]
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy, Pi.single_add]
    | tmul n m =>
        funext j
        by_cases h : j = i
        · subst h
          simp [f, bil, embed, scalarInv, singleM, singleN]
        · simp [f, bil, embed, scalarInv, singleM, singleN, Pi.single_eq_of_ne h]
  have hfg : f ∘ₗ g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, g, LinearMap.sum_apply, proj]
    change f (∑ i, embed i (x i)) = x
    rw [map_sum]
    simp_rw [hEmbed]
    exact Finset.univ_sum_single x
  have hPure (n : forall i, N i) (m : forall i, M i) :
      g (fun i => n i ⊗ₜ[R i] m i) = n ⊗ₜ[P] m := by
    simp only [g, LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, proj]
    change ∑ i, Pi.single i (n i) ⊗ₜ[P] Pi.single i (m i) = n ⊗ₜ[P] m
    have hterm (i : ι) :
        Pi.single i (n i) ⊗ₜ[P] Pi.single i (m i) =
          (Pi.single i (1 : R i) : P) • (n ⊗ₜ[P] m) := by
      let e : P := Pi.single i 1
      have he : e * e = e := by
        ext j
        change e j * e j = e j
        by_cases h : j = i
        · subst h
          simp [e]
        · simp [e, Pi.single_eq_of_ne h]
      calc
        Pi.single i (n i) ⊗ₜ[P] Pi.single i (m i) =
            (e • n) ⊗ₜ[P] (e • m) := by
          congr 1
          · ext j
            change Pi.single i (n i) j = e j • n j
            by_cases h : j = i
            · subst h
              simp [e]
            · simp [e, Pi.single_eq_of_ne h]
          · ext j
            change Pi.single i (m i) j = e j • m j
            by_cases h : j = i
            · subst h
              simp [e]
            · simp [e, Pi.single_eq_of_ne h]
        _ = n ⊗ₜ[P] (e • (e • m)) := TensorProduct.smul_tmul e n (e • m)
        _ = n ⊗ₜ[P] (e • m) := by
          rw [smul_smul, he]
        _ = e • (n ⊗ₜ[P] m) := by rw [TensorProduct.tmul_smul]
    simp_rw [hterm]
    rw [← Finset.sum_smul]
    have he : ∑ i : ι, (Pi.single i 1 : P) = 1 := by
      ext j
      simp
    rw [he, one_smul]
  have hgf : g ∘ₗ f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, LinearMap.id_apply, LinearMap.id_apply]; rfl
    | tmul n m => exact hPure n m
  exact LinearEquiv.ofLinear f g hfg hgf

end TensorPi

section InvertiblePi

variable {ι : Type v} [Finite ι]
variable (R : ι -> Type u) [forall i, CommSemiring (R i)]
variable (M : ι -> Type u) [forall i, AddCommMonoid (M i)]
variable [forall i, Module (R i) (M i)]

/-- A finite dependent product of invertible modules is invertible over the dependent
product of their base rings. -/
theorem Invertible.pi [forall i, Module.Invertible (R i) (M i)] :
    letI : Module (forall i, R i) (forall i, M i) := Pi.module'
    Module.Invertible (forall i, R i) (forall i, M i) := by
  classical
  letI := Fintype.ofFinite ι
  let P := forall i, R i
  letI : Module P (forall i, M i) := Pi.module'
  letI : forall i, Module P (Module.Dual (R i) (M i)) :=
    fun i => Module.compHom _ (Pi.evalRingHom R i)
  letI : Module P (forall i, Module.Dual (R i) (M i)) := Pi.module'
  letI : Module P (forall i, Module.Dual (R i) (M i) ⊗[R i] M i) := Pi.module'
  let e₁ := tensorPiEquiv R M (fun i => Module.Dual (R i) (M i))
  let e₂ : (forall i, Module.Dual (R i) (M i) ⊗[R i] M i) ≃ₗ[P] P :=
    { toFun := fun x i => Module.Invertible.linearEquiv (R i) (M i) (x i)
      invFun := fun x i => (Module.Invertible.linearEquiv (R i) (M i)).symm (x i)
      left_inv := fun x => by
        funext i
        exact (Module.Invertible.linearEquiv (R i) (M i)).symm_apply_apply (x i)
      right_inv := fun x => by
        funext i
        exact (Module.Invertible.linearEquiv (R i) (M i)).apply_symm_apply (x i)
      map_add' := fun x y => by
        funext i
        exact (Module.Invertible.linearEquiv (R i) (M i)).map_add (x i) (y i)
      map_smul' := fun p x => by
        funext i
        exact (Module.Invertible.linearEquiv (R i) (M i)).map_smul (p i) (x i) }
  exact Module.Invertible.right (e₁ ≪≫ₗ e₂)

end InvertiblePi

end Module
