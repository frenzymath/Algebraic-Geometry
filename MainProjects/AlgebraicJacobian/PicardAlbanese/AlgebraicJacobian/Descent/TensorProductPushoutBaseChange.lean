/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Scalar extension of tensor-product pushouts

This file gives the canonical equivalence expressing that scalar extension commutes with
a pushout of commutative algebras.  The explicit homomorphisms and pure-tensor formulas
make the equivalence usable without relying on definitional choices of `Algebra` instances.
-/

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace AlgebraicJacobian

noncomputable section

/-- The canonical map on scalar extensions induced by an algebra map in a scalar tower. -/
def scalarExtensionMap {M K A B : Type u}
    [CommRing M] [CommRing K] [CommRing A] [CommRing B]
    [Algebra M K] [Algebra M A] [Algebra M B] [Algebra A B]
    [IsScalarTower M A B] :
    (K ⊗[M] A) →ₐ[K] (K ⊗[M] B) :=
  Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom M A B)

/-- The forward map distributing scalar extension over a tensor-product pushout. -/
def tensorProductPushoutBaseChangeHom {M K A B₁ B₂ : Type u}
    [CommRing M] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra M K] [Algebra M A]
    [Algebra A B₁] [Algebra A B₂]
    [Algebra M B₁] [Algebra M B₂]
    [IsScalarTower M A B₁] [IsScalarTower M A B₂] :
    let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
    let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
    (K ⊗[M] (B₁ ⊗[A] B₂)) →ₐ[K]
      ((K ⊗[M] B₁) ⊗[K ⊗[M] A] (K ⊗[M] B₂)) := by
  dsimp only
  let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
  let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
  let R := (K ⊗[M] B₁) ⊗[K ⊗[M] A] (K ⊗[M] B₂)
  let leftIncl : (K ⊗[M] B₁) →ₐ[K] R :=
    Algebra.TensorProduct.includeLeft
  let rightIncl : (K ⊗[M] B₂) →ₐ[K] R :=
    Algebra.TensorProduct.includeRight.restrictScalars K
  let b₁InclM : B₁ →ₐ[M] R :=
    (leftIncl.restrictScalars M).comp Algebra.TensorProduct.includeRight
  let b₂InclM : B₂ →ₐ[M] R :=
    (rightIncl.restrictScalars M).comp Algebra.TensorProduct.includeRight
  letI : Algebra A R :=
    (b₁InclM.toRingHom.comp (algebraMap A B₁)).toAlgebra
  letI : Algebra B₁ R := b₁InclM.toRingHom.toAlgebra
  letI : Algebra B₂ R := b₂InclM.toRingHom.toAlgebra
  haveI : IsScalarTower A B₁ R :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hB₂ : b₂InclM.toRingHom.comp (algebraMap A B₂) =
      algebraMap A R := by
    ext a
    change 1 ⊗ₜ[K ⊗[M] A] (1 ⊗ₜ[M] (algebraMap A B₂) a) =
      (1 ⊗ₜ[M] (algebraMap A B₁) a) ⊗ₜ[K ⊗[M] A] 1
    have hf₁ : f₁ (1 ⊗ₜ[M] a) = 1 ⊗ₜ[M] (algebraMap A B₁) a := by
      simp [f₁, scalarExtensionMap]
    have hf₂ : f₂ (1 ⊗ₜ[M] a) = 1 ⊗ₜ[M] (algebraMap A B₂) a := by
      simp [f₂, scalarExtensionMap]
    rw [← hf₁, ← hf₂]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
      (R := K ⊗[M] A) (A := K ⊗[M] B₁) (B := K ⊗[M] B₂)
      (1 ⊗ₜ[M] a)).symm
  haveI : IsScalarTower A B₂ R :=
    IsScalarTower.of_algebraMap_eq
      (fun a => (DFunLike.congr_fun hB₂ a).symm)
  haveI : IsScalarTower M B₁ R :=
    IsScalarTower.of_algebraMap_eq
      (fun m => (b₁InclM.commutes m).symm)
  haveI : IsScalarTower M A R :=
    IsScalarTower.of_algebraMap_eq (fun m => by
      calc
        (algebraMap M R) m =
            (algebraMap B₁ R) ((algebraMap M B₁) m) :=
          IsScalarTower.algebraMap_apply M B₁ R m
        _ = (algebraMap B₁ R) ((algebraMap A B₁) ((algebraMap M A) m)) := by
          rw [← IsScalarTower.algebraMap_apply M A B₁ m]
        _ = (algebraMap A R) ((algebraMap M A) m) :=
          (IsScalarTower.algebraMap_apply A B₁ R _).symm)
  let inner : (B₁ ⊗[A] B₂) →ₐ[A] R :=
    Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom A B₁ R)
      (IsScalarTower.toAlgHom A B₂ R)
      (fun _ _ => Commute.all _ _)
  exact AlgHom.liftEquiv M K (B₁ ⊗[A] B₂) R (inner.restrictScalars M)

/-- The inverse map collecting a tensor product of scalar extensions into one scalar
extension of the pushout. -/
def tensorProductPushoutBaseChangeInvHom {M K A B₁ B₂ : Type u}
    [CommRing M] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra M K] [Algebra M A]
    [Algebra A B₁] [Algebra A B₂]
    [Algebra M B₁] [Algebra M B₂]
    [IsScalarTower M A B₁] [IsScalarTower M A B₂] :
    let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
    let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
    ((K ⊗[M] B₁) ⊗[K ⊗[M] A] (K ⊗[M] B₂)) →ₐ[K]
      (K ⊗[M] (B₁ ⊗[A] B₂)) := by
  dsimp only
  let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
  let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
  let P := K ⊗[M] A
  let X₁ := K ⊗[M] B₁
  let X₂ := K ⊗[M] B₂
  let Q := B₁ ⊗[A] B₂
  let L := K ⊗[M] Q
  let q₁ : B₁ →ₐ[A] Q := Algebra.TensorProduct.includeLeft
  let q₂ : B₂ →ₐ[A] Q := Algebra.TensorProduct.includeRight
  let q₁M : B₁ →ₐ[M] Q := q₁.restrictScalars M
  let q₂M : B₂ →ₐ[M] Q := q₂.restrictScalars M
  let b₁L : B₁ →ₐ[M] L := Algebra.TensorProduct.includeRight.comp q₁M
  let b₂L : B₂ →ₐ[M] L := Algebra.TensorProduct.includeRight.comp q₂M
  let aL : A →ₐ[M] L := b₁L.comp (IsScalarTower.toAlgHom M A B₁)
  let pL : P →ₐ[K] L := AlgHom.liftEquiv M K A L aL
  let x₁L : X₁ →ₐ[K] L := AlgHom.liftEquiv M K B₁ L b₁L
  let x₂L : X₂ →ₐ[K] L := AlgHom.liftEquiv M K B₂ L b₂L
  letI : Algebra P L := pL.toRingHom.toAlgebra
  letI : Algebra X₁ L := x₁L.toRingHom.toAlgebra
  letI : Algebra X₂ L := x₂L.toRingHom.toAlgebra
  have hp₁ : x₁L.comp f₁ = pL := by
    apply DFunLike.ext _ _
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k a =>
        change x₁L (f₁ (k ⊗ₜ[M] a)) = pL (k ⊗ₜ[M] a)
        rw [show f₁ (k ⊗ₜ[M] a) = k ⊗ₜ[M] (algebraMap A B₁) a by
          simp [f₁, scalarExtensionMap]]
        rw [AlgHom.liftEquiv_tmul, AlgHom.liftEquiv_tmul]
        rfl
    | add x y hx hy =>
        change x₁L (f₁ x) = pL x at hx
        change x₁L (f₁ y) = pL y at hy
        change x₁L (f₁ (x + y)) = pL (x + y)
        rw [map_add, map_add, map_add, hx, hy]
  have hp₂ : x₂L.comp f₂ = pL := by
    apply DFunLike.ext _ _
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k a =>
        change x₂L (f₂ (k ⊗ₜ[M] a)) = pL (k ⊗ₜ[M] a)
        rw [show f₂ (k ⊗ₜ[M] a) = k ⊗ₜ[M] (algebraMap A B₂) a by
          simp [f₂, scalarExtensionMap]]
        rw [AlgHom.liftEquiv_tmul, AlgHom.liftEquiv_tmul]
        apply congrArg (k • ·)
        change 1 ⊗ₜ[M] (1 ⊗ₜ[A] (algebraMap A B₂) a) =
          1 ⊗ₜ[M] ((algebraMap A B₁) a ⊗ₜ[A] 1)
        apply congrArg (fun q : Q => (1 : K) ⊗ₜ[M] q)
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
          (R := A) (A := B₁) (B := B₂) a).symm
    | add x y hx hy =>
        change x₂L (f₂ x) = pL x at hx
        change x₂L (f₂ y) = pL y at hy
        change x₂L (f₂ (x + y)) = pL (x + y)
        rw [map_add, map_add, map_add, hx, hy]
  haveI : IsScalarTower P X₁ L :=
    IsScalarTower.of_algebraMap_eq
      (fun z => (DFunLike.congr_fun hp₁ z).symm)
  haveI : IsScalarTower P X₂ L :=
    IsScalarTower.of_algebraMap_eq
      (fun z => (DFunLike.congr_fun hp₂ z).symm)
  haveI : IsScalarTower K P L :=
    IsScalarTower.of_algebraMap_eq
      (fun k => (pL.commutes k).symm)
  exact (Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom P X₁ L)
    (IsScalarTower.toAlgHom P X₂ L)
    (fun _ _ => Commute.all _ _)).restrictScalars K

/-- The forward base-change map on a pure tensor. -/
theorem tensorProductPushoutBaseChangeHom_tmul {M K A B₁ B₂ : Type u}
    [CommRing M] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra M K] [Algebra M A]
    [Algebra A B₁] [Algebra A B₂]
    [Algebra M B₁] [Algebra M B₂]
    [IsScalarTower M A B₁] [IsScalarTower M A B₂]
    (k : K) (b₁ : B₁) (b₂ : B₂) :
    let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
    let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
    tensorProductPushoutBaseChangeHom
        (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
        (k ⊗ₜ[M] (b₁ ⊗ₜ[A] b₂)) =
      (k ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] (1 ⊗ₜ[M] b₂) := by
  dsimp only
  let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
  let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
  simp only [tensorProductPushoutBaseChangeHom, Lean.Elab.WF.paramLet,
    AlgHom.toRingHom_eq_coe, id_eq, AlgHom.liftEquiv_tmul,
    AlgHom.coe_restrictScalars', Algebra.TensorProduct.lift_tmul,
    IsScalarTower.coe_toAlgHom']
  change k • ((((1 : K) ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A]
        (1 : K ⊗[M] B₂)) *
      ((1 : K ⊗[M] B₁) ⊗ₜ[K ⊗[M] A] ((1 : K) ⊗ₜ[M] b₂))) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [TensorProduct.smul_tmul']
  congr 1
  rw [TensorProduct.smul_tmul']
  simp

/-- The inverse base-change map on pure tensors. -/
theorem tensorProductPushoutBaseChangeInvHom_tmul {M K A B₁ B₂ : Type u}
    [CommRing M] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra M K] [Algebra M A]
    [Algebra A B₁] [Algebra A B₂]
    [Algebra M B₁] [Algebra M B₂]
    [IsScalarTower M A B₁] [IsScalarTower M A B₂]
    (k₁ k₂ : K) (b₁ : B₁) (b₂ : B₂) :
    let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
    let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
    tensorProductPushoutBaseChangeInvHom
        (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
        ((k₁ ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] (k₂ ⊗ₜ[M] b₂)) =
      (k₁ * k₂) ⊗ₜ[M] (b₁ ⊗ₜ[A] b₂) := by
  dsimp only
  let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
  let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
  simp only [tensorProductPushoutBaseChangeInvHom, Lean.Elab.WF.paramLet,
    AlgHom.toRingHom_eq_coe, id_eq, AlgHom.coe_restrictScalars']
  change (k₁ • ((1 : K) ⊗ₜ[M] (b₁ ⊗ₜ[A] 1))) *
      (k₂ • ((1 : K) ⊗ₜ[M] (1 ⊗ₜ[A] b₂))) = _
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp

/-- Scalar extension commutes with a tensor-product pushout of commutative algebras. -/
def tensorProductPushoutBaseChange {M K A B₁ B₂ : Type u}
    [CommRing M] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra M K] [Algebra M A]
    [Algebra A B₁] [Algebra A B₂]
    [Algebra M B₁] [Algebra M B₂]
    [IsScalarTower M A B₁] [IsScalarTower M A B₂] :
    let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
    let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
    (K ⊗[M] (B₁ ⊗[A] B₂)) ≃ₐ[K]
      ((K ⊗[M] B₁) ⊗[K ⊗[M] A] (K ⊗[M] B₂)) := by
  dsimp only
  let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
  let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
  let forward := tensorProductPushoutBaseChangeHom
    (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
  let inverse := tensorProductPushoutBaseChangeInvHom
    (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
  apply AlgEquiv.ofAlgHom forward inverse
  · apply DFunLike.ext _ _
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x₁ x₂ =>
        induction x₁ using TensorProduct.induction_on with
        | zero => simp
        | tmul k₁ b₁ =>
            induction x₂ using TensorProduct.induction_on with
            | zero => simp
            | tmul k₂ b₂ =>
                change forward (inverse
                    ((k₁ ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] (k₂ ⊗ₜ[M] b₂))) = _
                rw [tensorProductPushoutBaseChangeInvHom_tmul,
                  tensorProductPushoutBaseChangeHom_tmul]
                change ((k₁ * k₂) ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A]
                    (1 ⊗ₜ[M] b₂) =
                  (k₁ ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] (k₂ ⊗ₜ[M] b₂)
                have hk₂ : k₂ ⊗ₜ[M] b₂ = k₂ • ((1 : K) ⊗ₜ[M] b₂) := by
                  rw [TensorProduct.smul_tmul']
                  simp
                rw [hk₂, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
                apply congrArg (fun x : K ⊗[M] B₁ =>
                  x ⊗ₜ[K ⊗[M] A] ((1 : K) ⊗ₜ[M] b₂))
                apply congrArg (fun c : K => c ⊗ₜ[M] b₁)
                simpa [smul_eq_mul] using (mul_comm k₁ k₂)
            | add x y hx hy =>
                change forward (inverse
                    ((k₁ ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] x)) = _ at hx
                change forward (inverse
                    ((k₁ ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] y)) = _ at hy
                change forward (inverse
                    ((k₁ ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] (x + y))) = _
                rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy]
        | add x y hx hy =>
            change forward (inverse (x ⊗ₜ[K ⊗[M] A] x₂)) = _ at hx
            change forward (inverse (y ⊗ₜ[K ⊗[M] A] x₂)) = _ at hy
            change forward (inverse ((x + y) ⊗ₜ[K ⊗[M] A] x₂)) = _
            rw [TensorProduct.add_tmul, map_add, map_add, map_add, hx, hy]
    | add x y hx hy =>
        change forward (inverse x) = _ at hx
        change forward (inverse y) = _ at hy
        change forward (inverse (x + y)) = _
        rw [map_add, map_add, map_add, hx, hy]
  · apply DFunLike.ext _ _
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k q =>
        induction q using TensorProduct.induction_on with
        | zero => simp
        | tmul b₁ b₂ =>
            change inverse (forward (k ⊗ₜ[M] (b₁ ⊗ₜ[A] b₂))) = _
            rw [tensorProductPushoutBaseChangeHom_tmul,
              tensorProductPushoutBaseChangeInvHom_tmul]
            simp
        | add x y hx hy =>
            change inverse (forward (k ⊗ₜ[M] x)) = _ at hx
            change inverse (forward (k ⊗ₜ[M] y)) = _ at hy
            change inverse (forward (k ⊗ₜ[M] (x + y))) = _
            rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy]
    | add x y hx hy =>
        change inverse (forward x) = _ at hx
        change inverse (forward y) = _ at hy
        change inverse (forward (x + y)) = _
        rw [map_add, map_add, map_add, hx, hy]

/-- The base-change equivalence on a pure tensor. -/
theorem tensorProductPushoutBaseChange_tmul {M K A B₁ B₂ : Type u}
    [CommRing M] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra M K] [Algebra M A]
    [Algebra A B₁] [Algebra A B₂]
    [Algebra M B₁] [Algebra M B₂]
    [IsScalarTower M A B₁] [IsScalarTower M A B₂]
    (k : K) (b₁ : B₁) (b₂ : B₂) :
    let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
    let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
    tensorProductPushoutBaseChange
        (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
        (k ⊗ₜ[M] (b₁ ⊗ₜ[A] b₂)) =
      (k ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] (1 ⊗ₜ[M] b₂) := by
  dsimp only
  let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
  let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
  change tensorProductPushoutBaseChangeHom
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      (k ⊗ₜ[M] (b₁ ⊗ₜ[A] b₂)) = _
  exact tensorProductPushoutBaseChangeHom_tmul k b₁ b₂

/-- The inverse base-change equivalence on pure tensors. -/
theorem tensorProductPushoutBaseChange_symm_tmul {M K A B₁ B₂ : Type u}
    [CommRing M] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra M K] [Algebra M A]
    [Algebra A B₁] [Algebra A B₂]
    [Algebra M B₁] [Algebra M B₂]
    [IsScalarTower M A B₁] [IsScalarTower M A B₂]
    (k₁ k₂ : K) (b₁ : B₁) (b₂ : B₂) :
    let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
    let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
    (tensorProductPushoutBaseChange
        (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)).symm
        ((k₁ ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] (k₂ ⊗ₜ[M] b₂)) =
      (k₁ * k₂) ⊗ₜ[M] (b₁ ⊗ₜ[A] b₂) := by
  dsimp only
  let f₁ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)
  let f₂ := scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₁) := f₁.toRingHom.toAlgebra
  letI : Algebra (K ⊗[M] A) (K ⊗[M] B₂) := f₂.toRingHom.toAlgebra
  change tensorProductPushoutBaseChangeInvHom
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      ((k₁ ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] (k₂ ⊗ₜ[M] b₂)) = _
  exact tensorProductPushoutBaseChangeInvHom_tmul k₁ k₂ b₁ b₂

/-! ## Core pinned package

The definitions above predate the data facade and expose their generated tensor-product
`Algebra` instances through nested `letI` expressions.  The following small package keeps
those two witnesses as parameters of one object, so a lower-layer consumer can carry the
equivalence without recreating the dependent target type at every call site.
-/

section PinnedPackage

variable {M K A B₁ B₂ : Type u}
variable [CommRing M] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
variable [Algebra M K] [Algebra M A]
variable [Algebra A B₁] [Algebra A B₂]
variable [Algebra M B₁] [Algebra M B₂]
variable [IsScalarTower M A B₁] [IsScalarTower M A B₂]

/-! ### Explicit target carrier -/

/- The usual notation for the target tensor product obtains its module structures
from the two `Algebra` instances by typeclass search.  The carrier below passes
those module structures as explicit arguments instead.  Under `leftAlgebra` and
`rightAlgebra` this is definitionally the same tensor product, but its public
type no longer contains a `letI` block that callers must reproduce. -/
abbrev tensorProductPushoutBaseChangeTarget
    (leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁))
    (rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)) : Type u :=
  @TensorProduct (K ⊗[M] A) _ (K ⊗[M] B₁) (K ⊗[M] B₂) _ _
    (@Algebra.toModule (K ⊗[M] A) (K ⊗[M] B₁) _ _ leftAlgebra)
    (@Algebra.toModule (K ⊗[M] A) (K ⊗[M] B₂) _ _ rightAlgebra)

/-- A pure tensor in an explicitly pinned target carrier. -/
abbrev tensorProductPushoutBaseChangeTargetTmul
    (leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁))
    (rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂))
    (x : K ⊗[M] B₁) (y : K ⊗[M] B₂) :
    tensorProductPushoutBaseChangeTarget leftAlgebra rightAlgebra :=
  @TensorProduct.tmul (K ⊗[M] A) _ (K ⊗[M] B₁) (K ⊗[M] B₂) _ _
    (@Algebra.toModule (K ⊗[M] A) (K ⊗[M] B₁) _ _ leftAlgebra)
    (@Algebra.toModule (K ⊗[M] A) (K ⊗[M] B₂) _ _ rightAlgebra) x y

/-- A scalar-extension pushout equivalence with its two target algebra witnesses pinned.

The witnesses are explicit parameters of the package rather than locally regenerated
instances.  This is intentionally a small core object; richer carrier/map records can
decorate it in modules that also need the factor inclusions.
-/
structure TensorProductPushoutBaseChangePackage
    (leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁))
    (rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)) where
  equivalence :
    (K ⊗[M] (B₁ ⊗[A] B₂)) ≃ₐ[K]
      tensorProductPushoutBaseChangeTarget leftAlgebra rightAlgebra

namespace TensorProductPushoutBaseChangePackage

/-- The source carrier of a pinned package. -/
abbrev source
    {leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁)}
    {rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)}
    (_P : TensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra) : Type u :=
  K ⊗[M] (B₁ ⊗[A] B₂)

/-- The target carrier of a pinned package. -/
abbrev target
    {leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁)}
    {rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)}
    (_P : TensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra) : Type u :=
  tensorProductPushoutBaseChangeTarget leftAlgebra rightAlgebra

/-- The forward map carried by a pinned package. -/
noncomputable def hom
    {leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁)}
    {rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)}
    (P : TensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra) :
    P.source →ₐ[K] P.target :=
  P.equivalence.toAlgHom

/-- The inverse map carried by a pinned package. -/
noncomputable def inv
    {leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁)}
    {rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)}
    (P : TensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra) :
    P.target →ₐ[K] P.source :=
  P.equivalence.symm.toAlgHom

omit [IsScalarTower M A B₂] in
@[simp]
theorem hom_inv
    {leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁)}
    {rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)}
    (P : TensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra) :
    P.inv.comp P.hom = AlgHom.id K P.source := by
  letI := leftAlgebra
  letI := rightAlgebra
  dsimp only [inv, hom]
  apply DFunLike.ext _ _
  intro x
  exact P.equivalence.left_inv x

omit [IsScalarTower M A B₂] in
@[simp]
theorem inv_hom
    {leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁)}
    {rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)}
    (P : TensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra) :
    P.hom.comp P.inv = AlgHom.id K P.target := by
  letI := leftAlgebra
  letI := rightAlgebra
  dsimp only [inv, hom]
  apply DFunLike.ext _ _
  intro x
  exact P.equivalence.right_inv x

end TensorProductPushoutBaseChangePackage

/-! ## Explicit map data -/

/- The package above stores an equivalence.  This record is the map-level
interface for clients that need to transport the two directions separately.
Its target carrier uses the explicit module arguments above, so all four
fields share one pinned carrier without relying on instance search. -/
structure TensorProductPushoutBaseChangeMaps
    (leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁))
    (rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)) where
  /-- The forward base-change map. -/
  hom :
    (K ⊗[M] (B₁ ⊗[A] B₂)) →ₐ[K]
      tensorProductPushoutBaseChangeTarget leftAlgebra rightAlgebra
  /-- The inverse base-change map. -/
  inv :
    tensorProductPushoutBaseChangeTarget leftAlgebra rightAlgebra →ₐ[K]
      (K ⊗[M] (B₁ ⊗[A] B₂))
  /-- The inverse followed by the forward map is the identity on the source. -/
  left_inv :
    inv.comp hom = AlgHom.id K (K ⊗[M] (B₁ ⊗[A] B₂))
  /-- The forward followed by the inverse map is the identity on the target. -/
  right_inv :
    hom.comp inv =
      AlgHom.id K (tensorProductPushoutBaseChangeTarget leftAlgebra rightAlgebra)

namespace TensorProductPushoutBaseChangeMaps

/-- Recover the algebra equivalence represented by explicit maps and inverse laws. -/
noncomputable def equiv
    {leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁)}
    {rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)}
    (P : TensorProductPushoutBaseChangeMaps
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra) :
    (K ⊗[M] (B₁ ⊗[A] B₂)) ≃ₐ[K]
      tensorProductPushoutBaseChangeTarget leftAlgebra rightAlgebra :=
  AlgEquiv.ofAlgHom P.hom P.inv P.right_inv P.left_inv

omit [IsScalarTower M A B₂] in
@[simp]
theorem left_inv_apply
    {leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁)}
    {rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)}
    (P : TensorProductPushoutBaseChangeMaps
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra)
    (x : K ⊗[M] (B₁ ⊗[A] B₂)) :
    P.inv (P.hom x) = x := by
  exact DFunLike.congr_fun P.left_inv x

omit [IsScalarTower M A B₂] in
@[simp]
theorem right_inv_apply
    {leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁)}
    {rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)}
    (P : TensorProductPushoutBaseChangeMaps
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra)
    (x : tensorProductPushoutBaseChangeTarget leftAlgebra rightAlgebra) :
    P.hom (P.inv x) = x := by
  exact DFunLike.congr_fun P.right_inv x

end TensorProductPushoutBaseChangeMaps

/-! ### Package adapter -/

/-- View a pinned equivalence package as explicit forward and inverse map data. -/
noncomputable def TensorProductPushoutBaseChangePackage.toMaps
    {leftAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₁)}
    {rightAlgebra : Algebra (K ⊗[M] A) (K ⊗[M] B₂)}
    (P : TensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra) :
    TensorProductPushoutBaseChangeMaps
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      leftAlgebra rightAlgebra := by
  refine { hom := P.equivalence.toAlgHom
           inv := P.equivalence.symm.toAlgHom
           left_inv := ?_
           right_inv := ?_ }
  · apply DFunLike.ext _ _
    intro x
    exact P.equivalence.left_inv x
  · apply DFunLike.ext _ _
    intro x
    exact P.equivalence.right_inv x

/-! ### Canonical map data -/

/- These names expose the particular algebra witnesses used by the canonical
comparison.  Keeping them as reducible definitions lets clients state maps and
carriers with short, reusable types while retaining definitional transparency. -/
@[reducible]
noncomputable def tensorProductPushoutBaseChangeLeftAlgebra :
    Algebra (K ⊗[M] A) (K ⊗[M] B₁) :=
  (scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)).toRingHom.toAlgebra

@[reducible]
noncomputable def tensorProductPushoutBaseChangeRightAlgebra :
    Algebra (K ⊗[M] A) (K ⊗[M] B₂) :=
  (scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)).toRingHom.toAlgebra

/-- The canonical package associated with the scalar-extension maps in this file. -/
noncomputable def tensorProductPushoutBaseChangePackage :
    TensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      ((scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)).toRingHom.toAlgebra)
      ((scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)).toRingHom.toAlgebra) := by
  let leftAlgebra :=
    (scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)).toRingHom.toAlgebra
  let rightAlgebra :=
    (scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)).toRingHom.toAlgebra
  letI := leftAlgebra
  letI := rightAlgebra
  exact ⟨tensorProductPushoutBaseChange
    (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)⟩

@[simp]
theorem tensorProductPushoutBaseChangePackage_tmul
    (k : K) (b₁ : B₁) (b₂ : B₂) :
    let leftAlgebra :=
      (scalarExtensionMap (M := M) (K := K) (A := A) (B := B₁)).toRingHom.toAlgebra
    let rightAlgebra :=
      (scalarExtensionMap (M := M) (K := K) (A := A) (B := B₂)).toRingHom.toAlgebra
    letI := leftAlgebra
    letI := rightAlgebra
    (tensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)).equivalence
        (k ⊗ₜ[M] (b₁ ⊗ₜ[A] b₂)) =
      (k ⊗ₜ[M] b₁) ⊗ₜ[K ⊗[M] A] (1 ⊗ₜ[M] b₂) := by
  dsimp only [tensorProductPushoutBaseChangePackage]
  exact tensorProductPushoutBaseChange_tmul k b₁ b₂

/- The canonical maps are now available as one object.  In particular, a
consumer can carry this value through a larger record instead of reconstructing
the equivalence (and its target instances) at every use site. -/
noncomputable def tensorProductPushoutBaseChangeMaps :
    TensorProductPushoutBaseChangeMaps
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
      (tensorProductPushoutBaseChangeLeftAlgebra
        (M := M) (K := K) (A := A) (B₁ := B₁))
      (tensorProductPushoutBaseChangeRightAlgebra
        (M := M) (K := K) (A := A) (B₂ := B₂)) :=
  TensorProductPushoutBaseChangePackage.toMaps
    (tensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂))

@[simp]
theorem tensorProductPushoutBaseChangeMaps_hom_tmul
    (k : K) (b₁ : B₁) (b₂ : B₂) :
    (tensorProductPushoutBaseChangeMaps
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)).hom
        (k ⊗ₜ[M] (b₁ ⊗ₜ[A] b₂)) =
      tensorProductPushoutBaseChangeTargetTmul
        (tensorProductPushoutBaseChangeLeftAlgebra
          (M := M) (K := K) (A := A) (B₁ := B₁))
        (tensorProductPushoutBaseChangeRightAlgebra
          (M := M) (K := K) (A := A) (B₂ := B₂))
        (k ⊗ₜ[M] b₁) (1 ⊗ₜ[M] b₂) := by
  change (tensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)).equivalence
      (k ⊗ₜ[M] (b₁ ⊗ₜ[A] b₂)) = _
  exact tensorProductPushoutBaseChangePackage_tmul k b₁ b₂

@[simp]
theorem tensorProductPushoutBaseChangeMaps_inv_tmul
    (k₁ k₂ : K) (b₁ : B₁) (b₂ : B₂) :
    (tensorProductPushoutBaseChangeMaps
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)).inv
        (tensorProductPushoutBaseChangeTargetTmul
          (tensorProductPushoutBaseChangeLeftAlgebra
            (M := M) (K := K) (A := A) (B₁ := B₁))
          (tensorProductPushoutBaseChangeRightAlgebra
            (M := M) (K := K) (A := A) (B₂ := B₂))
          (k₁ ⊗ₜ[M] b₁) (k₂ ⊗ₜ[M] b₂)) =
      (k₁ * k₂) ⊗ₜ[M] (b₁ ⊗ₜ[A] b₂) := by
  change (tensorProductPushoutBaseChangePackage
      (M := M) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)).equivalence.symm
      (tensorProductPushoutBaseChangeTargetTmul
        (tensorProductPushoutBaseChangeLeftAlgebra
          (M := M) (K := K) (A := A) (B₁ := B₁))
        (tensorProductPushoutBaseChangeRightAlgebra
          (M := M) (K := K) (A := A) (B₂ := B₂))
        (k₁ ⊗ₜ[M] b₁) (k₂ ⊗ₜ[M] b₂)) = _
  exact tensorProductPushoutBaseChange_symm_tmul k₁ k₂ b₁ b₂

end PinnedPackage

end

end AlgebraicJacobian
