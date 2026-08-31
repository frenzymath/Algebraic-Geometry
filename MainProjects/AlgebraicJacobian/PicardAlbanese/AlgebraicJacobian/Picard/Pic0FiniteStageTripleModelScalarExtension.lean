/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleOverlapRings
import AlgebraicJacobian.Descent.TensorProductPushoutData

/-!
# Scalar extension of finite-stage triple-overlap models

This file supplies canonical faces of a tensor-pushout model and the arbitrary-scalar
version of its base-change equivalence.  The generic interface keeps all tensor-product
instances tied to the algebra maps that select them, so dependent consumers can specialize
the results under an expected type without reconstructing those instances.
-/

set_option autoImplicit false

open CategoryTheory Limits TopologicalSpace TensorProduct
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

/-! ## Instance-stable tensor-pushout faces -/

/-- The left factor inclusion into the tensor pushout selected by two algebra maps. -/
noncomputable def finiteStageTensorPushoutFaceLeft
    {R A B₁ B₂ : Type u}
    [CommRing R] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :
    B₁ →ₐ[R] Pic0FiniteStageTensorPushoutRing f₁ f₂ := by
  letI := pic0FiniteStageAlgebraOfMap f₁
  letI := pic0FiniteStageAlgebraOfMap f₂
  letI := pic0FiniteStageTowerOfMap f₁
  exact Algebra.TensorProduct.includeLeft
    (R := A) (S := R) (A := B₁) (B := B₂)

/-- The right factor inclusion into the tensor pushout selected by two algebra maps. -/
noncomputable def finiteStageTensorPushoutFaceRight
    {R A B₁ B₂ : Type u}
    [CommRing R] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :
    B₂ →ₐ[R] Pic0FiniteStageTensorPushoutRing f₁ f₂ := by
  letI := pic0FiniteStageAlgebraOfMap f₁
  letI := pic0FiniteStageAlgebraOfMap f₂
  letI := pic0FiniteStageTowerOfMap f₁
  exact (Algebra.TensorProduct.includeRight
    (R := A) (A := B₁) (B := B₂)).restrictScalars R

/-! ## Arbitrary scalar extension -/

/-- Arbitrary scalar extension commutes with the tensor pushout selected by two algebra
maps. -/
noncomputable def finiteStageTensorPushoutScalarExtension
    {R K A B₁ B₂ : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R K] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :=
  by
    letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
    letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
    letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
    letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
    exact AlgebraicJacobian.tensorProductPushoutBaseChangeEquivPinned
      (M := R) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)

/-- The arbitrary-scalar tensor-pushout equivalence on a pure tensor. -/
theorem finiteStageTensorPushoutScalarExtension_tmul
    {R K A B₁ B₂ : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R K] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂)
    (c : K) (b₁ : B₁) (b₂ : B₂) :
    letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
    letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
    letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
    letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
    let kf₁ := AlgebraicJacobian.scalarExtensionMap
      (M := R) (K := K) (A := A) (B := B₁)
    let kf₂ := AlgebraicJacobian.scalarExtensionMap
      (M := R) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[R] A) (K ⊗[R] B₁) := kf₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[R] A) (K ⊗[R] B₂) := kf₂.toRingHom.toAlgebra
    finiteStageTensorPushoutScalarExtension f₁ f₂
        (c ⊗ₜ[R] (b₁ ⊗ₜ[A] b₂)) =
      (c ⊗ₜ[R] b₁) ⊗ₜ[K ⊗[R] A] ((1 : K) ⊗ₜ[R] b₂) := by
  dsimp only
  letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
  letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
  letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
  letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
  exact AlgebraicJacobian.tensorProductPushoutBaseChange_tmul c b₁ b₂

/-- Scalar extension carries the left face to the left factor in the literal pushout. -/
theorem finiteStageTensorPushoutScalarExtension_faceLeft
    {R K A B₁ B₂ : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R K] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) (c : K) (b₁ : B₁) :
    letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
    letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
    letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
    letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
    let kf₁ := AlgebraicJacobian.scalarExtensionMap
      (M := R) (K := K) (A := A) (B := B₁)
    let kf₂ := AlgebraicJacobian.scalarExtensionMap
      (M := R) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[R] A) (K ⊗[R] B₁) := kf₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[R] A) (K ⊗[R] B₂) := kf₂.toRingHom.toAlgebra
    finiteStageTensorPushoutScalarExtension f₁ f₂
        (c ⊗ₜ[R] (finiteStageTensorPushoutFaceLeft f₁ f₂ b₁)) =
      (c ⊗ₜ[R] b₁) ⊗ₜ[K ⊗[R] A] 1 := by
  dsimp only
  letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
  letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
  letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
  letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
  let kf₁ := AlgebraicJacobian.scalarExtensionMap
    (M := R) (K := K) (A := A) (B := B₁)
  let kf₂ := AlgebraicJacobian.scalarExtensionMap
    (M := R) (K := K) (A := A) (B := B₂)
  letI := kf₁.toRingHom.toAlgebra
  letI := kf₂.toRingHom.toAlgebra
  change finiteStageTensorPushoutScalarExtension f₁ f₂
      (c ⊗ₜ[R] (b₁ ⊗ₜ[A] 1)) =
    (c ⊗ₜ[R] b₁) ⊗ₜ[K ⊗[R] A] 1
  exact finiteStageTensorPushoutScalarExtension_tmul f₁ f₂ c b₁ 1

/-- Scalar extension carries the right face to the right factor in the literal pushout. -/
theorem finiteStageTensorPushoutScalarExtension_faceRight
    {R K A B₁ B₂ : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R K] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) (c : K) (b₂ : B₂) :
    letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
    letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
    letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
    letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
    let kf₁ := AlgebraicJacobian.scalarExtensionMap
      (M := R) (K := K) (A := A) (B := B₁)
    let kf₂ := AlgebraicJacobian.scalarExtensionMap
      (M := R) (K := K) (A := A) (B := B₂)
    letI : Algebra (K ⊗[R] A) (K ⊗[R] B₁) := kf₁.toRingHom.toAlgebra
    letI : Algebra (K ⊗[R] A) (K ⊗[R] B₂) := kf₂.toRingHom.toAlgebra
    finiteStageTensorPushoutScalarExtension f₁ f₂
        (c ⊗ₜ[R] (finiteStageTensorPushoutFaceRight f₁ f₂ b₂)) =
      (c ⊗ₜ[R] (1 : B₁)) ⊗ₜ[K ⊗[R] A] ((1 : K) ⊗ₜ[R] b₂) := by
  dsimp only
  letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
  letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
  letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
  letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
  let kf₁ := AlgebraicJacobian.scalarExtensionMap
    (M := R) (K := K) (A := A) (B := B₁)
  let kf₂ := AlgebraicJacobian.scalarExtensionMap
    (M := R) (K := K) (A := A) (B := B₂)
  letI := kf₁.toRingHom.toAlgebra
  letI := kf₂.toRingHom.toAlgebra
  change finiteStageTensorPushoutScalarExtension f₁ f₂
      (c ⊗ₜ[R] ((1 : B₁) ⊗ₜ[A] b₂)) =
    (c ⊗ₜ[R] (1 : B₁)) ⊗ₜ[K ⊗[R] A] ((1 : K) ⊗ₜ[R] b₂)
  exact finiteStageTensorPushoutScalarExtension_tmul f₁ f₂ c 1 b₂

end

end AlgebraicGeometry
