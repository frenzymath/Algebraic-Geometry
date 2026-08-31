/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.TensorProductFieldTowerMap
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelScalarExtension

/-!
# Map-level faces for finite-stage triple-model scalar extension

The canonical scalar-extension equivalence for a tensor pushout carries the scalar
extension of each original face map to the corresponding face of the scalar-extended
pushout.  These map equalities strengthen the pointwise pure-tensor formulas and can be
composed directly with descended triple-transition maps.
-/

set_option autoImplicit false

open TensorProduct
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

/-- Scalar extension of the left face, followed by the tensor-pushout base-change
equivalence, is the left face of the scalar-extended pushout. -/
theorem finiteStageTensorPushoutScalarExtension_faceLeft_map
    {R K A B₁ B₂ : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R K] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :
    let kf₁ := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := R) (K := K) f₁
    let kf₂ := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := R) (K := K) f₂
    let beta :
        (K ⊗[R] Pic0FiniteStageTensorPushoutRing f₁ f₂) ≃ₐ[K]
          Pic0FiniteStageTensorPushoutRing kf₁ kf₂ :=
      finiteStageTensorPushoutScalarExtension (K := K) f₁ f₂
    beta.toAlgHom.comp
        (AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := R) (K := K) (finiteStageTensorPushoutFaceLeft f₁ f₂)) =
      finiteStageTensorPushoutFaceLeft kf₁ kf₂ := by
  dsimp only
  let kf₁ := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f₁
  let kf₂ := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f₂
  let beta :
      (K ⊗[R] Pic0FiniteStageTensorPushoutRing f₁ f₂) ≃ₐ[K]
        Pic0FiniteStageTensorPushoutRing kf₁ kf₂ :=
    finiteStageTensorPushoutScalarExtension (K := K) f₁ f₂
  let lhs :
      (K ⊗[R] B₁) →ₐ[K] Pic0FiniteStageTensorPushoutRing kf₁ kf₂ :=
    beta.toAlgHom.comp
      (AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := R) (K := K) (finiteStageTensorPushoutFaceLeft f₁ f₂))
  let rhs :
      (K ⊗[R] B₁) →ₐ[K] Pic0FiniteStageTensorPushoutRing kf₁ kf₂ :=
    finiteStageTensorPushoutFaceLeft kf₁ kf₂
  change lhs = rhs
  apply DFunLike.ext _ _
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact lhs.map_zero.trans rhs.map_zero.symm
  | add x y hx hy =>
      calc
        lhs (x + y) = lhs x + lhs y := lhs.map_add x y
        _ = rhs x + rhs y := congrArg₂ (· + ·) hx hy
        _ = rhs (x + y) := (rhs.map_add x y).symm
  | tmul c b₁ =>
      letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
      letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
      letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
      letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
      let g₁ := AlgebraicJacobian.scalarExtensionMap
        (M := R) (K := K) (A := A) (B := B₁)
      let g₂ := AlgebraicJacobian.scalarExtensionMap
        (M := R) (K := K) (A := A) (B := B₂)
      letI : Algebra (K ⊗[R] A) (K ⊗[R] B₁) := g₁.toRingHom.toAlgebra
      letI : Algebra (K ⊗[R] A) (K ⊗[R] B₂) := g₂.toRingHom.toAlgebra
      change
        AlgebraicJacobian.tensorProductPushoutBaseChangeHomPinned
            (M := R) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
            (c ⊗ₜ[R] (b₁ ⊗ₜ[A] (1 : B₂))) =
          Algebra.TensorProduct.includeLeft
            (R := K ⊗[R] A) (S := K) (A := K ⊗[R] B₁) (B := K ⊗[R] B₂)
            (c ⊗ₜ[R] b₁)
      rw [AlgebraicJacobian.tensorProductPushoutBaseChangeHomPinned_tmul]
      rfl

/-- Scalar extension of the right face, followed by the tensor-pushout base-change
equivalence, is the right face of the scalar-extended pushout. -/
theorem finiteStageTensorPushoutScalarExtension_faceRight_map
    {R K A B₁ B₂ : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R K] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :
    let kf₁ := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := R) (K := K) f₁
    let kf₂ := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := R) (K := K) f₂
    let beta :
        (K ⊗[R] Pic0FiniteStageTensorPushoutRing f₁ f₂) ≃ₐ[K]
          Pic0FiniteStageTensorPushoutRing kf₁ kf₂ :=
      finiteStageTensorPushoutScalarExtension (K := K) f₁ f₂
    beta.toAlgHom.comp
        (AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := R) (K := K) (finiteStageTensorPushoutFaceRight f₁ f₂)) =
      finiteStageTensorPushoutFaceRight kf₁ kf₂ := by
  dsimp only
  let kf₁ := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f₁
  let kf₂ := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f₂
  let beta :
      (K ⊗[R] Pic0FiniteStageTensorPushoutRing f₁ f₂) ≃ₐ[K]
        Pic0FiniteStageTensorPushoutRing kf₁ kf₂ :=
    finiteStageTensorPushoutScalarExtension (K := K) f₁ f₂
  let lhs :
      (K ⊗[R] B₂) →ₐ[K] Pic0FiniteStageTensorPushoutRing kf₁ kf₂ :=
    beta.toAlgHom.comp
      (AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := R) (K := K) (finiteStageTensorPushoutFaceRight f₁ f₂))
  let rhs :
      (K ⊗[R] B₂) →ₐ[K] Pic0FiniteStageTensorPushoutRing kf₁ kf₂ :=
    finiteStageTensorPushoutFaceRight kf₁ kf₂
  change lhs = rhs
  apply DFunLike.ext _ _
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact lhs.map_zero.trans rhs.map_zero.symm
  | add x y hx hy =>
      calc
        lhs (x + y) = lhs x + lhs y := lhs.map_add x y
        _ = rhs x + rhs y := congrArg₂ (· + ·) hx hy
        _ = rhs (x + y) := (rhs.map_add x y).symm
  | tmul c b₂ =>
      have hunit :
          lhs ((1 : K) ⊗ₜ[R] b₂) =
            rhs ((1 : K) ⊗ₜ[R] b₂) := by
        letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
        letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
        letI : IsScalarTower R A B₁ := pic0FiniteStageTowerOfMap f₁
        letI : IsScalarTower R A B₂ := pic0FiniteStageTowerOfMap f₂
        let g₁ := AlgebraicJacobian.scalarExtensionMap
          (M := R) (K := K) (A := A) (B := B₁)
        let g₂ := AlgebraicJacobian.scalarExtensionMap
          (M := R) (K := K) (A := A) (B := B₂)
        letI : Algebra (K ⊗[R] A) (K ⊗[R] B₁) := g₁.toRingHom.toAlgebra
        letI : Algebra (K ⊗[R] A) (K ⊗[R] B₂) := g₂.toRingHom.toAlgebra
        change
          AlgebraicJacobian.tensorProductPushoutBaseChangeHomPinned
              (M := R) (K := K) (A := A) (B₁ := B₁) (B₂ := B₂)
              ((1 : K) ⊗ₜ[R] ((1 : B₁) ⊗ₜ[A] b₂)) =
            ((Algebra.TensorProduct.includeRight
              (R := K ⊗[R] A) (A := K ⊗[R] B₁) (B := K ⊗[R] B₂)
                ).restrictScalars K) ((1 : K) ⊗ₜ[R] b₂)
        rw [AlgebraicJacobian.tensorProductPushoutBaseChangeHomPinned_tmul]
        rfl
      have hcb :
          c ⊗ₜ[R] b₂ = c • ((1 : K) ⊗ₜ[R] b₂) := by
        rw [TensorProduct.smul_tmul']
        simp
      calc
        lhs (c ⊗ₜ[R] b₂) =
            lhs (c • ((1 : K) ⊗ₜ[R] b₂)) := congrArg lhs hcb
        _ = c • lhs ((1 : K) ⊗ₜ[R] b₂) :=
          lhs.toLinearMap.map_smul c _
        _ = c • rhs ((1 : K) ⊗ₜ[R] b₂) :=
          congrArg (fun z => c • z) hunit
        _ = rhs (c • ((1 : K) ⊗ₜ[R] b₂)) :=
          (rhs.toLinearMap.map_smul c _).symm
        _ = rhs (c ⊗ₜ[R] b₂) := congrArg rhs hcb.symm

end

end AlgebraicGeometry
