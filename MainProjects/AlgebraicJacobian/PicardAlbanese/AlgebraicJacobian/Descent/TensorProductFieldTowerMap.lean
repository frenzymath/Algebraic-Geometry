/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.TensorProductPushoutBaseChange

/-!
# Maps through a tower of scalar extensions

This file isolates the elementary algebra behind finite-stage maps.  An algebra map can
be extended along a scalar map, and the cancellation equivalence for a tower identifies
that extension with any ambient map which commutes with the direct scalar extension.
-/

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace AlgebraicJacobian

noncomputable section

/-- Scalar extension of an algebra map.  This is the map-level form of
`scalarExtensionMap`, whose special case induced by an algebra structure is recorded
separately in the pushout base-change file. -/
def scalarExtensionMapOfAlgHom {R K A B : Type u}
    [CommRing R] [CommRing K] [Semiring A] [Semiring B]
    [Algebra R K] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    (K ⊗[R] A) →ₐ[K] (K ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id K K) f

/-- `scalarExtensionMapOfAlgHom` sends a pure tensor by applying the original map to
its algebra factor. -/
@[simp]
theorem scalarExtensionMapOfAlgHom_tmul {R K A B : Type u}
    [CommRing R] [CommRing K] [Semiring A] [Semiring B]
    [Algebra R K] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (c : K) (a : A) :
    scalarExtensionMapOfAlgHom (R := R) (K := K) f (c ⊗ₜ[R] a) =
      c ⊗ₜ[R] f a := by
  simp [scalarExtensionMapOfAlgHom]

/-- Scalar extension of a map is natural in a tower of scalar rings. -/
theorem scalarExtensionMapOfAlgHom_tower {F L K A B : Type u}
    [CommRing F] [CommRing L] [CommRing K] [Semiring A] [Semiring B]
    [Algebra F L] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [Algebra F A] [Algebra F B]
    (f : A →ₐ[F] B) :
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F L K)
        (AlgHom.id F B)).comp
        ((scalarExtensionMapOfAlgHom (R := F) (K := L) f).restrictScalars F) =
      ((scalarExtensionMapOfAlgHom (R := F) (K := K) f).restrictScalars F).comp
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F L K)
          (AlgHom.id F A)) := by
  ext x
  · simp [scalarExtensionMapOfAlgHom]
  · simp [scalarExtensionMapOfAlgHom]

/-- Scalar extension preserves composition of algebra maps. -/
@[simp]
theorem scalarExtensionMapOfAlgHom_comp {R K A B D : Type u}
    [CommRing R] [CommRing K] [Semiring A] [Semiring B] [Semiring D]
    [Algebra R K] [Algebra R A] [Algebra R B] [Algebra R D]
    (f : A →ₐ[R] B) (g : B →ₐ[R] D) :
    (scalarExtensionMapOfAlgHom (R := R) (K := K) g).comp
        (scalarExtensionMapOfAlgHom (R := R) (K := K) f) =
      scalarExtensionMapOfAlgHom (R := R) (K := K) (g.comp f) := by
  ext x
  · simp [scalarExtensionMapOfAlgHom]

/-- Scalar extension preserves the identity algebra map. -/
@[simp]
theorem scalarExtensionMapOfAlgHom_id {R K A : Type u}
    [CommRing R] [CommRing K] [Semiring A]
    [Algebra R K] [Algebra R A] :
    scalarExtensionMapOfAlgHom (R := R) (K := K) (AlgHom.id R A) =
      AlgHom.id K (K ⊗[R] A) := by
  ext x
  · simp [scalarExtensionMapOfAlgHom]

/-- Cancellation on a tensor whose right factor is itself a scalar extension. -/
theorem cancelBaseChange_tmul_baseChange {F L K A : Type u}
    [CommRing F] [CommRing L] [CommRing K] [CommRing A]
    [Algebra F L] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [Algebra F A] (c : K) (x : L ⊗[F] A) :
    Algebra.TensorProduct.cancelBaseChange F L K K A (c ⊗ₜ[L] x) =
      c • Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom F L K) (AlgHom.id F A) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, hx, hy, map_add, smul_add]
  | tmul l a =>
      simp [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_comm]

/-- Cancellation is natural for maps between two base changes from `F` to `L` which
commute with their direct scalar extensions from `L` to `K`. -/
theorem cancelBaseChange_naturality {F L K A B : Type u}
    [CommRing F] [CommRing L] [CommRing K] [CommRing A] [CommRing B]
    [Algebra F L] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [Algebra F A] [Algebra F B]
    (phiL : L ⊗[F] A →ₐ[L] L ⊗[F] B)
    (phiK : K ⊗[F] A →ₐ[K] K ⊗[F] B)
    (hphi :
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F L K) (AlgHom.id F B)).comp
          (phiL.restrictScalars F) =
        (phiK.restrictScalars F).comp
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F L K) (AlgHom.id F A))) :
    (Algebra.TensorProduct.cancelBaseChange F L K K B).toAlgHom.comp
        (scalarExtensionMapOfAlgHom (R := L) (K := K) phiL) =
      phiK.comp (Algebra.TensorProduct.cancelBaseChange F L K K A).toAlgHom := by
  apply DFunLike.ext _ _
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul c x =>
      change Algebra.TensorProduct.cancelBaseChange F L K K B
          (scalarExtensionMapOfAlgHom (R := L) (K := K) phiL (c ⊗ₜ[L] x)) =
        phiK (Algebra.TensorProduct.cancelBaseChange F L K K A (c ⊗ₜ[L] x))
      rw [scalarExtensionMapOfAlgHom_tmul, cancelBaseChange_tmul_baseChange,
        cancelBaseChange_tmul_baseChange]
      rw [show phiK (c • (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom F L K) (AlgHom.id F A)) x) =
          c • phiK ((Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom F L K) (AlgHom.id F A)) x) from
        phiK.toLinearMap.map_smul c _]
      have h := DFunLike.congr_fun hphi x
      change
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F L K) (AlgHom.id F B))
            (phiL x) =
          phiK ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom F L K)
            (AlgHom.id F A)) x) at h
      exact congrArg (fun z => c • z) h

end

end AlgebraicJacobian
