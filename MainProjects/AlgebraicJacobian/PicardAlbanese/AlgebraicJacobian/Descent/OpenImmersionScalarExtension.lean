/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.TensorProductFieldTowerMap
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.IsTensorProduct

/-!
# Open immersions under scalar extension

This file identifies scalar extension of an algebra map with the ring pushout along the
scalar-ring map.  On affine spectra this is a pullback square, so properties stable under
base change, in particular open immersions and isomorphisms, ascend to scalar extensions.
-/

set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicJacobian

noncomputable section

/-- The scalar extension of an algebra map is the pushout of that map along the scalar
extension of its source. -/
theorem isPushout_scalarExtensionMapOfAlgHom {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra R B]
    (phi : A →ₐ[R] B) :
    let psi := scalarExtensionMapOfAlgHom (R := R) (K := K) phi
    IsPushout
      (CommRingCat.ofHom phi.toRingHom)
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          A →ₐ[R] K ⊗[R] A).toRingHom)
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          B →ₐ[R] K ⊗[R] B).toRingHom)
      (CommRingCat.ofHom psi.toRingHom) := by
  dsimp only
  let psi := scalarExtensionMapOfAlgHom (R := R) (K := K) phi
  let iA : A →ₐ[R] K ⊗[R] A := Algebra.TensorProduct.includeRight
  let iB : B →ₐ[R] K ⊗[R] B := Algebra.TensorProduct.includeRight
  let aKB : A →ₐ[R] K ⊗[R] B := iB.comp phi
  letI : Algebra A B := phi.toRingHom.toAlgebra
  letI : Algebra A (K ⊗[R] A) := iA.toRingHom.toAlgebra
  letI : Algebra B (K ⊗[R] B) := iB.toRingHom.toAlgebra
  letI : Algebra A (K ⊗[R] B) := aKB.toRingHom.toAlgebra
  letI : Algebra (K ⊗[R] A) (K ⊗[R] B) := psi.toRingHom.toAlgebra
  haveI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun r => (phi.commutes r).symm
  haveI : IsScalarTower R A (K ⊗[R] A) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (algebraMap R K r) ⊗ₜ[R] (1 : A) =
        (1 : K) ⊗ₜ[R] algebraMap R A r
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
  haveI : IsScalarTower R B (K ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (algebraMap R K r) ⊗ₜ[R] (1 : B) =
        (1 : K) ⊗ₜ[R] algebraMap R B r
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
  haveI : IsScalarTower R A (K ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (algebraMap R K r) ⊗ₜ[R] (1 : B) =
        (1 : K) ⊗ₜ[R] phi (algebraMap R A r)
      rw [phi.commutes]
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
  haveI : IsScalarTower A B (K ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A (K ⊗[R] A) (K ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change aKB a = psi (iA a)
      simp [aKB, iA, iB, psi, scalarExtensionMapOfAlgHom]
  haveI : IsScalarTower R (K ⊗[R] A) (K ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (algebraMap R K r) ⊗ₜ[R] (1 : B) =
        psi ((algebraMap R K r) ⊗ₜ[R] (1 : A))
      simp [psi, scalarExtensionMapOfAlgHom]
  haveI : IsScalarTower K (K ⊗[R] A) (K ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun k => (psi.commutes k).symm
  letI : Algebra.IsPushout R A K (K ⊗[R] A) :=
    TensorProduct.isPushout'
  letI : Algebra.IsPushout A B (K ⊗[R] A) (K ⊗[R] B) :=
    (Algebra.IsPushout.comp_iff R A K (K ⊗[R] A)).mp
      TensorProduct.isPushout'
  have hphi : algebraMap A B = phi.toRingHom := rfl
  have hiA : algebraMap A (K ⊗[R] A) = iA.toRingHom := rfl
  have hiB : algebraMap B (K ⊗[R] B) = iB.toRingHom := rfl
  have hpsi : algebraMap (K ⊗[R] A) (K ⊗[R] B) = psi.toRingHom := rfl
  rw [← hphi, ← hiA, ← hiB, ← hpsi]
  exact CommRingCat.isPushout_of_isPushout A B (K ⊗[R] A) (K ⊗[R] B)

end

end AlgebraicJacobian

namespace AlgebraicGeometry

noncomputable section

/-- The affine-spectrum map of a scalar-extended algebra map is the base change of the
original affine-spectrum map. -/
lemma isPullback_specMap_scalarExtensionMapOfAlgHom {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra R B]
    (phi : A →ₐ[R] B) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          B →ₐ[R] K ⊗[R] B).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := R) (K := K) phi).toRingHom))
      (Spec.map (CommRingCat.ofHom phi.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          A →ₐ[R] K ⊗[R] A).toRingHom)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (AlgebraicJacobian.isPushout_scalarExtensionMapOfAlgHom
      (R := R) (K := K) phi)

/-- Open immersions of affine spectra remain open immersions after arbitrary scalar
extension. -/
theorem isOpenImmersion_scalarExtensionMapOfAlgHom {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra R B]
    (phi : A →ₐ[R] B)
    (hphi : IsOpenImmersion (Spec.map
      (CommRingCat.ofHom phi.toRingHom))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := R) (K := K) phi).toRingHom)) :=
  MorphismProperty.of_isPullback
    (P := @IsOpenImmersion)
    (isPullback_specMap_scalarExtensionMapOfAlgHom
      (R := R) (K := K) phi)
    hphi

/-- Isomorphisms of affine spectra remain isomorphisms after arbitrary scalar extension. -/
theorem isIso_specMap_scalarExtensionMapOfAlgHom {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra R B]
    (phi : A →ₐ[R] B)
    (hphi : IsIso (Spec.map
      (CommRingCat.ofHom phi.toRingHom))) :
    IsIso (Spec.map (CommRingCat.ofHom
      (AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := R) (K := K) phi).toRingHom)) :=
  MorphismProperty.of_isPullback
    (P := MorphismProperty.isomorphisms Scheme)
    (isPullback_specMap_scalarExtensionMapOfAlgHom
      (R := R) (K := K) phi)
    hphi

end

end AlgebraicGeometry
