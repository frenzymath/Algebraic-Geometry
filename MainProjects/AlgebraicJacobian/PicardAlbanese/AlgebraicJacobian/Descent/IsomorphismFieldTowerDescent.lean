/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.OpenImmersionFieldTowerDescent

/-!
# Isomorphisms and iterated field extension

An affine spectrum map is an isomorphism if it becomes one after a faithfully flat field
extension.  This file packages that fpqc descent statement in the same tensor-product and
field-tower forms used by the finite-stage Picard atlas.
-/

set_option autoImplicit false

universe u

open CategoryTheory MorphismProperty
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Isomorphisms descend across a faithfully flat pushout square of rings. -/
theorem isIso_specMap_of_fpqc_pushout {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (iA : A →+* A') (phi : A →+* B) (phi' : A' →+* B') (iB : B →+* B')
    (hsq : IsPushout (CommRingCat.ofHom iA) (CommRingCat.ofHom phi)
      (CommRingCat.ofHom phi') (CommRingCat.ofHom iB))
    (hiA : RingHom.FaithfullyFlat iA)
    (hphi' : IsIso (Spec.map (CommRingCat.ofHom phi'))) :
    IsIso (Spec.map (CommRingCat.ofHom phi)) := by
  apply CategoryTheory.MorphismProperty.of_isPullback_of_descendsAlong
    (P := isomorphisms Scheme)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_SpecMap_of_isPushout
      (CommRingCat.ofHom iA) (CommRingCat.ofHom phi)
      (CommRingCat.ofHom phi') (CommRingCat.ofHom iB) hsq)
  · have hff := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom iA)).2 hiA
    exact ⟨⟨hff.2, hff.1⟩, inferInstance⟩
  · exact hphi'

noncomputable section

/-- Isomorphisms of affine spectra descend after extending scalars to a field. -/
theorem isIso_specMap_of_tensorProduct {L K A B : Type u}
    [Field L] [Field K] [Algebra L K]
    [CommRing A] [CommRing B] [Algebra L A] [Algebra L B]
    (phi : A →ₐ[L] B)
    (hK : IsIso (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map phi (AlgHom.id L K)).toRingHom))) :
    IsIso (Spec.map (CommRingCat.ofHom phi.toRingHom)) := by
  letI : Algebra A B := phi.toRingHom.toAlgebra
  haveI : IsScalarTower L A B :=
    IsScalarTower.of_algebraMap_eq fun x => (phi.commutes x).symm
  let psi := Algebra.TensorProduct.map phi (AlgHom.id L K)
  letI : Algebra (A ⊗[L] K) (B ⊗[L] K) := psi.toRingHom.toAlgebra
  have hphi : algebraMap A B = phi.toRingHom := by rfl
  have hpsi : algebraMap (A ⊗[L] K) (B ⊗[L] K) = psi.toRingHom := by rfl
  haveI : IsScalarTower A (A ⊗[L] K) (B ⊗[L] K) :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext a
      change phi a ⊗ₜ[L] 1 = psi (a ⊗ₜ[L] 1)
      simp [psi]
  have hright :
      (algebraMap (A ⊗[L] K) (B ⊗[L] K)).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext k
    change psi (1 ⊗ₜ[L] k) = 1 ⊗ₜ[L] k
    simp [psi]
  letI : Algebra.IsPushout A B (A ⊗[L] K) (B ⊗[L] K) :=
    Algebra.IsPushout.tensorProduct_tensorProduct L K A B hright
  have hsq : IsPushout
      (CommRingCat.ofHom (algebraMap A (A ⊗[L] K)))
      (CommRingCat.ofHom phi.toRingHom)
      (CommRingCat.ofHom psi.toRingHom)
      (CommRingCat.ofHom (algebraMap B (B ⊗[L] K))) := by
    simpa [hphi, hpsi] using
      (CommRingCat.isPushout_of_isPushout A B (A ⊗[L] K) (B ⊗[L] K)).flip
  apply isIso_specMap_of_fpqc_pushout
    (algebraMap A (A ⊗[L] K)) phi.toRingHom psi.toRingHom
      (algebraMap B (B ⊗[L] K)) hsq
  · rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  · simpa [psi] using hK

/-- Conjugating a ring map by ring equivalences preserves whether its affine spectrum is
an isomorphism. -/
theorem isIso_specMap_conjugate {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (eA : A ≃+* A') (eB : B ≃+* B') (phi : A' →+* B')
    (hphi : IsIso (Spec.map (CommRingCat.ofHom phi))) :
    IsIso (Spec.map (CommRingCat.ofHom
      (eB.symm.toRingHom.comp (phi.comp eA.toRingHom)))) := by
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
    Spec.map_comp, Spec.map_comp]
  letI : IsIso (Spec.map (CommRingCat.ofHom phi)) := hphi
  haveI : IsIso (CommRingCat.ofHom eA.toRingHom) := by
    change IsIso eA.toCommRingCatIso.hom
    infer_instance
  haveI : IsIso (CommRingCat.ofHom eB.symm.toRingHom) := by
    change IsIso eB.symm.toCommRingCatIso.hom
    infer_instance
  infer_instance

/-- If the scalar extension of an algebra map is conjugate to an isomorphism, then its
affine spectrum is already an isomorphism. -/
theorem isIso_specMap_of_tensorProduct_conjugate {L K A B A' B' : Type u}
    [Field L] [Field K] [Algebra L K]
    [CommRing A] [CommRing B] [Algebra L A] [Algebra L B]
    [CommRing A'] [CommRing B']
    (phi : A →ₐ[L] B)
    (eA : (A ⊗[L] K) ≃+* A') (eB : (B ⊗[L] K) ≃+* B')
    (psi : A' →+* B')
    (hconj : eB.toRingHom.comp
        (Algebra.TensorProduct.map phi (AlgHom.id L K)).toRingHom =
      psi.comp eA.toRingHom)
    (hpsi : IsIso (Spec.map (CommRingCat.ofHom psi))) :
    IsIso (Spec.map (CommRingCat.ofHom phi.toRingHom)) := by
  apply isIso_specMap_of_tensorProduct (K := K) phi
  let basePhi : (A ⊗[L] K) →+* (B ⊗[L] K) :=
    (Algebra.TensorProduct.map phi (AlgHom.id L K)).toRingHom
  have hbase :
      basePhi = eB.symm.toRingHom.comp (psi.comp eA.toRingHom) := by
    apply DFunLike.ext _ _
    intro x
    apply eB.injective
    change eB (basePhi x) = eB (eB.symm (psi (eA x)))
    rw [eB.apply_symm_apply]
    exact DFunLike.congr_fun hconj x
  change IsIso (Spec.map (CommRingCat.ofHom basePhi))
  rw [hbase, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
    Spec.map_comp, Spec.map_comp]
  letI : IsIso (Spec.map (CommRingCat.ofHom psi)) := hpsi
  haveI : IsIso (CommRingCat.ofHom eA.toRingHom) := by
    change IsIso eA.toCommRingCatIso.hom
    infer_instance
  haveI : IsIso (CommRingCat.ofHom eB.symm.toRingHom) := by
    change IsIso eB.symm.toCommRingCatIso.hom
    infer_instance
  infer_instance

/-- Isomorphisms descend through a tower of fields when the iterated tensor-product square
commutes. -/
theorem isIso_specMap_of_fieldTower_tensorProducts {F L K A B : Type u}
    [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]
    (phi : (L ⊗[F] A) →ₐ[L] (L ⊗[F] B))
    (psi : (K ⊗[F] A) →ₐ[K] (K ⊗[F] B))
    (hcomm :
      (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom F L K) (AlgHom.id F B)).comp
          (phi.restrictScalars F) =
        (psi.restrictScalars F).comp
          (Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom F L K) (AlgHom.id F A)))
    (hpsi : IsIso (Spec.map (CommRingCat.ofHom psi.toRingHom))) :
    IsIso (Spec.map (CommRingCat.ofHom phi.toRingHom)) := by
  apply isIso_specMap_of_tensorProduct_conjugate (K := K) phi
    (tensorProductFieldTowerEquiv (F := F) (L := L) (K := K) (A := A))
    (tensorProductFieldTowerEquiv (F := F) (L := L) (K := K) (A := B))
    psi.toRingHom
  · apply DFunLike.ext _ _
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c =>
        change
          tensorProductFieldTowerEquiv
              ((Algebra.TensorProduct.map phi (AlgHom.id L K)) (x ⊗ₜ[L] c)) =
            psi (tensorProductFieldTowerEquiv (x ⊗ₜ[L] c))
        rw [Algebra.TensorProduct.map_tmul, tensorProductFieldTowerEquiv_tmul,
          tensorProductFieldTowerEquiv_tmul, map_smul]
        exact congrArg (c • ·) (DFunLike.congr_fun hcomm x)
    | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · exact hpsi

end

end AlgebraicGeometry
