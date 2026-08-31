/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.IsTensorProduct

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- Open immersions descend across a faithfully flat pushout square of rings. -/
theorem isOpenImmersion_of_fpqc_pushout {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (iA : A →+* A') (phi : A →+* B) (phi' : A' →+* B') (iB : B →+* B')
    (hsq : IsPushout (CommRingCat.ofHom iA) (CommRingCat.ofHom phi)
      (CommRingCat.ofHom phi') (CommRingCat.ofHom iB))
    (hiA : RingHom.FaithfullyFlat iA)
    (hphi' : IsOpenImmersion (Spec.map (CommRingCat.ofHom phi'))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom phi)) := by
  apply CategoryTheory.MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_SpecMap_of_isPushout
      (CommRingCat.ofHom iA) (CommRingCat.ofHom phi)
      (CommRingCat.ofHom phi') (CommRingCat.ofHom iB) hsq)
  · have hff := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom iA)).2 hiA
    exact ⟨⟨hff.2, hff.1⟩, inferInstance⟩
  · exact hphi'

noncomputable section

/-- Open immersions of affine spectra descend after extending scalars to a field. -/
theorem isOpenImmersion_of_tensorProduct {L K A B : Type u}
    [Field L] [Field K] [Algebra L K]
    [CommRing A] [CommRing B] [Algebra L A] [Algebra L B]
    (phi : A →ₐ[L] B)
    (hK : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map phi (AlgHom.id L K)).toRingHom))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom phi.toRingHom)) := by
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
  apply isOpenImmersion_of_fpqc_pushout
    (algebraMap A (A ⊗[L] K)) phi.toRingHom psi.toRingHom
      (algebraMap B (B ⊗[L] K)) hsq
  · rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  · simpa [psi] using hK

end
end AlgebraicGeometry
