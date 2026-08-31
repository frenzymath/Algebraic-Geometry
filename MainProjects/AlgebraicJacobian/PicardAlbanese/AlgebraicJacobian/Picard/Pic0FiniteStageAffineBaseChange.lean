/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageChartBaseChange

/-!
# Naturality of affine scalar extension

For an algebra map A -> B, base change carries Spec B -> Spec A to the
contravariant Spec of the scalar-extended algebra map.  The tensor factors are
ordered with the extension ring on the left, matching the finite-stage Picard
ring comparisons.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

namespace Pic0FiniteStageGluePackage

variable (R K A B : Type u)
variable [CommRing R] [CommRing K] [CommRing A] [CommRing B]
variable [Algebra R K] [Algebra R A] [Algebra R B]

/-- The affine base-change isomorphism with the extension ring as the left
tensor factor. -/
noncomputable def affineBaseChangeIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅
      Spec (.of (K ⊗[R] A)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso R K A

@[reassoc (attr := simp)]
theorem affineBaseChangeIso_inv_fst :
    (affineBaseChangeIso R K A).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          A →ₐ[R] K ⊗[R] A).toRingHom) := by
  simp [affineBaseChangeIso]

@[reassoc (attr := simp)]
theorem affineBaseChangeIso_inv_snd :
    (affineBaseChangeIso R K A).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          K →+* K ⊗[R] A)) := by
  simp [affineBaseChangeIso]

/-- Base change of an affine morphism over Spec R. -/
noncomputable def affineBaseChangeMap (phi : A →ₐ[R] B) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  pullback.map _ _ _ _
    (Spec.map (CommRingCat.ofHom phi.toRingHom)) (𝟙 _) (𝟙 _)
    (by
      rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact phi.comp_algebraMap.symm)
    (by simp)

@[reassoc (attr := simp)]
theorem affineBaseChangeMap_fst (phi : A →ₐ[R] B) :
    affineBaseChangeMap R K A B phi ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom phi.toRingHom) := by
  unfold affineBaseChangeMap
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem affineBaseChangeMap_snd (phi : A →ₐ[R] B) :
    affineBaseChangeMap R K A B phi ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  unfold affineBaseChangeMap
  rw [pullback.lift_snd]
  simp

set_option maxHeartbeats 12800000 in
-- Both pullback projections expand tensor-product universal maps.
/-- The affine base-change isomorphisms intertwine a base-changed morphism with
the Spec of its scalar extension. -/
theorem affineBaseChangeIso_naturality (phi : A →ₐ[R] B) :
    affineBaseChangeMap R K A B phi ≫ (affineBaseChangeIso R K A).hom =
      (affineBaseChangeIso R K B).hom ≫
        Spec.map (CommRingCat.ofHom
          (AlgebraicJacobian.scalarExtensionMapOfAlgHom
            (R := R) (K := K) phi).toRingHom) := by
  rw [← cancel_epi (affineBaseChangeIso R K B).inv]
  simp only [Iso.inv_hom_id_assoc]
  rw [← cancel_mono (affineBaseChangeIso R K A).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc, affineBaseChangeMap_fst]
    simp only [Category.assoc]
    rw [affineBaseChangeIso_inv_fst_assoc (R := R) (K := K) (A := B)]
    rw [affineBaseChangeIso_inv_fst (R := R) (K := K) (A := A)]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  · rw [Category.assoc, affineBaseChangeMap_snd]
    simp only [Category.assoc]
    rw [affineBaseChangeIso_inv_snd (R := R) (K := K) (A := B)]
    rw [affineBaseChangeIso_inv_snd (R := R) (K := K) (A := A)]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [AlgebraicJacobian.scalarExtensionMapOfAlgHom]

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
