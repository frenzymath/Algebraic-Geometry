/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GaloisDescent.PicEtGaloisCover
import AlgebraicJacobian.Picard.PicEtDescentExistence
import Mathlib.AlgebraicGeometry.EffectiveEpi

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicJacobian.GaloisDescent

open scoped TensorProduct
open AlgebraicGeometry.Scheme.PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  [FiniteDimensional k k'] [IsGalois k k']

noncomputable def fieldSelfSection (γ : k' ≃ₐ[k] k') :
    Spec (CommRingCat.of k') ⟶
      pullback (specMapAlgebra k k') (specMapAlgebra k k') :=
  Limits.Sigma.ι (fun _ : k' ≃ₐ[k] k' => Spec (CommRingCat.of k')) γ ≫
    (selfTensorSpecCoproduct k k').hom ≫
    (AlgebraicGeometry.pullbackSpecIso k k' k').inv

@[simp, reassoc]
theorem fieldSelfSection_fst (γ : k' ≃ₐ[k] k') :
    fieldSelfSection (k := k) (k' := k') γ ≫
      pullback.fst (specMapAlgebra k k') (specMapAlgebra k k') = 𝟙 _ := by
  unfold fieldSelfSection
  rw [Category.assoc, Category.assoc,
    AlgebraicGeometry.pullbackSpecIso_inv_fst]
  unfold selfTensorSpecCoproduct
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [AlgebraicGeometry.ι_sigmaSpec_assoc]
  simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
    Quiver.Hom.unop_op]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact AlgebraicGeometry.Scheme.PicScheme.galoisSelfTensor_includeLeft k' γ x

@[simp, reassoc]
theorem fieldSelfSection_snd (γ : k' ≃ₐ[k] k') :
    fieldSelfSection (k := k) (k' := k') γ ≫
      pullback.snd (specMapAlgebra k k') (specMapAlgebra k k') = specGal γ := by
  unfold fieldSelfSection
  rw [Category.assoc, Category.assoc,
    AlgebraicGeometry.pullbackSpecIso_inv_snd]
  unfold selfTensorSpecCoproduct
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [AlgebraicGeometry.ι_sigmaSpec_assoc]
  simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
    Quiver.Hom.unop_op]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact AlgebraicGeometry.Scheme.PicScheme.galoisSelfTensor_includeRight k' γ x

instance fieldSelfSection_isOpenImmersion (γ : k' ≃ₐ[k] k') :
    IsOpenImmersion (fieldSelfSection (k := k) (k' := k') γ) := by
  haveI : IsOpenImmersion
      (Limits.Sigma.ι (fun _ : k' ≃ₐ[k] k' => Spec (CommRingCat.of k')) γ) :=
    (AlgebraicGeometry.sigmaOpenCover
      (fun _ : k' ≃ₐ[k] k' => Spec (CommRingCat.of k'))).map_prop γ
  unfold fieldSelfSection
  infer_instance

theorem fieldSelfSection_jointlySurjective :
    ∀ x : (Limits.pullback (specMapAlgebra k k')
      (specMapAlgebra k k') : Scheme.{u}),
      ∃ (γ : k' ≃ₐ[k] k') (y : Spec (CommRingCat.of k')),
        fieldSelfSection (k := k) (k' := k') γ y = x := by
  intro x
  let e := selfTensorSpecCoproduct k k' ≪≫
    (AlgebraicGeometry.pullbackSpecIso k k' k').symm
  obtain ⟨⟨γ, y⟩, hy⟩ := (AlgebraicGeometry.sigmaMk
    (fun _ : k' ≃ₐ[k] k' => Spec (CommRingCat.of k'))).surjective (e.inv x)
  rw [AlgebraicGeometry.sigmaMk_mk] at hy
  refine ⟨γ, y, ?_⟩
  change e.hom ((Limits.Sigma.ι
    (fun _ : k' ≃ₐ[k] k' => Spec (CommRingCat.of k')) γ) y) = x
  rw [hy]
  exact (Scheme.homeoOfIso e).apply_symm_apply x

noncomputable def fieldSelfOpenCover :
    Scheme.OpenCover (pullback (specMapAlgebra k k') (specMapAlgebra k k')) :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (k' ≃ₐ[k] k')
    (fun _ => Spec (CommRingCat.of k'))
    (fun γ => fieldSelfSection (k := k) (k' := k') γ)
    (fieldSelfSection_jointlySurjective (k := k) (k' := k'))
    (fun γ => fieldSelfSection_isOpenImmersion (k := k) (k' := k') γ)

@[simp]
theorem fieldSelfOpenCover_f (γ : k' ≃ₐ[k] k') :
    (fieldSelfOpenCover (k := k) (k' := k')).f γ =
      fieldSelfSection (k := k) (k' := k') γ := rfl

noncomputable def relativeFieldSelfSection
    (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    pullback T.hom (specMapAlgebra k k') ⟶
      pullback (pullback.snd T.hom (specMapAlgebra k k'))
        (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) :=
  pullback.lift (𝟙 _)
    (pullback.snd T.hom (specMapAlgebra k k') ≫
      fieldSelfSection (k := k) (k' := k') γ)
    (by simp)

noncomputable def relativeFieldSelfOpenCover
    (T : Over (Spec (CommRingCat.of k))) :
    Scheme.OpenCover
      (pullback (pullback.snd T.hom (specMapAlgebra k k'))
        (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k'))) :=
  Scheme.Pullback.openCoverOfRight (fieldSelfOpenCover (k := k) (k' := k'))
    (pullback.snd T.hom (specMapAlgebra k k'))
    (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k'))

set_option backward.isDefEq.respectTransparency false in
theorem relativeFieldSelfOpenCover_factors
    (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    (relativeFieldSelfOpenCover (k := k) (k' := k') T).f γ =
      pullback.fst (pullback.snd T.hom (specMapAlgebra k k'))
          (fieldSelfSection (k := k) (k' := k') γ ≫
            pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) ≫
      relativeFieldSelfSection (k := k) (k' := k') T γ := by
  change (Scheme.Pullback.openCoverOfRight
    (fieldSelfOpenCover (k := k) (k' := k'))
    (pullback.snd T.hom (specMapAlgebra k k'))
    (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k'))).f γ = _
  rw [Scheme.Pullback.openCoverOfRight_f]
  simp only [fieldSelfOpenCover_f]
  apply pullback.hom_ext
  · simp only [pullback.map, relativeFieldSelfSection, pullback.lift_fst]
    rw [Category.comp_id, Category.assoc, pullback.lift_fst]
    simp
  · simp only [pullback.map, relativeFieldSelfSection, pullback.lift_snd]
    rw [Category.assoc, pullback.lift_snd]
    simp only [← Category.assoc]
    rw [pullback.condition]
    simp

theorem relativeFieldSelfSection_jointlySurjective
    (T : Over (Spec (CommRingCat.of k))) :
    ∀ x : (Limits.pullback (pullback.snd T.hom (specMapAlgebra k k'))
        (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) : Scheme.{u}),
      ∃ (γ : k' ≃ₐ[k] k')
        (y : (Limits.pullback T.hom (specMapAlgebra k k') : Scheme.{u})),
        relativeFieldSelfSection (k := k) (k' := k') T γ y = x := by
  intro x
  obtain ⟨γ, z, hz⟩ :=
    (relativeFieldSelfOpenCover (k := k) (k' := k') T).exists_eq x
  refine ⟨γ,
    pullback.fst (pullback.snd T.hom (specMapAlgebra k k'))
      (fieldSelfSection (k := k) (k' := k') γ ≫
        pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← relativeFieldSelfOpenCover_factors]
  exact hz

omit [FiniteDimensional k k'] [IsGalois k k'] in
theorem forget_coverMap_eq_pullbackFst
    (T : Over (Spec (CommRingCat.of k))) :
    (Over.forget (Spec (CommRingCat.of k))).map
        (coverMap (k := k) (k' := k') T) =
      pullback.fst T.hom (specMapAlgebra k k') := rfl

noncomputable def coverSelfRelativeFieldIsoUnderlying
    (T : Over (Spec (CommRingCat.of k))) :
    (Over.forget (Spec (CommRingCat.of k))).obj
        (pullback (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)) ≅
      pullback (pullback.snd T.hom (specMapAlgebra k k'))
        (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) :=
  (PreservesPullback.iso (Over.forget (Spec (CommRingCat.of k)))
      (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T)) ≪≫
    pullback.congrHom (forget_coverMap_eq_pullbackFst (k := k) (k' := k') T)
      (forget_coverMap_eq_pullbackFst (k := k) (k' := k') T) ≪≫
    pullbackRightPullbackFstIso T.hom (specMapAlgebra k k')
      (pullback.fst T.hom (specMapAlgebra k k')) ≪≫
    ((pullbackRightPullbackFstIso (specMapAlgebra k k')
        (specMapAlgebra k k')
        (pullback.snd T.hom (specMapAlgebra k k'))) ≪≫
      pullback.congrHom pullback.condition.symm rfl).symm

noncomputable def coverSelfRelativeFieldIso
    (T : Over (Spec (CommRingCat.of k))) :
    (pullback (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T)).left ≅
      pullback (pullback.snd T.hom (specMapAlgebra k k'))
        (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) :=
  coverSelfRelativeFieldIsoUnderlying (k := k) (k' := k') T

omit [FiniteDimensional k k'] [IsGalois k k'] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem coverSelfRelativeFieldIso_hom_fst
    (T : Over (Spec (CommRingCat.of k))) :
    (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom ≫
        pullback.fst (pullback.snd T.hom (specMapAlgebra k k'))
          (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) =
      (pullback.fst (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left := by
  change (coverSelfRelativeFieldIsoUnderlying (k := k) (k' := k') T).hom ≫ _ =
    (Over.forget (Spec (CommRingCat.of k))).map
      (pullback.fst (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T))
  simp only [coverSelfRelativeFieldIsoUnderlying,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    pullbackRightPullbackFstIso_inv_fst,
    pullback.congrHom_inv, pullback.congrHom_hom,
    pullback.lift_fst, Category.comp_id,
    pullbackRightPullbackFstIso_hom_fst,
    PreservesPullback.iso_hom_fst]

omit [FiniteDimensional k k'] [IsGalois k k'] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem coverSelfRelativeFieldIso_hom_snd_fst
    (T : Over (Spec (CommRingCat.of k))) :
    (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom ≫
          pullback.snd (pullback.snd T.hom (specMapAlgebra k k'))
            (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) ≫
          pullback.fst (specMapAlgebra k k') (specMapAlgebra k k') =
      (pullback.fst (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)).left ≫
        pullback.snd T.hom (specMapAlgebra k k') := by
  change (coverSelfRelativeFieldIsoUnderlying (k := k) (k' := k') T).hom ≫ _ ≫ _ =
    (Over.forget (Spec (CommRingCat.of k))).map
        (pullback.fst (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)) ≫ _
  simp only [coverSelfRelativeFieldIsoUnderlying,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_fst,
    pullback.congrHom_inv, pullback.congrHom_hom,
    pullback.lift_fst_assoc, Category.comp_id,
    pullbackRightPullbackFstIso_hom_fst_assoc,
    PreservesPullback.iso_hom_fst_assoc]

omit [FiniteDimensional k k'] [IsGalois k k'] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem coverSelfRelativeFieldIso_hom_snd_snd
    (T : Over (Spec (CommRingCat.of k))) :
    (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom ≫
          pullback.snd (pullback.snd T.hom (specMapAlgebra k k'))
            (pullback.fst (specMapAlgebra k k') (specMapAlgebra k k')) ≫
          pullback.snd (specMapAlgebra k k') (specMapAlgebra k k') =
      (pullback.snd (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)).left ≫
        pullback.snd T.hom (specMapAlgebra k k') := by
  change (coverSelfRelativeFieldIsoUnderlying (k := k) (k' := k') T).hom ≫ _ ≫ _ =
    (Over.forget (Spec (CommRingCat.of k))).map
        (pullback.snd (coverMap (k := k) (k' := k') T)
          (coverMap (k := k) (k' := k') T)) ≫ _
  simp only [coverSelfRelativeFieldIsoUnderlying,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_snd,
    pullback.congrHom_inv, pullback.congrHom_hom,
    pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
    pullbackRightPullbackFstIso_hom_snd,
    PreservesPullback.iso_hom_snd_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem coverSelfSection_comp_coverSelfRelativeFieldIso
    (T : Over (Spec (CommRingCat.of k))) (γ : k' ≃ₐ[k] k') :
    (coverSelfSection (k := k) (k' := k') T γ).left ≫
        (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom =
      relativeFieldSelfSection (k := k) (k' := k') T γ := by
  have hfst := congrArg Over.Hom.left
    (coverSelfSection_fst (k := k) (k' := k') T γ)
  have hsnd := congrArg Over.Hom.left
    (coverSelfSection_snd (k := k) (k' := k') T γ)
  simp only [Over.comp_left, Over.id_left] at hfst hsnd
  apply pullback.hom_ext
  · simp only [relativeFieldSelfSection, pullback.lift_fst]
    rw [Category.assoc, coverSelfRelativeFieldIso_hom_fst, hfst]
    change 𝟙 ((restrictTest k k').obj (baseTest (k' := k') T)).left =
      𝟙 ((restrictTest k k').obj (baseTest (k' := k') T)).left
    rfl
  · apply pullback.hom_ext
    · simp only [relativeFieldSelfSection, pullback.lift_snd,
        Category.assoc, fieldSelfSection_fst, Category.comp_id]
      have hproj := congrArg
        (fun z => (coverSelfSection (k := k) (k' := k') T γ).left ≫ z)
        (coverSelfRelativeFieldIso_hom_snd_fst (k := k) (k' := k') T)
      calc
        _ = ((coverSelfSection (k := k) (k' := k') T γ).left ≫
              (pullback.fst (coverMap (k := k) (k' := k') T)
                (coverMap (k := k) (k' := k') T)).left) ≫
            pullback.snd T.hom (specMapAlgebra k k') := by
          simpa only [Category.assoc] using hproj
        _ = 𝟙 ((restrictTest k k').obj (baseTest (k' := k') T)).left ≫
            pullback.snd T.hom (specMapAlgebra k k') :=
          congrArg (fun z => z ≫ pullback.snd T.hom (specMapAlgebra k k')) hfst
        _ = _ := Category.id_comp _
    · simp only [relativeFieldSelfSection, pullback.lift_snd,
        Category.assoc, fieldSelfSection_snd]
      have hproj := congrArg
        (fun z => (coverSelfSection (k := k) (k' := k') T γ).left ≫ z)
        (coverSelfRelativeFieldIso_hom_snd_snd (k := k) (k' := k') T)
      calc
        _ = ((coverSelfSection (k := k) (k' := k') T γ).left ≫
              (pullback.snd (coverMap (k := k) (k' := k') T)
                (coverMap (k := k) (k' := k') T)).left) ≫
            pullback.snd T.hom (specMapAlgebra k k') := by
          simpa only [Category.assoc] using hproj
        _ = (twistTest T γ).left ≫
            pullback.snd T.hom (specMapAlgebra k k') :=
          congrArg (fun z => z ≫ pullback.snd T.hom (specMapAlgebra k k')) hsnd
        _ = _ := by simp [twistTest, twistLeft]

theorem coverSelfSection_jointlySurjective
    (T : Over (Spec (CommRingCat.of k))) :
    ∀ x : (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left,
      ∃ (γ : k' ≃ₐ[k] k')
        (y : ((restrictTest k k').obj (baseTest (k' := k') T)).left),
        (coverSelfSection (k := k) (k' := k') T γ).left y = x := by
  intro x
  obtain ⟨γ, y, hy⟩ := relativeFieldSelfSection_jointlySurjective
    (k := k) (k' := k') T
    ((coverSelfRelativeFieldIso (k := k) (k' := k') T).hom x)
  change ((restrictTest k k').obj (baseTest (k' := k') T)).left at y
  refine ⟨γ, y, ?_⟩
  apply (Scheme.homeoOfIso
    (coverSelfRelativeFieldIso (k := k) (k' := k') T)).injective
  have hp := congrArg
    (fun m : ((restrictTest k k').obj (baseTest (k' := k') T)).left ⟶ _ => m y)
    (coverSelfSection_comp_coverSelfRelativeFieldIso
      (k := k) (k' := k') T γ)
  rw [Scheme.Hom.comp_apply] at hp
  change (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom
      ((coverSelfSection (k := k) (k' := k') T γ).left y) =
    (coverSelfRelativeFieldIso (k := k) (k' := k') T).hom x
  exact hp.trans hy

noncomputable def coverSelfSectionOpenCover
    (T : Over (Spec (CommRingCat.of k))) :
    Scheme.OpenCover
      (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)).left :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (k' ≃ₐ[k] k')
    (fun _ => ((restrictTest k k').obj (baseTest (k' := k') T)).left)
    (fun γ => (coverSelfSection (k := k) (k' := k') T γ).left)
    (coverSelfSection_jointlySurjective (k := k) (k' := k') T)
    (fun γ => isOpenImmersion_coverSelfSection_left T γ)

theorem coverSelfSection_hom_ext
    (T : Over (Spec (CommRingCat.of k))) {Z : Scheme.{u}}
    {a b : (pullback (coverMap (k := k) (k' := k') T)
      (coverMap (k := k) (k' := k') T)).left ⟶ Z}
    (h : ∀ γ : k' ≃ₐ[k] k',
      (coverSelfSection (k := k) (k' := k') T γ).left ≫ a =
        (coverSelfSection (k := k) (k' := k') T γ).left ≫ b) :
    a = b :=
  Scheme.Cover.hom_ext (coverSelfSectionOpenCover (k := k) (k' := k') T) a b h

theorem coverSelfSection_generate_mem_etaleTopology
    (T : Over (Spec (CommRingCat.of k))) :
    Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      AlgebraicGeometry.Scheme.etaleTopologyOver k
        (pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)) :=
  hcov_of_jointlySurjective T
    (coverSelfSection_jointlySurjective (k := k) (k' := k') T)

end AlgebraicJacobian.GaloisDescent
