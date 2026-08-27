/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionComplex
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegAux

/-!
# Comparison of the two section Cech augmentations

The evaluated scheme-level Cech augmentation agrees with the direct product of
restriction maps defined in `CechSectionComplex`.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

private lemma eqToHom_eq_restriction (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab.{u})
    {A B : TopologicalSpace.Opens X} (hAB : A = B) (hle : B ≤ A)
    (h : P.obj (Opposite.op A) = P.obj (Opposite.op B)) :
    eqToHom h = P.map (homOfLE hle).op := by
  subst hAB
  refine Eq.trans (eqToHom_refl _ h) ?_
  refine Eq.trans (P.map_id (Opposite.op A)).symm ?_
  exact congrArg P.map (congrArg Quiver.Hom.op (Subsingleton.elim (𝟙 A) (homOfLE hle)))

private lemma rawPushPullMap_unit {Z₁ Z₂ : Scheme.{u}} (a : Z₂ ⟶ Z₁)
    (p₁ : Z₁ ⟶ X) (p₂ : Z₂ ⟶ X) (w : a ≫ p₁ = p₂) (F : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction p₁).unit.app F ≫
        rawPushPullMap a p₁ p₂ w F =
      (Scheme.Modules.pullbackPushforwardAdjunction p₂).unit.app F := by
  subst w
  rw [rawPushPullMap_self, pushPull_unit_comp a p₁ F]
  refine congrArg (fun m =>
    (Scheme.Modules.pullbackPushforwardAdjunction p₁).unit.app F ≫ m) ?_
  refine Eq.trans ((Scheme.Modules.pushforward p₁).map_comp _ _) ?_
  refine congrArg (fun m => (Scheme.Modules.pushforward p₁).map
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
      ((Scheme.Modules.pullback p₁).obj F)) ≫ m) ?_
  apply Scheme.Modules.hom_ext
  intro U
  rfl

private lemma cechNervePointIso_inv_eq_unit (𝒰 : X.OpenCover) (F : X.Modules) :
    (cechNervePointIso 𝒰 F).inv =
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F := by
  have star := unit_conjugateEquiv (Adjunction.id (C := X.Modules))
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)) (Scheme.Modules.pullbackId X).hom F
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at star
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj] at star
  have star2 : (Scheme.Modules.pushforwardId X).inv.app F =
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F ≫
        (Scheme.Modules.pushforward (𝟙 X)).map ((Scheme.Modules.pullbackId X).hom.app F) :=
    (Category.id_comp _).symm.trans star
  have hnat := (Scheme.Modules.pushforwardId X).inv.naturality
    ((Scheme.Modules.pullbackId X).inv.app F)
  simp only [Functor.id_obj, Functor.id_map] at hnat
  refine Eq.trans (hnat : (cechNervePointIso 𝒰 F).inv = _) ?_
  refine Eq.trans (congrArg (fun m => m ≫ (Scheme.Modules.pushforward (𝟙 X)).map
    ((Scheme.Modules.pullbackId X).inv.app F)) star2) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m =>
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F ≫ m)
    (((Scheme.Modules.pushforward (𝟙 X)).map_comp _ _).symm)) ?_
  refine Eq.trans (congrArg (fun m =>
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F ≫
      (Scheme.Modules.pushforward (𝟙 X)).map m) (Iso.hom_inv_id_app _ _)) ?_
  exact (congrArg (fun m =>
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app F ≫ m)
      ((Scheme.Modules.pushforward (𝟙 X)).map_id _)).trans (Category.comp_id _)

private lemma cechAugmentation_pushPullMap (𝒰 : X.OpenCover) (F : X.Modules)
    {Y : Over X}
    (g : Y ⟶ (coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk 0))) :
    cechAugmentation 𝒰 F ≫ pushPullMap F g =
      (Scheme.Modules.pullbackPushforwardAdjunction Y.hom).unit.app F := by
  have happ : (CechNerve 𝒰 F).hom.app (SimplexCategory.mk 0) =
      pushPullMap F
        ((coverCechNerveOverAug 𝒰).hom.app (Opposite.op (SimplexCategory.mk 0))) :=
    Eq.trans rfl (Category.id_comp _)
  rw [cechAugmentation, Category.assoc]
  refine Eq.trans (congrArg (fun m => (cechNervePointIso 𝒰 F).inv ≫ m)
    (Eq.trans (congrArg (fun m => m ≫ pushPullMap F g) happ)
      ((pushPullMap_comp F _ g).symm))) ?_
  rw [cechNervePointIso_inv_eq_unit, pushPullMap_eq_raw]
  exact rawPushPullMap_unit _ _ _ _ F

private lemma unit_pushPull_leg_sections (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) {p : ℕ} (σ : Fin (p + 1) → 𝒰.I₀)
    (V : TopologicalSpace.Opens X) :
    (Scheme.Modules.toPresheaf X ⋙
        (evaluation (TopologicalSpace.Opens X)ᵒᵖ (Ab.{u})).obj
          (Opposite.op V)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).unit.app F) ≫
      (pushPull_leg_sections 𝒰 F σ V).hom =
    ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
      (homOfLE (inf_le_right : coverInterOpen 𝒰 σ ⊓ V ≤ V)).op := by
  have hW : Scheme.Opens.ι (coverInterOpen 𝒰 σ) ''ᵁ
        (Scheme.Opens.ι (coverInterOpen 𝒰 σ) ⁻¹ᵁ V) = coverInterOpen 𝒰 σ ⊓ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hdec : (pushPull_leg_sections 𝒰 F σ V).hom =
      (Scheme.Modules.toPresheaf X ⋙
          (evaluation (TopologicalSpace.Opens X)ᵒᵖ (Ab.{u})).obj
            (Opposite.op V)).map
        ((Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).map
          ((Scheme.Modules.restrictFunctorIsoPullback
            (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).inv.app F)) ≫
      eqToHom (congrArg
        (fun W => ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op W)) hW) := rfl
  have hLAU : (Scheme.Modules.pullbackPushforwardAdjunction
        (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).unit.app F ≫
      (Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).map
        ((Scheme.Modules.restrictFunctorIsoPullback
          (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).inv.app F) =
      (Scheme.Modules.restrictAdjunction
        (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).unit.app F := by
    have h0 : (Scheme.Modules.restrictAdjunction
          (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).unit.app F ≫
        (Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).map
          ((Scheme.Modules.restrictFunctorIsoPullback
            (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).hom.app F) =
        (Scheme.Modules.pullbackPushforwardAdjunction
          (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).unit.app F :=
      Adjunction.unit_leftAdjointUniq_hom_app _ _ F
    refine Eq.trans (congrArg (fun m => m ≫
      (Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).map
        ((Scheme.Modules.restrictFunctorIsoPullback
          (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).inv.app F)) h0.symm) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun m => (Scheme.Modules.restrictAdjunction
        (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).unit.app F ≫ m)
      (((Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).map_comp
        _ _).symm)) ?_
    refine Eq.trans (congrArg (fun m => (Scheme.Modules.restrictAdjunction
        (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).unit.app F ≫
        (Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).map m)
      (Iso.hom_inv_id_app _ _)) ?_
    exact (congrArg (fun m => (Scheme.Modules.restrictAdjunction
        (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).unit.app F ≫ m)
      ((Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).map_id _)).trans
      (Category.comp_id _)
  have hunit : (Scheme.Modules.toPresheaf X ⋙
        (evaluation (TopologicalSpace.Opens X)ᵒᵖ (Ab.{u})).obj
          (Opposite.op V)).map
      ((Scheme.Modules.restrictAdjunction
        (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).unit.app F) =
    ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
      (homOfLE ((Scheme.Opens.ι (coverInterOpen 𝒰 σ)).image_preimage_le V)).op := rfl
  refine Eq.trans (congrArg (fun m => (Scheme.Modules.toPresheaf X ⋙
      (evaluation (TopologicalSpace.Opens X)ᵒᵖ (Ab.{u})).obj
        (Opposite.op V)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).unit.app F) ≫ m) hdec) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m => m ≫ eqToHom (congrArg
      (fun W => ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
        (Opposite.op W)) hW))
    (Eq.trans (((Scheme.Modules.toPresheaf X ⋙
        (evaluation (TopologicalSpace.Opens X)ᵒᵖ (Ab.{u})).obj
          (Opposite.op V)).map_comp _ _).symm)
      (Eq.trans (congrArg (Scheme.Modules.toPresheaf X ⋙
        (evaluation (TopologicalSpace.Opens X)ᵒᵖ (Ab.{u})).obj
          (Opposite.op V)).map hLAU) hunit))) ?_
  refine Eq.trans (congrArg (fun m =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
        (homOfLE ((Scheme.Opens.ι (coverInterOpen 𝒰 σ)).image_preimage_le V)).op ≫ m)
    (eqToHom_eq_restriction (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf)
      hW (le_of_eq hW.symm) _)) ?_
  refine Eq.trans
    ((((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map_comp _ _).symm) ?_
  refine Eq.trans (congrArg ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
    (op_comp (f := homOfLE (le_of_eq hW.symm))
      (g := homOfLE ((Scheme.Opens.ι (coverInterOpen 𝒰 σ)).image_preimage_le V))).symm) ?_
  exact congrArg (fun m => ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
    (Quiver.Hom.op m)) (Subsingleton.elim _ _)

private lemma mappedSectionCechAugV_π (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (V : TopologicalSpace.Opens X) (σ : Fin 1 → 𝒰.I₀) :
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat).obj
            (Opposite.op V)).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (cechAugmentation 𝒰 F)) ≫
      (coreIso_objIso 𝒰 F 0 V).hom) ≫
        Pi.π (fun τ : Fin 1 → 𝒰.I₀ =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
            (Opposite.op (⨅ k, (coverOpen 𝒰 (τ k) ⊓ V)))) σ =
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
        (homOfLE (sectionCechV_intersection_le 𝒰 V σ)).op := by
  have hproj := coreIso_objIso_π 𝒰 F 0 V σ
  have hGE := GVΨ_map_eq V (cechAugmentation 𝒰 F)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m => _ ≫ m) hproj) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m => m ≫ ((pushPull_leg_sections 𝒰 F σ V).hom ≫
      eqToHom (congrArg
        (fun W => ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 σ V))))
    (Eq.trans (congrArg (fun m => m ≫ _) hGE)
      (Eq.trans (((Scheme.Modules.toPresheaf X ⋙
          (evaluation (TopologicalSpace.Opens X)ᵒᵖ (Ab.{u})).obj
            (Opposite.op V)).map_comp _ _).symm)
        (congrArg (Scheme.Modules.toPresheaf X ⋙
            (evaluation (TopologicalSpace.Opens X)ᵒᵖ (Ab.{u})).obj
              (Opposite.op V)).map
          (cechAugmentation_pushPullMap 𝒰 F (backboneIncl 𝒰 0 σ)))))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m => m ≫ eqToHom (congrArg
      (fun W => ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
        (Opposite.op W))
      (coverInterOpen_inf_eq_iInf_inf 𝒰 σ V)))
    (unit_pushPull_leg_sections 𝒰 F σ V)) ?_
  refine Eq.trans (congrArg (fun m =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
        (homOfLE (inf_le_right : coverInterOpen 𝒰 σ ⊓ V ≤ V)).op ≫ m)
    (eqToHom_eq_restriction (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf)
      (coverInterOpen_inf_eq_iInf_inf 𝒰 σ V)
      (le_of_eq (coverInterOpen_inf_eq_iInf_inf 𝒰 σ V).symm) _)) ?_
  refine Eq.trans
    ((((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map_comp _ _).symm) ?_
  refine Eq.trans (congrArg ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
    (op_comp (f := homOfLE
      (le_of_eq (coverInterOpen_inf_eq_iInf_inf 𝒰 σ V).symm))
      (g := homOfLE (inf_le_right : coverInterOpen 𝒰 σ ⊓ V ≤ V))).symm) ?_
  exact congrArg (fun m => ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
    (Quiver.Hom.op m)) (Subsingleton.elim _ _)

/-- The evaluated scheme-level augmentation is the direct section restriction product. -/
lemma mappedSectionCechAugV_eq (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (V : TopologicalSpace.Opens X) :
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat).obj
            (Opposite.op V)).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (cechAugmentation 𝒰 F)) ≫
      (coreIso_objIso 𝒰 F 0 V).hom =
        sectionCechAugV 𝒰 F V := by
  apply Pi.hom_ext
  intro σ
  exact (mappedSectionCechAugV_π 𝒰 F V σ).trans
    (sectionCechAugV_π 𝒰 F V σ).symm

end AlgebraicGeometry
