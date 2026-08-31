/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegAux
import AlgebraicJacobian.Cohomology.CechSectionAugmentationComparison

/-!
# Sectionwise Čech comparison

This file transports the evaluated augmented Čech complex to the concrete section complex.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

/-- The evaluated augmented Čech complex is the augmented concrete section complex. -/
noncomputable def cechSection_complex_iso (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (V : TopologicalSpace.Opens X) :
    let α : X.ringCatSheaf.obj ⟶ X.ringCatSheaf.obj := 𝟙 X.ringCatSheaf.obj
    let cc := ComplexShape.up ℕ
    let K := cechAugmentedComplex 𝒰 F
    let Kp := ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars α).mapHomologicalComplex cc).obj K
    let GV :=
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
      (evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)
    let D := (GV.mapHomologicalComplex cc).obj Kp
    D ≅ (sectionCechComplexV 𝒰 F V).augment (sectionCechAugV 𝒰 F V)
      (sectionCechAugV_comp_d 𝒰 F V) := by
  intro α cc K Kp GV D
  -- The push–pull functor `Ψ` through which the evaluated complex `D` is built.  We keep it
  -- inline (rather than abstracted by `set`) so the `Ψ.Additive` instance resolves directly.
  haveI hΨadd :
      (SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.restrictScalars α).Additive :=
    inferInstance
  haveI : GV.Additive := inferInstance
  -- The non-augmented evaluated Cech complex is identified degreewise with the concrete
  -- section complex over the restricted family `U'_σ = coverInterOpen 𝒰 σ ⊓ V`.
  let coreIso : (GV.mapHomologicalComplex cc).obj
        (((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars α).mapHomologicalComplex cc).obj
            (cechComplexOnX 𝒰 F)) ≅ sectionCechComplexV 𝒰 F V :=
    HomologicalComplex.Hom.isoOfComponents (fun p => coreIso_objIso 𝒰 F p V)
      (coreIso_comm 𝒰 F V)
  -- (adapter) The augmentation node `GV(Ψ F)` is the section group `Γ(V, F)`: definitional,
  -- since `restrictScalars (𝟙 ·)` and `toPresheaf` leave the underlying abelian-group presheaf
  -- unchanged and evaluation extracts the section over `V`.
  let eY : GV.obj ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars α).obj F) ≅
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op V) := Iso.refl _
  -- The comparison theorem isolates the mate calculus equating the evaluated augmentation with
  -- the direct product of section restrictions.
  have hcompat : GV.map ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars α).map (cechAugmentation 𝒰 F)) ≫
        (HomologicalComplex.Hom.isoApp coreIso 0).hom = eY.hom ≫ sectionCechAugV 𝒰 F V := by
    have happ : (HomologicalComplex.Hom.isoApp coreIso 0).hom = (coreIso_objIso 𝒰 F 0 V).hom :=
      congrArg Iso.hom (HomologicalComplex.Hom.isoOfComponents_app _ _ 0)
    rw [happ]
    exact (mappedSectionCechAugV_eq 𝒰 F V).trans (Category.id_comp _).symm
  -- Peel the augmentation node off `D` with `mapHC_augment_iso` (twice), then glue the
  -- non-augmented `coreIso` to the augmentation data with `augmentCochainIso`.
  exact (GV.mapHomologicalComplex cc).mapIso
      (mapHC_augment_iso (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars α) hΨadd (cechComplexOnX 𝒰 F) (cechAugmentation 𝒰 F)
        (cechAugmentation_comp_d 𝒰 F)) ≪≫
    mapHC_augment_iso GV ‹GV.Additive› (((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars α).mapHomologicalComplex cc).obj (cechComplexOnX 𝒰 F))
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars α).map (cechAugmentation 𝒰 F))
      (map_augment_cond (SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars α) hΨadd (cechComplexOnX 𝒰 F) (cechAugmentation 𝒰 F)
        (cechAugmentation_comp_d 𝒰 F)) ≪≫
    augmentCochainIso coreIso eY (GV.map ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars α).map (cechAugmentation 𝒰 F)))
      (map_augment_cond GV ‹GV.Additive› (((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars α).mapHomologicalComplex cc).obj (cechComplexOnX 𝒰 F))
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars α).map (cechAugmentation 𝒰 F))
        (map_augment_cond (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars α) hΨadd (cechComplexOnX 𝒰 F) (cechAugmentation 𝒰 F)
          (cechAugmentation_comp_d 𝒰 F))) (sectionCechAugV 𝒰 F V)
      (sectionCechAugV_comp_d 𝒰 F V) hcompat


end AlgebraicGeometry
