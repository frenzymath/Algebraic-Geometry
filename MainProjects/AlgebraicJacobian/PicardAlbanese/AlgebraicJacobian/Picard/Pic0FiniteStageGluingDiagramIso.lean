/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageOverlapBaseChange
import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionNaturality
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingBaseChange

/-!
# The finite-stage Picard gluing diagram after base change

The chart and overlap comparisons identify the multispan diagram obtained by
base-changing the finite-stage gluing with the canonical diagram of the exact
separably closed atlas.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

theorem pullback_congrHom_hom_fst
    {X Y Z : Scheme.{u}} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.fst f₂ g₂ =
      pullback.fst f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom, pullback.map]

theorem pullback_congrHom_hom_fst_assoc
    {X Y Z W : Scheme.{u}} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (t : X ⟶ W) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.fst f₂ g₂ ≫ t =
      pullback.fst f₁ g₁ ≫ t := by
  rw [← Category.assoc, pullback_congrHom_hom_fst]

theorem pullback_congrHom_hom_snd
    {X Y Z : Scheme.{u}} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.snd f₂ g₂ =
      pullback.snd f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom, pullback.map]

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageGluePackage

set_option synthInstance.maxHeartbeats 3200000 in
-- The composite retains the package's dependent finite-subextension towers.
set_option maxHeartbeats 12800000 in
/-- The finite-stage overlap structure map becomes the canonical structure map
after scalar extension to the separably closed field. -/
theorem glueData_f_comp_inclusion_comp_gluedMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    P.glueData.f U V ≫ P.glueData.ι U ≫ P.gluedMap =
      overlapBaseChangeMap C P U V := by
  rw [glueData_f_pinned C P U V, glueData_ι_gluedMap C P U]
  exact restrictionSpecMap_comp_chartBaseChangeMap C P U V

set_option synthInstance.maxHeartbeats 3200000 in
-- The two projections reduce to the specialized flattening identities.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
theorem gluingOverlapIso_pre_fst
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f U V ≫
        (pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom =
      (gluingOverlapFlatteningIso C P U V).hom ≫
        (pullback.congrHom
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫
        restrictionBaseChangeMap C P U V := by
  apply pullback.hom_ext
    (f := chartBaseChangeMap C P U)
    (g := Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))
  · simp only [Category.assoc]
    refine Eq.trans
      (congrArg
        (fun q =>
          (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f U V ≫ q)
        (pullback_congrHom_hom_fst (glueData_ι_gluedMap C P U) rfl)) ?_
    refine Eq.trans ?_
      (congrArg
        (fun q =>
          (gluingOverlapFlatteningIso C P U V).hom ≫
            (pullback.congrHom
              (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫ q)
        (restrictionBaseChangeMap_fst (C := C) P U V)).symm
    refine Eq.trans ?_
      (congrArg
        (fun q => (gluingOverlapFlatteningIso C P U V).hom ≫ q)
        (pullback_congrHom_hom_fst_assoc
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl
          (Spec.map (CommRingCat.ofHom
            (restrictionBaseChangeRingHom C P U V))))).symm
    refine Eq.trans ?_
      (congrArg
        (fun q =>
          (gluingOverlapFlatteningIso C P U V).hom ≫
            pullback.fst
              (P.glueData.f U V ≫ P.glueData.ι U ≫ P.gluedMap)
              (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≫ q)
        (glueData_f_pinned C P U V))
    exact (gluingOverlapFlatteningIso_hom_comp_fst_comp_f C P U V).symm
  · simp only [Category.assoc]
    refine Eq.trans
      (congrArg
        (fun q =>
          (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f U V ≫ q)
        (pullback_congrHom_hom_snd (glueData_ι_gluedMap C P U) rfl)) ?_
    refine Eq.trans ?_
      (congrArg
        (fun q =>
          (gluingOverlapFlatteningIso C P U V).hom ≫
            (pullback.congrHom
              (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫ q)
        (restrictionBaseChangeMap_snd (C := C) P U V)).symm
    refine Eq.trans ?_
      (congrArg
        (fun q => (gluingOverlapFlatteningIso C P U V).hom ≫ q)
        (pullback_congrHom_hom_snd
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl)).symm
    exact (gluingOverlapFlatteningIso_hom_comp_snd C P U V).symm

set_option synthInstance.maxHeartbeats 3200000 in
-- Raw tensor carriers keep the dependent finite-subextension instances visible.
set_option maxHeartbeats 12800000 in
/-- An overlap in the base-changed finite-stage gluing is the corresponding
overlap in the canonical gluing diagram of the exact Picard atlas. -/
noncomputable def gluingOverlapIso
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).V (U, V) ≅
      (pic0SepClosedAtlasGlueData C).V (U, V) := by
  exact
    gluingOverlapFlatteningIso C P U V ≪≫
      pullback.congrHom (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl ≪≫
      overlapBaseChangeIso C P U V ≪≫
      pic0SepClosedAtlasOverlapIso C U V

set_option synthInstance.maxHeartbeats 3200000 in
-- This exact-atlas projection is independent of the finite-stage package.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem overlapAtlasProjection_left
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0SepClosedAtlasOverlapIso C U V).hom ≫
        ((pic0SepClosedAtlasGlueData C).f U V ≫ U.1.1.ι) =
      (pic0FiniteStageAffineOverlap C U V).1.ι := by
  calc
    _ = ((pic0SepClosedAtlasOverlapIso C U V).hom ≫
          (pic0SepClosedAtlasGlueData C).f U V) ≫ U.1.1.ι :=
      (Category.assoc _ _ _).symm
    _ = ((pic0_sepClosed_representableBy (C := C)).1.left.homOfLE
          (pic0FiniteStageAffineOverlap_le_left C U V)) ≫ U.1.1.ι :=
      congrArg (fun q => q ≫ U.1.1.ι)
        (pic0SepClosedAtlasOverlapIso_hom_f C U V)
    _ = _ := Scheme.homOfLE_ι _ _

set_option synthInstance.maxHeartbeats 3200000 in
-- Isolate the exact-atlas projection from the full dependent diagram equality.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem overlapBaseChangeIso_hom_atlas_f_ι
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (overlapBaseChangeIso C P U V).hom ≫
        ((pic0SepClosedAtlasOverlapIso C U V).hom ≫
          ((pic0SepClosedAtlasGlueData C).f U V ≫ U.1.1.ι)) =
    (overlapRingBaseChangeIso C P U V).hom ≫
        (pic0FiniteStageAffineOverlap C U V).2.fromSpec := by
  calc
    _ = (overlapBaseChangeIso C P U V).hom ≫
        (pic0FiniteStageAffineOverlap C U V).1.ι :=
      congrArg (fun q => (overlapBaseChangeIso C P U V).hom ≫ q)
        (overlapAtlasProjection_left C U V)
    _ = _ := overlapBaseChangeIso_hom_ι C P U V

set_option synthInstance.maxHeartbeats 3200000 in
-- Seal the overlap comparison only after recording its stable projection law.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The overlap comparison carries the exact atlas projection to the pinned
finite-stage overlap projection. -/
theorem gluingOverlapIso_hom_atlas_f_ι
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (gluingOverlapIso C P U V).hom ≫
        ((pic0SepClosedAtlasGlueData C).f U V ≫ U.1.1.ι) =
      (gluingOverlapFlatteningIso C P U V).hom ≫
        (pullback.congrHom
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫
      (overlapRingBaseChangeIso C P U V).hom ≫
        (pic0FiniteStageAffineOverlap C U V).2.fromSpec := by
  unfold gluingOverlapIso
  simpa only [Iso.trans_hom, Category.assoc] using
    congrArg
      (fun q => (gluingOverlapFlatteningIso C P U V).hom ≫
        (pullback.congrHom
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫ q)
      (overlapBaseChangeIso_hom_atlas_f_ι C P U V)

attribute [irreducible] gluingOverlapIso

set_option synthInstance.maxHeartbeats 3200000 in
-- Matching the complete glued multispan equality crosses several dependent pullbacks.
set_option maxHeartbeats 32000000 in
set_option backward.isDefEq.respectTransparency false in
theorem gluingOverlapIso_fst
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f U V ≫
        (gluingChartIso C P U).hom =
      (gluingOverlapIso C P U V).hom ≫
        (pic0SepClosedAtlasGlueData C).f U V := by
  apply (cancel_mono U.1.1.ι).1
  calc
    _ = ((Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f U V ≫
        (pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom) ≫
        ((chartRingBaseChangeIso C P U).hom ≫ U.1.2.fromSpec) := by
      simpa only [Category.assoc] using congrArg
        (fun q =>
          (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f U V ≫ q)
        (gluingChartIso_hom_ι C P U)
    _ = ((gluingOverlapFlatteningIso C P U V).hom ≫
          (pullback.congrHom
            (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫
          restrictionBaseChangeMap C P U V) ≫
        ((chartRingBaseChangeIso C P U).hom ≫ U.1.2.fromSpec) := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫
          ((chartRingBaseChangeIso C P U).hom ≫ U.1.2.fromSpec))
        (gluingOverlapIso_pre_fst C P U V)
    _ = ((gluingOverlapFlatteningIso C P U V).hom ≫
          (pullback.congrHom
            (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom) ≫
        ((overlapRingBaseChangeIso C P U V).hom ≫
          (pic0FiniteStageAffineOverlap C U V).2.fromSpec) := by
      simpa only [Category.assoc] using congrArg
        (fun q => ((gluingOverlapFlatteningIso C P U V).hom ≫
          (pullback.congrHom
            (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom) ≫ q)
        (restrictionBaseChangeMap_fromSpec C P U V)
    _ = _ := by
      simpa only [Category.assoc] using
        (gluingOverlapIso_hom_atlas_f_ι C P U V).symm

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
