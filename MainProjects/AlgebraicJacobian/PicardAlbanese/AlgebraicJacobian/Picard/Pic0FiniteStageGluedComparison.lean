/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoSnd

/-!
# The global finite-stage Picard gluing comparison

The chart and overlap comparisons identify the two multicoequalizer diagrams, hence
their glued schemes.  Composing this global comparison with compatibility of gluing
and base change identifies the scalar extension of the finite-stage model with the
exact separably closed Picard representer.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageGluePackage

private noncomputable abbrev baseChangedGlueData
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) : Scheme.GlueData :=
  Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
    (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))

set_option synthInstance.maxHeartbeats 3200000 in
-- Descending the chart maps checks the dependent overlap comparison once.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def gluingGluedHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    (baseChangedGlueData C P).glued ⟶
      (pic0SepClosedAtlasGlueData C).glued := by
  fapply Multicoequalizer.desc
  · intro U
    exact (gluingChartIso C P U).hom ≫
      (pic0SepClosedAtlasGlueData C).ι U
  · rintro ⟨U, V⟩
    change
      (baseChangedGlueData C P).f U V ≫
          ((gluingChartIso C P U).hom ≫
            (pic0SepClosedAtlasGlueData C).ι U) =
        ((baseChangedGlueData C P).t U V ≫
            (baseChangedGlueData C P).f V U) ≫
          ((gluingChartIso C P V).hom ≫
            (pic0SepClosedAtlasGlueData C).ι V)
    calc
      _ = ((baseChangedGlueData C P).f U V ≫
            (gluingChartIso C P U).hom) ≫
          (pic0SepClosedAtlasGlueData C).ι U :=
        (Category.assoc _ _ _).symm
      _ = ((gluingOverlapIso C P U V).hom ≫
            (pic0SepClosedAtlasGlueData C).f U V) ≫
          (pic0SepClosedAtlasGlueData C).ι U :=
        congrArg (fun q => q ≫ (pic0SepClosedAtlasGlueData C).ι U)
          (gluingOverlapIso_fst C P U V)
      _ = (gluingOverlapIso C P U V).hom ≫
          ((pic0SepClosedAtlasGlueData C).f U V ≫
            (pic0SepClosedAtlasGlueData C).ι U) :=
        Category.assoc _ _ _
      _ = (gluingOverlapIso C P U V).hom ≫
          ((pic0SepClosedAtlasGlueData C).t U V ≫
            (pic0SepClosedAtlasGlueData C).f V U ≫
              (pic0SepClosedAtlasGlueData C).ι V) :=
        congrArg (fun q => (gluingOverlapIso C P U V).hom ≫ q)
          ((pic0SepClosedAtlasGlueData C).glue_condition U V).symm
      _ = ((gluingOverlapIso C P U V).hom ≫
            ((pic0SepClosedAtlasGlueData C).t U V ≫
              (pic0SepClosedAtlasGlueData C).f V U)) ≫
          (pic0SepClosedAtlasGlueData C).ι V := by
        simp only [Category.assoc]
      _ = (((baseChangedGlueData C P).t U V ≫
              (baseChangedGlueData C P).f V U) ≫
            (gluingChartIso C P V).hom) ≫
          (pic0SepClosedAtlasGlueData C).ι V :=
        congrArg (fun q => q ≫ (pic0SepClosedAtlasGlueData C).ι V)
          (gluingOverlapIso_snd C P U V).symm
      _ = _ := Category.assoc _ _ _

set_option synthInstance.maxHeartbeats 3200000 in
-- Projecting the descended map unfolds the multicoequalizer descriptor.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem gluingGluedHom_ι
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    (baseChangedGlueData C P).ι U ≫ gluingGluedHom C P =
      (gluingChartIso C P U).hom ≫
        (pic0SepClosedAtlasGlueData C).ι U := by
  unfold gluingGluedHom
  exact Multicoequalizer.π_desc _ _ _ _ _

set_option synthInstance.maxHeartbeats 3200000 in
-- Cancelling the overlap isomorphism retains the dependent glued objects.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem gluingOverlapIso_inv_fst
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0SepClosedAtlasGlueData C).f U V ≫
        (gluingChartIso C P U).inv =
      (gluingOverlapIso C P U V).inv ≫
        (baseChangedGlueData C P).f U V := by
  apply (cancel_epi (gluingOverlapIso C P U V).hom).1
  calc
    _ = ((gluingOverlapIso C P U V).hom ≫
          (pic0SepClosedAtlasGlueData C).f U V) ≫
        (gluingChartIso C P U).inv :=
      (Category.assoc _ _ _).symm
    _ = (((baseChangedGlueData C P).f U V ≫
          (gluingChartIso C P U).hom)) ≫
        (gluingChartIso C P U).inv :=
      congrArg (fun q => q ≫ (gluingChartIso C P U).inv)
        (gluingOverlapIso_fst C P U V).symm
    _ = (baseChangedGlueData C P).f U V := by simp
    _ = (gluingOverlapIso C P U V).hom ≫
        ((gluingOverlapIso C P U V).inv ≫
          (baseChangedGlueData C P).f U V) := by simp

set_option synthInstance.maxHeartbeats 3200000 in
-- The right inverse projection crosses both transition legs of the glue data.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem gluingOverlapIso_inv_snd
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    ((pic0SepClosedAtlasGlueData C).t U V ≫
        (pic0SepClosedAtlasGlueData C).f V U) ≫
      (gluingChartIso C P V).inv =
    (gluingOverlapIso C P U V).inv ≫
      ((baseChangedGlueData C P).t U V ≫
        (baseChangedGlueData C P).f V U) := by
  apply (cancel_epi (gluingOverlapIso C P U V).hom).1
  calc
    _ = ((gluingOverlapIso C P U V).hom ≫
          ((pic0SepClosedAtlasGlueData C).t U V ≫
            (pic0SepClosedAtlasGlueData C).f V U)) ≫
        (gluingChartIso C P V).inv :=
      (Category.assoc _ _ _).symm
    _ = (((baseChangedGlueData C P).t U V ≫
            (baseChangedGlueData C P).f V U) ≫
          (gluingChartIso C P V).hom) ≫
        (gluingChartIso C P V).inv :=
      congrArg (fun q => q ≫ (gluingChartIso C P V).inv)
        (gluingOverlapIso_snd C P U V).symm
    _ = (baseChangedGlueData C P).t U V ≫
        (baseChangedGlueData C P).f V U := by simp
    _ = (gluingOverlapIso C P U V).hom ≫
        ((gluingOverlapIso C P U V).inv ≫
          ((baseChangedGlueData C P).t U V ≫
            (baseChangedGlueData C P).f V U)) := by simp

set_option synthInstance.maxHeartbeats 3200000 in
-- Descending the inverse chart maps checks the reverse overlap comparison once.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def gluingGluedInv
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    (pic0SepClosedAtlasGlueData C).glued ⟶
      (baseChangedGlueData C P).glued := by
  fapply Multicoequalizer.desc
  · intro U
    exact (gluingChartIso C P U).inv ≫
      (baseChangedGlueData C P).ι U
  · rintro ⟨U, V⟩
    change
      (pic0SepClosedAtlasGlueData C).f U V ≫
          ((gluingChartIso C P U).inv ≫
            (baseChangedGlueData C P).ι U) =
        ((pic0SepClosedAtlasGlueData C).t U V ≫
            (pic0SepClosedAtlasGlueData C).f V U) ≫
          ((gluingChartIso C P V).inv ≫
            (baseChangedGlueData C P).ι V)
    calc
      _ = ((pic0SepClosedAtlasGlueData C).f U V ≫
            (gluingChartIso C P U).inv) ≫
          (baseChangedGlueData C P).ι U :=
        (Category.assoc _ _ _).symm
      _ = ((gluingOverlapIso C P U V).inv ≫
            (baseChangedGlueData C P).f U V) ≫
          (baseChangedGlueData C P).ι U :=
        congrArg (fun q => q ≫ (baseChangedGlueData C P).ι U)
          (gluingOverlapIso_inv_fst C P U V)
      _ = (gluingOverlapIso C P U V).inv ≫
          ((baseChangedGlueData C P).f U V ≫
            (baseChangedGlueData C P).ι U) :=
        Category.assoc _ _ _
      _ = (gluingOverlapIso C P U V).inv ≫
          ((baseChangedGlueData C P).t U V ≫
            (baseChangedGlueData C P).f V U ≫
              (baseChangedGlueData C P).ι V) :=
        congrArg (fun q => (gluingOverlapIso C P U V).inv ≫ q)
          ((baseChangedGlueData C P).glue_condition U V).symm
      _ = ((gluingOverlapIso C P U V).inv ≫
            ((baseChangedGlueData C P).t U V ≫
              (baseChangedGlueData C P).f V U)) ≫
          (baseChangedGlueData C P).ι V := by
        simp only [Category.assoc]
      _ = (((pic0SepClosedAtlasGlueData C).t U V ≫
              (pic0SepClosedAtlasGlueData C).f V U) ≫
            (gluingChartIso C P V).inv) ≫
          (baseChangedGlueData C P).ι V :=
        congrArg (fun q => q ≫ (baseChangedGlueData C P).ι V)
          (gluingOverlapIso_inv_snd C P U V).symm
      _ = _ := Category.assoc _ _ _

set_option synthInstance.maxHeartbeats 3200000 in
-- Projecting the descended inverse unfolds the multicoequalizer descriptor.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem gluingGluedInv_ι
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    (pic0SepClosedAtlasGlueData C).ι U ≫ gluingGluedInv C P =
      (gluingChartIso C P U).inv ≫
        (baseChangedGlueData C P).ι U := by
  unfold gluingGluedInv
  exact Multicoequalizer.π_desc _ _ _ _ _

set_option synthInstance.maxHeartbeats 3200000 in
-- Check the glued inverse law one chart at a time without expanding the full diagram.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem gluingGluedHom_inv
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    gluingGluedHom C P ≫ gluingGluedInv C P = 𝟙 _ := by
  apply Multicoequalizer.hom_ext
  intro U
  calc
    (baseChangedGlueData C P).ι U ≫
        (gluingGluedHom C P ≫ gluingGluedInv C P) =
      ((baseChangedGlueData C P).ι U ≫ gluingGluedHom C P) ≫
        gluingGluedInv C P := (Category.assoc _ _ _).symm
    _ = ((gluingChartIso C P U).hom ≫
          (pic0SepClosedAtlasGlueData C).ι U) ≫
        gluingGluedInv C P :=
      congrArg (fun q => q ≫ gluingGluedInv C P)
        (gluingGluedHom_ι C P U)
    _ = (gluingChartIso C P U).hom ≫
        ((pic0SepClosedAtlasGlueData C).ι U ≫ gluingGluedInv C P) :=
      Category.assoc _ _ _
    _ = (gluingChartIso C P U).hom ≫
        ((gluingChartIso C P U).inv ≫
          (baseChangedGlueData C P).ι U) :=
      congrArg (fun q => (gluingChartIso C P U).hom ≫ q)
        (gluingGluedInv_ι C P U)
    _ = (baseChangedGlueData C P).ι U := by simp
    _ = (baseChangedGlueData C P).ι U ≫ 𝟙 _ := by simp

set_option synthInstance.maxHeartbeats 3200000 in
-- Check the reverse glued inverse law through the same pinned chart boundary.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem gluingGluedInv_hom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    gluingGluedInv C P ≫ gluingGluedHom C P = 𝟙 _ := by
  apply Multicoequalizer.hom_ext
  intro U
  calc
    (pic0SepClosedAtlasGlueData C).ι U ≫
        (gluingGluedInv C P ≫ gluingGluedHom C P) =
      ((pic0SepClosedAtlasGlueData C).ι U ≫ gluingGluedInv C P) ≫
        gluingGluedHom C P := (Category.assoc _ _ _).symm
    _ = ((gluingChartIso C P U).inv ≫
          (baseChangedGlueData C P).ι U) ≫
        gluingGluedHom C P :=
      congrArg (fun q => q ≫ gluingGluedHom C P)
        (gluingGluedInv_ι C P U)
    _ = (gluingChartIso C P U).inv ≫
        ((baseChangedGlueData C P).ι U ≫ gluingGluedHom C P) :=
      Category.assoc _ _ _
    _ = (gluingChartIso C P U).inv ≫
        ((gluingChartIso C P U).hom ≫
          (pic0SepClosedAtlasGlueData C).ι U) :=
      congrArg (fun q => (gluingChartIso C P U).inv ≫ q)
        (gluingGluedHom_ι C P U)
    _ = (pic0SepClosedAtlasGlueData C).ι U := by simp
    _ = (pic0SepClosedAtlasGlueData C).ι U ≫ 𝟙 _ := by simp

set_option synthInstance.maxHeartbeats 3200000 in
-- The record seals inverse laws instead of retaining their dependent proof terms.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The glued base-changed finite-stage atlas is the canonical exact Picard atlas glue. -/
noncomputable def gluingGluedIso
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).glued ≅
      (pic0SepClosedAtlasGlueData C).glued where
  hom := gluingGluedHom C P
  inv := gluingGluedInv C P
  hom_inv_id := gluingGluedHom_inv C P
  inv_hom_id := gluingGluedInv_hom C P

private noncomputable def exactAtlasFromGluedIso :
    (pic0SepClosedAtlasGlueData C).glued ≅
      (pic0_sepClosed_representableBy (C := C)).1.left := by
  change (pic0SepClosedAtlasOpenCover C).gluedCover.glued ≅
    (pic0_sepClosed_representableBy (C := C)).1.left
  exact asIso (pic0SepClosedAtlasOpenCover C).fromGlued

set_option maxHeartbeats 12800000 in
/-- On each chart, the exact-atlas comparison is the chosen open immersion. -/
private theorem exactAtlasFromGluedIso_hom_ι
    (U : Pic0FiniteStageChartIndex C) :
    (pic0SepClosedAtlasGlueData C).ι U ≫
        (exactAtlasFromGluedIso C).hom = U.1.1.ι := by
  change (pic0SepClosedAtlasOpenCover C).gluedCover.ι U ≫
      (pic0SepClosedAtlasOpenCover C).fromGlued =
        (pic0SepClosedAtlasOpenCover C).f U
  exact Scheme.Cover.ι_fromGlued _ _

set_option maxHeartbeats 12800000 in
/-- The chosen affine-chart spectrum map preserves the structure map to the
separably closed base field. -/
private theorem pic0SepClosedChart_fromSpec_structureMap
    (U : Pic0FiniteStageChartIndex C) :
    U.1.2.fromSpec ≫
        (pic0_sepClosed_representableBy (C := C)).1.hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (Pic0FiniteStageRing C (Sum.inl U)))) := by
  exact Over.w (Over.fromSpecAffine
    (pic0_sepClosed_representableBy (C := C)).1 U.1)

set_option synthInstance.maxHeartbeats 3200000 in
-- This projection crosses the pinned chart scalar-extension comparison.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The pinned chart comparison preserves the structure map to the separably
closed base field. -/
private theorem gluingChartIso_hom_structureMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    (gluingChartIso C P U).hom ≫ U.1.1.ι ≫
        (pic0_sepClosed_representableBy (C := C)).1.hom =
      pullback.snd (P.glueData.ι U ≫ P.gluedMap)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
  calc
    _ = (pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom ≫
          (chartRingBaseChangeIso C P U).hom ≫
            U.1.2.fromSpec ≫
              (pic0_sepClosed_representableBy (C := C)).1.hom := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ (pic0_sepClosed_representableBy (C := C)).1.hom)
        (gluingChartIso_hom_ι C P U)
    _ = (pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom ≫
          (chartRingBaseChangeIso C P U).hom ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap k (Pic0FiniteStageRing C (Sum.inl U)))) := by
      simpa only [Category.assoc] using congrArg
        (fun q => (pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom ≫
          (chartRingBaseChangeIso C P U).hom ≫ q)
        (pic0SepClosedChart_fromSpec_structureMap C U)
    _ = (pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom ≫
          pullback.snd (chartBaseChangeMap C P U)
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
      simpa only [Category.assoc] using congrArg
        (fun q => (pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom ≫ q)
        (chartRingBaseChangeIso_hom_structureMap C P U)
    _ = _ := by
      rw [pullback_congrHom_hom_snd (glueData_ι_gluedMap C P U) rfl]

set_option synthInstance.maxHeartbeats 3200000 in
-- Keep the local gluing projection separate from the global cover extensionality.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The second pullback projection is the restriction of the glued projection
to a base-changed finite-stage chart. -/
private theorem pullback_snd_eq_baseChangedGlueData_ι_p2
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    pullback.snd (P.glueData.ι U ≫ P.gluedMap)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
      (baseChangedGlueData C P).ι U ≫
        Scheme.Pullback.p2 P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
  rw [Scheme.Pullback.gluing_ι, Scheme.Pullback.p2,
    Multicoequalizer.π_desc]
  rfl

set_option synthInstance.maxHeartbeats 3200000 in
-- Globalize the chart projection without unfolding the glued inverse laws.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The global glued comparison, followed by the exact-atlas comparison,
preserves the map to the separably closed base. -/
private theorem gluingGluedIso_hom_structureMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    (gluingGluedIso C P).hom ≫
        (exactAtlasFromGluedIso C).hom ≫
          (pic0_sepClosed_representableBy (C := C)).1.hom =
      Scheme.Pullback.p2 P.glueData.openCover P.gluedMap
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
  refine Scheme.Cover.hom_ext (baseChangedGlueData C P).openCover _ _ ?_
  intro U
  calc
    (baseChangedGlueData C P).ι U ≫
        ((gluingGluedIso C P).hom ≫
          (exactAtlasFromGluedIso C).hom ≫
            (pic0_sepClosed_representableBy (C := C)).1.hom) =
      (gluingChartIso C P U).hom ≫
        (pic0SepClosedAtlasGlueData C).ι U ≫
          (exactAtlasFromGluedIso C).hom ≫
            (pic0_sepClosed_representableBy (C := C)).1.hom := by
      simpa only [gluingGluedIso, Category.assoc] using
        congrArg (fun q => q ≫ (exactAtlasFromGluedIso C).hom ≫
          (pic0_sepClosed_representableBy (C := C)).1.hom)
          (gluingGluedHom_ι C P U)
    _ = (gluingChartIso C P U).hom ≫ U.1.1.ι ≫
          (pic0_sepClosed_representableBy (C := C)).1.hom := by
      simpa only [Category.assoc] using congrArg
        (fun q => (gluingChartIso C P U).hom ≫ q ≫
          (pic0_sepClosed_representableBy (C := C)).1.hom)
        (exactAtlasFromGluedIso_hom_ι C U)
    _ = pullback.snd (P.glueData.ι U ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
      gluingChartIso_hom_structureMap C P U
    _ = (baseChangedGlueData C P).ι U ≫
        Scheme.Pullback.p2 P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
      pullback_snd_eq_baseChangedGlueData_ι_p2 C P U

set_option synthInstance.maxHeartbeats 3200000 in
-- Compose the three large glued isomorphisms without unfolding their implementations.
set_option maxHeartbeats 12800000 in
/-- Scalar extension of the descended finite-stage glue recovers the exact separably
closed Picard representing scheme. -/
noncomputable def finiteStageBaseChangeIso
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    pullback P.gluedMap
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≅
      (pic0_sepClosed_representableBy (C := C)).1.left :=
  baseChangeGluingIso C P ≪≫
    gluingGluedIso C P ≪≫
      exactAtlasFromGluedIso C

set_option synthInstance.maxHeartbeats 3200000 in
-- Keep the final proof at the three named global comparison boundaries.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The finite-stage comparison is an isomorphism over the separably closed
base field. -/
theorem finiteStageBaseChangeIso_hom_structureMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    (finiteStageBaseChangeIso C P).hom ≫
        (pic0_sepClosed_representableBy (C := C)).1.hom =
      pullback.snd P.gluedMap
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
  calc
    _ = (baseChangeGluingIso C P).hom ≫
        ((gluingGluedIso C P).hom ≫
          (exactAtlasFromGluedIso C).hom ≫
            (pic0_sepClosed_representableBy (C := C)).1.hom) := by
      simp only [finiteStageBaseChangeIso, Iso.trans_hom, Category.assoc]
    _ = (baseChangeGluingIso C P).hom ≫
        Scheme.Pullback.p2 P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
      congrArg (fun q => (baseChangeGluingIso C P).hom ≫ q)
        (gluingGluedIso_hom_structureMap C P)
    _ = pullback.snd P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
      change (baseChangeGluingIso C P).hom ≫
          Scheme.Pullback.p2 P.presentation.glueData.openCover P.presentation.map
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
        pullback.snd P.presentation.map
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))
      exact baseChangeGluingIso_hom_p2 C P

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
