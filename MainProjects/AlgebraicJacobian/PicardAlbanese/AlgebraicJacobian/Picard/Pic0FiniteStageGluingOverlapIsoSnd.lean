/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoPreSnd

/-!
# The right leg of the finite-stage Picard gluing comparison

The overlap comparison in `Pic0FiniteStageGluingDiagramIso` respects the second
multispan leg as well as the first.  This is the remaining local naturality
equation needed to assemble the chart and overlap comparisons into a natural
isomorphism of gluing diagrams.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageGluePackage

set_option synthInstance.maxHeartbeats 3200000 in
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The overlap comparison respects the right multispan projection. -/
theorem gluingOverlapIso_snd
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    ((Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).t U V ≫
        (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f V U) ≫
        (gluingChartIso C P V).hom =
      (gluingOverlapIso C P U V).hom ≫
        ((pic0SepClosedAtlasGlueData C).t U V ≫
          (pic0SepClosedAtlasGlueData C).f V U) := by
  have chart_fac :
      (chartBaseChangeIso C P V).hom ≫ V.1.1.ι =
        (chartRingBaseChangeIso C P V).hom ≫ V.1.2.fromSpec := by
    calc
      _ = (chartRingBaseChangeIso C P V).hom ≫
          (V.1.2.isoSpec.inv ≫ V.1.1.ι) := by
        simp only [chartBaseChangeIso, chartRingBaseChangeIso,
          chartFinalBaseChangeEquiv, affineBaseChangeIso, Iso.trans_hom,
          Iso.symm_hom, Category.assoc]
      _ = _ := congrArg (fun q => (chartRingBaseChangeIso C P V).hom ≫ q)
        V.1.2.isoSpec_inv_ι
  have overlap_fac :
      (overlapBaseChangeIso C P U V).hom ≫
          (pic0FiniteStageAffineOverlap C U V).1.ι =
      (overlapRingBaseChangeIso C P U V).hom ≫
          (pic0FiniteStageAffineOverlap C U V).2.fromSpec := by
    calc
      _ = (overlapRingBaseChangeIso C P U V).hom ≫
          ((pic0FiniteStageAffineOverlap C U V).2.isoSpec.inv ≫
            (pic0FiniteStageAffineOverlap C U V).1.ι) := by
        simp only [overlapBaseChangeIso, overlapRingBaseChangeIso,
          overlapFinalBaseChangeEquiv, affineBaseChangeIso, Iso.trans_hom,
          Iso.symm_hom, Category.assoc]
      _ = _ := congrArg
        (fun q => (overlapRingBaseChangeIso C P U V).hom ≫ q)
        (pic0FiniteStageAffineOverlap C U V).2.isoSpec_inv_ι
  have atlas_projection :
      (pic0SepClosedAtlasOverlapIso C U V).hom ≫
          (((pic0SepClosedAtlasGlueData C).t U V ≫
            (pic0SepClosedAtlasGlueData C).f V U) ≫ V.1.1.ι) =
        (pic0FiniteStageAffineOverlap C U V).1.ι := by
    calc
      _ = ((pic0SepClosedAtlasOverlapIso C U V).hom ≫
            ((pic0SepClosedAtlasGlueData C).t U V ≫
              (pic0SepClosedAtlasGlueData C).f V U)) ≫ V.1.1.ι :=
        (Category.assoc _ _ _).symm
      _ = ((pic0_sepClosed_representableBy (C := C)).1.left.homOfLE
          (pic0FiniteStageAffineOverlap_le_right C U V)) ≫ V.1.1.ι :=
        congrArg (fun q => q ≫ V.1.1.ι)
          (pic0SepClosedAtlasOverlapIso_hom_t_f C U V)
      _ = _ := Scheme.homOfLE_ι _ _
  have overlap_atlas_fac :
      (overlapBaseChangeIso C P U V).hom ≫
          ((pic0SepClosedAtlasOverlapIso C U V).hom ≫
            (((pic0SepClosedAtlasGlueData C).t U V ≫
              (pic0SepClosedAtlasGlueData C).f V U) ≫ V.1.1.ι)) =
        (overlapRingBaseChangeIso C P U V).hom ≫
          (pic0FiniteStageAffineOverlap C U V).2.fromSpec := by
    calc
      _ = (overlapBaseChangeIso C P U V).hom ≫
          (pic0FiniteStageAffineOverlap C U V).1.ι :=
        congrArg (fun q => (overlapBaseChangeIso C P U V).hom ≫ q)
          atlas_projection
      _ = _ := overlap_fac
  apply (cancel_mono V.1.1.ι).1
  simp only [gluingChartIso, Iso.trans_hom, Category.assoc]
  rw [chart_fac]
  rw [reassoc_of% gluingOverlapIso_pre_snd C P U V]
  simp only [gluingOverlapIso, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc (rightRestrictionBaseChangeMap C P U V)]
  rw [rightRestrictionBaseChangeMap_naturality C P U V]
  rw [Category.assoc (overlapRingBaseChangeIso C P U V).hom]
  rw [exactRightRestrictionAlgHom_fromSpec C U V]
  exact congrArg
    (fun q => (gluingOverlapFlatteningIso C P U V).hom ≫
      (pullback.congrHom
        (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫ q)
    overlap_atlas_fac.symm

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
