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
-- The right-leg comparison crosses the fully dependent glued overlap square.
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
  apply (cancel_mono V.1.1.ι).1
  calc
    _ = (((Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).t U V ≫
        (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f V U) ≫
        (pullback.congrHom (glueData_ι_gluedMap C P V) rfl).hom) ≫
        ((chartRingBaseChangeIso C P V).hom ≫ V.1.2.fromSpec) := by
      simpa only [Category.assoc] using congrArg
        (fun q => ((Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).t U V ≫
          (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f V U) ≫ q)
        (gluingChartIso_hom_ι C P V)
    _ = ((gluingOverlapFlatteningIso C P U V).hom ≫
          (pullback.congrHom
            (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫
          rightRestrictionBaseChangeMap C P U V) ≫
        ((chartRingBaseChangeIso C P V).hom ≫ V.1.2.fromSpec) := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫
          ((chartRingBaseChangeIso C P V).hom ≫ V.1.2.fromSpec))
        (gluingOverlapIso_pre_snd C P U V)
    _ = ((gluingOverlapFlatteningIso C P U V).hom ≫
          (pullback.congrHom
            (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom) ≫
        ((overlapRingBaseChangeIso C P U V).hom ≫
          (pic0FiniteStageAffineOverlap C U V).2.fromSpec) := by
      simpa only [Category.assoc] using congrArg
        (fun q => ((gluingOverlapFlatteningIso C P U V).hom ≫
          (pullback.congrHom
            (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom) ≫ q)
        (rightRestrictionBaseChangeMap_fromSpec C P U V)
    _ = _ := by
      simpa only [gluingOverlapIso, Iso.trans_hom, Category.assoc] using congrArg
        (fun q => (gluingOverlapFlatteningIso C P U V).hom ≫
          (pullback.congrHom
            (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫ q)
        (overlapBaseChangeIso_hom_atlas_t_f_ι C P U V).symm

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
