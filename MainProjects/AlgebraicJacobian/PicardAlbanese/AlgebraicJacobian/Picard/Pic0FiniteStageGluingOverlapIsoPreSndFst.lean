/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoPreSndBridge
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoPreSndTFstFst

/-!
# The first projection of the right gluing-leg source factorization

This module proves the first pullback projection equation before the final
comparison with the canonical separably closed atlas.
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
-- The first projection keeps the final chart and base pullback explicit.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
theorem gluingOverlapIso_pre_snd_fst
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (((Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).t U V ≫
        (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f V U) ≫
        (pullback.congrHom (glueData_ι_gluedMap C P V) rfl).hom) ≫
      pullback.fst
        (chartBaseChangeMap C P V)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
    (((gluingOverlapFlatteningIso C P U V).hom ≫
        (pullback.congrHom
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom) ≫
        rightRestrictionBaseChangeMap C P U V) ≫
      pullback.fst
        (chartBaseChangeMap C P V)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
  simp only [Category.assoc]
  have hι_fst :
      (pullback.congrHom (glueData_ι_gluedMap C P V) rfl).hom ≫
          pullback.fst
            (chartBaseChangeMap C P V)
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
        pullback.fst (P.glueData.ι V ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
    pullback_congrHom_hom_fst (glueData_ι_gluedMap C P V) rfl
  have hfst :
      rightRestrictionBaseChangeMap C P U V ≫
          pullback.fst
            (chartBaseChangeMap C P V)
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
        pullback.fst
            (overlapBaseChangeMap C P U V)
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≫
          Spec.map (CommRingCat.ofHom
            (rightRestrictionBaseChangeRingHom C P U V)) :=
    rightRestrictionBaseChangeMap_fst (C := C) (P := P) (U := U) (V := V)
  have hcongr_fst :
      (pullback.congrHom
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫
        pullback.fst
          (overlapBaseChangeMap C P U V)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≫
        Spec.map (CommRingCat.ofHom
          (rightRestrictionBaseChangeRingHom C P U V)) =
      pullback.fst
        (P.glueData.f U V ≫ P.glueData.ι U ≫ P.gluedMap)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≫
        Spec.map (CommRingCat.ofHom
          (rightRestrictionBaseChangeRingHom C P U V)) :=
    pullback_congrHom_hom_fst_assoc
      (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl
      (Spec.map (CommRingCat.ofHom
        (rightRestrictionBaseChangeRingHom C P U V)))
  refine Eq.trans
    (congrArg
      (fun q =>
        (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).t U V ≫
            (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
              (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f V U ≫ q)
      hι_fst) ?_
  refine Eq.trans (baseChangedGluing_t_fst_fst C P U V) ?_
  refine Eq.trans ?_
    (congrArg
      (fun q =>
        (gluingOverlapFlatteningIso C P U V).hom ≫
          (pullback.congrHom
            (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫ q)
      hfst).symm
  refine Eq.trans ?_
    (congrArg
      (fun q => (gluingOverlapFlatteningIso C P U V).hom ≫ q)
      hcongr_fst).symm
  refine Eq.trans ?_
    (congrArg
      (fun q => (gluingOverlapFlatteningIso C P U V).hom ≫
        pullback.fst
          (P.glueData.f U V ≫ P.glueData.ι U ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≫ q)
      (glueData_t_comp_f_eq_spec_rightRestriction C P U V))
  exact (gluingOverlapFlatteningIso_hom_comp_fst_comp_t_f C P U V).symm

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
