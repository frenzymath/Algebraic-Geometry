/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoPreSndSndCommon

/-! The target half of the second right-gluing projection. -/

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
-- The target projection retains both pinned pullback instance towers.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
theorem gluingOverlapIso_pre_snd_snd_target
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (gluingOverlapFlatteningIso C P U V).hom ≫
      (pullback.congrHom
        (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫
      rightRestrictionBaseChangeMap C P U V ≫
      pullback.snd (chartBaseChangeMap C P V)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
    gluingOverlapIso_pre_snd_snd_common C P U V := by
  have hsnd :
      rightRestrictionBaseChangeMap C P U V ≫
          pullback.snd (chartBaseChangeMap C P V)
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
        pullback.snd (overlapBaseChangeMap C P U V)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
    rightRestrictionBaseChangeMap_snd (C := C) (P := P) (U := U) (V := V)
  have hcongr_snd :
      (pullback.congrHom
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫
        pullback.snd (overlapBaseChangeMap C P U V)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
      pullback.snd
        (P.glueData.f U V ≫ P.glueData.ι U ≫ P.gluedMap)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
    pullback_congrHom_hom_snd
      (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl
  calc
    _ = (gluingOverlapFlatteningIso C P U V).hom ≫
        (pullback.congrHom
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫
        pullback.snd (overlapBaseChangeMap C P U V)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
      congrArg (fun q => (gluingOverlapFlatteningIso C P U V).hom ≫
        (pullback.congrHom
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫ q) hsnd
    _ = (gluingOverlapFlatteningIso C P U V).hom ≫
        pullback.snd
          (P.glueData.f U V ≫ P.glueData.ι U ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
      congrArg (fun q => (gluingOverlapFlatteningIso C P U V).hom ≫ q) hcongr_snd
    _ = gluingOverlapIso_pre_snd_snd_common C P U V := by
      exact (gluingOverlapFlatteningIso_hom_comp_snd C P U V).trans rfl

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
