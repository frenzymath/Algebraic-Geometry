/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoPreSndSndCommon

/-! The source half of the second right-gluing projection. -/

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
-- The source projection retains the glued chart pullback instance tower.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
theorem gluingOverlapIso_pre_snd_snd_source
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).t U V ≫
      (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f V U ≫
      (pullback.congrHom (glueData_ι_gluedMap C P V) rfl).hom ≫
      pullback.snd (chartBaseChangeMap C P V)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
    gluingOverlapIso_pre_snd_snd_common C P U V := by
  have hι_snd :
      (pullback.congrHom (glueData_ι_gluedMap C P V) rfl).hom ≫
          pullback.snd (chartBaseChangeMap C P V)
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
        pullback.snd (P.glueData.ι V ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
    pullback_congrHom_hom_snd (glueData_ι_gluedMap C P V) rfl
  calc
    _ = (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).t U V ≫
        (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f V U ≫
        pullback.snd (P.glueData.ι V ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
      congrArg
        (fun q =>
          (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).t U V ≫
            (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
              (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f V U ≫ q)
        hι_snd
    _ = gluingOverlapIso_pre_snd_snd_common C P U V := by
      simpa only [gluingOverlapIso_pre_snd_snd_common] using
        (baseChangedGluing_t_fst_snd C P U V)

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
