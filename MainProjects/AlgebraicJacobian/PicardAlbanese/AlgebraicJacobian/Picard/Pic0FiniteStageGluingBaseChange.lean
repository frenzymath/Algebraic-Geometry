/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionBaseChange

/-!
# Base change of the finite-stage Picard gluing

The global base change of the finite-stage glued scheme is the scheme obtained by
gluing its locally base-changed charts.  The chart and overlap pullbacks are identified
with the corresponding exact separably closed affine opens.
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
-- Projecting the package retains nested finite-subextension scalar towers.
set_option maxHeartbeats 12800000 in
/-- The base change of the finite-stage glue is the gluing of its base-changed charts. -/
noncomputable def baseChangeGluingIso
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    pullback P.presentation.map
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≅
      (Scheme.Pullback.gluing P.presentation.glueData.openCover P.presentation.map
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).glued :=
  limit.isoLimitCone
    ⟨_, Scheme.Pullback.gluedIsLimit P.presentation.glueData.openCover P.presentation.map
      (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))⟩

set_option maxHeartbeats 12800000 in
/-- The canonical gluing-to-pullback isomorphism preserves the second projection. -/
theorem baseChangeGluingIso_hom_p2
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    (baseChangeGluingIso C P).hom ≫
        Scheme.Pullback.p2 P.presentation.glueData.openCover P.presentation.map
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
      pullback.snd P.presentation.map
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
  exact limit.isoLimitCone_hom_π
    ⟨_, Scheme.Pullback.gluedIsLimit P.presentation.glueData.openCover
      P.presentation.map (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))⟩
    WalkingCospan.right

set_option synthInstance.maxHeartbeats 3200000 in
-- The chart comparison elaborates the package's dependent scalar towers.
set_option maxHeartbeats 12800000 in
/-- A chart in the base-changed gluing is its corresponding exact Picard chart. -/
noncomputable def gluingChartIso
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    (Scheme.Pullback.gluing P.presentation.glueData.openCover P.presentation.map
      (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).U U ≅
      (pic0SepClosedAtlasOpenCover C).X U :=
  pullback.congrHom (by
    change P.presentation.glueData.ι U ≫ P.presentation.map = _
    simpa only [presentation_glueData, presentation_mapData,
      gluedMapData_chartMap] using P.presentation.chartMap_factor U) rfl ≪≫
    chartBaseChangeIso C P U

set_option synthInstance.maxHeartbeats 3200000 in
-- Comparing the two chart presentations unfolds their pinned tensor witnesses once.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The chart comparison intertwines the exact affine-open inclusion. -/
theorem chartBaseChangeIso_hom_ι
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    (chartBaseChangeIso C P U).hom ≫ U.1.1.ι =
      (chartRingBaseChangeIso C P U).hom ≫ U.1.2.fromSpec := by
  calc
    _ = (chartRingBaseChangeIso C P U).hom ≫
        (U.1.2.isoSpec.inv ≫ U.1.1.ι) := by
      simp only [chartBaseChangeIso, chartRingBaseChangeIso,
        chartBaseChangeMap, chartFinalBaseChangeEquiv, affineBaseChangeIso,
        Iso.trans_hom, Iso.symm_hom, Category.assoc]
    _ = _ := congrArg (fun q => (chartRingBaseChangeIso C P U).hom ≫ q)
      U.1.2.isoSpec_inv_ι

set_option synthInstance.maxHeartbeats 3200000 in
-- Keep the glued-chart projection in the pinned chart comparison normal form.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The glued chart comparison intertwines the exact affine-open inclusion. -/
theorem gluingChartIso_hom_ι
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    (gluingChartIso C P U).hom ≫ U.1.1.ι =
      (pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom ≫
        (chartRingBaseChangeIso C P U).hom ≫ U.1.2.fromSpec := by
  change
    ((pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom ≫
      (chartBaseChangeIso C P U).hom) ≫ U.1.1.ι = _
  calc
    _ = (pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom ≫
        ((chartBaseChangeIso C P U).hom ≫ U.1.1.ι) :=
      Category.assoc _ _ _
    _ = _ := congrArg
      (fun q => (pullback.congrHom (glueData_ι_gluedMap C P U) rfl).hom ≫ q)
      (chartBaseChangeIso_hom_ι C P U)

set_option synthInstance.maxHeartbeats 3200000 in
set_option maxHeartbeats 12800000 in
/-- The chart comparison carries the scalar-extension structure map to the
second projection of the chart pullback. -/
theorem chartRingBaseChangeIso_hom_structureMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    (chartRingBaseChangeIso C P U).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (Pic0FiniteStageRing C (Sum.inl U)))) =
      pullback.snd (chartBaseChangeMap C P U)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
  letI : CommRing
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    pic0FiniteStageChartBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U
  letI : CommSemiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    (inferInstance : CommRing
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    (inferInstance : CommSemiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)).toSemiring
  letI : Algebra P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    pic0FiniteStageChartBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U
  letI : CommRing
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    @Algebra.TensorProduct.instCommRing P.N.1 k
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)
      (inferInstance : CommSemiring P.N.1) (inferInstance : CommRing k)
      (inferInstance : Algebra P.N.1 k)
      (inferInstance : CommSemiring
        (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U))
      (inferInstance : Algebra P.N.1
        (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U))
  letI : CommSemiring
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    (inferInstance : CommRing
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)).toCommSemiring
  letI : Semiring
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
      (Sum.inl U)
  letI : Algebra k
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
      (Sum.inl U)
  change
    (affineBaseChangeIso P.N.1 k
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) ≪≫
      Scheme.Spec.mapIso
        (chartFinalBaseChangeEquiv C P U).symm.toRingEquiv.toCommRingCatIso.op).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap k (Pic0FiniteStageRing C (Sum.inl U)))) = _
  exact affineBaseChangeIso_hom_structureMap
    (chartFinalBaseChangeEquiv C P U)

set_option synthInstance.maxHeartbeats 3200000 in
-- The overlap comparison elaborates the package's dependent scalar towers.
set_option maxHeartbeats 12800000 in
/-- Base change of a finite-stage overlap recovers the corresponding exact affine overlap. -/
noncomputable def overlapBaseChangeIso
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    pullback (overlapBaseChangeMap C P U V)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≅
      (pic0FiniteStageAffineOverlap C U V).1.toScheme :=
  letI : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V
  letI : Algebra P.N.1
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V
  letI : Algebra P.N.1
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
    pic0FiniteStageFinalModelRingAlgebra C P.L P.n P.m P.relation P.M P.N
      (Sum.inr (U, V))
  letI : Module P.N.1
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
    pic0FiniteStageFinalModelRingModule C P.L P.n P.m P.relation P.M P.N
      (Sum.inr (U, V))
  letI : CommRing
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
    pic0FiniteStageFinalModelRingCommRing C P.L P.n P.m P.relation P.M P.N
      (Sum.inr (U, V))
  letI : CommSemiring
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
    (inferInstance : CommRing
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
    (pic0FiniteStageFinalModelRingCommSemiring C P.L P.n P.m P.relation P.M P.N
      (Sum.inr (U, V))).toSemiring
  letI : CommRing
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
    @Algebra.TensorProduct.instCommRing P.N.1 k
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (inferInstance : CommSemiring P.N.1)
      (inferInstance : CommRing k)
      (inferInstance : Algebra P.N.1 k)
      (inferInstance : CommSemiring
        (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
          (Sum.inr (U, V))))
      (pic0FiniteStageFinalModelRingAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
  letI : CommSemiring
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
    (inferInstance : CommRing
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))).toCommSemiring
  letI : Semiring
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
    (inferInstance : CommSemiring
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))).toSemiring
  letI : Algebra k
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
    pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
      (Sum.inr (U, V))
  pullbackSymmetry _ _ ≪≫
    pullbackSpecIso P.N.1 k
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V) ≪≫
    Scheme.Spec.mapIso
      (pic0FiniteStageFinalBaseChangeEquiv
        C P.L P.n P.m P.relation P.e P.M P.N
          (Sum.inr (U, V))).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (pic0FiniteStageAffineOverlap C U V).2.isoSpec.symm

set_option synthInstance.maxHeartbeats 3200000 in
-- Comparing the two overlap presentations unfolds their pinned tensor witnesses once.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The overlap comparison intertwines the exact affine-open inclusion. -/
theorem overlapBaseChangeIso_hom_ι
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (overlapBaseChangeIso C P U V).hom ≫
        (pic0FiniteStageAffineOverlap C U V).1.ι =
      (overlapRingBaseChangeIso C P U V).hom ≫
        (pic0FiniteStageAffineOverlap C U V).2.fromSpec := by
  calc
    _ = (overlapRingBaseChangeIso C P U V).hom ≫
        ((pic0FiniteStageAffineOverlap C U V).2.isoSpec.inv ≫
          (pic0FiniteStageAffineOverlap C U V).1.ι) := by
      simp only [overlapBaseChangeIso, overlapRingBaseChangeIso,
        overlapBaseChangeMap, overlapBaseChangeStructureRingHom,
        overlapFinalBaseChangeEquiv, affineBaseChangeIso, Iso.trans_hom,
        Iso.symm_hom, Category.assoc]
    _ = _ := congrArg
      (fun q => (overlapRingBaseChangeIso C P U V).hom ≫ q)
      (pic0FiniteStageAffineOverlap C U V).2.isoSpec_inv_ι

set_option synthInstance.maxHeartbeats 3200000 in
-- Normalize the right atlas projection at the overlap comparison boundary.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The overlap comparison carries the exact right atlas projection to the
pinned finite-stage overlap projection. -/
theorem overlapBaseChangeIso_hom_atlas_t_f_ι
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (overlapBaseChangeIso C P U V).hom ≫
        ((pic0SepClosedAtlasOverlapIso C U V).hom ≫
          (((pic0SepClosedAtlasGlueData C).t U V ≫
            (pic0SepClosedAtlasGlueData C).f V U) ≫ V.1.1.ι)) =
      (overlapRingBaseChangeIso C P U V).hom ≫
        (pic0FiniteStageAffineOverlap C U V).2.fromSpec := by
  have atlas_projection :
      (pic0SepClosedAtlasOverlapIso C U V).hom ≫
          (((pic0SepClosedAtlasGlueData C).t U V ≫
            (pic0SepClosedAtlasGlueData C).f V U) ≫ V.1.1.ι) =
        (pic0FiniteStageAffineOverlap C U V).1.ι := by
    calc
      _ = ((pic0_sepClosed_representableBy (C := C)).1.left.homOfLE
            (pic0FiniteStageAffineOverlap_le_right C U V)) ≫ V.1.1.ι := by
        simpa only [Category.assoc] using
          pic0SepClosedAtlasOverlapIso_hom_t_f_assoc C U V V.1.1.ι
      _ = _ := Scheme.homOfLE_ι _ _
  calc
    _ = (overlapBaseChangeIso C P U V).hom ≫
        (pic0FiniteStageAffineOverlap C U V).1.ι :=
      congrArg (fun q => (overlapBaseChangeIso C P U V).hom ≫ q)
        atlas_projection
    _ = _ := overlapBaseChangeIso_hom_ι C P U V

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
