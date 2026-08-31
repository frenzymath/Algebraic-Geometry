/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageFinalBaseChange
import AlgebraicJacobian.Picard.Pic0FiniteStageGluedOver

/-!
# Base change of the finite-stage Picard charts

Each chart inclusion in the finite-stage glue lies over its affine structure map.
After extending from the final finite subextension to the separably closed field,
the affine pullback formula and the final ring comparison identify that chart with
the corresponding chart in the exact Picard atlas.
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
-- Projecting the package retains the nested finite-subextension scalar towers.
set_option maxHeartbeats 12800000 in
/-- Every finite-stage chart inclusion lies over the chart's affine structure map. -/
@[reassoc]
theorem glueData_ι_gluedMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    P.glueData.ι U ≫ P.gluedMap =
      chartBaseChangeMap C P U := by
  simpa only [gluedMap_presentation, presentation_glueData, presentation_mapData,
    gluedMapData_chartMap] using P.presentation.chartMap_factor U

set_option synthInstance.maxHeartbeats 3200000 in
-- The composite infers the same nested tensor-product instances as the ring comparison.
set_option maxHeartbeats 12800000 in
/-- Base change of a finite-stage affine chart recovers the corresponding chart in the
exact separably closed Picard atlas. -/
noncomputable def chartBaseChangeIso
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    pullback (chartBaseChangeMap C P U)
      (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≅
      (pic0SepClosedAtlasOpenCover C).X U := by
  letI : Algebra P.N.1
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U)) :=
    pic0FiniteStageFinalModelRingAlgebra C P.L P.n P.m P.relation P.M P.N
      (Sum.inl U)
  letI : Module P.N.1
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U)) :=
    pic0FiniteStageFinalModelRingModule C P.L P.n P.m P.relation P.M P.N
      (Sum.inl U)
  letI : CommRing
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U)) :=
    pic0FiniteStageFinalModelRingCommRing C P.L P.n P.m P.relation P.M P.N
      (Sum.inl U)
  letI : CommSemiring
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U)) :=
    (inferInstance : CommRing
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U))).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U)) :=
    (pic0FiniteStageFinalModelRingCommSemiring C P.L P.n P.m P.relation P.M P.N
      (Sum.inl U)).toSemiring
  letI : CommRing
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U)) :=
    @Algebra.TensorProduct.instCommRing P.N.1 k
      (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N (Sum.inl U))
      (inferInstance : CommSemiring P.N.1)
      (inferInstance : CommRing k)
      (inferInstance : Algebra P.N.1 k)
      (inferInstance : CommSemiring
        (Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N (Sum.inl U)))
      (pic0FiniteStageFinalModelRingAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U))
  letI : CommSemiring
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U)) :=
    (inferInstance : CommRing
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U))).toCommSemiring
  letI : Semiring
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U)) :=
    (inferInstance : CommSemiring
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U))).toSemiring
  letI : Algebra k
      (k ⊗[P.N.1] Pic0FiniteStageFinalModelRing C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U)) :=
    pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
      (Sum.inl U)
  exact pullbackSymmetry _ _ ≪≫
      pullbackSpecIso P.N.1 k
        (Pic0FiniteStageChartBaseChangeRing
          C P.L P.n P.m P.relation P.M P.N U) ≪≫
      Scheme.Spec.mapIso
        (pic0FiniteStageFinalBaseChangeEquiv
          C P.L P.n P.m P.relation P.e P.M P.N
            (Sum.inl U)).symm.toRingEquiv.toCommRingCatIso.op ≪≫
      U.1.2.isoSpec.symm

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
