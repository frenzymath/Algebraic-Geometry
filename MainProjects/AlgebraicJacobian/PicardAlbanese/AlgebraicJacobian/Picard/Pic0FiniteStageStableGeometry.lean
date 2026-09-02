/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageChartBaseChange
import AlgebraicJacobian.Picard.Pic0FiniteStageStableGluePackage

/-!
# Basic geometry of the stable finite-stage Picard glue

The stable package keeps its canonical presentation behind a sealed boundary.  These
theorems expose the geometric properties that follow from its finite affine chart cover,
without reconstructing the legacy package or requiring a projectivity hypothesis.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

variable {k F : Type u} [Field k] [Field F]
variable [Algebra F k] [Algebra.IsAlgebraic F k]
variable (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageStableGluePackage

set_option synthInstance.maxHeartbeats 3200000 in
-- The canonical presentation retains nested finite-subextension tensor carriers.
set_option maxHeartbeats 12800000 in
/-- The structure morphism of a stable finite-stage Picard glue is locally of finite type. -/
theorem locallyOfFiniteType_gluedMap
    (P : Pic0FiniteStageStableGluePackage C F) :
    LocallyOfFiniteType P.gluedMap := by
  let D := pic0FiniteStageAffineRingGluePresentation_of_canonical_context C P.context
  have aux : ∀ (A : AlgebraicJacobian.AffineRingGluePresentation P.context.triple.N.1),
      A = D → LocallyOfFiniteType A.map := by
    intro A hA
    subst A
    apply IsZariskiLocalAtSource.of_openCover D.glueData.openCover
    intro U
    change LocallyOfFiniteType (D.glueData.ι U ≫ D.map)
    rw [D.chartMap_factor]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr
        (AlgebraicGeometry.Pic0FiniteStageGluePackage.finiteType_pic0FiniteStageChartBaseChangeRing
          C P.context.models.L P.context.models.n P.context.models.m
            P.context.models.relation P.context.models.M P.context.triple.N U))
  exact aux P.presentation (P.presentation_spec C)

instance instLocallyOfFiniteTypeGluedMap
    (P : Pic0FiniteStageStableGluePackage C F) :
    LocallyOfFiniteType P.gluedMap :=
  locallyOfFiniteType_gluedMap C P

set_option synthInstance.maxHeartbeats 3200000 in
-- The canonical presentation retains nested finite-subextension tensor carriers.
set_option maxHeartbeats 12800000 in
/-- The structure morphism of a stable finite-stage Picard glue is quasi-compact. -/
theorem quasiCompact_gluedMap
    (P : Pic0FiniteStageStableGluePackage C F) :
    QuasiCompact P.gluedMap := by
  let D := pic0FiniteStageAffineRingGluePresentation_of_canonical_context C P.context
  have aux : ∀ (A : AlgebraicJacobian.AffineRingGluePresentation P.context.triple.N.1),
      A = D → QuasiCompact A.map := by
    intro A hA
    subst A
    haveI : Finite D.glueData.openCover.I₀ := by
      change Finite (Pic0FiniteStageChartIndex C)
      infer_instance
    haveI : ∀ U, CompactSpace (D.glueData.openCover.X U) := by
      intro U
      change CompactSpace
        (Spec (CommRingCat.of
          (Pic0FiniteStageChartBaseChangeRing
            C P.context.models.L P.context.models.n P.context.models.m
              P.context.models.relation P.context.models.M P.context.triple.N U)))
      infer_instance
    haveI : CompactSpace D.glueData.glued :=
      D.glueData.openCover.compactSpace
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr
      (inferInstance : CompactSpace D.glueData.glued)
  exact aux P.presentation (P.presentation_spec C)

instance instQuasiCompactGluedMap
    (P : Pic0FiniteStageStableGluePackage C F) :
    QuasiCompact P.gluedMap :=
  quasiCompact_gluedMap C P

end Pic0FiniteStageStableGluePackage

end

end AlgebraicGeometry
