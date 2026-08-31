/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageChartBaseChange

/-!
# Basic geometry of the finite-stage Picard glue

The finite-stage glue is covered by finitely many affine spectra of explicit
finite-presentation algebras over its field of definition.  Consequently its structure
morphism is locally of finite type and quasi-compact, without any additional geometric
hypothesis on the package.
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

namespace Pic0FiniteStageGluePackage

set_option synthInstance.maxHeartbeats 3200000 in
-- The chart rings retain two nested finite-subextension tensor products.
set_option maxHeartbeats 12800000 in
/-- The structure morphism of the finite-stage Picard glue is locally of finite type. -/
theorem locallyOfFiniteType_gluedMap
    (P : Pic0FiniteStageGluePackage C F) :
    LocallyOfFiniteType P.gluedMap := by
  apply IsZariskiLocalAtSource.of_openCover P.glueData.openCover
  intro U
  change LocallyOfFiniteType (P.glueData.ι U ≫ P.gluedMap)
  rw [glueData_ι_gluedMap C P U]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

instance instLocallyOfFiniteTypeGluedMap
    (P : Pic0FiniteStageGluePackage C F) :
    LocallyOfFiniteType P.gluedMap :=
  locallyOfFiniteType_gluedMap C P

set_option synthInstance.maxHeartbeats 3200000 in
-- Unfolding the dependent affine glue identifies its finite spectrum charts.
set_option maxHeartbeats 12800000 in
/-- The structure morphism of the finite-stage Picard glue is quasi-compact. -/
theorem quasiCompact_gluedMap
    (P : Pic0FiniteStageGluePackage C F) :
    QuasiCompact P.gluedMap := by
  haveI : Finite P.glueData.openCover.I₀ := by
    change Finite (Pic0FiniteStageChartIndex C)
    infer_instance
  haveI : ∀ U, CompactSpace (P.glueData.openCover.X U) := by
    intro U
    change CompactSpace
      (Spec (CommRingCat.of
        (Pic0FiniteStageChartBaseChangeRing
          C P.L P.n P.m P.relation P.M P.N U)))
    infer_instance
  haveI : CompactSpace P.glueData.glued :=
    P.glueData.openCover.compactSpace
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr
    (inferInstance : CompactSpace P.glueData.glued)

instance instQuasiCompactGluedMap
    (P : Pic0FiniteStageGluePackage C F) :
    QuasiCompact P.gluedMap :=
  quasiCompact_gluedMap C P

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
