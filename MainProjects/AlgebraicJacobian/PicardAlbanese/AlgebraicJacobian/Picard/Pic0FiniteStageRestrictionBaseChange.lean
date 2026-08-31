/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageAffineBaseChange

/-!
# Naturality of finite-stage Picard restrictions after base change

The restriction legs in a finite-stage glue package are affine morphisms over the
final finite subextension.  Their pullbacks to the separably closed field agree,
under the final ring comparisons, with the canonical restrictions in the exact
Picard atlas.
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

-- Pin the descended restriction to the same nested tensor witnesses used by the
-- final-stage affine comparison APIs.  The raw scalar-extension definition
-- otherwise asks typeclass search to reconstruct the dependent model carrier.
noncomputable def restrictionBaseChangeAlgHomCanonical
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
      (inferInstance : CommSemiring P.N.1)
      (pic0FiniteStageChartBaseChangeCommRing C P.L P.n P.m P.relation P.M P.N U).toSemiring
      (pic0FiniteStageOverlapBaseChangeCommRing C P.L P.n P.m P.relation P.M P.N U V).toSemiring
      (pic0FiniteStageChartBaseChangeAlgebra C P.L P.n P.m P.relation P.M P.N U)
      (pic0FiniteStageOverlapBaseChangeAlgebra C P.L P.n P.m P.relation P.M P.N U V) :=
  pic0FiniteStageRestrictionBaseChange
    C P.L P.n P.m P.relation P.M P.mapM P.N U V

set_option synthInstance.maxHeartbeats 3200000 in
-- Projecting the package unfolds the dependent finite-subextension towers.
set_option maxHeartbeats 12800000 in
/-- The left restriction leg of the glue package is the spectrum of the
scalar-extended descended restriction. -/
theorem glueData_f
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    P.glueData.f U V =
      Spec.map (CommRingCat.ofHom
        (restrictionBaseChangeAlgHomCanonical C P U V).toRingHom) := by
  rfl

set_option synthInstance.maxHeartbeats 3200000 in
-- The annotation fixes the source and target instances hidden by dependent indices.
set_option maxHeartbeats 12800000 in
/-- The scalar-extended descended restriction, with its chart and overlap types
fixed opaquely for use by the affine base-change API. -/
noncomputable def restrictionBaseChangeAlgHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
      (inferInstance : CommSemiring P.N.1)
      (pic0FiniteStageChartBaseChangeCommRing C P.L P.n P.m P.relation P.M P.N U).toSemiring
      (pic0FiniteStageOverlapBaseChangeCommRing C P.L P.n P.m P.relation P.M P.N U V).toSemiring
      (pic0FiniteStageChartBaseChangeAlgebra C P.L P.n P.m P.relation P.M P.N U)
      (pic0FiniteStageOverlapBaseChangeAlgebra C P.L P.n P.m P.relation P.M P.N U V) :=
  restrictionBaseChangeAlgHomCanonical C P U V

set_option synthInstance.maxHeartbeats 3200000 in
-- The pinned wrapper is used only to export a typeclass-independent ring homomorphism.
set_option maxHeartbeats 12800000 in
/-- The descended restriction with the same explicit tensor witnesses as the named
chart and overlap structure maps. -/
noncomputable def restrictionBaseChangeAlgHomPinned
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
      (inferInstance : CommSemiring P.N.1)
      (pic0FiniteStageChartBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N U).toSemiring
      (pic0FiniteStageOverlapBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N U V).toSemiring
      (pic0FiniteStageChartBaseChangeRingAlgebra
        C P.L P.n P.m P.relation P.M P.N U)
      (pic0FiniteStageOverlapBaseChangeRingAlgebra
        C P.L P.n P.m P.relation P.M P.N U V) :=
  restrictionBaseChangeAlgHomCanonical C P U V

set_option synthInstance.maxHeartbeats 3200000 in
-- Projecting the pinned algebra hom fixes both dependent tensor witnesses.
set_option maxHeartbeats 12800000 in
/-- The descended restriction as a ring homomorphism with all carrier structures
fixed in its type.  Downstream scheme statements can use this without synthesizing
dependent `Algebra` instances. -/
noncomputable def restrictionBaseChangeRingHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @RingHom
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
      (pic0FiniteStageChartBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N U).toNonAssocSemiring
      (pic0FiniteStageOverlapBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N U V).toNonAssocSemiring :=
  @AlgHom.toRingHom P.N.1
    (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)
    (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
    (inferInstance : CommSemiring P.N.1)
    (pic0FiniteStageChartBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U).toSemiring
    (pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V).toSemiring
    (pic0FiniteStageChartBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U)
    (pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V)
    (restrictionBaseChangeAlgHomPinned C P U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- The structure map retains the chart tensor witnesses in its public type.
set_option maxHeartbeats 12800000 in
/-- The pinned ring homomorphism underlying a finite-stage chart's structure map. -/
noncomputable def chartBaseChangeStructureRingHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    @RingHom P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)
      (inferInstance : NonAssocSemiring P.N.1)
      (pic0FiniteStageChartBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N U).toNonAssocSemiring :=
  @algebraMap P.N.1
    (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)
    (inferInstance : CommSemiring P.N.1)
    (pic0FiniteStageChartBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U).toSemiring
    (pic0FiniteStageChartBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U)

set_option synthInstance.maxHeartbeats 3200000 in
-- The structure map retains the overlap tensor witnesses in its public type.
set_option maxHeartbeats 12800000 in
/-- The pinned ring homomorphism underlying a finite-stage overlap's structure map. -/
noncomputable def overlapBaseChangeStructureRingHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @RingHom P.N.1
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
      (inferInstance : NonAssocSemiring P.N.1)
      (pic0FiniteStageOverlapBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N U V).toNonAssocSemiring :=
  @algebraMap P.N.1
    (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
    (inferInstance : CommSemiring P.N.1)
    (pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V).toSemiring
    (pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- The equality uses the explicitly pinned algebra-homomorphism witnesses.
set_option maxHeartbeats 12800000 in
/-- The pinned restriction preserves the named chart and overlap structure maps. -/
theorem restrictionBaseChangeRingHom_comp_structure
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (restrictionBaseChangeRingHom C P U V).comp
        (chartBaseChangeStructureRingHom C P U) =
      overlapBaseChangeStructureRingHom C P U V := by
  ext x
  exact @AlgHom.commutes P.N.1
    (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)
    (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
    (inferInstance : CommSemiring P.N.1)
    (pic0FiniteStageChartBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U).toSemiring
    (pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V).toSemiring
    (pic0FiniteStageChartBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U)
    (pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V)
    (restrictionBaseChangeAlgHomPinned C P U V) x

set_option synthInstance.maxHeartbeats 3200000 in
-- Relating the raw glue leg to the pinned wrapper unfolds the package presentation once.
set_option maxHeartbeats 12800000 in
/-- The left glue leg is the spectrum of the pinned restriction ring homomorphism. -/
theorem glueData_f_pinned
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    P.glueData.f U V = Spec.map (CommRingCat.ofHom
      (restrictionBaseChangeRingHom C P U V)) := by
  rw [glueData_f C P U V]
  rfl

set_option synthInstance.maxHeartbeats 3200000 in
-- The scheme map is exposed independently of global instance search.
set_option maxHeartbeats 12800000 in
/-- The named chart map is the spectrum of the pinned chart structure ring homomorphism. -/
theorem chartBaseChangeMap_eq_spec
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    chartBaseChangeMap C P U = Spec.map (CommRingCat.ofHom
      (chartBaseChangeStructureRingHom C P U)) := by
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- The explicit map fixes the overlap's dependent tensor witnesses.
set_option maxHeartbeats 12800000 in
/-- The pinned structure map from a finite-stage overlap to its field of definition. -/
noncomputable def overlapBaseChangeMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    Spec (CommRingCat.of
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V)) ⟶ Spec (.of P.N.1) :=
  Spec.map (CommRingCat.ofHom
    (overlapBaseChangeStructureRingHom C P U V))

set_option synthInstance.maxHeartbeats 3200000 in
-- Functoriality now consumes only named ring homomorphisms with fixed structures.
set_option maxHeartbeats 12800000 in
/-- The finite-stage restriction followed by the chart structure map is the
overlap structure map. -/
theorem restrictionSpecMap_comp_chartBaseChangeMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    Spec.map (CommRingCat.ofHom (restrictionBaseChangeRingHom C P U V)) ≫
        chartBaseChangeMap C P U =
      overlapBaseChangeMap C P U V := by
  rw [chartBaseChangeMap_eq_spec]
  unfold overlapBaseChangeMap
  rw [← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp]
  rw [restrictionBaseChangeRingHom_comp_structure]

/-- The exact left restriction with indexed source and target rings.  Keeping
the indexed rings avoids relying on typeclass transparency for their aliases. -/
noncomputable def exactRestrictionAlgHom
    (U V : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageRing C (Sum.inl U) →ₐ[k]
      Pic0FiniteStageRing C (Sum.inr (U, V)) :=
  pic0FiniteStageMap C (Sum.inl (Sum.inl (U, V)))

set_option synthInstance.maxHeartbeats 3200000 in
-- The annotation fixes the indexed exact-ring instance on the chart target.
set_option maxHeartbeats 12800000 in
/-- Final scalar-extension comparison for a chart, with an indexed exact-ring
target. -/
noncomputable def chartFinalBaseChangeEquiv
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    @AlgEquiv k
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing
          C P.L P.n P.m P.relation P.M P.N U)
      (Pic0FiniteStageRing C (Sum.inl U))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U))
      (instCommRingPic0FiniteStageRing C (Sum.inl U)).toSemiring
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U))
      (instAlgebraPic0FiniteStageRing C (Sum.inl U)) :=
  pic0FiniteStageFinalBaseChangeEquiv
    C P.L P.n P.m P.relation P.e P.M P.N (Sum.inl U)

set_option synthInstance.maxHeartbeats 3200000 in
-- The annotation fixes the indexed exact-ring instance on the overlap target.
set_option maxHeartbeats 12800000 in
/-- Final scalar-extension comparison for an overlap, with an indexed
exact-ring target. -/
noncomputable def overlapFinalBaseChangeEquiv
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgEquiv k
      (k ⊗[P.N.1]
        Pic0FiniteStageOverlapBaseChangeRing
          C P.L P.n P.m P.relation P.M P.N U V)
      (Pic0FiniteStageRing C (Sum.inr (U, V)))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (instCommRingPic0FiniteStageRing C (Sum.inr (U, V))).toSemiring
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (instAlgebraPic0FiniteStageRing C (Sum.inr (U, V))) :=
  pic0FiniteStageFinalBaseChangeEquiv
    C P.L P.n P.m P.relation P.e P.M P.N (Sum.inr (U, V))

set_option synthInstance.maxHeartbeats 3200000 in
-- Specializing the generic pullback map infers both scalar-extended model rings.
set_option maxHeartbeats 12800000 in
/-- Pullback of a finite-stage left restriction from an overlap to its left
chart. -/
noncomputable def restrictionBaseChangeMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    pullback (overlapBaseChangeMap C P U V)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ⟶
      pullback (chartBaseChangeMap C P U)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
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
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V
  letI : CommSemiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V)).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommSemiring
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V)).toSemiring
  letI : Algebra P.N.1
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V
  affineBaseChangeMap P.N.1 k
    (Pic0FiniteStageChartBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N U)
    (Pic0FiniteStageOverlapBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N U V)
    (restrictionBaseChangeAlgHomPinned C P U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- Projecting the pinned map still exposes the package's dependent tensor carriers.
set_option maxHeartbeats 12800000 in
/-- The pulled-back restriction has the expected map on the affine projection.

The pullback objects are inferred from `restrictionBaseChangeMap`, so consumers do
not have to reconstruct the dependent chart and overlap ring instances. -/
theorem restrictionBaseChangeMap_fst
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    restrictionBaseChangeMap C P U V ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom
        (restrictionBaseChangeRingHom C P U V)) := by
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
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V
  letI : CommSemiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V)).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommSemiring
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V)).toSemiring
  letI : Algebra P.N.1
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V
  unfold restrictionBaseChangeMap
  exact affineBaseChangeMap_fst P.N.1 k
    (Pic0FiniteStageChartBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N U)
    (Pic0FiniteStageOverlapBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N U V)
    (restrictionBaseChangeAlgHomPinned C P U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- Projecting the pinned map still exposes the package's dependent tensor carriers.
set_option maxHeartbeats 12800000 in
/-- The pulled-back restriction is the identity on the base projection. -/
theorem restrictionBaseChangeMap_snd
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    restrictionBaseChangeMap C P U V ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
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
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V
  letI : CommSemiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V)).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommSemiring
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V)).toSemiring
  letI : Algebra P.N.1
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V
  unfold restrictionBaseChangeMap
  exact affineBaseChangeMap_snd P.N.1 k
    (Pic0FiniteStageChartBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N U)
    (Pic0FiniteStageOverlapBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N U V)
    (restrictionBaseChangeAlgHomPinned C P U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- The chart comparison cancels the package's nested scalar extensions.
set_option maxHeartbeats 12800000 in
/-- The tensor-product and final-ring comparison for a chart, before applying
the chart's affine-open identification. -/
noncomputable def chartRingBaseChangeIso
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    pullback (chartBaseChangeMap C P U)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≅
      Spec (.of (Pic0FiniteStageRing C (Sum.inl U))) :=
  by
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
    exact affineBaseChangeIso P.N.1 k
        (Pic0FiniteStageChartBaseChangeRing
          C P.L P.n P.m P.relation P.M P.N U) ≪≫
      Scheme.Spec.mapIso
        (chartFinalBaseChangeEquiv C P U).symm.toRingEquiv.toCommRingCatIso.op

set_option synthInstance.maxHeartbeats 3200000 in
-- The overlap comparison cancels the package's nested scalar extensions.
set_option maxHeartbeats 12800000 in
/-- The tensor-product and final-ring comparison for an overlap, before applying
the overlap's affine-open identification. -/
noncomputable def overlapRingBaseChangeIso
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    pullback (overlapBaseChangeMap C P U V)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≅
      Spec (.of (Pic0FiniteStageRing C (Sum.inr (U, V)))) :=
  by
    letI : CommRing
        (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
      pic0FiniteStageOverlapBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N U V
    letI : CommSemiring
        (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
      (inferInstance : CommRing
        (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)).toCommSemiring
    letI : Semiring
        (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
      (inferInstance : CommSemiring
        (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)).toSemiring
    letI : Algebra P.N.1
        (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
      pic0FiniteStageOverlapBaseChangeRingAlgebra
        C P.L P.n P.m P.relation P.M P.N U V
    letI : CommRing
        (k ⊗[P.N.1]
          Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
      @Algebra.TensorProduct.instCommRing P.N.1 k
        (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
        (inferInstance : CommSemiring P.N.1) (inferInstance : CommRing k)
        (inferInstance : Algebra P.N.1 k)
        (inferInstance : CommSemiring
          (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V))
        (inferInstance : Algebra P.N.1
          (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V))
    letI : CommSemiring
        (k ⊗[P.N.1]
          Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
      (inferInstance : CommRing
        (k ⊗[P.N.1]
          Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)).toCommSemiring
    letI : Semiring
        (k ⊗[P.N.1]
          Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
      pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))
    letI : Algebra k
        (k ⊗[P.N.1]
          Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
      pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))
    exact affineBaseChangeIso P.N.1 k
        (Pic0FiniteStageOverlapBaseChangeRing
          C P.L P.n P.m P.relation P.M P.N U V) ≪≫
      Scheme.Spec.mapIso
        (overlapFinalBaseChangeEquiv C P U V).symm.toRingEquiv.toCommRingCatIso.op

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
