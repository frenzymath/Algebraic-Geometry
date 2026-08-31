/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageRightLegEquality

/-!
# The scalar-extended right finite-stage Picard restriction

The right restriction is the reversed left restriction followed by the ordered-overlap
transition.  Composing the named scalar-extension maps retains their dependent carrier
instances during fresh elaboration.  The composite agrees with the directly descended
right restriction in the indexed finite family.
-/

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageGluePackage

set_option synthInstance.maxHeartbeats 3200000 in
-- The explicit result type fixes the dependent scalar-extension witnesses.
set_option maxHeartbeats 12800000 in
/-- The descended right restriction at the final finite stage.

The transition-after-left-restriction description is propositionally equal to
this direct scalar extension by
`scalarExtension_transition_comp_restrictionLeft_eq_right`. -/
noncomputable def rightRestrictionBaseChangeAlgHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
      (inferInstance : CommSemiring P.N.1)
      (pic0FiniteStageChartBaseChangeCommRing
        C P.L P.n P.m P.relation P.M P.N V).toSemiring
      (pic0FiniteStageOverlapBaseChangeCommRing
        C P.L P.n P.m P.relation P.M P.N U V).toSemiring
      (pic0FiniteStageChartBaseChangeAlgebra
        C P.L P.n P.m P.relation P.M P.N V)
      (pic0FiniteStageOverlapBaseChangeAlgebra
        C P.L P.n P.m P.relation P.M P.N U V) :=
  AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := P.M.1) (K := P.N.1)
    (P.mapM (Sum.inl (Sum.inr (U, V))))

set_option synthInstance.maxHeartbeats 3200000 in
-- The pinned wrapper fixes both dependent tensor-product structures.
set_option maxHeartbeats 12800000 in
/-- The final-stage right restriction with the chart and overlap witnesses used
by the named base-change maps. -/
noncomputable def rightRestrictionBaseChangeAlgHomPinned
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
      (inferInstance : CommSemiring P.N.1)
      (pic0FiniteStageChartBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N V).toSemiring
      (pic0FiniteStageOverlapBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N U V).toSemiring
      (pic0FiniteStageChartBaseChangeRingAlgebra
        C P.L P.n P.m P.relation P.M P.N V)
      (pic0FiniteStageOverlapBaseChangeRingAlgebra
        C P.L P.n P.m P.relation P.M P.N U V) :=
  rightRestrictionBaseChangeAlgHom C P U V

set_option synthInstance.maxHeartbeats 3200000 in
-- Projecting the pinned algebra hom keeps instance search out of scheme statements.
set_option maxHeartbeats 12800000 in
/-- The right restriction as a ring homomorphism with fixed carrier structures. -/
noncomputable def rightRestrictionBaseChangeRingHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) (U V : Pic0FiniteStageChartIndex C) :
    @RingHom
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
      (pic0FiniteStageChartBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N V).toNonAssocSemiring
      (pic0FiniteStageOverlapBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N U V).toNonAssocSemiring :=
  @AlgHom.toRingHom P.N.1
    (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)
    (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
    (inferInstance : CommSemiring P.N.1)
    (pic0FiniteStageChartBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N V).toSemiring
    (pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V).toSemiring
    (pic0FiniteStageChartBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N V)
    (pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V)
    (rightRestrictionBaseChangeAlgHomPinned C P U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- The equality retains the same dependent tensor-product instances.
set_option maxHeartbeats 12800000 in
/-- The composite final-stage right restriction is the directly descended
right restriction in the indexed finite family. -/
theorem rightRestrictionBaseChangeAlgHom_eq_direct
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) (U V : Pic0FiniteStageChartIndex C) :
    rightRestrictionBaseChangeAlgHom C P U V =
      AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := P.M.1) (K := P.N.1)
        (P.mapM (Sum.inl (Sum.inr (U, V)))) := by
  rfl

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
