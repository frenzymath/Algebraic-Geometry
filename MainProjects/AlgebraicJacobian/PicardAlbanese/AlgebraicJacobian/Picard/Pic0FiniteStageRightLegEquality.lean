/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluePackage

/-!
# The right leg of the finite-stage Picard glue datum

The transition from the reversed overlap carries its left restriction to the
right restriction of the forward overlap.  This file reflects that identity to
the finite stage and then extends it to the final finite subextension.
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

/-- On the exact Picard atlas, transition from the reversed overlap followed
by its left restriction is the right restriction of the forward overlap. -/
theorem transition_comp_restrictionLeft_eq_restrictionRight
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageTransition C (U, V)).comp
        (pic0FiniteStageRestrictionLeft C V U) =
      pic0FiniteStageRestrictionRight C U V := by
  apply DFunLike.ext _ _
  intro x
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  let hLeft : V.1.1 ⊓ U.1.1 ≤ V.1.1 :=
    pic0FiniteStageAffineOverlap_le_left C V U
  let hTransition : U.1.1 ⊓ V.1.1 ≤ V.1.1 ⊓ U.1.1 := by
    rw [inf_comm]
  let hRight : U.1.1 ⊓ V.1.1 ≤ V.1.1 :=
    pic0FiniteStageAffineOverlap_le_right C U V
  change (J.left.resHom hTransition) ((J.left.resHom hLeft) x) =
    (J.left.resHom hRight) x
  calc
    _ = (J.left.resHom (hTransition.trans hLeft)) x :=
      Scheme.resHom_resHom hLeft hTransition x
    _ = (J.left.resHom hRight) x := by rfl

/-- The exact right-leg equation transported to the ambient tensor-product
models used by the finite-stage package. -/
theorem transportedMap_transition_comp_restrictionLeft_eq_right
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageTransportedMap C P.L P.n P.m P.relation P.e
        (Sum.inr (U, V))).comp
        (pic0FiniteStageTransportedMap C P.L P.n P.m P.relation P.e
          (Sum.inl (Sum.inl (V, U)))) =
      pic0FiniteStageTransportedMap C P.L P.n P.m P.relation P.e
        (Sum.inl (Sum.inr (U, V))) := by
  have hExact := transition_comp_restrictionLeft_eq_restrictionRight C U V
  apply DFunLike.ext _ _
  intro x
  change
    (P.e (Sum.inr (U, V))).symm
      (pic0FiniteStageTransition C (U, V)
        ((P.e (Sum.inr (V, U)))
          ((P.e (Sum.inr (V, U))).symm
            (pic0FiniteStageRestrictionLeft C V U ((P.e (Sum.inl V)) x))))) =
    (P.e (Sum.inr (U, V))).symm
      (pic0FiniteStageRestrictionRight C U V ((P.e (Sum.inl V)) x))
  rw [(P.e (Sum.inr (V, U))).apply_symm_apply]
  exact congrArg (P.e (Sum.inr (U, V))).symm
    (DFunLike.congr_fun hExact ((P.e (Sum.inl V)) x))

set_option synthInstance.maxHeartbeats 3200000 in
-- The reflected maps retain distinct dependent tensor-product instances.
set_option maxHeartbeats 12800000 in
-- The three reflected maps retain distinct dependent tensor-product carriers.
/-- The descended transition followed by the descended reversed left
restriction is the descended forward right restriction. -/
theorem mapM_transition_comp_restrictionLeft_eq_right
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (P.mapM (Sum.inr (U, V))).comp
        (P.mapM (Sum.inl (Sum.inl (V, U)))) =
      P.mapM (Sum.inl (Sum.inr (U, V))) := by
  apply DatG0.tensorProduct_algHom_comp_eq_of_baseChange P.M
    (P.mapM (Sum.inl (Sum.inl (V, U))))
    (P.mapM (Sum.inr (U, V)))
    (P.mapM (Sum.inl (Sum.inr (U, V))))
    (pic0FiniteStageTransportedMap C P.L P.n P.m P.relation P.e
      (Sum.inl (Sum.inl (V, U))))
    (pic0FiniteStageTransportedMap C P.L P.n P.m P.relation P.e
      (Sum.inr (U, V)))
    (pic0FiniteStageTransportedMap C P.L P.n P.m P.relation P.e
      (Sum.inl (Sum.inr (U, V))))
  · exact P.hmapM (Sum.inl (Sum.inl (V, U)))
  · exact P.hmapM (Sum.inr (U, V))
  · exact P.hmapM (Sum.inl (Sum.inr (U, V)))
  · exact transportedMap_transition_comp_restrictionLeft_eq_right C P U V

set_option synthInstance.maxHeartbeats 3200000 in
-- The scalar extensions retain indexed source and target instances.
set_option maxHeartbeats 12800000 in
-- Both scalar extensions retain the indexed source and target model rings.
/-- Scalar extension to the package's final finite subextension preserves the
transition/restriction equation.  The statement keeps the three package maps
explicit so it does not inherit unrelated axioms from legacy wrapper aliases. -/
theorem scalarExtension_transition_comp_restrictionLeft_eq_right
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (AlgebraicJacobian.scalarExtensionMapOfAlgHom (R := P.M.1) (K := P.N.1)
      (P.mapM (Sum.inr (U, V)))).comp
      (AlgebraicJacobian.scalarExtensionMapOfAlgHom (R := P.M.1) (K := P.N.1)
        (P.mapM (Sum.inl (Sum.inl (V, U))))) =
    AlgebraicJacobian.scalarExtensionMapOfAlgHom (R := P.M.1) (K := P.N.1)
      (P.mapM (Sum.inl (Sum.inr (U, V)))) := by
  rw [AlgebraicJacobian.scalarExtensionMapOfAlgHom_comp,
    mapM_transition_comp_restrictionLeft_eq_right C P U V]
  rfl

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
