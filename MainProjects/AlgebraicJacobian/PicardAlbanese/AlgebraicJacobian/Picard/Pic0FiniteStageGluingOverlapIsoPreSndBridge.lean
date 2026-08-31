/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoPreSndCore

/-!
# The exact right-restriction formula for the finite-stage glue datum

This module isolates the dependent transition/restriction composition from the
pullback projection equations that consume it.
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
-- The named scalar-extension maps retain the dependent carrier instances.
set_option maxHeartbeats 12800000 in
-- Functoriality is stated propositionally so later proofs do not rely on deep defeq.
theorem glueData_t_comp_f_eq_spec_rightRestriction
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    P.glueData.t U V ≫ P.glueData.f V U =
      Spec.map (CommRingCat.ofHom
        (rightRestrictionBaseChangeRingHom C P U V)) := by
  rw [glueData_t C P U V, glueData_f C P V U]
  calc
    _ = Spec.map (CommRingCat.ofHom
          ((pic0FiniteStageTransitionBaseChange
            C P.L P.n P.m P.relation P.M P.mapM P.N U V).comp
           (pic0FiniteStageRestrictionBaseChange
            C P.L P.n P.m P.relation P.M P.mapM P.N V U)).toRingHom) :=
      specMap_ringHom_comp
        (pic0FiniteStageRestrictionBaseChange
          C P.L P.n P.m P.relation P.M P.mapM P.N V U).toRingHom
        (pic0FiniteStageTransitionBaseChange
          C P.L P.n P.m P.relation P.M P.mapM P.N U V).toRingHom
    _ = _ := by
      rw [show
        (pic0FiniteStageTransitionBaseChange
            C P.L P.n P.m P.relation P.M P.mapM P.N U V).comp
          (pic0FiniteStageRestrictionBaseChange
            C P.L P.n P.m P.relation P.M P.mapM P.N V U) =
          rightRestrictionBaseChangeAlgHom C P U V from
        scalarExtension_transition_comp_restrictionLeft_eq_right C P U V]
      rfl

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
