/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingDiagramIso
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingRightBaseChange

/-!
# Ring-map formulas for the source factorization of the right gluing leg

This module records the transition formula and generic spectrum-map
functoriality shared by the right gluing comparison.
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
-- Projecting the package unfolds the dependent finite-subextension towers.
set_option maxHeartbeats 12800000 in
-- The explicit transition formula avoids unfolding the full glue datum downstream.
theorem glueData_t
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    P.glueData.t U V =
      Spec.map (CommRingCat.ofHom
        (pic0FiniteStageTransitionBaseChange
          C P.L P.n P.m P.relation P.M P.mapM P.N U V).toRingHom) := by
  rfl

set_option synthInstance.maxHeartbeats 3200000 in
-- Raw ring maps avoid introducing hidden algebra instances in dependent glue carriers.
set_option maxHeartbeats 12800000 in
theorem specMap_ringHom_comp
    {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    (f : A →+* B) (g : B →+* D) :
    Spec.map (CommRingCat.ofHom g) ≫
        Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  calc
    _ = Spec.map (CommRingCat.ofHom f ≫ CommRingCat.ofHom g) :=
      (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm
    _ = _ := congrArg
      (fun q : CommRingCat.of A ⟶ CommRingCat.of D => Spec.map q)
      (CommRingCat.ofHom_comp f g).symm

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
