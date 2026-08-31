/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluePackage
import AlgebraicJacobian.Picard.Pic0FiniteStageGluedOver
import AlgebraicJacobian.Picard.Pic0FiniteStageCanonicalGlueContext
import AlgebraicJacobian.Picard.Pic0FiniteStageStableGluePackage

/-!
# Adapter from the legacy finite-stage glue package

The historical package stores the pair-transition inverse only implicitly (through the
comparison squares).  This module packages those fields as
`Pic0FiniteStageTransitionModelsData`, then builds a canonical context while keeping the
chosen comparison family and its dependent triple data together.  The stable package derives
its presentation from that context, so this adapter never transports a dependent record along
an equality of comparison families.
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

variable {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]

-- The legacy package projections expose dependent tensor-map witnesses.
set_option synthInstance.maxHeartbeats 400000 in
-- The inverse comparison proof normalizes two nested finite-stage tensors.
set_option maxHeartbeats 6400000 in
/-- Repackage the finite-stage models carried by a legacy glue package. -/
noncomputable def toTransitionModelsData
    (P : Pic0FiniteStageGluePackage C F) :
  Pic0FiniteStageTransitionModelsData C F := by
  letI : Algebra.IsAlgebraic P.L.1 k := by infer_instance
  letI : Algebra.IsAlgebraic P.M.1 k := by infer_instance
  refine {
    L := P.L
    n := P.n
    m := P.m
    relation := P.relation
    e := P.e
    M := P.M
    mapM := P.mapM
    comparison := P.hmapM
    openImmersion := ?_
    inverse := ?_ }
  · intro i
    simpa only [Pic0FiniteStageTransitionOpenImmersion,
      pic0FiniteStageModelMapToRingHom] using P.hOpen i
  · intro U V
    apply DatG0.tensorProduct_algHom_comp_eq_of_baseChange P.M
      (P.mapM (Sum.inr (U, V)))
      (P.mapM (Sum.inr (V, U)))
      (AlgHom.id P.M.1
        (Pic0FiniteStageModelRing C P.L P.n P.m P.relation P.M
          (Sum.inr (V, U))))
      (pic0FiniteStageTransportedMap C P.L P.n P.m P.relation P.e
        (Sum.inr (U, V)))
      (pic0FiniteStageTransportedMap C P.L P.n P.m P.relation P.e
        (Sum.inr (V, U)))
      (AlgHom.id k
        (k ⊗[P.L.1] DatG0.FiniteRelationAlgebra P.L.1
          (P.n (Sum.inr (V, U))) (P.m (Sum.inr (V, U)))
          (P.relation (Sum.inr (V, U)))))
    · exact P.hmapM (Sum.inr (U, V))
    · exact P.hmapM (Sum.inr (V, U))
    · ext x
      rfl
    · exact pic0FiniteStageTransportedTransition_inverse
        C P.L P.n P.m P.relation P.e U V

-- Rebuilding the canonical Q/T context specializes those dependent witnesses.
set_option synthInstance.maxHeartbeats 400000 in
-- The dependent Q/T record must be elaborated against the selected family.
set_option maxHeartbeats 6400000 in
/-- Build the canonical context associated to the legacy package. -/
noncomputable def toCanonicalContext
    (P : Pic0FiniteStageGluePackage C F) :
    Pic0FiniteStageCanonicalGlueContext C F := by
  letI : Algebra.IsAlgebraic P.L.1 k := by infer_instance
  letI : Algebra.IsAlgebraic P.M.1 k := by infer_instance
  let D := P.toTransitionModelsData
  let Q := pic0FiniteStageTripleModelComparisonFamily
    C D.L D.n D.m D.relation D.e D.M D.mapM D.comparison
  have hQ : Q = Pic0FiniteStageGlueContext.canonicalComparisonFamily C D := by
    symm
    exact Pic0FiniteStageGlueContext.canonicalComparisonFamily_spec C D
  let T : Pic0FiniteStageTripleTransitionFamilyData C
      D.L D.n D.m D.relation D.M D.mapM Q := {
    N := P.N
    thetaN := P.thetaN
    comparison := by
      intro p
      rcases p with ⟨U, V, W⟩
      convert P.hthetaN (U, (V, W)) using 1; rfl }
  exact Pic0FiniteStageCanonicalGlueContext.ofModelsWithComparison C D Q T hQ

/-- Convert a legacy package to the canonical stable package. -/
noncomputable def toStable
    (P : Pic0FiniteStageGluePackage C F) :
    Pic0FiniteStageStableGluePackage C F := by
  exact Pic0FiniteStageStableGluePackage.ofContext C P.toCanonicalContext

@[simp]
theorem toTransitionModelsData_L (P : Pic0FiniteStageGluePackage C F) :
    P.toTransitionModelsData.L = P.L := rfl

@[simp]
theorem toTransitionModelsData_M (P : Pic0FiniteStageGluePackage C F) :
    P.toTransitionModelsData.M = P.M := rfl

@[simp]
theorem toStable_context (P : Pic0FiniteStageGluePackage C F) :
    P.toStable.context = P.toCanonicalContext := rfl

/-- Produce a stable package by mapping the existing legacy finite-stage producer through the
canonical adapter. -/
theorem exists_stable :
    Nonempty (Pic0FiniteStageStableGluePackage C F) :=
  Nonempty.map (fun P => P.toStable C)
    (exists_pic0FiniteStageGluePackage (C := C) (F := F))

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
