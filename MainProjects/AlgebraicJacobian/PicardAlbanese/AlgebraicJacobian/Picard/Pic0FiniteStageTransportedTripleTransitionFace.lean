/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelComparisonNamed
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleTransitionModels

/-!
# The face equation for transported finite-stage triple transitions

The concrete comparison from each scalar-extended finite-stage triple model to the exact
triple-intersection ring preserves both tensor-pushout faces.  Conjugating the exact cyclic
transition by these comparisons therefore carries the rotated right face to the original
left face after the descended pair transition.
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

section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 6400000

variable {F : Type u} [Field F] [Algebra F k]
variable (L : DatG0.FinSubext F k)
variable (n m : Pic0FiniteStageRingIndex C -> Nat)
variable (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
variable (e : forall j,
  k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
    Pic0FiniteStageRing C j)
variable (M : DatG0.FinSubext L.1 k)
variable (mapM : forall q : Pic0FiniteStageMapIndex C,
  Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapSource C q) →ₐ[M.1]
    Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapTarget C q))
variable (hmapM : forall q,
  (Algebra.TensorProduct.map M.1.val
      (AlgHom.id L.1
        (DatG0.FiniteRelationAlgebra L.1
          (n (Pic0FiniteStageMapTarget C q))
          (m (Pic0FiniteStageMapTarget C q))
          (relation (Pic0FiniteStageMapTarget C q))))).comp
      ((mapM q).restrictScalars L.1) =
    ((pic0FiniteStageTransportedMap C L n m relation e q).restrictScalars
      L.1).comp
      (Algebra.TensorProduct.map M.1.val
        (AlgHom.id L.1
          (DatG0.FiniteRelationAlgebra L.1
            (n (Pic0FiniteStageMapSource C q))
            (m (Pic0FiniteStageMapSource C q))
            (relation (Pic0FiniteStageMapSource C q))))))

set_option maxHeartbeats 3200000 in
-- The family codomain contains a dependent named tensor-pushout instance.
/-- The concrete triple-model comparisons, packaged in the family shape used by the
transported cyclic transitions. -/
noncomputable def pic0FiniteStageTripleModelComparisonFamily
    (q : Pic0FiniteStageTripleTransitionIndex C) :=
  pic0FiniteStageTripleModelComparison
    C L n m relation e M mapM hmapM q.1 q.2.1 q.2.2

set_option maxHeartbeats 3200000 in
-- The transported map conjugates two dependent triple-model comparisons.
/-- The exact cyclic transition transported through the concrete triple-model
comparisons. -/
noncomputable def pic0FiniteStageTransportedTripleTransitionOfModels
    (U V W : Pic0FiniteStageChartIndex C) :=
  pic0FiniteStageTransportedTripleTransition C L n m relation M mapM
    (pic0FiniteStageTripleModelComparisonFamily
      C L n m relation e M mapM hmapM) (U, (V, W))

set_option maxHeartbeats 3200000 in
-- Inferred source and target types preserve the component-comparison instances.
/-- The exact pair transition conjugated through the two component model comparisons. -/
noncomputable def pic0FiniteStagePairModelComparisonTransition
    (U V : Pic0FiniteStageChartIndex C) :=
  (pic0FiniteStageModelBaseChangeEquiv
      C L n m relation e M (Sum.inr (U, V))).symm.toAlgHom.comp
    ((pic0FiniteStageTransition C (U, V)).comp
      (pic0FiniteStageModelBaseChangeEquiv
        C L n m relation e M (Sum.inr (V, U))).toAlgHom)

set_option maxHeartbeats 6400000 in
-- The proof reduces three dependent comparisons and their face maps simultaneously.
/-- The transported cyclic transition carries the scalar extension of the rotated right
face to the scalar extension of the original left face after the pair transition. -/
theorem pic0FiniteStageTransportedTripleTransition_fac
    (U V W : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageTransportedTripleTransitionOfModels
        C L n m relation e M mapM hmapM U V W).comp
        (AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := M.1) (K := k)
          (pic0FiniteStageTripleModelFaceRight
            C L n m relation M mapM V W U)) =
      (AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := M.1) (K := k)
        (pic0FiniteStageTripleModelFaceLeft
          C L n m relation M mapM U V W)).comp
        (pic0FiniteStagePairModelComparisonTransition
          C L n m relation e M U V) := by
  let QUVW := pic0FiniteStageTripleModelComparison
    C L n m relation e M mapM hmapM U V W
  let QVWU := pic0FiniteStageTripleModelComparison
    C L n m relation e M mapM hmapM V W U
  let EUV := pic0FiniteStageModelBaseChangeEquiv
    C L n m relation e M (Sum.inr (U, V))
  let EVU := pic0FiniteStageModelBaseChangeEquiv
    C L n m relation e M (Sum.inr (V, U))
  let tau := pic0FiniteStagePairModelComparisonTransition
    C L n m relation e M U V
  have hright := pic0FiniteStageTripleModelComparison_faceRight
    C L n m relation e M mapM hmapM V W U
  have hleft := pic0FiniteStageTripleModelComparison_faceLeft
    C L n m relation e M mapM hmapM U V W
  apply DFunLike.ext _ _
  intro x
  apply QUVW.injective
  change
    QUVW
        (QUVW.symm
          (pic0FiniteStageTripleTransition C U V W
            (QVWU
              ((AlgebraicJacobian.scalarExtensionMapOfAlgHom
                (R := M.1) (K := k)
                (pic0FiniteStageTripleModelFaceRight
                  C L n m relation M mapM V W U)) x)))) =
      QUVW
        ((AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := M.1) (K := k)
          (pic0FiniteStageTripleModelFaceLeft
            C L n m relation M mapM U V W)) (tau x))
  rw [QUVW.apply_symm_apply]
  calc
    pic0FiniteStageTripleTransition C U V W
        (QVWU
          ((AlgebraicJacobian.scalarExtensionMapOfAlgHom
            (R := M.1) (K := k)
            (pic0FiniteStageTripleModelFaceRight
              C L n m relation M mapM V W U)) x)) =
        pic0FiniteStageTripleTransition C U V W
          (pic0FiniteStageOverlapToTripleRight C V W U (EVU x)) := by
      exact congrArg (pic0FiniteStageTripleTransition C U V W)
        (DFunLike.congr_fun hright x)
    _ = pic0FiniteStageOverlapToTripleLeft C U V W
        (pic0FiniteStageTransition C (U, V) (EVU x)) := by
      exact DFunLike.congr_fun (pic0FiniteStageTripleTransition_fac C U V W) (EVU x)
    _ = pic0FiniteStageOverlapToTripleLeft C U V W (EUV (tau x)) := by
      exact congrArg (pic0FiniteStageOverlapToTripleLeft C U V W)
        (EUV.apply_symm_apply
          (pic0FiniteStageTransition C (U, V) (EVU x))).symm
    _ = QUVW
        ((AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := M.1) (K := k)
          (pic0FiniteStageTripleModelFaceLeft
            C L n m relation M mapM U V W)) (tau x)) := by
      exact (DFunLike.congr_fun hleft (tau x)).symm

end

end

end AlgebraicGeometry
