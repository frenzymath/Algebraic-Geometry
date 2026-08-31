/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleTransitions
import AlgebraicJacobian.Picard.Pic0FiniteStageTransitionModels

/-!
# Diagonal pair transitions at a finite Picard stage

The exact transition on a diagonal overlap is the identity.  Conjugating by the chosen
finite-presentation comparison gives the corresponding identity on the ambient tensor
model, and injectivity of scalar extension reflects it to every compatible finite-stage
pair-transition model.
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

set_option synthInstance.maxHeartbeats 400000 in
-- Dependent finite-relation tensor algebras occur on both sides.
set_option maxHeartbeats 3200000 in
/-- Transporting the exact diagonal pair transition through the finite-presentation
comparison gives the identity on the ambient tensor model. -/
theorem pic0FiniteStageTransportedTransition_self
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → ℕ)
    (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (e : ∀ j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (U : Pic0FiniteStageChartIndex C) :
    pic0FiniteStageTransportedMap C L n m relation e (Sum.inr (U, U)) =
      AlgHom.id k
        (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
          (n (Sum.inr (U, U))) (m (Sum.inr (U, U)))
          (relation (Sum.inr (U, U)))) := by
  change
    (e (Sum.inr (U, U))).symm.toAlgHom.comp
        ((pic0FiniteStageTransition C (U, U)).comp
          (e (Sum.inr (U, U))).toAlgHom) = _
  rw [pic0FiniteStageTransition_self]
  apply DFunLike.ext _ _
  intro x
  exact (e (Sum.inr (U, U))).symm_apply_apply x

set_option synthInstance.maxHeartbeats 400000 in
-- Reflection sees the source model through its dependent quotient presentation.
set_option maxHeartbeats 3200000 in
/-- Every pair-transition model compatible with scalar extension is the identity on a
diagonal overlap. -/
theorem pic0FiniteStageTransitionModel_self
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    [Algebra.IsAlgebraic L.1 k]
    (n m : Pic0FiniteStageRingIndex C → ℕ)
    (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (e : ∀ j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (mapM : ∀ q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (hmapM : ∀ q,
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
    (U : Pic0FiniteStageChartIndex C) :
    mapM (Sum.inr (U, U)) =
      AlgHom.id M.1
        (Pic0FiniteStageModelRing C L n m relation M (Sum.inr (U, U))) := by
  apply DatG0.tensorProduct_algHom_eq_of_map_comp_eq M
  rw [hmapM (Sum.inr (U, U)),
    pic0FiniteStageTransportedTransition_self C L n m relation e U]
  ext x <;> rfl

end

end AlgebraicGeometry
