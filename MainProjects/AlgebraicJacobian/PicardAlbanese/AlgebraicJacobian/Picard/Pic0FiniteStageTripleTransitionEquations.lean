/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FinitePresentationAlgebraMapTripleReflection
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleTransitionModels

/-!
# Equations for descended finite-stage triple transitions

The cyclic identity for exact triple-overlap transitions is preserved by the comparison
conjugations used before finite descent.  It can therefore be reflected from the ambient
separably closed field to any finite stage carrying compatible descended transition maps.
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
-- The three dependent tensor models and comparison conjugations elaborate simultaneously.
set_option maxHeartbeats 3200000 in
/-- Three transported cyclic transitions compose to the identity over the ambient field. -/
theorem pic0FiniteStageTransportedTripleTransition_cocycle
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → ℕ)
    (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : ∀ q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (Q : ∀ q : Pic0FiniteStageTripleTransitionIndex C,
      k ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM q ≃ₐ[k]
        Pic0FiniteStageTripleRing C q.1 q.2.1 q.2.2)
    (U V W : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageTransportedTripleTransition
        C L n m relation M mapM Q (U, (V, W))).comp
        ((pic0FiniteStageTransportedTripleTransition
          C L n m relation M mapM Q (V, (W, U))).comp
          (pic0FiniteStageTransportedTripleTransition
            C L n m relation M mapM Q (W, (U, V)))) =
      AlgHom.id k
        (k ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM (U, (V, W))) := by
  change
    ((Q (U, (V, W))).symm.toAlgHom.comp
        ((pic0FiniteStageTripleTransition C U V W).comp
          (Q (V, (W, U))).toAlgHom)).comp
        (((Q (V, (W, U))).symm.toAlgHom.comp
          ((pic0FiniteStageTripleTransition C V W U).comp
            (Q (W, (U, V))).toAlgHom)).comp
          ((Q (W, (U, V))).symm.toAlgHom.comp
            ((pic0FiniteStageTripleTransition C W U V).comp
              (Q (U, (V, W))).toAlgHom))) = _
  apply DFunLike.ext _ _
  intro x
  change
    (Q (U, (V, W))).symm
      (pic0FiniteStageTripleTransition C U V W
        ((Q (V, (W, U)))
          ((Q (V, (W, U))).symm
            (pic0FiniteStageTripleTransition C V W U
              ((Q (W, (U, V)))
                ((Q (W, (U, V))).symm
                  (pic0FiniteStageTripleTransition C W U V
                    ((Q (U, (V, W))) x)))))))) = x
  rw [(Q (V, (W, U))).apply_symm_apply,
    (Q (W, (U, V))).apply_symm_apply]
  have htransition :=
    DFunLike.congr_fun (pic0FiniteStageTripleTransition_cocycle C U V W)
      ((Q (U, (V, W))) x)
  calc
    _ = (Q (U, (V, W))).symm ((Q (U, (V, W))) x) := by
      exact congrArg (Q (U, (V, W))).symm htransition
    _ = x := (Q (U, (V, W))).symm_apply_apply x

set_option synthInstance.maxHeartbeats 400000 in
-- Reflection elaborates four dependent scalar-extension squares in one theorem application.
set_option maxHeartbeats 3200000 in
/-- Compatible finite-stage triple transitions satisfy the same three-cycle identity. -/
theorem pic0FiniteStageTripleTransitionModel_cocycle
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → ℕ)
    (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    [Algebra.IsAlgebraic M.1 k]
    (mapM : ∀ q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (Q : ∀ q : Pic0FiniteStageTripleTransitionIndex C,
      k ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM q ≃ₐ[k]
        Pic0FiniteStageTripleRing C q.1 q.2.1 q.2.2)
    (N : DatG0.FinSubext M.1 k)
    (thetaN : ∀ p : Pic0FiniteStageTripleTransitionIndex C,
      N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelSource
          C L n m relation M mapM p →ₐ[N.1]
        N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM p)
    (hthetaN : ∀ p : Pic0FiniteStageTripleTransitionIndex C,
      (Algebra.TensorProduct.map N.1.val
          (AlgHom.id M.1
            (Pic0FiniteStageTripleTransitionModelTarget
              C L n m relation M mapM p))).comp
          ((thetaN p).restrictScalars M.1) =
        ((pic0FiniteStageTransportedTripleTransition
          C L n m relation M mapM Q p).restrictScalars M.1).comp
          (Algebra.TensorProduct.map N.1.val
            (AlgHom.id M.1
              (Pic0FiniteStageTripleTransitionModelSource
                C L n m relation M mapM p))))
    (U V W : Pic0FiniteStageChartIndex C) :
    (thetaN (U, (V, W))).comp
        ((thetaN (V, (W, U))).comp (thetaN (W, (U, V)))) =
      AlgHom.id N.1
        (N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM (U, (V, W))) := by
  apply DatG0.tensorProduct_algHom_triple_comp_eq_of_baseChange N
    (thetaN (W, (U, V)))
    (thetaN (V, (W, U)))
    (thetaN (U, (V, W)))
    (AlgHom.id N.1
      (N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
        C L n m relation M mapM (U, (V, W))))
    (pic0FiniteStageTransportedTripleTransition
      C L n m relation M mapM Q (W, (U, V)))
    (pic0FiniteStageTransportedTripleTransition
      C L n m relation M mapM Q (V, (W, U)))
    (pic0FiniteStageTransportedTripleTransition
      C L n m relation M mapM Q (U, (V, W)))
    (AlgHom.id k
      (k ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
        C L n m relation M mapM (U, (V, W))))
  · exact hthetaN (W, (U, V))
  · exact hthetaN (V, (W, U))
  · exact hthetaN (U, (V, W))
  · ext x
    rfl
  · exact pic0FiniteStageTransportedTripleTransition_cocycle
      C L n m relation M mapM Q U V W

end

end AlgebraicGeometry
