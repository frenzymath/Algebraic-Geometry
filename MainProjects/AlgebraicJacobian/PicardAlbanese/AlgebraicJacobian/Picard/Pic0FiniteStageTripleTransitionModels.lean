/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleOverlapRings
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleTransitions

/-!
# Finite-stage models of cyclic triple transitions

Given comparison equivalences from scalar extensions of the descended tensor models to
the exact triple-overlap rings, the exact cyclic transitions can be conjugated to maps of
scalar-extended models.  Since the source triple models are finite type, all of these
conjugated maps descend simultaneously through one further finite subextension.

The comparison family is an explicit parameter.  Thus this file isolates the finite
descent step from the separate problem of constructing those equivalences compatibly with
the two triple faces.
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

/-- A right-associated index `(U, (V, W))` for the cyclic transition whose source is the
rotated triple model `(V, W, U)` and whose target is `(U, V, W)`. -/
abbrev Pic0FiniteStageTripleTransitionIndex :=
  Pic0FiniteStageChartIndex C ×
    (Pic0FiniteStageChartIndex C × Pic0FiniteStageChartIndex C)

/-- The descended source ring of the cyclic triple transition indexed by
`(U, (V, W))`. -/
noncomputable abbrev Pic0FiniteStageTripleTransitionModelSource
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
    (p : Pic0FiniteStageTripleTransitionIndex C) : Type u :=
  Pic0FiniteStageTripleModelRing C L n m relation M mapM p.2.1 p.2.2 p.1

/-- The descended target ring of the cyclic triple transition indexed by
`(U, (V, W))`. -/
noncomputable abbrev Pic0FiniteStageTripleTransitionModelTarget
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
    (p : Pic0FiniteStageTripleTransitionIndex C) : Type u :=
  Pic0FiniteStageTripleModelRing C L n m relation M mapM p.1 p.2.1 p.2.2

noncomputable instance
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
    (p : Pic0FiniteStageTripleTransitionIndex C) :
    CommRing (Pic0FiniteStageTripleTransitionModelSource
      C L n m relation M mapM p) := by
  rcases p with ⟨U, V, W⟩
  change CommRing
    (Pic0FiniteStageTripleModelRing C L n m relation M mapM V W U)
  infer_instance

noncomputable instance
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
    (p : Pic0FiniteStageTripleTransitionIndex C) :
    Algebra M.1 (Pic0FiniteStageTripleTransitionModelSource
      C L n m relation M mapM p) := by
  rcases p with ⟨U, V, W⟩
  change Algebra M.1
    (Pic0FiniteStageTripleModelRing C L n m relation M mapM V W U)
  infer_instance

noncomputable instance
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
    (p : Pic0FiniteStageTripleTransitionIndex C) :
    CommRing (Pic0FiniteStageTripleTransitionModelTarget
      C L n m relation M mapM p) := by
  rcases p with ⟨U, V, W⟩
  change CommRing
    (Pic0FiniteStageTripleModelRing C L n m relation M mapM U V W)
  infer_instance

noncomputable instance
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
    (p : Pic0FiniteStageTripleTransitionIndex C) :
    Algebra M.1 (Pic0FiniteStageTripleTransitionModelTarget
      C L n m relation M mapM p) := by
  rcases p with ⟨U, V, W⟩
  change Algebra M.1
    (Pic0FiniteStageTripleModelRing C L n m relation M mapM U V W)
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
-- Three dependent tensor models occur in the comparison conjugation.
set_option maxHeartbeats 3200000 in
/-- The exact cyclic transition, transported to scalar extensions of the descended triple
models by the comparison equivalences. -/
noncomputable def pic0FiniteStageTransportedTripleTransition
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
    (p : Pic0FiniteStageTripleTransitionIndex C) :
    k ⊗[M.1] Pic0FiniteStageTripleTransitionModelSource
        C L n m relation M mapM p →ₐ[k]
      k ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
        C L n m relation M mapM p :=
  (Q p).symm.toAlgHom.comp
    ((pic0FiniteStageTripleTransition C p.1 p.2.1 p.2.2).comp
      (Q (p.2.1, (p.2.2, p.1))).toAlgHom)

set_option synthInstance.maxHeartbeats 400000 in
-- The finite family contains dependent tensor-pushout algebras in both map directions.
set_option maxHeartbeats 6400000 in
/-- Given scalar-extension comparisons for the triple models, all transported cyclic
triple transitions descend simultaneously through one finite subextension `N/M`.  The
displayed square is the precise comparison with the transported exact transition. -/
theorem exists_finSubext_pic0FiniteStageTripleTransition_models_of_comparisons
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
        Pic0FiniteStageTripleRing C q.1 q.2.1 q.2.2) :
    ∃ N : DatG0.FinSubext M.1 k,
      ∀ p : Pic0FiniteStageTripleTransitionIndex C,
        ∃ thetaN :
          N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelSource
              C L n m relation M mapM p →ₐ[N.1]
            N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
              C L n m relation M mapM p,
          (Algebra.TensorProduct.map N.1.val
              (AlgHom.id M.1
                (Pic0FiniteStageTripleTransitionModelTarget
                  C L n m relation M mapM p))).comp
              (thetaN.restrictScalars M.1) =
            ((pic0FiniteStageTransportedTripleTransition
              C L n m relation M mapM Q p).restrictScalars M.1).comp
              (Algebra.TensorProduct.map N.1.val
                (AlgHom.id M.1
                  (Pic0FiniteStageTripleTransitionModelSource
                    C L n m relation M mapM p))) := by
  letI : ∀ p : Pic0FiniteStageTripleTransitionIndex C,
      Algebra.FiniteType M.1
        (Pic0FiniteStageTripleTransitionModelSource
          C L n m relation M mapM p) := fun p =>
    finiteType_pic0FiniteStageTripleModelRing
      C L n m relation M mapM p.2.1 p.2.2 p.1
  exact DatG0.exists_finSubext_tensorProduct_algHom_finite
    (F := M.1) (K := k)
    (fun p : Pic0FiniteStageTripleTransitionIndex C =>
      Pic0FiniteStageTripleTransitionModelSource C L n m relation M mapM p)
    (fun p : Pic0FiniteStageTripleTransitionIndex C =>
      Pic0FiniteStageTripleTransitionModelTarget C L n m relation M mapM p)
    (pic0FiniteStageTransportedTripleTransition C L n m relation M mapM Q)

/-- The finite-stage map carrier produced at the next scalar level.

Naming this dependent tensor carrier once keeps package fields and consumers from repeating
the full source/target expression (and from asking typeclass search to reconstruct it at each
occurrence).
-/
abbrev Pic0FiniteStageTripleTransitionFamilyMap
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
    (N : DatG0.FinSubext M.1 k)
    (p : Pic0FiniteStageTripleTransitionIndex C) : Type u :=
  N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelSource
      C L n m relation M mapM p →ₐ[N.1]
    N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
      C L n m relation M mapM p

set_option synthInstance.maxHeartbeats 400000 in
-- The dependent tensor maps in the comparison square need a larger local synthesis budget.
set_option maxHeartbeats 6400000 in
/-- The comparison square attached to one member of a finite transition family. -/
abbrev Pic0FiniteStageTripleTransitionFamilyComparison
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
    (N : DatG0.FinSubext M.1 k)
    (p : Pic0FiniteStageTripleTransitionIndex C)
    (thetaN : Pic0FiniteStageTripleTransitionFamilyMap
      C L n m relation M mapM N p) : Prop :=
  (Algebra.TensorProduct.map N.1.val
      (AlgHom.id M.1
        (Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM p))).comp
      (thetaN.restrictScalars M.1) =
    ((pic0FiniteStageTransportedTripleTransition
      C L n m relation M mapM Q p).restrictScalars M.1).comp
      (Algebra.TensorProduct.map N.1.val
        (AlgHom.id M.1
          (Pic0FiniteStageTripleTransitionModelSource
            C L n m relation M mapM p)))

/-- The complete finite-stage family output: one `N`, all transition maps, and their squares. -/
structure Pic0FiniteStageTripleTransitionFamilyData
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
        Pic0FiniteStageTripleRing C q.1 q.2.1 q.2.2) where
  N : DatG0.FinSubext M.1 k
  thetaN : ∀ p : Pic0FiniteStageTripleTransitionIndex C,
    Pic0FiniteStageTripleTransitionFamilyMap C L n m relation M mapM N p
  comparison : ∀ p : Pic0FiniteStageTripleTransitionIndex C,
    Pic0FiniteStageTripleTransitionFamilyComparison
      C L n m relation M mapM Q N p (thetaN p)

namespace Pic0FiniteStageTripleTransitionFamilyData

/-- Repackage the nested existential producer output without losing its dependent witnesses. -/
noncomputable def of_raw
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
    (h : ∃ N : DatG0.FinSubext M.1 k,
      ∀ p : Pic0FiniteStageTripleTransitionIndex C,
        ∃ thetaN : Pic0FiniteStageTripleTransitionFamilyMap
            C L n m relation M mapM N p,
          Pic0FiniteStageTripleTransitionFamilyComparison
            C L n m relation M mapM Q N p thetaN) :
    Pic0FiniteStageTripleTransitionFamilyData C L n m relation M mapM Q := by
  choose N hN using h
  choose thetaN hcomparison using hN
  exact { N := N, thetaN := thetaN, comparison := hcomparison }

/-- Bundle the canonical finite-subextension producer directly. -/
noncomputable def of_comparisons
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
        Pic0FiniteStageTripleRing C q.1 q.2.1 q.2.2) :
    Pic0FiniteStageTripleTransitionFamilyData C L n m relation M mapM Q :=
  of_raw C L n m relation M mapM Q
    (exists_finSubext_pic0FiniteStageTripleTransition_models_of_comparisons
      C L n m relation M mapM Q)

@[simp]
theorem comparison_eq
    {F : Type u} [Field F] [Algebra F k]
    {L : DatG0.FinSubext F k}
    {n m : Pic0FiniteStageRingIndex C → ℕ}
    {relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1}
    {M : DatG0.FinSubext L.1 k}
    [Algebra.IsAlgebraic M.1 k]
    {mapM : ∀ q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q)}
    {Q : ∀ q : Pic0FiniteStageTripleTransitionIndex C,
      k ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM q ≃ₐ[k]
        Pic0FiniteStageTripleRing C q.1 q.2.1 q.2.2}
    (D : Pic0FiniteStageTripleTransitionFamilyData C L n m relation M mapM Q)
    (p : Pic0FiniteStageTripleTransitionIndex C) :
    Pic0FiniteStageTripleTransitionFamilyComparison
      C L n m relation M mapM Q D.N p (D.thetaN p) :=
  D.comparison p

/-- Expose the packaged witnesses in the legacy existential shape for gradual migration. -/
theorem exists_raw
    {F : Type u} [Field F] [Algebra F k]
    {L : DatG0.FinSubext F k}
    {n m : Pic0FiniteStageRingIndex C → ℕ}
    {relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1}
    {M : DatG0.FinSubext L.1 k}
    [Algebra.IsAlgebraic M.1 k]
    {mapM : ∀ q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q)}
    {Q : ∀ q : Pic0FiniteStageTripleTransitionIndex C,
      k ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM q ≃ₐ[k]
        Pic0FiniteStageTripleRing C q.1 q.2.1 q.2.2}
    (D : Pic0FiniteStageTripleTransitionFamilyData C L n m relation M mapM Q) :
    ∃ N : DatG0.FinSubext M.1 k,
      ∀ p : Pic0FiniteStageTripleTransitionIndex C,
        ∃ thetaN : Pic0FiniteStageTripleTransitionFamilyMap
            C L n m relation M mapM N p,
          Pic0FiniteStageTripleTransitionFamilyComparison
            C L n m relation M mapM Q N p thetaN := by
  exact ⟨D.N, fun p => ⟨D.thetaN p, D.comparison p⟩⟩

end Pic0FiniteStageTripleTransitionFamilyData

end

end AlgebraicGeometry
