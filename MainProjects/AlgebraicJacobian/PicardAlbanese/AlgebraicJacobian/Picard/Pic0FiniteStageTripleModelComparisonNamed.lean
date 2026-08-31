/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageTensorPushoutComparison
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelComparison

/-!
# Named comparison for finite-stage Picard triple-overlap models

The component comparisons identify scalar extensions of the descended chart and
pair-overlap rings with their exact section rings.  Specializing the generic named
tensor-pushout comparison gives the exact triple-intersection ring without exposing
dependent tensor-product instances at the declaration boundary.

The final two equations identify the forward faces of this comparison with the two
exact overlap-to-triple restriction maps.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

section Comparison

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000

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

section ModelMapCompatibility

set_option maxHeartbeats 3200000
-- The compatibility family contains two dependent quotient-algebra towers.
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

set_option synthInstance.maxHeartbeats 400000 in
-- Expected-type guidance avoids eager reduction of the dependent named pushout.
set_option maxHeartbeats 6400000 in
/-- Scalar extension of a descended triple model is canonically the exact
triple-intersection ring. -/
noncomputable def pic0FiniteStageTripleModelComparison
    (U V W : Pic0FiniteStageChartIndex C) :
    (k ⊗[M.1] Pic0FiniteStageTripleModelRing
      C L n m relation M mapM U V W) ≃ₐ[k]
      Pic0FiniteStageTripleRing C U V W :=
  finiteStageTensorPushoutComparison
    (R := M.1) (K := k)
    (A := Pic0FiniteStageChartModelRing C L n m relation M U)
    (B1 := Pic0FiniteStageOverlapModelRing C L n m relation M U V)
    (B2 := Pic0FiniteStageOverlapModelRing C L n m relation M U W)
    (A0 := Pic0FiniteStageChartRing C U)
    (B10 := Pic0FiniteStageOverlapRing C U V)
    (B20 := Pic0FiniteStageOverlapRing C U W)
    (T := Pic0FiniteStageTripleRing C U V W)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U W)
    (pic0FiniteStageModelBaseChangeEquiv
      C L n m relation e M (Sum.inl U))
    (pic0FiniteStageModelBaseChangeEquiv
      C L n m relation e M (Sum.inr (U, V)))
    (pic0FiniteStageModelBaseChangeEquiv
      C L n m relation e M (Sum.inr (U, W)))
    (pic0FiniteStageRestrictionLeft C U V)
    (pic0FiniteStageRestrictionLeft C U W)
    (pic0FiniteStageOverlapToTripleLeft C U V W)
    (pic0FiniteStageOverlapToTripleRight C U V W)
    (by
      apply DFunLike.ext _ _
      intro x
      exact DFunLike.congr_fun
        (pic0FiniteStageModelBaseChangeEquiv_restrictionLeft
          C L n m relation e M mapM hmapM U V) x)
    (by
      apply DFunLike.ext _ _
      intro x
      exact DFunLike.congr_fun
        (pic0FiniteStageModelBaseChangeEquiv_restrictionLeft
          C L n m relation e M mapM hmapM U W) x)
    (isPushout_pic0FiniteStageTripleRing C U V W)

set_option maxHeartbeats 3200000 in
-- Pin the codomain so consumers do not infer the dependent pushout instances.
noncomputable def pic0FiniteStageTripleModelFaceLeft
    (U V W : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageOverlapModelRing C L n m relation M U V →ₐ[M.1]
      Pic0FiniteStageTripleModelRing C L n m relation M mapM U V W :=
  finiteStageTensorPushoutFaceLeft
    (R := M.1)
    (A := Pic0FiniteStageChartModelRing C L n m relation M U)
    (B₁ := Pic0FiniteStageOverlapModelRing C L n m relation M U V)
    (B₂ := Pic0FiniteStageOverlapModelRing C L n m relation M U W)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U W)

set_option maxHeartbeats 3200000 in
-- Pin the codomain so consumers do not infer the dependent pushout instances.
noncomputable def pic0FiniteStageTripleModelFaceRight
    (U V W : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageOverlapModelRing C L n m relation M U W →ₐ[M.1]
      Pic0FiniteStageTripleModelRing C L n m relation M mapM U V W :=
  finiteStageTensorPushoutFaceRight
    (R := M.1)
    (A := Pic0FiniteStageChartModelRing C L n m relation M U)
    (B₁ := Pic0FiniteStageOverlapModelRing C L n m relation M U V)
    (B₂ := Pic0FiniteStageOverlapModelRing C L n m relation M U W)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U W)

set_option maxHeartbeats 3200000 in
-- Both sides retain the same dependent named-pushout instances.
/-- The triple-model comparison carries the scalar extension of its left face to
exact restriction from the first pair-overlap. -/
theorem pic0FiniteStageTripleModelComparison_faceLeft
    (U V W : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageTripleModelComparison
        C L n m relation e M mapM hmapM U V W).toAlgHom.comp
      (AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := M.1) (K := k)
        (pic0FiniteStageTripleModelFaceLeft
          C L n m relation M mapM U V W)) =
      (pic0FiniteStageOverlapToTripleLeft C U V W).comp
        (pic0FiniteStageModelBaseChangeEquiv
          C L n m relation e M (Sum.inr (U, V))).toAlgHom := by
  have hface := @finiteStageTensorPushoutComparison_faceLeft
    M.1 k
    (Pic0FiniteStageChartModelRing C L n m relation M U)
    (Pic0FiniteStageOverlapModelRing C L n m relation M U V)
    (Pic0FiniteStageOverlapModelRing C L n m relation M U W)
    (Pic0FiniteStageChartRing C U)
    (Pic0FiniteStageOverlapRing C U V)
    (Pic0FiniteStageOverlapRing C U W)
    (Pic0FiniteStageTripleRing C U V W)
    _ _ _ _ _
    (instCommRingPic0FiniteStageChartRing C U)
    (instCommRingPic0FiniteStageOverlapRing C U V)
    (instCommRingPic0FiniteStageOverlapRing C U W)
    (instCommRingPic0FiniteStageTripleRing C U V W)
    _ _ _ _
    (instAlgebraPic0FiniteStageChartRing C U)
    (instAlgebraPic0FiniteStageOverlapRing C U V)
    (instAlgebraPic0FiniteStageOverlapRing C U W)
    (instAlgebraPic0FiniteStageTripleRing C U V W)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U W)
    (pic0FiniteStageModelBaseChangeEquiv
      C L n m relation e M (Sum.inl U))
    (pic0FiniteStageModelBaseChangeEquiv
      C L n m relation e M (Sum.inr (U, V)))
    (pic0FiniteStageModelBaseChangeEquiv
      C L n m relation e M (Sum.inr (U, W)))
    (pic0FiniteStageRestrictionLeft C U V)
    (pic0FiniteStageRestrictionLeft C U W)
    (pic0FiniteStageOverlapToTripleLeft C U V W)
    (pic0FiniteStageOverlapToTripleRight C U V W)
    (by
      apply DFunLike.ext _ _
      intro x
      exact DFunLike.congr_fun
        (pic0FiniteStageModelBaseChangeEquiv_restrictionLeft
          C L n m relation e M mapM hmapM U V) x)
    (by
      apply DFunLike.ext _ _
      intro x
      exact DFunLike.congr_fun
        (pic0FiniteStageModelBaseChangeEquiv_restrictionLeft
          C L n m relation e M mapM hmapM U W) x)
    (isPushout_pic0FiniteStageTripleRing C U V W)
  exact hface

set_option maxHeartbeats 3200000 in
-- Both sides retain the same dependent named-pushout instances.
/-- The triple-model comparison carries the scalar extension of its right face to
exact restriction from the second pair-overlap. -/
theorem pic0FiniteStageTripleModelComparison_faceRight
    (U V W : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageTripleModelComparison
        C L n m relation e M mapM hmapM U V W).toAlgHom.comp
      (AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := M.1) (K := k)
        (pic0FiniteStageTripleModelFaceRight
          C L n m relation M mapM U V W)) =
      (pic0FiniteStageOverlapToTripleRight C U V W).comp
        (pic0FiniteStageModelBaseChangeEquiv
          C L n m relation e M (Sum.inr (U, W))).toAlgHom := by
  have hface := @finiteStageTensorPushoutComparison_faceRight
    M.1 k
    (Pic0FiniteStageChartModelRing C L n m relation M U)
    (Pic0FiniteStageOverlapModelRing C L n m relation M U V)
    (Pic0FiniteStageOverlapModelRing C L n m relation M U W)
    (Pic0FiniteStageChartRing C U)
    (Pic0FiniteStageOverlapRing C U V)
    (Pic0FiniteStageOverlapRing C U W)
    (Pic0FiniteStageTripleRing C U V W)
    _ _ _ _ _
    (instCommRingPic0FiniteStageChartRing C U)
    (instCommRingPic0FiniteStageOverlapRing C U V)
    (instCommRingPic0FiniteStageOverlapRing C U W)
    (instCommRingPic0FiniteStageTripleRing C U V W)
    _ _ _ _
    (instAlgebraPic0FiniteStageChartRing C U)
    (instAlgebraPic0FiniteStageOverlapRing C U V)
    (instAlgebraPic0FiniteStageOverlapRing C U W)
    (instAlgebraPic0FiniteStageTripleRing C U V W)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V)
    (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U W)
    (pic0FiniteStageModelBaseChangeEquiv
      C L n m relation e M (Sum.inl U))
    (pic0FiniteStageModelBaseChangeEquiv
      C L n m relation e M (Sum.inr (U, V)))
    (pic0FiniteStageModelBaseChangeEquiv
      C L n m relation e M (Sum.inr (U, W)))
    (pic0FiniteStageRestrictionLeft C U V)
    (pic0FiniteStageRestrictionLeft C U W)
    (pic0FiniteStageOverlapToTripleLeft C U V W)
    (pic0FiniteStageOverlapToTripleRight C U V W)
    (by
      apply DFunLike.ext _ _
      intro x
      exact DFunLike.congr_fun
        (pic0FiniteStageModelBaseChangeEquiv_restrictionLeft
          C L n m relation e M mapM hmapM U V) x)
    (by
      apply DFunLike.ext _ _
      intro x
      exact DFunLike.congr_fun
        (pic0FiniteStageModelBaseChangeEquiv_restrictionLeft
          C L n m relation e M mapM hmapM U W) x)
    (isPushout_pic0FiniteStageTripleRing C U V W)
  exact hface

end ModelMapCompatibility

end Comparison

end

end AlgebraicGeometry
