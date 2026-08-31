/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGlueData
import AlgebraicJacobian.Picard.Pic0FiniteStageCanonicalGlueContext

/-!
# The face equation for the finite-stage Picard glue datum

The descended transition first acts on scalar extensions of the named triple-overlap
models.  Conjugating by the canonical tensor-pushout scalar-extension equivalences puts
that transition on the literal tensor products used by affine gluing.  The two canonical
face squares then transport the reflected model-level face equation to those literal
tensor products.
-/

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

/-- A face equation survives conjugating its upper map, provided the two face maps and
the lower map are carried to the chosen target diagram. -/
theorem conjugateAlgHom_face_of_squares
    {R A B D E B' E' : Type u}
    [CommSemiring R]
    [CommSemiring A] [CommSemiring B] [CommSemiring D] [CommSemiring E]
    [CommSemiring B'] [CommSemiring E']
    [Algebra R A] [Algebra R B] [Algebra R D] [Algebra R E]
    [Algebra R B'] [Algebra R E']
    (eB : B ≃ₐ[R] B') (eE : E ≃ₐ[R] E')
    (right : A →ₐ[R] B) (theta : B →ₐ[R] E)
    (tau : A →ₐ[R] D) (left : D →ₐ[R] E)
    (right' : A →ₐ[R] B') (tau' : A →ₐ[R] D) (left' : D →ₐ[R] E')
    (hright : eB.toAlgHom.comp right = right')
    (htau : tau = tau')
    (hleft : eE.toAlgHom.comp left = left')
    (hface : theta.comp right = left.comp tau) :
    (eE.toAlgHom.comp (theta.comp eB.symm.toAlgHom)).comp right' =
      left'.comp tau' := by
  apply DFunLike.ext _ _
  intro x
  change eE (theta (eB.symm (right' x))) = left' (tau' x)
  calc
    _ = eE (theta (right x)) := congrArg (fun y => eE (theta y))
      ((congrArg eB.symm (DFunLike.congr_fun hright x).symm).trans
        (eB.symm_apply_apply (right x)))
    _ = eE (left (tau x)) := congrArg eE (DFunLike.congr_fun hface x)
    _ = left' (tau x) := DFunLike.congr_fun hleft (tau x)
    _ = left' (tau' x) := congrArg left' (DFunLike.congr_fun htau x)

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 3200000

variable {F : Type u} [Field F] [Algebra F k]
variable (L : DatG0.FinSubext F k)
variable (n m : Pic0FiniteStageRingIndex C -> Nat)
variable (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
variable (M : DatG0.FinSubext L.1 k)
variable (mapM : forall q : Pic0FiniteStageMapIndex C,
  Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapSource C q) →ₐ[M.1]
    Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapTarget C q))
variable (N : DatG0.FinSubext M.1 k)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 6400000 in
-- The package projections keep all four dependent tensor-product carriers aligned.
/-- The descended affine triple transition intertwines the overlap transition with the
two literal tensor-pushout face maps used by affine gluing. -/
theorem pic0FiniteStageAffineTripleTransition_fac
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    [Algebra.IsAlgebraic M.1 k]
    (hmapM : forall q,
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
    (thetaN : forall p : Pic0FiniteStageTripleTransitionIndex C,
      N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelSource
          C L n m relation M mapM p →ₐ[N.1]
        N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM p)
    (hthetaN : forall p : Pic0FiniteStageTripleTransitionIndex C,
      (Algebra.TensorProduct.map N.1.val
          (AlgHom.id M.1
            (Pic0FiniteStageTripleTransitionModelTarget
              C L n m relation M mapM p))).comp
          ((thetaN p).restrictScalars M.1) =
        ((pic0FiniteStageTransportedTripleTransitionOfModels
          C L n m relation e M mapM hmapM p.1 p.2.1 p.2.2).restrictScalars
            M.1).comp
          (Algebra.TensorProduct.map N.1.val
            (AlgHom.id M.1
              (Pic0FiniteStageTripleTransitionModelSource
                C L n m relation M mapM p))))
    (U V W : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageAffineTripleTransition
        C L n m relation M mapM N thetaN U V W).comp
        (finiteStageTensorPushoutFaceRight
          (pic0FiniteStageRestrictionBaseChange
            C L n m relation M mapM N V W)
          (pic0FiniteStageRestrictionBaseChange
            C L n m relation M mapM N V U)) =
      (finiteStageTensorPushoutFaceLeft
        (pic0FiniteStageRestrictionBaseChange
          C L n m relation M mapM N U V)
        (pic0FiniteStageRestrictionBaseChange
          C L n m relation M mapM N U W)).comp
        (pic0FiniteStageTransitionBaseChange
          C L n m relation M mapM N U V) := by
  let P := pic0FiniteStageTripleTransitionFacePackage
    C L n m relation M mapM e hmapM N U V W thetaN hthetaN
  have hright :
      (pic0FiniteStageTripleBaseChangeEquiv
        C L n m relation M mapM N V W U).toAlgHom.comp P.rightN =
        finiteStageTensorPushoutFaceRight
          (pic0FiniteStageRestrictionBaseChange
            C L n m relation M mapM N V W)
          (pic0FiniteStageRestrictionBaseChange
            C L n m relation M mapM N V U) := by
    change
      (finiteStageTensorPushoutScalarExtension_named (K := N.1)
        (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM V W)
        (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM V U)).toAlgHom.comp
          (AlgebraicJacobian.scalarExtensionMapOfAlgHom
            (R := M.1) (K := N.1)
              (pic0FiniteStageTripleModelFaceRight
                C L n m relation M mapM V W U)) = _
    exact finiteStageTensorPushoutScalarExtension_faceRight_map
      (K := N.1)
      (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM V W)
      (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM V U)
  have htau :
      P.tauN = pic0FiniteStageTransitionBaseChange
        C L n m relation M mapM N U V := by
    rfl
  have hleft :
      (pic0FiniteStageTripleBaseChangeEquiv
        C L n m relation M mapM N U V W).toAlgHom.comp P.leftN =
        finiteStageTensorPushoutFaceLeft
          (pic0FiniteStageRestrictionBaseChange
            C L n m relation M mapM N U V)
          (pic0FiniteStageRestrictionBaseChange
            C L n m relation M mapM N U W) := by
    change
      (finiteStageTensorPushoutScalarExtension_named (K := N.1)
        (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V)
        (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U W)).toAlgHom.comp
          (AlgebraicJacobian.scalarExtensionMapOfAlgHom
            (R := M.1) (K := N.1)
              (pic0FiniteStageTripleModelFaceLeft
                C L n m relation M mapM U V W)) = _
    exact finiteStageTensorPushoutScalarExtension_faceLeft_map
      (K := N.1)
      (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V)
      (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U W)
  have hface : P.thetaN.comp P.rightN = P.leftN.comp P.tauN := P.face
  exact conjugateAlgHom_face_of_squares
    (pic0FiniteStageTripleBaseChangeEquiv
      C L n m relation M mapM N V W U)
    (pic0FiniteStageTripleBaseChangeEquiv
      C L n m relation M mapM N U V W)
    P.rightN P.thetaN P.tauN P.leftN
    (finiteStageTensorPushoutFaceRight
      (pic0FiniteStageRestrictionBaseChange C L n m relation M mapM N V W)
      (pic0FiniteStageRestrictionBaseChange C L n m relation M mapM N V U))
    (pic0FiniteStageTransitionBaseChange C L n m relation M mapM N U V)
    (finiteStageTensorPushoutFaceLeft
      (pic0FiniteStageRestrictionBaseChange C L n m relation M mapM N U V)
      (pic0FiniteStageRestrictionBaseChange C L n m relation M mapM N U W))
    hright htau hleft hface

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 6400000 in
/-! The canonical facade supplies the comparison square from its stored model invariant.
Face consumers therefore pass one context and do not rebuild a dependent certificate. -/
theorem pic0FiniteStageAffineTripleTransition_fac_of_canonical_context
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (D : Pic0FiniteStageCanonicalGlueContext C F)
    [Algebra.IsAlgebraic D.context.models.L.1 k]
    [Algebra.IsAlgebraic D.context.models.M.1 k]
    (U V W : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageAffineTripleTransition
        C D.context.L D.context.n D.context.m D.context.relation D.context.M
        D.context.mapM D.context.N D.context.thetaN U V W).comp
        (finiteStageTensorPushoutFaceRight
          (pic0FiniteStageRestrictionBaseChange
            C D.context.L D.context.n D.context.m D.context.relation D.context.M
            D.context.mapM D.context.N V W)
          (pic0FiniteStageRestrictionBaseChange
            C D.context.L D.context.n D.context.m D.context.relation D.context.M
            D.context.mapM D.context.N V U)) =
      (finiteStageTensorPushoutFaceLeft
        (pic0FiniteStageRestrictionBaseChange
          C D.context.L D.context.n D.context.m D.context.relation D.context.M
          D.context.mapM D.context.N U V)
        (pic0FiniteStageRestrictionBaseChange
          C D.context.L D.context.n D.context.m D.context.relation D.context.M
          D.context.mapM D.context.N U W)).comp
        (pic0FiniteStageTransitionBaseChange
          C D.context.L D.context.n D.context.m D.context.relation D.context.M
          D.context.mapM D.context.N U V) := by
  exact pic0FiniteStageAffineTripleTransition_fac
    C D.context.models.L D.context.models.n D.context.models.m
      D.context.models.relation D.context.models.M D.context.models.mapM
      D.context.triple.N D.context.models.e D.context.models.comparison
      D.context.triple.thetaN (fun p => D.comparison_of_models C p) U V W

end

end

end AlgebraicGeometry
