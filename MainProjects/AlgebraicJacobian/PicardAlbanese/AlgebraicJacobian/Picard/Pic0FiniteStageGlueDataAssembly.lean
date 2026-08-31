/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGlueDataFace

/-!
# Assembly of the finite-stage Picard glue datum

The scalar-extended chart and overlap rings, their restriction maps, and the descended
pair and triple transitions satisfy the five hypotheses of
`AlgebraicJacobian.affineRingGlueData`.  This file packages those inputs into a scheme
glue datum.
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
set_option maxHeartbeats 3200000

variable {F : Type u} [Field F] [Algebra F k]
variable (L : DatG0.FinSubext F k)
variable [Algebra.IsAlgebraic L.1 k]
variable (n m : Pic0FiniteStageRingIndex C -> Nat)
variable (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
variable (M : DatG0.FinSubext L.1 k)
variable (mapM : forall q : Pic0FiniteStageMapIndex C,
  Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapSource C q) →ₐ[M.1]
    Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapTarget C q))
variable (N : DatG0.FinSubext M.1 k)

set_option maxHeartbeats 25600000 in
-- The five dependent tensor-product coherence fields elaborate in one constructor term.
/-- Assemble the descended finite-stage affine charts, transition maps, and structure map
into one pinned presentation.

Keeping the `Scheme.GlueData` and its `GluedMapData` in the same constructor scope prevents
later consumers from rebuilding a propositionally equal multicoequalizer map with different
dependent tensor instances. -/
noncomputable def pic0FiniteStageAffineRingGluePresentation
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
    (hOpen : forall i : Pic0FiniteStageRestrictionIndex C,
      IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (mapM (Sum.inl i)).toRingHom)))
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
                C L n m relation M mapM p)))) :
    AlgebraicJacobian.AffineRingGluePresentation N.1 := by
  let A : Pic0FiniteStageChartIndex C -> Type u := fun U =>
    Pic0FiniteStageChartBaseChangeRing C L n m relation M N U
  let B : Pic0FiniteStageChartIndex C -> Pic0FiniteStageChartIndex C -> Type u :=
    fun U V => Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V
  /- Keep the chart and overlap carriers tied to the explicit tensor-product
     witnesses used by the scalar-extension maps below.  Inferring these from
     the reducible aliases can select a propositionally equal, but different,
     semiring instance and make `Algebra (A U) (B U V)` ill-typed. -/
  letI (U : Pic0FiniteStageChartIndex C) : CommRing (A U) :=
    pic0FiniteStageChartBaseChangeCommRing C L n m relation M N U
  letI (U V : Pic0FiniteStageChartIndex C) : CommRing (B U V) :=
    pic0FiniteStageOverlapBaseChangeCommRing C L n m relation M N U V
  letI (U : Pic0FiniteStageChartIndex C) : Algebra N.1 (A U) :=
    pic0FiniteStageChartBaseChangeAlgebra C L n m relation M N U
  letI (U V : Pic0FiniteStageChartIndex C) : Algebra N.1 (B U V) :=
    pic0FiniteStageOverlapBaseChangeAlgebra C L n m relation M N U V
  let r : ∀ U V, A U →ₐ[N.1] B U V := fun U V =>
    pic0FiniteStageRestrictionBaseChange C L n m relation M mapM N U V
  letI : ∀ U V, Algebra (A U) (B U V) := fun U V =>
    @pic0FiniteStageAlgebraOfMap N.1 (A U) (B U V)
      (inferInstance : CommRing N.1)
      (inferInstance : CommRing (A U))
      (inferInstance : CommRing (B U V))
      (inferInstance : Algebra N.1 (A U))
      (inferInstance : Algebra N.1 (B U V))
      (r U V)
  letI : ∀ U V, IsScalarTower N.1 (A U) (B U V) := fun U V =>
    @pic0FiniteStageTowerOfMap N.1 (A U) (B U V)
      (inferInstance : CommRing N.1)
      (inferInstance : CommRing (A U))
      (inferInstance : CommRing (B U V))
      (inferInstance : Algebra N.1 (A U))
      (inferInstance : Algebra N.1 (B U V))
      (r U V)
  let tau : ∀ U V, B V U →ₐ[N.1] B U V := fun U V =>
    pic0FiniteStageTransitionBaseChange C L n m relation M mapM N U V
  let theta : ∀ U V W,
      AlgebraicJacobian.AffineTripleTensor A B V W U →ₐ[N.1]
        AlgebraicJacobian.AffineTripleTensor A B U V W := fun U V W =>
    pic0FiniteStageAffineTripleTransition
      C L n m relation M mapM N thetaN U V W
  refine AlgebraicJacobian.affineRingGluePresentation
    (R := N.1) A B tau theta ?_ ?_ ?_ ?_ ?_
  · intro U
    exact isIso_pic0FiniteStageRestrictionBaseChange_diagonal
      C L n m relation e M mapM hmapM N U
  · intro U V
    exact isOpenImmersion_pic0FiniteStageRestrictionBaseChange
      C L n m relation M mapM hOpen N U V
  · intro U
    exact pic0FiniteStageTransitionBaseChange_self
      C L n m relation e M mapM hmapM N U
  · intro U V W
    change
      (pic0FiniteStageAffineTripleTransition
        C L n m relation M mapM N thetaN U V W).comp
          (finiteStageTensorPushoutFaceRight (r V W) (r V U)) =
        (finiteStageTensorPushoutFaceLeft (r U V) (r U W)).comp
          (pic0FiniteStageTransitionBaseChange
            C L n m relation M mapM N U V)
    exact pic0FiniteStageAffineTripleTransition_fac
      C L n m relation M mapM N e hmapM thetaN hthetaN U V W
  · intro U V W
    change
      (pic0FiniteStageAffineTripleTransition
        C L n m relation M mapM N thetaN U V W).comp
          ((pic0FiniteStageAffineTripleTransition
            C L n m relation M mapM N thetaN V W U).comp
            (pic0FiniteStageAffineTripleTransition
              C L n m relation M mapM N thetaN W U V)) =
        AlgHom.id N.1
          (Pic0FiniteStageTripleBaseChangeRing
            C L n m relation M mapM N U V W)
    exact pic0FiniteStageAffineTripleTransition_cocycle
      C L n m relation M mapM N e hmapM thetaN hthetaN U V W

set_option maxHeartbeats 25600000 in
-- Projecting the presentation retains the same dependent tensor constructor term.
/-- Compatibility projection of the pinned affine presentation to its glue datum. -/
noncomputable def pic0FiniteStageAffineRingGlueData
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
    (hOpen : forall i : Pic0FiniteStageRestrictionIndex C,
      IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (mapM (Sum.inl i)).toRingHom)))
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
                C L n m relation M mapM p)))) :
    Scheme.GlueData.{u} :=
  (pic0FiniteStageAffineRingGluePresentation C L n m relation M mapM N
    e hmapM hOpen thetaN hthetaN).glueData

set_option synthInstance.maxHeartbeats 400000 in
-- The facade reuses three nested finite-subextension scalar towers from the context.
set_option maxHeartbeats 12800000 in
-- Elaborating the canonical face certificate normalizes its dependent tensor carriers.
/-- Assemble a pinned affine presentation directly from the canonical context facade.

The context stores the model comparison, open-immersion certificates, and final-stage
face equations with their dependent carriers already aligned.  This wrapper keeps those
witnesses opaque to consumers and makes the presentation a certified output of the context,
rather than an independent value sharing only its coefficient-field type.
-/
noncomputable def pic0FiniteStageAffineRingGluePresentation_of_canonical_context
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (D : Pic0FiniteStageCanonicalGlueContext C F) :
    AlgebraicJacobian.AffineRingGluePresentation D.context.triple.N.1 := by
  letI : Algebra.IsAlgebraic D.context.models.L.1 k := by infer_instance
  letI : Algebra.IsAlgebraic D.context.models.M.1 k := by infer_instance
  exact pic0FiniteStageAffineRingGluePresentation
    C D.context.models.L D.context.models.n D.context.models.m
      D.context.models.relation D.context.models.M D.context.models.mapM
      D.context.triple.N D.context.models.e D.context.models.comparison
      D.context.models.openImmersion D.context.triple.thetaN
      (fun p => D.comparison_of_models C p)

/-- Compatibility projection of the canonical presentation to its glue datum. -/
noncomputable def pic0FiniteStageAffineRingGlueData_of_canonical_context
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (D : Pic0FiniteStageCanonicalGlueContext C F) :
    Scheme.GlueData :=
  (pic0FiniteStageAffineRingGluePresentation_of_canonical_context C D).glueData

end

end

end AlgebraicGeometry
