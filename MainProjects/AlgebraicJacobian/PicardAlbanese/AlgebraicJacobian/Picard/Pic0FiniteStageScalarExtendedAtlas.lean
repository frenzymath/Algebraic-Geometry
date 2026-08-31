/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.OpenImmersionScalarExtension
import AlgebraicJacobian.Descent.TensorProductFieldTowerMap
import AlgebraicJacobian.Picard.Pic0FiniteStageDiagonalRestrictions
import AlgebraicJacobian.Picard.Pic0FiniteStageTransitionIdentity

/-!
# Scalar extension of the finite-stage Picard atlas

After the chart rings, overlap rings, restriction maps, and pair transitions have been
modeled over a finite subextension `M`, the triple transitions may require a further finite
subextension `N/M`.  This file puts the chart and pair data over that same field `N`.

The resulting restriction legs remain open immersions, diagonal restrictions remain
isomorphisms, and diagonal pair transitions remain the identity.  These are three of the
five inputs required by `AlgebraicJacobian.affineRingGlueData`; the triple face and cocycle
equations are supplied by the triple-transition descent modules.
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

/-- A finite-stage chart ring after the further scalar extension `M -> N`. -/
noncomputable abbrev Pic0FiniteStageChartBaseChangeRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (U : Pic0FiniteStageChartIndex C) : Type u :=
  N.1 ⊗[M.1] Pic0FiniteStageChartModelRing C L n m relation M U

/-- A finite-stage ordered overlap ring after the further scalar extension `M -> N`. -/
noncomputable abbrev Pic0FiniteStageOverlapBaseChangeRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (U V : Pic0FiniteStageChartIndex C) : Type u :=
  N.1 ⊗[M.1] Pic0FiniteStageOverlapModelRing C L n m relation M U V

/-!
The scalar-extended rings admit several propositionally equal tensor-product hierarchy
witnesses.  A raw `AlgHom` remembers the witnesses selected when it was elaborated, while
`CommRingCat.ofHom` normally asks typeclass search to synthesize them again.  The resulting
terms need not be definitionally equal.  Keep one explicit set of witnesses at this API
boundary and use it for every exported map.
-/

/-- The canonical commutative-ring structure on a scalar-extended chart carrier. -/
@[reducible]
noncomputable def pic0FiniteStageChartBaseChangeCommRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (U : Pic0FiniteStageChartIndex C) :
    CommRing (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U) :=
  @Algebra.TensorProduct.instCommRing M.1 N.1
    (Pic0FiniteStageChartModelRing C L n m relation M U)
    (inferInstance : CommSemiring M.1) (inferInstance : CommRing N.1)
    (inferInstance : Algebra M.1 N.1)
    (inferInstance : CommSemiring
      (Pic0FiniteStageChartModelRing C L n m relation M U))
    (inferInstance : Algebra M.1
      (Pic0FiniteStageChartModelRing C L n m relation M U))

/-- The canonical `N`-algebra structure on a scalar-extended chart carrier. -/
@[reducible]
noncomputable def pic0FiniteStageChartBaseChangeAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (U : Pic0FiniteStageChartIndex C) :
    @Algebra N.1
      (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U)
      (inferInstance : CommSemiring N.1)
      (pic0FiniteStageChartBaseChangeCommRing
        C L n m relation M N U).toSemiring :=
  @Algebra.TensorProduct.leftAlgebra M.1 N.1 N.1
    (Pic0FiniteStageChartModelRing C L n m relation M U)
    (inferInstance : CommSemiring M.1) (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (inferInstance : Semiring
      (Pic0FiniteStageChartModelRing C L n m relation M U))
    (inferInstance : Algebra M.1
      (Pic0FiniteStageChartModelRing C L n m relation M U))
    (inferInstance : CommSemiring N.1) (inferInstance : Algebra N.1 N.1)
    (inferInstance : SMulCommClass M.1 N.1 N.1)

/-- The canonical commutative-ring structure on a scalar-extended overlap carrier. -/
@[reducible]
noncomputable def pic0FiniteStageOverlapBaseChangeCommRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (U V : Pic0FiniteStageChartIndex C) :
    CommRing (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V) :=
  @Algebra.TensorProduct.instCommRing M.1 N.1
    (Pic0FiniteStageOverlapModelRing C L n m relation M U V)
    (inferInstance : CommSemiring M.1) (inferInstance : CommRing N.1)
    (inferInstance : Algebra M.1 N.1)
    (inferInstance : CommSemiring
      (Pic0FiniteStageOverlapModelRing C L n m relation M U V))
    (inferInstance : Algebra M.1
      (Pic0FiniteStageOverlapModelRing C L n m relation M U V))

/-- The canonical `N`-algebra structure on a scalar-extended overlap carrier. -/
@[reducible]
noncomputable def pic0FiniteStageOverlapBaseChangeAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (U V : Pic0FiniteStageChartIndex C) :
    @Algebra N.1
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V)
      (inferInstance : CommSemiring N.1)
      (pic0FiniteStageOverlapBaseChangeCommRing
        C L n m relation M N U V).toSemiring :=
  @Algebra.TensorProduct.leftAlgebra M.1 N.1 N.1
    (Pic0FiniteStageOverlapModelRing C L n m relation M U V)
    (inferInstance : CommSemiring M.1) (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (inferInstance : Semiring
      (Pic0FiniteStageOverlapModelRing C L n m relation M U V))
    (inferInstance : Algebra M.1
      (Pic0FiniteStageOverlapModelRing C L n m relation M U V))
    (inferInstance : CommSemiring N.1) (inferInstance : Algebra N.1 N.1)
    (inferInstance : SMulCommClass M.1 N.1 N.1)

/-- Scalar extension to `N` of the descended left restriction from a chart to an
ordered overlap. -/
noncomputable def pic0FiniteStageRestrictionBaseChange
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (N : DatG0.FinSubext M.1 k)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom N.1
      (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U)
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V)
      (inferInstance : CommSemiring N.1)
      (pic0FiniteStageChartBaseChangeCommRing
        C L n m relation M N U).toSemiring
      (pic0FiniteStageOverlapBaseChangeCommRing
        C L n m relation M N U V).toSemiring
      (pic0FiniteStageChartBaseChangeAlgebra C L n m relation M N U)
      (pic0FiniteStageOverlapBaseChangeAlgebra C L n m relation M N U V) :=
  AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := N.1) (mapM (Sum.inl (Sum.inl (U, V))))

/-- Scalar extension to `N` of the descended transition from the reversed ordered
overlap to the forward ordered overlap. -/
noncomputable def pic0FiniteStageTransitionBaseChange
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (N : DatG0.FinSubext M.1 k)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom N.1
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N V U)
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V)
      (inferInstance : CommSemiring N.1)
      (pic0FiniteStageOverlapBaseChangeCommRing
        C L n m relation M N V U).toSemiring
      (pic0FiniteStageOverlapBaseChangeCommRing
        C L n m relation M N U V).toSemiring
      (pic0FiniteStageOverlapBaseChangeAlgebra C L n m relation M N V U)
      (pic0FiniteStageOverlapBaseChangeAlgebra C L n m relation M N U V) :=
  AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := N.1) (mapM (Sum.inr (U, V)))

/-- The scalar-extended left restriction as a bundled commutative-ring morphism.

This is the stable scheme-facing API: its source and target remember the same hierarchy
witnesses as `pic0FiniteStageRestrictionBaseChange`. -/
noncomputable def pic0FiniteStageRestrictionBaseChangeRingHom
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (N : DatG0.FinSubext M.1 k)
    (U V : Pic0FiniteStageChartIndex C) :=
  @CommRingCat.ofHom _ _
    (pic0FiniteStageChartBaseChangeCommRing C L n m relation M N U)
    (pic0FiniteStageOverlapBaseChangeCommRing C L n m relation M N U V)
    (pic0FiniteStageRestrictionBaseChange
      C L n m relation M mapM N U V).toRingHom

/-- The scalar-extended finite-stage restriction legs remain open immersions. -/
theorem isOpenImmersion_pic0FiniteStageRestrictionBaseChange
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (hOpen : forall i : Pic0FiniteStageRestrictionIndex C,
      IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (mapM (Sum.inl i)).toRingHom)))
    (N : DatG0.FinSubext M.1 k)
    (U V : Pic0FiniteStageChartIndex C) :
    IsOpenImmersion (Spec.map
      (pic0FiniteStageRestrictionBaseChangeRingHom
        C L n m relation M mapM N U V)) := by
  letI : CommRing
      (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U) :=
    pic0FiniteStageChartBaseChangeCommRing C L n m relation M N U
  letI : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V) :=
    pic0FiniteStageOverlapBaseChangeCommRing C L n m relation M N U V
  letI : Algebra N.1
      (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U) :=
    pic0FiniteStageChartBaseChangeAlgebra C L n m relation M N U
  letI : Algebra N.1
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V) :=
    pic0FiniteStageOverlapBaseChangeAlgebra C L n m relation M N U V
  exact isOpenImmersion_scalarExtensionMapOfAlgHom
    (mapM (Sum.inl (Sum.inl (U, V)))) (hOpen (Sum.inl (U, V)))

/-- A diagonal scalar-extended restriction is an isomorphism. -/
theorem isIso_pic0FiniteStageRestrictionBaseChange_diagonal
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
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
    (N : DatG0.FinSubext M.1 k)
    (U : Pic0FiniteStageChartIndex C) :
    IsIso (Spec.map
      (pic0FiniteStageRestrictionBaseChangeRingHom
        C L n m relation M mapM N U U)) := by
  letI : CommRing
      (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U) :=
    pic0FiniteStageChartBaseChangeCommRing C L n m relation M N U
  letI : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U U) :=
    pic0FiniteStageOverlapBaseChangeCommRing C L n m relation M N U U
  letI : Algebra N.1
      (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U) :=
    pic0FiniteStageChartBaseChangeAlgebra C L n m relation M N U
  letI : Algebra N.1
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U U) :=
    pic0FiniteStageOverlapBaseChangeAlgebra C L n m relation M N U U
  exact isIso_specMap_scalarExtensionMapOfAlgHom
    (mapM (Sum.inl (Sum.inl (U, U))))
    (isIso_specMap_pic0FiniteStageModelRestriction_diagonal_left
      C L n m relation e M mapM hmapM U)

/-- The diagonal pair transition remains the identity after scalar extension to `N`. -/
theorem pic0FiniteStageTransitionBaseChange_self
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    [Algebra.IsAlgebraic L.1 k]
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
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
    (N : DatG0.FinSubext M.1 k)
    (U : Pic0FiniteStageChartIndex C) :
    pic0FiniteStageTransitionBaseChange C L n m relation M mapM N U U =
      AlgHom.id N.1
        (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U U) := by
  rw [pic0FiniteStageTransitionBaseChange,
    pic0FiniteStageTransitionModel_self C L n m relation e M mapM hmapM U]
  exact AlgebraicJacobian.scalarExtensionMapOfAlgHom_id

end

end

end AlgebraicGeometry
