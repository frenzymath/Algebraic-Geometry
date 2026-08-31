import AlgebraicJacobian.Picard.Pic0FiniteStageTransitionModels
import AlgebraicJacobian.Descent.TensorProductFieldTowerMap

set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct
namespace AlgebraicGeometry
noncomputable section
variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

@[reducible] private noncomputable def probeRelationCommRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    CommRing (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
  Ideal.Quotient.commRing (Ideal.span (Set.range (relation j)))

@[reducible] private noncomputable def probeRelationSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
  (probeRelationCommRing C L n m relation j).toSemiring

@[reducible] private noncomputable def probeRelationAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra L.1 (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
  Ideal.instAlgebraQuotient L.1 (Ideal.span (Set.range (relation j)))

attribute [local instance] probeRelationCommRing probeRelationSemiring probeRelationAlgebra

@[reducible] private noncomputable def probeModelSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (Pic0FiniteStageModelRing C L n m relation M j) :=
  @Algebra.TensorProduct.instSemiring
    L.1 M.1 (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : CommSemiring L.1)
    (inferInstance : Semiring M.1)
    (inferInstance : Algebra L.1 M.1)
    (probeRelationSemiring C L n m relation j)
    (probeRelationAlgebra C L n m relation j)

attribute [local instance] probeModelSemiring

@[reducible] private noncomputable def probeModelAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) := by
  dsimp only [Pic0FiniteStageModelRing]
  exact @Algebra.TensorProduct.leftAlgebra
    L.1 M.1 M.1
    (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : CommSemiring L.1)
    (inferInstance : Semiring M.1)
    (inferInstance : Algebra L.1 M.1)
    (probeRelationSemiring C L n m relation j)
    (probeRelationAlgebra C L n m relation j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Algebra M.1 M.1)
    (inferInstance : SMulCommClass L.1 M.1 M.1)

@[reducible] private noncomputable def probeModelCommRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    CommRing (Pic0FiniteStageModelRing C L n m relation M j) := by
  dsimp only [Pic0FiniteStageModelRing]
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    probeModelAlgebra C L n m relation M j
  exact Algebra.TensorProduct.instCommRing

set_option synthInstance.maxHeartbeats 3200000 in
set_option maxHeartbeats 12800000 in
private noncomputable def probeRestriction
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
    (U V : Pic0FiniteStageChartIndex C) := by
  letI : Algebra N.1
      (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M
        (Pic0FiniteStageMapSource C (Sum.inl (Sum.inl (U, V))))) :=
    @Algebra.TensorProduct.leftAlgebra
      M.1 N.1 N.1
      (Pic0FiniteStageModelRing C L n m relation M
        (Pic0FiniteStageMapSource C (Sum.inl (Sum.inl (U, V)))))
      (inferInstance : CommSemiring M.1)
      (inferInstance : Semiring N.1)
      (inferInstance : Algebra M.1 N.1)
      (probeModelSemiring C L n m relation M
        (Pic0FiniteStageMapSource C (Sum.inl (Sum.inl (U, V)))))
      (probeModelAlgebra C L n m relation M
        (Pic0FiniteStageMapSource C (Sum.inl (Sum.inl (U, V)))))
      (inferInstance : CommSemiring N.1)
      (inferInstance : Algebra N.1 N.1)
      (inferInstance : SMulCommClass M.1 N.1 N.1)
  letI : Algebra N.1
      (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M
        (Pic0FiniteStageMapTarget C (Sum.inl (Sum.inl (U, V))))) :=
    @Algebra.TensorProduct.leftAlgebra
      M.1 N.1 N.1
      (Pic0FiniteStageModelRing C L n m relation M
        (Pic0FiniteStageMapTarget C (Sum.inl (Sum.inl (U, V)))))
      (inferInstance : CommSemiring M.1)
      (inferInstance : Semiring N.1)
      (inferInstance : Algebra M.1 N.1)
      (probeModelSemiring C L n m relation M
        (Pic0FiniteStageMapTarget C (Sum.inl (Sum.inl (U, V)))))
      (probeModelAlgebra C L n m relation M
        (Pic0FiniteStageMapTarget C (Sum.inl (Sum.inl (U, V)))))
      (inferInstance : CommSemiring N.1)
      (inferInstance : Algebra N.1 N.1)
      (inferInstance : SMulCommClass M.1 N.1 N.1)
  exact @AlgebraicJacobian.scalarExtensionMapOfAlgHom
    M.1 N.1
      (Pic0FiniteStageModelRing C L n m relation M
        (Pic0FiniteStageMapSource C (Sum.inl (Sum.inl (U, V)))))
      (Pic0FiniteStageModelRing C L n m relation M
        (Pic0FiniteStageMapTarget C (Sum.inl (Sum.inl (U, V)))))
      (inferInstance : CommRing M.1)
      (inferInstance : CommRing N.1)
      (probeModelCommRing C L n m relation M
        (Pic0FiniteStageMapSource C (Sum.inl (Sum.inl (U, V))))).toSemiring
      (probeModelCommRing C L n m relation M
        (Pic0FiniteStageMapTarget C (Sum.inl (Sum.inl (U, V))))).toSemiring
      (inferInstance : Algebra M.1 N.1)
      (probeModelAlgebra C L n m relation M
        (Pic0FiniteStageMapSource C (Sum.inl (Sum.inl (U, V)))))
      (probeModelAlgebra C L n m relation M
        (Pic0FiniteStageMapTarget C (Sum.inl (Sum.inl (U, V)))))
      (mapM (Sum.inl (Sum.inl (U, V))))

end
end AlgebraicGeometry
