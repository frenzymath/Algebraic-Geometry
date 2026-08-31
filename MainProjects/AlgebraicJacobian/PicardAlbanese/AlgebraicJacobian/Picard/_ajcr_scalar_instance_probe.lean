import AlgebraicJacobian.Picard.Pic0FiniteStageScalarExtendedAtlas

set_option autoImplicit false
universe u
open CategoryTheory TensorProduct
open scoped TensorProduct
namespace AlgebraicGeometry
noncomputable section
variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

private noncomputable def scalarSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k) (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j) :=
  @Algebra.TensorProduct.instSemiring M.1 N.1
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1) (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (inferInstance : Semiring (Pic0FiniteStageModelRing C L n m relation M j))
    (inferInstance : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j))

private noncomputable def scalarAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k) (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    @Algebra N.1
      (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j)
      (inferInstance : CommSemiring N.1) (scalarSemiring C L n m relation M N j) :=
  @Algebra.TensorProduct.leftAlgebra M.1 N.1 N.1
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1) (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (inferInstance : Semiring (Pic0FiniteStageModelRing C L n m relation M j))
    (inferInstance : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j))
    (inferInstance : CommSemiring N.1) (inferInstance : Algebra N.1 N.1)
    (inferInstance : SMulCommClass M.1 N.1 N.1)

private noncomputable def foo
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
      (scalarSemiring C L n m relation M N (Sum.inl U))
      (scalarSemiring C L n m relation M N (Sum.inr (U, V)))
      (scalarAlgebra C L n m relation M N (Sum.inl U))
      (scalarAlgebra C L n m relation M N (Sum.inr (U, V))) := by
  exact AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := N.1) (mapM (Sum.inl (Sum.inl (U, V))))

private noncomputable def triple
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
    (U V W : Pic0FiniteStageChartIndex C) : Type u := by
  letI : CommRing
      (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U) :=
    pic0FiniteStageChartBaseChangeCommRing C L n m relation M N U
  letI : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V) :=
    pic0FiniteStageOverlapBaseChangeCommRing C L n m relation M N U V
  letI : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U W) :=
    pic0FiniteStageOverlapBaseChangeCommRing C L n m relation M N U W
  letI : Algebra N.1
      (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U) :=
    pic0FiniteStageChartBaseChangeAlgebra C L n m relation M N U
  letI : Algebra N.1
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V) :=
    pic0FiniteStageOverlapBaseChangeAlgebra C L n m relation M N U V
  letI : Algebra N.1
      (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U W) :=
    pic0FiniteStageOverlapBaseChangeAlgebra C L n m relation M N U W
  let f1 := pic0FiniteStageRestrictionBaseChange C L n m relation M mapM N U V
  let f2 := pic0FiniteStageRestrictionBaseChange C L n m relation M mapM N U W
  exact @Pic0FiniteStageTensorPushoutRing
    N.1
    (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U)
    (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V)
    (Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U W)
    (inferInstance : CommRing N.1)
    (pic0FiniteStageChartBaseChangeCommRing C L n m relation M N U)
    (pic0FiniteStageOverlapBaseChangeCommRing C L n m relation M N U V)
    (pic0FiniteStageOverlapBaseChangeCommRing C L n m relation M N U W)
    (pic0FiniteStageChartBaseChangeAlgebra C L n m relation M N U)
    (pic0FiniteStageOverlapBaseChangeAlgebra C L n m relation M N U V)
    (pic0FiniteStageOverlapBaseChangeAlgebra C L n m relation M N U W)
    f1 f2

example {F : Type u} [Field F] [Algebra F k]
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
    (U V W : Pic0FiniteStageChartIndex C) :
    Type u := triple C L n m relation M mapM N U V W

example {F : Type u} [Field F] [Algebra F k]
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
    Spec.map (CommRingCat.ofHom
      (foo C L n m relation M mapM N U V).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (foo C L n m relation M mapM N U V).toRingHom) := by
  rfl
end
end AlgebraicGeometry
