import AlgebraicJacobian.Picard.Pic0FiniteStageGluePackage

set_option autoImplicit false
universe u
open CategoryTheory TensorProduct
open scoped TensorProduct
namespace AlgebraicGeometry
noncomputable section
variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

noncomputable instance probeChartCommRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (U : Pic0FiniteStageChartIndex C) :
    CommRing (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U) := by
  letI : Algebra M.1
      (Pic0FiniteStageChartModelRing C L n m relation M U) :=
    Algebra.TensorProduct.leftAlgebra
      (R := L.1) (S := M.1) (A := M.1)
      (B := DatG0.FiniteRelationAlgebra L.1
        (n (Sum.inl U)) (m (Sum.inl U)) (relation (Sum.inl U)))
  letI : CommRing
      (Pic0FiniteStageChartModelRing C L n m relation M U) := inferInstance
  letI : CommSemiring
      (Pic0FiniteStageChartModelRing C L n m relation M U) :=
    (inferInstance : CommRing
      (Pic0FiniteStageChartModelRing C L n m relation M U)).toCommSemiring
  dsimp only [Pic0FiniteStageChartBaseChangeRing]
  exact Algebra.TensorProduct.instCommRing

noncomputable def probeChartAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (U : Pic0FiniteStageChartIndex C) :
    Algebra N.1 (Pic0FiniteStageChartBaseChangeRing C L n m relation M N U) := by
  letI : Algebra M.1
      (Pic0FiniteStageChartModelRing C L n m relation M U) :=
    Algebra.TensorProduct.leftAlgebra
      (R := L.1) (S := M.1) (A := M.1)
      (B := DatG0.FiniteRelationAlgebra L.1
        (n (Sum.inl U)) (m (Sum.inl U)) (relation (Sum.inl U)))
  dsimp only [Pic0FiniteStageChartBaseChangeRing]
  exact Algebra.TensorProduct.leftAlgebra
    (R := M.1) (S := N.1) (A := N.1)
    (B := Pic0FiniteStageChartModelRing C L n m relation M U)

end
end AlgebraicGeometry
