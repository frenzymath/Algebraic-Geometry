import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionBaseChange
set_option autoImplicit false
universe u
open CategoryTheory Limits TensorProduct
open scoped TensorProduct
namespace AlgebraicGeometry
noncomputable section
variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

private noncomputable def probeRelationCommRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    CommRing (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
  Ideal.Quotient.commRing (Ideal.span (Set.range (relation j)))

private noncomputable def probeRelationSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
  (probeRelationCommRing C L n m relation j).toSemiring

private noncomputable def probeRelationAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra L.1 (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
  Ideal.instAlgebraQuotient L.1 (Ideal.span (Set.range (relation j)))

private noncomputable def probeModelAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
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

private noncomputable def probeModelSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (Pic0FiniteStageModelRing C L n m relation M j) := by
  dsimp only [Pic0FiniteStageModelRing]
  exact @Algebra.TensorProduct.instSemiring L.1 M.1
    (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : CommSemiring L.1)
    (inferInstance : Semiring M.1)
    (inferInstance : Algebra L.1 M.1)
    (probeRelationSemiring C L n m relation j)
    (probeRelationAlgebra C L n m relation j)

private noncomputable instance probeModelCommRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    CommRing (Pic0FiniteStageModelRing C L n m relation M j) := by
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    probeModelAlgebra C L n m relation M j
  letI : CommRing (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
    probeRelationCommRing C L n m relation j
  letI : CommSemiring
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
    (probeRelationCommRing C L n m relation j).toCommSemiring
  letI : Algebra L.1
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
    probeRelationAlgebra C L n m relation j
  dsimp only [Pic0FiniteStageModelRing]
  exact @Algebra.TensorProduct.instCommRing
    L.1 M.1
    (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : CommSemiring L.1)
    (inferInstance : CommRing M.1)
    (inferInstance : Algebra L.1 M.1)
    (inferInstance : CommSemiring
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))
    (inferInstance : Algebra L.1
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))

private noncomputable instance probeModelScalarSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j) := by
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    probeModelAlgebra C L n m relation M j
  exact @Algebra.TensorProduct.instSemiring M.1 N.1
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (probeModelSemiring C L n m relation M j)
    (probeModelAlgebra C L n m relation M j)

private noncomputable instance probeModelScalarAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra N.1 (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j) := by
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    probeModelAlgebra C L n m relation M j
  letI : Semiring (Pic0FiniteStageModelRing C L n m relation M j) :=
    probeModelSemiring C L n m relation M j
  exact @Algebra.TensorProduct.leftAlgebra M.1 N.1 N.1
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (probeModelSemiring C L n m relation M j)
    (probeModelAlgebra C L n m relation M j)
    (inferInstance : CommSemiring N.1)
    (inferInstance : Algebra N.1 N.1)
    (inferInstance : SMulCommClass M.1 N.1 N.1)

namespace Pic0FiniteStageGluePackage
example {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    Spec.map (CommRingCat.ofHom
      (pic0FiniteStageRestrictionBaseChange
        C P.L P.n P.m P.relation P.M P.mapM P.N U V).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (pic0FiniteStageRestrictionBaseChange
          C P.L P.n P.m P.relation P.M P.mapM P.N U V).toRingHom) := by
  rfl
end Pic0FiniteStageGluePackage
end
end AlgebraicGeometry
