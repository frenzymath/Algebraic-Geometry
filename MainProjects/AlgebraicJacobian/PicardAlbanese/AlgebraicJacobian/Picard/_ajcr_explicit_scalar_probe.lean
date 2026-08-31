import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionBaseChange
set_option autoImplicit false
universe u
open CategoryTheory TensorProduct
open scoped TensorProduct
namespace AlgebraicGeometry
noncomputable section
variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

private noncomputable def probeModelSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (Pic0FiniteStageModelRing C L n m relation M j) := by
  dsimp only [Pic0FiniteStageModelRing]
  infer_instance

private noncomputable def probeModelAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) := by
  dsimp only [Pic0FiniteStageModelRing]
  infer_instance

private noncomputable def probeScalarSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j) :=
  @Algebra.TensorProduct.instSemiring M.1 N.1
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (probeModelSemiring C L n m relation M j)
    (probeModelAlgebra C L n m relation M j)

private noncomputable def probeScalarAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    @Algebra N.1
      (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j)
      (inferInstance : CommSemiring N.1)
      (probeScalarSemiring C L n m relation M N j) :=
  @Algebra.TensorProduct.leftAlgebra M.1 N.1 N.1
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (probeModelSemiring C L n m relation M j)
    (probeModelAlgebra C L n m relation M j)
    (inferInstance : CommSemiring N.1)
    (inferInstance : Algebra N.1 N.1)
    (inferInstance : SMulCommClass M.1 N.1 N.1)

private noncomputable def probeRestriction
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C → Nat)
    (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (N : DatG0.FinSubext M.1 k)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom N.1
      (N.1 ⊗[M.1] Pic0FiniteStageChartModelRing C L n m relation M U)
      (N.1 ⊗[M.1] Pic0FiniteStageOverlapModelRing C L n m relation M U V)
      (inferInstance : CommSemiring N.1)
      (probeScalarSemiring C L n m relation M N (Sum.inl U))
      (probeScalarSemiring C L n m relation M N (Sum.inr (U, V)))
      (probeScalarAlgebra C L n m relation M N (Sum.inl U))
      (probeScalarAlgebra C L n m relation M N (Sum.inr (U, V))) := by
  exact AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := N.1) (mapM (Sum.inl (Sum.inl (U, V))))

attribute [local instance 100000] probeScalarSemiring probeScalarAlgebra

namespace Pic0FiniteStageGluePackage
example {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    Spec.map (CommRingCat.ofHom
      (probeRestriction C P.L P.n P.m P.relation P.M P.mapM P.N U V).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (probeRestriction C P.L P.n P.m P.relation P.M P.mapM P.N U V).toRingHom) := by
  rfl
end Pic0FiniteStageGluePackage
end
end AlgebraicGeometry
