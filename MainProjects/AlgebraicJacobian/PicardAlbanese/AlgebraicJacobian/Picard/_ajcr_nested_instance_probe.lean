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
variable {F : Type u} [Field F] [Algebra F k]
variable (L : DatG0.FinSubext F k)
variable (n m : Pic0FiniteStageRingIndex C → Nat)
variable (relation : forall j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
variable (M : DatG0.FinSubext L.1 k)
variable (N : DatG0.FinSubext M.1 k)
variable (U V : Pic0FiniteStageChartIndex C)
variable (P : Pic0FiniteStageGluePackage C F)

example : Algebra N.1
    (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M
      (Sum.inr (U, V))) := by infer_instance

example : Algebra N.1
    (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M
      (Sum.inr (U, V))) :=
  pic0FiniteStageModelScalarExtensionAlgebra C L n m relation M N
    (Sum.inr (U, V))

example : Semiring
    (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M
      (Sum.inr (U, V))) :=
  pic0FiniteStageModelScalarExtensionSemiring C L n m relation M N
    (Sum.inr (U, V))

example :
    Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U →ₐ[P.N.1]
      Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V := by
  exact (pic0FiniteStageRestrictionBaseChange
    C P.L P.n P.m P.relation P.M P.mapM P.N U V)

end
end AlgebraicGeometry
