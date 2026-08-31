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
namespace Pic0FiniteStageGluePackage
example {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom P.M.1
      (Pic0FiniteStageModelRing C P.L P.n P.m P.relation P.M
        (Pic0FiniteStageMapSource C (Sum.inl (Sum.inl (U, V)))))
      (Pic0FiniteStageModelRing C P.L P.n P.m P.relation P.M
        (Pic0FiniteStageMapTarget C (Sum.inl (Sum.inl (U, V)))))
      (inferInstance : CommSemiring P.M.1)
      (pic0FiniteStageModelRingCommRing C P.L P.n P.m P.relation P.M
        (Pic0FiniteStageMapSource C (Sum.inl (Sum.inl (U, V))))).toSemiring
      (pic0FiniteStageModelRingCommRing C P.L P.n P.m P.relation P.M
        (Pic0FiniteStageMapTarget C (Sum.inl (Sum.inl (U, V))))).toSemiring
      (pic0FiniteStageModelRingAlgebra C P.L P.n P.m P.relation P.M
        (Pic0FiniteStageMapSource C (Sum.inl (Sum.inl (U, V)))))
      (pic0FiniteStageModelRingAlgebra C P.L P.n P.m P.relation P.M
        (Pic0FiniteStageMapTarget C (Sum.inl (Sum.inl (U, V))))) := by
  exact P.mapM (Sum.inl (Sum.inl (U, V)))
end Pic0FiniteStageGluePackage
end
end AlgebraicGeometry
