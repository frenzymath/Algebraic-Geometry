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

private noncomputable def probeAliasRestriction
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
      (pic0FiniteStageChartBaseChangeRingCommRing C L n m relation M N U).toSemiring
      (pic0FiniteStageOverlapBaseChangeRingCommRing C L n m relation M N U V).toSemiring
      (pic0FiniteStageChartBaseChangeRingAlgebra C L n m relation M N U)
      (pic0FiniteStageOverlapBaseChangeRingAlgebra C L n m relation M N U V) := by
  exact AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := N.1) (mapM (Sum.inl (Sum.inl (U, V))))

example {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    Spec.map (CommRingCat.ofHom
      (probeAliasRestriction C P.L P.n P.m P.relation P.M P.mapM P.N U V).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (probeAliasRestriction C P.L P.n P.m P.relation P.M P.mapM P.N U V).toRingHom) := by
  rfl
end Pic0FiniteStageGluePackage
end
end AlgebraicGeometry
