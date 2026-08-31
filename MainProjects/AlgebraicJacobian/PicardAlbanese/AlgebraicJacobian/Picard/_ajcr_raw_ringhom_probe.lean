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
@[reducible] private noncomputable def probeFinalScalarAlgebra
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) (j : Pic0FiniteStageRingIndex C) :
    @Algebra P.N.1
      (P.N.1 ⊗[P.M.1] Pic0FiniteStageModelRing C P.L P.n P.m P.relation P.M j)
      (inferInstance : CommSemiring P.N.1)
      (pic0FiniteStageFinalModelRingCommSemiring C P.L P.n P.m P.relation P.M P.N j).toSemiring :=
  pic0FiniteStageFinalModelRingAlgebra C P.L P.n P.m P.relation P.M P.N j

@[reducible] private noncomputable def probeSeparateScalarAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    @Algebra N.1
      (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j)
      (inferInstance : CommSemiring N.1)
      (pic0FiniteStageModelScalarExtensionSemiring C L n m relation M N j) :=
  pic0FiniteStageModelScalarExtensionAlgebra C L n m relation M N j

@[reducible] private noncomputable def probeChartScalarAlgebra
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    @Algebra P.N.1
      (P.N.1 ⊗[P.M.1]
        Pic0FiniteStageChartModelRing C P.L P.n P.m P.relation P.M U)
      (inferInstance : CommSemiring P.N.1)
      (pic0FiniteStageModelScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inl U)) :=
  pic0FiniteStageModelScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
    (Sum.inl U)

@[reducible] private noncomputable def probeOverlapScalarAlgebra
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @Algebra P.N.1
      (P.N.1 ⊗[P.M.1]
        Pic0FiniteStageOverlapModelRing C P.L P.n P.m P.relation P.M U V)
      (inferInstance : CommSemiring P.N.1)
      (pic0FiniteStageModelScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
  pic0FiniteStageModelScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
    (Sum.inr (U, V))

private noncomputable def probeExplicitRestriction
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
      (N.1 ⊗[M.1] Pic0FiniteStageChartModelRing C L n m relation M U)
      (N.1 ⊗[M.1] Pic0FiniteStageOverlapModelRing C L n m relation M U V)
      (inferInstance : CommSemiring N.1)
      (pic0FiniteStageModelScalarExtensionSemiring C L n m relation M N (Sum.inl U))
      (pic0FiniteStageModelScalarExtensionSemiring C L n m relation M N
        (Sum.inr (U, V)))
      (pic0FiniteStageModelScalarExtensionAlgebra C L n m relation M N (Sum.inl U))
      (pic0FiniteStageModelScalarExtensionAlgebra C L n m relation M N
        (Sum.inr (U, V))) := by
  exact AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := N.1) (mapM (Sum.inl (Sum.inl (U, V))))

private noncomputable def probeExplicitRingHom
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
    RingHom
      (N.1 ⊗[M.1] Pic0FiniteStageChartModelRing C L n m relation M U)
      (N.1 ⊗[M.1] Pic0FiniteStageOverlapModelRing C L n m relation M U V) :=
  @AlgHom.toRingHom
    N.1
    (N.1 ⊗[M.1] Pic0FiniteStageChartModelRing C L n m relation M U)
    (N.1 ⊗[M.1] Pic0FiniteStageOverlapModelRing C L n m relation M U V)
    (inferInstance : CommSemiring N.1)
    (pic0FiniteStageModelScalarExtensionSemiring C L n m relation M N (Sum.inl U))
    (pic0FiniteStageModelScalarExtensionSemiring C L n m relation M N (Sum.inr (U, V)))
    (pic0FiniteStageModelScalarExtensionAlgebra C L n m relation M N (Sum.inl U))
    (pic0FiniteStageModelScalarExtensionAlgebra C L n m relation M N (Sum.inr (U, V)))
    (probeExplicitRestriction C L n m relation M mapM N U V)

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
      (probeExplicitRingHom C P.L P.n P.m P.relation P.M P.mapM P.N U V)) =
      Spec.map (CommRingCat.ofHom
        (probeExplicitRingHom C P.L P.n P.m P.relation P.M P.mapM P.N U V)) := by
  rfl

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
