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
namespace Pic0FiniteStageGluePackage

@[reducible] private noncomputable def probeChartSemiring
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    Semiring (Pic0FiniteStageChartBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N U) :=
  (pic0FiniteStageFinalModelRingCommRing
    C P.L P.n P.m P.relation P.M P.N (Sum.inl U)).toSemiring

@[reducible] private noncomputable def probeChartAlgebra
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    @Algebra P.N.1
      (Pic0FiniteStageChartBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U)
      (inferInstance : CommSemiring P.N.1)
      (probeChartSemiring C P U) :=
  pic0FiniteStageFinalModelRingAlgebra
    C P.L P.n P.m P.relation P.M P.N (Sum.inl U)

@[reducible] private noncomputable def probeOverlapSemiring
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    Semiring (Pic0FiniteStageOverlapBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N U V) :=
  (pic0FiniteStageOverlapBaseChangeRingCommRing
    C P.L P.n P.m P.relation P.M P.N U V).toSemiring

@[reducible] private noncomputable def probeOverlapAlgebra
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @Algebra P.N.1
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V)
      (inferInstance : CommSemiring P.N.1)
      (probeOverlapSemiring C P U V) :=
  pic0FiniteStageOverlapBaseChangeRingAlgebra
    C P.L P.n P.m P.relation P.M P.N U V

attribute [local instance 100000] probeChartSemiring probeChartAlgebra
  probeOverlapSemiring probeOverlapAlgebra

@[reducible] private noncomputable def probeModelScalarSemiring
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (P.N.1 ⊗[P.M.1]
      Pic0FiniteStageModelRing C P.L P.n P.m P.relation P.M j) :=
  pic0FiniteStageModelScalarExtensionSemiring
    C P.L P.n P.m P.relation P.M P.N j

@[reducible] private noncomputable def probeModelScalarAlgebra
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (j : Pic0FiniteStageRingIndex C) :
    @Algebra P.N.1
      (P.N.1 ⊗[P.M.1]
        Pic0FiniteStageModelRing C P.L P.n P.m P.relation P.M j)
      (inferInstance : CommSemiring P.N.1)
      (probeModelScalarSemiring C P j) :=
  pic0FiniteStageModelScalarExtensionAlgebra
    C P.L P.n P.m P.relation P.M P.N j

attribute [local instance 100000] probeModelScalarSemiring probeModelScalarAlgebra

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
