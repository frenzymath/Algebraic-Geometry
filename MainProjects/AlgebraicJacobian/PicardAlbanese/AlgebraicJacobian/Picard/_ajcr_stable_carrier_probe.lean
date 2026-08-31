import AlgebraicJacobian.Picard.Pic0FiniteStageScalarExtendedAtlas
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleTransitionModels
import AlgebraicJacobian.Picard.Pic0FiniteStageTensorPushoutUniversal

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

noncomputable def StableChart
    (L : DatG0.FinSubext F k) (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k) (N : DatG0.FinSubext M.1 k)
    (U : Pic0FiniteStageChartIndex C) : Type u :=
  Pic0FiniteStageChartBaseChangeRing C L n m relation M N U

noncomputable def StableOverlap
    (L : DatG0.FinSubext F k) (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k) (N : DatG0.FinSubext M.1 k)
    (U V : Pic0FiniteStageChartIndex C) : Type u :=
  Pic0FiniteStageOverlapBaseChangeRing C L n m relation M N U V

noncomputable def StableTriple
    (L : DatG0.FinSubext F k) (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (N : DatG0.FinSubext M.1 k) (U V W : Pic0FiniteStageChartIndex C) : Type u :=
  Pic0FiniteStageTripleBaseChangeRing C L n m relation M mapM N U V W

noncomputable instance stableTripleCommRing
    (L : DatG0.FinSubext F k) (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (N : DatG0.FinSubext M.1 k) (U V W : Pic0FiniteStageChartIndex C) :
    CommRing (StableTriple C L n m relation M mapM N U V W) := by
  unfold StableTriple
  infer_instance

noncomputable instance stableTripleAlgebra
    (L : DatG0.FinSubext F k) (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (N : DatG0.FinSubext M.1 k) (U V W : Pic0FiniteStageChartIndex C) :
    Algebra N.1 (StableTriple C L n m relation M mapM N U V W) := by
  unfold StableTriple
  infer_instance

def stableTripleId
    (L : DatG0.FinSubext F k) (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (N : DatG0.FinSubext M.1 k) (U V W : Pic0FiniteStageChartIndex C) :
    AlgHom.id N.1 (StableTriple C L n m relation M mapM N U V W) :=
  AlgHom.id N.1 _

end
end AlgebraicGeometry
