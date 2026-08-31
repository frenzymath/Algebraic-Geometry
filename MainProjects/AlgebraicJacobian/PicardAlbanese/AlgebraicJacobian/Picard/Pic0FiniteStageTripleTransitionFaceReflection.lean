/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FinitePresentationAlgebraMapFiniteStage
import AlgebraicJacobian.Picard.Pic0FiniteStageTransportedTripleTransitionFace

/-!
# Reflection of the finite-stage triple-transition face equation

The canonical maps out of tensor products carry dependent module and algebra instances.
This file keeps those instances coherent by packaging a finite-stage transition, the two
canonical comparison maps, and their square under one inference boundary.  Applying the
package to the two paths around a triple-overlap face reflects the ambient face equation
without rebuilding any tensor-product carrier metadata.
-/

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

/-- A scalar-extension face diagram together with the canonical comparison square for its
lower transition.  All four algebra carriers and their instances are parameters of one
structure, so projections never resynthesize tensor-product metadata. -/
structure ScalarExtensionFacePackage
    {F K A B D E : Type u}
    [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]
    [CommRing D] [Algebra F D] [CommRing E] [Algebra F E]
    (N : DatG0.FinSubext F K) where
  thetaN : N.1 ⊗[F] B →ₐ[N.1] N.1 ⊗[F] E
  tauN : N.1 ⊗[F] A →ₐ[N.1] N.1 ⊗[F] D
  tauK : K ⊗[F] A →ₐ[K] K ⊗[F] D
  rightN : N.1 ⊗[F] A →ₐ[N.1] N.1 ⊗[F] B
  leftN : N.1 ⊗[F] D →ₐ[N.1] N.1 ⊗[F] E
  sourceComparison : N.1 ⊗[F] A →ₐ[F] K ⊗[F] A
  targetComparison : N.1 ⊗[F] D →ₐ[F] K ⊗[F] D
  tau_square :
    targetComparison.comp (tauN.restrictScalars F) =
      (tauK.restrictScalars F).comp sourceComparison
  face : thetaN.comp rightN = leftN.comp tauN

/-- Package a commutative scalar-extension face diagram.  Every finite and ambient map is
supplied as an already elaborated term, so the package never reconstructs the dependent
tensor-product metadata hidden in those maps. -/
noncomputable def scalarExtensionFacePackage
    {F K A B D E : Type u}
    [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]
    [CommRing D] [Algebra F D] [CommRing E] [Algebra F E]
    (N : DatG0.FinSubext F K)
    (rightN : N.1 ⊗[F] A →ₐ[N.1] N.1 ⊗[F] B)
    (thetaN : N.1 ⊗[F] B →ₐ[N.1] N.1 ⊗[F] E)
    (tauN : N.1 ⊗[F] A →ₐ[N.1] N.1 ⊗[F] D)
    (leftN : N.1 ⊗[F] D →ₐ[N.1] N.1 ⊗[F] E)
    (rightK : K ⊗[F] A →ₐ[K] K ⊗[F] B)
    (thetaK : K ⊗[F] B →ₐ[K] K ⊗[F] E)
    (tauK : K ⊗[F] A →ₐ[K] K ⊗[F] D)
    (leftK : K ⊗[F] D →ₐ[K] K ⊗[F] E)
    (hright :
      (Algebra.TensorProduct.map N.1.val (AlgHom.id F B)).comp
          (rightN.restrictScalars F) =
        (rightK.restrictScalars F).comp
          (Algebra.TensorProduct.map N.1.val (AlgHom.id F A)))
    (htheta :
      (Algebra.TensorProduct.map N.1.val (AlgHom.id F E)).comp
          (thetaN.restrictScalars F) =
        (thetaK.restrictScalars F).comp
          (Algebra.TensorProduct.map N.1.val (AlgHom.id F B)))
    (htau :
      (Algebra.TensorProduct.map N.1.val (AlgHom.id F D)).comp
          (tauN.restrictScalars F) =
        (tauK.restrictScalars F).comp
          (Algebra.TensorProduct.map N.1.val (AlgHom.id F A)))
    (hleft :
      (Algebra.TensorProduct.map N.1.val (AlgHom.id F E)).comp
          (leftN.restrictScalars F) =
        (leftK.restrictScalars F).comp
          (Algebra.TensorProduct.map N.1.val (AlgHom.id F D)))
    (hfaceK : thetaK.comp rightK = leftK.comp tauK) :
    ScalarExtensionFacePackage (A := A) (B := B) (D := D) (E := E) N := by
  let sourceComparison :=
    Algebra.TensorProduct.map N.1.val (AlgHom.id F A)
  let targetComparison :=
    Algebra.TensorProduct.map N.1.val (AlgHom.id F D)
  let faceTargetComparison :=
    Algebra.TensorProduct.map N.1.val (AlgHom.id F E)
  have hcomposite :
      faceTargetComparison.comp ((leftN.comp tauN).restrictScalars F) =
        ((leftK.comp tauK).restrictScalars F).comp
          sourceComparison := by
    apply DFunLike.ext _ _
    intro x
    calc
      faceTargetComparison ((leftN.comp tauN) x) =
          leftK (targetComparison (tauN x)) :=
        DFunLike.congr_fun hleft (tauN x)
      _ = leftK (tauK (sourceComparison x)) := by
        exact congrArg leftK (DFunLike.congr_fun htau x)
      _ = ((leftK.comp tauK).restrictScalars F).comp
            sourceComparison x := rfl
  have hface : thetaN.comp rightN = leftN.comp tauN := by
    apply DatG0.tensorProduct_algHom_comp_eq_of_baseChange N
      rightN thetaN (leftN.comp tauN)
      rightK thetaK (leftK.comp tauK)
    · exact hright
    · exact htheta
    · exact hcomposite
    · exact hfaceK
  exact {
    thetaN := thetaN
    tauN := tauN
    tauK := tauK
    rightN := rightN
    leftN := leftN
    sourceComparison := sourceComparison
    targetComparison := targetComparison
    tau_square := htau
    face := hface
  }

/-- The scalar-extension tower square, with the ambient map written using the
canonical value map of a finite subextension. -/
theorem scalarExtensionMapOfAlgHom_tower_finSubext
    {F K A B : Type u}
    [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [Semiring A] [Algebra F A] [Semiring B] [Algebra F B]
    (N : DatG0.FinSubext F K) (f : A →ₐ[F] B) :
    (Algebra.TensorProduct.map N.1.val (AlgHom.id F B)).comp
        ((AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := F) (K := N.1) f).restrictScalars F) =
      ((AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := F) (K := K) f).restrictScalars F).comp
        (Algebra.TensorProduct.map N.1.val (AlgHom.id F A)) := by
  have hval : N.1.val = IsScalarTower.toAlgHom F N.1 K := by
    ext x
    rfl
  have htower := AlgebraicJacobian.scalarExtensionMapOfAlgHom_tower
    (F := F) (L := N.1) (K := K) f
  rw [← hval] at htower
  exact htower

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

section

variable {F : Type u} [Field F] [Algebra F k]
variable (L : DatG0.FinSubext F k)
variable (n m : Pic0FiniteStageRingIndex C → Nat)
variable (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
variable (M : DatG0.FinSubext L.1 k)
variable [Algebra.IsAlgebraic M.1 k]
variable (mapM : ∀ q : Pic0FiniteStageMapIndex C,
  Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapSource C q) →ₐ[M.1]
    Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapTarget C q))

/-! The model-ring aliases are tensor products, but their `Algebra M.1` witness is
not recoverable from the alias alone once high-priority global instances are removed.
Keep one explicit provider here so the face package elaborates against the same
left-tensor action at every chart tag. -/
@[reducible] noncomputable def faceModelRingAlgebra
    (j : Pic0FiniteStageRingIndex C) :
    Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) := by
  dsimp only [Pic0FiniteStageModelRing]
  exact @Algebra.TensorProduct.leftAlgebra
    L.1 M.1 M.1
    (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : CommSemiring L.1)
    (inferInstance : Semiring M.1)
    (inferInstance : Algebra L.1 M.1)
    (DatG0.finiteRelationAlgebraCommRing L.1 (n j) (m j) (relation j)).toSemiring
    (DatG0.finiteRelationAlgebraAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : CommSemiring M.1)
    (inferInstance : Algebra M.1 M.1)
    (inferInstance : SMulCommClass L.1 M.1 M.1)

@[reducible] noncomputable def faceChartModelRingAlgebra
    (U : Pic0FiniteStageChartIndex C) :
    Algebra M.1 (Pic0FiniteStageChartModelRing C L n m relation M U) :=
  faceModelRingAlgebra C L n m relation M (Sum.inl U)

@[reducible] noncomputable def faceOverlapModelRingAlgebra
    (U V : Pic0FiniteStageChartIndex C) :
    Algebra M.1 (Pic0FiniteStageOverlapModelRing C L n m relation M U V) :=
  faceModelRingAlgebra C L n m relation M (Sum.inr (U, V))

/-! The triple model is itself a tensor pushout.  Its ambient `Algebra M.1`
instance is therefore sensitive to the two map-induced scalar towers.  Keep
that construction explicit as well, so consumers do not ask typeclass search
to rebuild the tower while elaborating a dependent face package. -/
set_option synthInstance.maxHeartbeats 3200000 in
-- The nested tensor-pushout algebra and scalar towers are expensive to normalize.
set_option maxHeartbeats 6400000 in
@[reducible] noncomputable def faceTripleModelRingAlgebra
    (U V W : Pic0FiniteStageChartIndex C) :
    Algebra M.1
      (Pic0FiniteStageTripleModelRing C L n m relation M mapM U V W) := by
  letI : Algebra M.1 (Pic0FiniteStageChartModelRing C L n m relation M U) :=
    faceChartModelRingAlgebra C L n m relation M U
  letI : Algebra M.1 (Pic0FiniteStageOverlapModelRing C L n m relation M U V) :=
    faceOverlapModelRingAlgebra C L n m relation M U V
  letI : Algebra M.1 (Pic0FiniteStageOverlapModelRing C L n m relation M U W) :=
    faceOverlapModelRingAlgebra C L n m relation M U W
  let f₁ := pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V
  let f₂ := pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U W
  letI : Algebra (Pic0FiniteStageChartModelRing C L n m relation M U)
      (Pic0FiniteStageOverlapModelRing C L n m relation M U V) :=
    pic0FiniteStageAlgebraOfMap f₁
  letI : Algebra (Pic0FiniteStageChartModelRing C L n m relation M U)
      (Pic0FiniteStageOverlapModelRing C L n m relation M U W) :=
    pic0FiniteStageAlgebraOfMap f₂
  letI : SMul (Pic0FiniteStageChartModelRing C L n m relation M U)
      (Pic0FiniteStageOverlapModelRing C L n m relation M U V) :=
    (pic0FiniteStageAlgebraOfMap f₁).toSMul
  letI : SMul (Pic0FiniteStageChartModelRing C L n m relation M U)
      (Pic0FiniteStageOverlapModelRing C L n m relation M U W) :=
    (pic0FiniteStageAlgebraOfMap f₂).toSMul
  letI := pic0FiniteStageTowerOfMap f₁
  letI := pic0FiniteStageTowerOfMap f₂
  dsimp only [Pic0FiniteStageTripleModelRing]
  exact @Algebra.TensorProduct.leftAlgebra
    (Pic0FiniteStageChartModelRing C L n m relation M U) M.1
    (Pic0FiniteStageOverlapModelRing C L n m relation M U V)
    (Pic0FiniteStageOverlapModelRing C L n m relation M U W)
    (inferInstance : CommSemiring
      (Pic0FiniteStageChartModelRing C L n m relation M U))
    (inferInstance : Semiring
      (Pic0FiniteStageOverlapModelRing C L n m relation M U V))
    (inferInstance : Algebra
      (Pic0FiniteStageChartModelRing C L n m relation M U)
      (Pic0FiniteStageOverlapModelRing C L n m relation M U V))
    (inferInstance : Semiring
      (Pic0FiniteStageOverlapModelRing C L n m relation M U W))
    (inferInstance : Algebra
      (Pic0FiniteStageChartModelRing C L n m relation M U)
      (Pic0FiniteStageOverlapModelRing C L n m relation M U W))
    (inferInstance : CommSemiring M.1)
    (faceOverlapModelRingAlgebra C L n m relation M U V)
    (SMulCommClass.of_commMonoid
      (Pic0FiniteStageChartModelRing C L n m relation M U) M.1
      (Pic0FiniteStageOverlapModelRing C L n m relation M U V))

set_option synthInstance.maxHeartbeats 400000 in
-- The comparison equivalences contain dependent quotient-algebra towers.
set_option maxHeartbeats 6400000 in
-- Naturality must expose both comparison equivalences at once.
omit [Algebra.IsAlgebraic M.1 k] in
/-- Scalar extension of a finite pair transition is the already-inferred ambient
pair-model comparison transition. -/
theorem scalarExtensionMapOfPairModel_eq_pairModelComparisonTransition
    (e : ∀ j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (hmapM : ∀ q,
      (Algebra.TensorProduct.map M.1.val
          (AlgHom.id L.1
            (DatG0.FiniteRelationAlgebra L.1
              (n (Pic0FiniteStageMapTarget C q))
              (m (Pic0FiniteStageMapTarget C q))
              (relation (Pic0FiniteStageMapTarget C q))))).comp
          ((mapM q).restrictScalars L.1) =
        ((pic0FiniteStageTransportedMap C L n m relation e q).restrictScalars
          L.1).comp
          (Algebra.TensorProduct.map M.1.val
            (AlgHom.id L.1
              (DatG0.FiniteRelationAlgebra L.1
                (n (Pic0FiniteStageMapSource C q))
                (m (Pic0FiniteStageMapSource C q))
                (relation (Pic0FiniteStageMapSource C q))))))
    (U V : Pic0FiniteStageChartIndex C) :
    AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := M.1) (K := k) (mapM (Sum.inr (U, V))) =
      pic0FiniteStagePairModelComparisonTransition
        C L n m relation e M U V := by
  let EUV := pic0FiniteStageModelBaseChangeEquiv
    C L n m relation e M (Sum.inr (U, V))
  let EVU := pic0FiniteStageModelBaseChangeEquiv
    C L n m relation e M (Sum.inr (V, U))
  have hnat := pic0FiniteStageModelBaseChangeEquiv_naturality
    C L n m relation e M mapM hmapM (Sum.inr (U, V))
  apply DFunLike.ext _ _
  intro x
  apply EUV.injective
  change EUV
      ((AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := M.1) (K := k) (mapM (Sum.inr (U, V)))) x) =
    EUV (EUV.symm (pic0FiniteStageTransition C (U, V) (EVU x)))
  rw [EUV.apply_symm_apply]
  exact DFunLike.congr_fun hnat x

set_option synthInstance.maxHeartbeats 3200000 in
-- The comparison family contains two dependent quotient-algebra towers; keep this
-- constructor boundary explicit so instance search does not time out before the
-- bundled face data is available to downstream declarations.
set_option maxHeartbeats 6400000 in
-- The package simultaneously infers four tensor-product model carriers.
/-- The inferred package for one Picard triple-transition face. -/
noncomputable def pic0FiniteStageTripleTransitionFacePackage
    (e : ∀ j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (hmapM : ∀ q,
      (Algebra.TensorProduct.map M.1.val
          (AlgHom.id L.1
            (DatG0.FiniteRelationAlgebra L.1
              (n (Pic0FiniteStageMapTarget C q))
              (m (Pic0FiniteStageMapTarget C q))
              (relation (Pic0FiniteStageMapTarget C q))))).comp
          ((mapM q).restrictScalars L.1) =
        ((pic0FiniteStageTransportedMap C L n m relation e q).restrictScalars
          L.1).comp
          (Algebra.TensorProduct.map M.1.val
            (AlgHom.id L.1
              (DatG0.FiniteRelationAlgebra L.1
                (n (Pic0FiniteStageMapSource C q))
                (m (Pic0FiniteStageMapSource C q))
                (relation (Pic0FiniteStageMapSource C q))))))
    (N : DatG0.FinSubext M.1 k)
    (U V W : Pic0FiniteStageChartIndex C)
    (thetaN : ∀ p : Pic0FiniteStageTripleTransitionIndex C,
      N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelSource
          C L n m relation M mapM p →ₐ[N.1]
        N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM p)
    (hthetaN : ∀ p : Pic0FiniteStageTripleTransitionIndex C,
      (Algebra.TensorProduct.map N.1.val
          (AlgHom.id M.1
            (Pic0FiniteStageTripleTransitionModelTarget
              C L n m relation M mapM p))).comp
          ((thetaN p).restrictScalars M.1) =
        ((pic0FiniteStageTransportedTripleTransitionOfModels
          C L n m relation e M mapM hmapM p.1 p.2.1 p.2.2).restrictScalars
            M.1).comp
          (Algebra.TensorProduct.map N.1.val
            (AlgHom.id M.1
                (Pic0FiniteStageTripleTransitionModelSource
                  C L n m relation M mapM p)))) :=
  -- A dependent `∀ j, Algebra ...` declaration is not used as a typeclass
  -- instance after the chart/overlap abbreviations are unfolded.  Pin each
  -- carrier that occurs in this face explicitly at the boundary.
  letI : Algebra M.1
      (Pic0FiniteStageChartModelRing C L n m relation M U) :=
    faceChartModelRingAlgebra C L n m relation M U
  letI : Algebra M.1
      (Pic0FiniteStageChartModelRing C L n m relation M V) :=
    faceChartModelRingAlgebra C L n m relation M V
  letI : Algebra M.1
      (Pic0FiniteStageChartModelRing C L n m relation M W) :=
    faceChartModelRingAlgebra C L n m relation M W
  letI : Algebra M.1
      (Pic0FiniteStageOverlapModelRing C L n m relation M U V) :=
    faceOverlapModelRingAlgebra C L n m relation M U V
  letI : Algebra M.1
      (Pic0FiniteStageOverlapModelRing C L n m relation M U W) :=
    faceOverlapModelRingAlgebra C L n m relation M U W
  letI : Algebra M.1
      (Pic0FiniteStageOverlapModelRing C L n m relation M V U) :=
    faceOverlapModelRingAlgebra C L n m relation M V U
  letI : Algebra M.1
      (Pic0FiniteStageOverlapModelRing C L n m relation M V W) :=
    faceOverlapModelRingAlgebra C L n m relation M V W
  letI : Algebra M.1
      (Pic0FiniteStageTripleModelRing C L n m relation M mapM V W U) :=
    faceTripleModelRingAlgebra C L n m relation M mapM V W U
  letI : Algebra M.1
      (Pic0FiniteStageTripleModelRing C L n m relation M mapM U V W) :=
    faceTripleModelRingAlgebra C L n m relation M mapM U V W
  let right := pic0FiniteStageTripleModelFaceRight
    C L n m relation M mapM V W U
  let tau := mapM (Sum.inr (U, V))
  let left := pic0FiniteStageTripleModelFaceLeft
    C L n m relation M mapM U V W
  let rightN := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := N.1) right
  let tauN := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := N.1) tau
  let leftN := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := N.1) left
  let rightK := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := k) right
  let thetaK := pic0FiniteStageTransportedTripleTransitionOfModels
    C L n m relation e M mapM hmapM U V W
  let tauK := pic0FiniteStagePairModelComparisonTransition
    C L n m relation e M U V
  let leftK := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := k) left
  have htauK := scalarExtensionMapOfPairModel_eq_pairModelComparisonTransition
    C L n m relation M mapM e hmapM U V
  have hfaceK := pic0FiniteStageTransportedTripleTransition_fac
    C L n m relation e M mapM hmapM U V W
  scalarExtensionFacePackage
    (F := M.1) (K := k)
    (A := Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapSource C (Sum.inr (U, V))))
    (D := Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapTarget C (Sum.inr (U, V)))) N
    rightN (thetaN (U, (V, W))) tauN leftN
    rightK thetaK tauK leftK
    (scalarExtensionMapOfAlgHom_tower_finSubext (K := k) N right)
    (hthetaN (U, (V, W))) (by
      have htauScalar := scalarExtensionMapOfAlgHom_tower_finSubext
        (K := k) N tau
      apply DFunLike.ext _ _
      intro x
      calc
        _ = (AlgebraicJacobian.scalarExtensionMapOfAlgHom
            (R := M.1) (K := k) tau) _ :=
          DFunLike.congr_fun htauScalar x
        _ = tauK _ := DFunLike.congr_fun htauK
          ((Algebra.TensorProduct.map N.1.val
            (AlgHom.id M.1
              (Pic0FiniteStageModelRing C L n m relation M
                (Pic0FiniteStageMapSource C (Sum.inr (U, V)))))) x))
    (scalarExtensionMapOfAlgHom_tower_finSubext (K := k) N left)
    hfaceK

set_option synthInstance.maxHeartbeats 3200000 in
-- The theorem statement repeats the dependent comparison family; keep the
-- migration wrapper on the same explicit synthesis budget as its producer.
set_option maxHeartbeats 6400000 in
-- The theorem boundary repeats the dependent comparison family used by the package.
/-- The ambient triple-transition face equation reflects to the common finite stage `N`.
The statement uses the inferred package projections so its tensor-product instances are
definitionally identical to those used to construct the descended maps. -/
theorem pic0FiniteStageTripleTransitionModel_fac
    (e : ∀ j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (hmapM : ∀ q,
      (Algebra.TensorProduct.map M.1.val
          (AlgHom.id L.1
            (DatG0.FiniteRelationAlgebra L.1
              (n (Pic0FiniteStageMapTarget C q))
              (m (Pic0FiniteStageMapTarget C q))
              (relation (Pic0FiniteStageMapTarget C q))))).comp
          ((mapM q).restrictScalars L.1) =
        ((pic0FiniteStageTransportedMap C L n m relation e q).restrictScalars
          L.1).comp
          (Algebra.TensorProduct.map M.1.val
            (AlgHom.id L.1
              (DatG0.FiniteRelationAlgebra L.1
                (n (Pic0FiniteStageMapSource C q))
                (m (Pic0FiniteStageMapSource C q))
                (relation (Pic0FiniteStageMapSource C q))))))
    (N : DatG0.FinSubext M.1 k)
    (U V W : Pic0FiniteStageChartIndex C)
    (thetaN : ∀ p : Pic0FiniteStageTripleTransitionIndex C,
      N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelSource
          C L n m relation M mapM p →ₐ[N.1]
        N.1 ⊗[M.1] Pic0FiniteStageTripleTransitionModelTarget
          C L n m relation M mapM p)
    (hthetaN : ∀ p : Pic0FiniteStageTripleTransitionIndex C,
      (Algebra.TensorProduct.map N.1.val
          (AlgHom.id M.1
            (Pic0FiniteStageTripleTransitionModelTarget
              C L n m relation M mapM p))).comp
          ((thetaN p).restrictScalars M.1) =
        ((pic0FiniteStageTransportedTripleTransitionOfModels
          C L n m relation e M mapM hmapM p.1 p.2.1 p.2.2).restrictScalars
            M.1).comp
          (Algebra.TensorProduct.map N.1.val
            (AlgHom.id M.1
              (Pic0FiniteStageTripleTransitionModelSource
                C L n m relation M mapM p)))) :
    let P := pic0FiniteStageTripleTransitionFacePackage
      C L n m relation M mapM e hmapM N U V W thetaN hthetaN
    P.thetaN.comp P.rightN = P.leftN.comp P.tauN := by
  exact (pic0FiniteStageTripleTransitionFacePackage
    C L n m relation M mapM e hmapM N U V W thetaN hthetaN).face

end

end

end AlgebraicGeometry
