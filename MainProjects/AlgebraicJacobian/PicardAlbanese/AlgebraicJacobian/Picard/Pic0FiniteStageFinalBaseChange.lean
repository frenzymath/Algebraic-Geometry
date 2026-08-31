/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelComparison
import AlgebraicJacobian.Descent.TensorProductPushoutData

/-!
# Base change of the final finite-stage Picard atlas

The glue package extends the finite-presentation models from `M` to a final finite
subextension `N`.  Extending once more to the separably closed field cancels the tower
`M -> N -> k`.  The resulting component equivalences recover the exact Picard atlas
rings and intertwine every restriction and transition map.
-/

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-- A finite-presentation model ring after extension to the final finite subextension. -/
noncomputable abbrev Pic0FiniteStageFinalModelRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) : Type u :=
  N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j

/-
The relation-algebra quotient has a generic `Algebra` instance, but letting
typeclass search rediscover it through a dependent `FinSubext` carrier can loop
on the quotient's `Module` parent.  Keep the quotient carriers canonical at
this boundary so every tensor instance below sees the same structures.
-/
@[reducible] noncomputable def pic0FiniteStageRelationAlgebraCommRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    CommRing (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
  DatG0.finiteRelationAlgebraCommRing L.1 (n j) (m j) (relation j)

@[reducible] noncomputable def pic0FiniteStageRelationAlgebraSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
  (DatG0.finiteRelationAlgebraCommRing L.1 (n j) (m j) (relation j)).toSemiring

@[reducible] noncomputable def pic0FiniteStageRelationAlgebraAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra L.1 (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
  DatG0.finiteRelationAlgebraAlgebra L.1 (n j) (m j) (relation j)

@[reducible] noncomputable def pic0FiniteStageRelationAlgebraModule
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    Module L.1 (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)) :=
  (DatG0.finiteRelationAlgebraAlgebra L.1 (n j) (m j) (relation j)).toModule

attribute [local instance] pic0FiniteStageRelationAlgebraCommRing
  pic0FiniteStageRelationAlgebraSemiring pic0FiniteStageRelationAlgebraAlgebra
  pic0FiniteStageRelationAlgebraModule

/-!
The nested tensor aliases above hide the carrier instances that `cancelBaseChange`
needs.  Keep the witnesses named and local to this module, mirroring the explicit
overlap instances in `Pic0FiniteStageGluePackage`.
-/
@[reducible] noncomputable instance pic0FiniteStageModelRingCommRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    CommRing (Pic0FiniteStageModelRing C L n m relation M j) := by
  dsimp only [Pic0FiniteStageModelRing]
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    @Algebra.TensorProduct.leftAlgebra
      L.1 M.1 M.1
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
      (inferInstance : CommSemiring L.1)
      (inferInstance : Semiring M.1)
      (inferInstance : Algebra L.1 M.1)
      (pic0FiniteStageRelationAlgebraSemiring C L n m relation j)
      (pic0FiniteStageRelationAlgebraAlgebra C L n m relation j)
      (inferInstance : CommSemiring M.1)
      (inferInstance : Algebra M.1 M.1)
      (inferInstance : SMulCommClass L.1 M.1 M.1)
  exact Algebra.TensorProduct.instCommRing

@[reducible] noncomputable instance pic0FiniteStageModelRingAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
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
    (pic0FiniteStageRelationAlgebraSemiring C L n m relation j)
    (pic0FiniteStageRelationAlgebraAlgebra C L n m relation j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Algebra M.1 M.1)
    (inferInstance : SMulCommClass L.1 M.1 M.1)

@[reducible] noncomputable instance pic0FiniteStageFinalModelRingCommRing
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    CommRing (Pic0FiniteStageFinalModelRing C L n m relation M N j) := by
  dsimp only [Pic0FiniteStageFinalModelRing]
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    @Algebra.TensorProduct.leftAlgebra
      L.1 M.1 M.1
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
      (inferInstance : CommSemiring L.1)
      (inferInstance : Semiring M.1)
      (inferInstance : Algebra L.1 M.1)
      (pic0FiniteStageRelationAlgebraSemiring C L n m relation j)
      (pic0FiniteStageRelationAlgebraAlgebra C L n m relation j)
      (inferInstance : CommSemiring M.1)
      (inferInstance : Algebra M.1 M.1)
      (inferInstance : SMulCommClass L.1 M.1 M.1)
  letI : CommRing (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingCommRing C L n m relation M j
  letI : CommSemiring (Pic0FiniteStageModelRing C L n m relation M j) :=
    (inferInstance : CommRing (Pic0FiniteStageModelRing C L n m relation M j)).toCommSemiring
  exact @Algebra.TensorProduct.instCommRing M.1 N.1
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : CommRing N.1)
    (inferInstance : Algebra M.1 N.1)
    (pic0FiniteStageModelRingCommRing C L n m relation M j).toCommSemiring
    (pic0FiniteStageModelRingAlgebra C L n m relation M j)

@[reducible] noncomputable instance pic0FiniteStageFinalModelRingCommSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    CommSemiring (Pic0FiniteStageFinalModelRing C L n m relation M N j) :=
  (pic0FiniteStageFinalModelRingCommRing C L n m relation M N j).toCommSemiring

@[reducible] noncomputable instance pic0FiniteStageFinalModelRingAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra N.1 (Pic0FiniteStageFinalModelRing C L n m relation M N j) := by
  dsimp only [Pic0FiniteStageFinalModelRing]
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    @Algebra.TensorProduct.leftAlgebra
      L.1 M.1 M.1
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
      (inferInstance : CommSemiring L.1)
      (inferInstance : Semiring M.1)
      (inferInstance : Algebra L.1 M.1)
      (pic0FiniteStageRelationAlgebraSemiring C L n m relation j)
      (pic0FiniteStageRelationAlgebraAlgebra C L n m relation j)
      (inferInstance : CommSemiring M.1)
      (inferInstance : Algebra M.1 M.1)
      (inferInstance : SMulCommClass L.1 M.1 M.1)
  exact @Algebra.TensorProduct.leftAlgebra
    M.1 N.1 N.1 (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (pic0FiniteStageModelRingCommRing C L n m relation M j).toSemiring
    (pic0FiniteStageModelRingAlgebra C L n m relation M j)
    (inferInstance : CommSemiring N.1)
    (inferInstance : Algebra N.1 N.1)
    (inferInstance : SMulCommClass M.1 N.1 N.1)

-- Keep this witness inside the module.  Exporting it at priority 2000 makes every
-- downstream tensor expression pick this proof term, even when a packaged stage
-- supplies a different (but propositionally equal) algebra structure.
attribute [local instance] pic0FiniteStageFinalModelRingAlgebra

@[reducible] noncomputable def pic0FiniteStageModelRingBaseAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra L.1 (Pic0FiniteStageModelRing C L n m relation M j) := by
  exact @Algebra.TensorProduct.instAlgebra L.1 M.1
    (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : CommSemiring L.1)
    (inferInstance : Semiring M.1)
    (inferInstance : Algebra L.1 M.1)
    (pic0FiniteStageRelationAlgebraSemiring C L n m relation j)
    (pic0FiniteStageRelationAlgebraAlgebra C L n m relation j)

attribute [local instance] pic0FiniteStageModelRingBaseAlgebra

private theorem pic0FiniteStageFinSubext_smul_assoc
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k) (M : DatG0.FinSubext L.1 k)
    (x : L.1) (y a : M.1) :
    (x • y) • a = x • (y • a) := by
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, map_mul]
  rw [mul_assoc]

@[reducible] noncomputable def pic0FiniteStageModelRingDistribMulActionM
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    DistribMulAction M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
  @TensorProduct.leftDistribMulAction
    L.1 M.1
    (inferInstance : CommSemiring L.1)
    (inferInstance : Monoid M.1)
    M.1 (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : AddCommMonoid M.1)
    (inferInstance : AddCommMonoid
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))
    (inferInstance : DistribMulAction M.1 M.1)
    (inferInstance : Module L.1 M.1)
    (pic0FiniteStageRelationAlgebraModule C L n m relation j)
    (inferInstance : SMulCommClass L.1 M.1 M.1)

@[reducible] noncomputable def pic0FiniteStageModelRingDistribMulActionL
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    DistribMulAction L.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
  @TensorProduct.instDistribMulAction
    L.1
    (inferInstance : CommSemiring L.1)
    M.1 (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : AddCommMonoid M.1)
    (inferInstance : AddCommMonoid
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))
    (inferInstance : Module L.1 M.1)
    (pic0FiniteStageRelationAlgebraModule C L n m relation j)

set_option synthInstance.maxHeartbeats 400000 in
-- Register the fixed tensor actions so dependent `restrictScalars` declarations see this tower.
set_option maxHeartbeats 6400000 in
noncomputable instance pic0FiniteStageModelRingIsScalarTower
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
  (j : Pic0FiniteStageRingIndex C) :
    IsScalarTower L.1 M.1 (Pic0FiniteStageModelRing C L n m relation M j) := by
  letI : Algebra L.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingBaseAlgebra C L n m relation M j
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingAlgebra C L n m relation M j
  letI : DistribMulAction M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingDistribMulActionM C L n m relation M j
  letI : SMul M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    (pic0FiniteStageModelRingDistribMulActionM C L n m relation M j).toDistribSMul.toSMul
  letI : DistribMulAction L.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingDistribMulActionL C L n m relation M j
  letI : SMul L.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    (pic0FiniteStageModelRingDistribMulActionL C L n m relation M j).toDistribSMul.toSMul
  refine { smul_assoc := ?_ }
  intro x y z
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | add z₁ z₂ ih₁ ih₂ => rw [smul_add, smul_add, ih₁, ih₂, smul_add]
  | tmul a b =>
      rw [TensorProduct.smul_tmul' (x • y) a b]
      rw [TensorProduct.smul_tmul' y a b]
      rw [TensorProduct.smul_tmul' x (y • a) b]
      exact congrArg (fun q : M.1 => q ⊗ₜ[L.1] b)
        (pic0FiniteStageFinSubext_smul_assoc L M x y a)

-- The tower is a declaration-local implementation detail; callers should use the
-- pinned stage data APIs instead of inheriting a global high-priority witness.
attribute [local instance] pic0FiniteStageModelRingIsScalarTower

/-
The source maps below are indexed by `q`, so elaborating `restrictScalars` directly
can select a different tensor-product action for the dependent source and target
models.  Freeze those actions at this private boundary.  The wrapper has the same
carrier map as `AlgHom.restrictScalars`; only its implicit algebra structures are
made explicit.  The original proof and public statement remain archived in the
preceding Horizon attempts.
-/
noncomputable abbrev pic0FiniteStageModelRingSMulLM
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k) (M : DatG0.FinSubext L.1 k) : SMul L.1 M.1 :=
  IntermediateField.instSMulSubtypeMem_1 M.1

noncomputable abbrev pic0FiniteStageModelRingSMulM
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    SMul M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
  (pic0FiniteStageModelRingDistribMulActionM C L n m relation M j).toDistribSMul.toSMul

noncomputable abbrev pic0FiniteStageModelRingSMulL
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    SMul L.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
  (pic0FiniteStageModelRingDistribMulActionL C L n m relation M j).toDistribSMul.toSMul

@[reducible] noncomputable def pic0FiniteStageModelRingTowerExplicit
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    @IsScalarTower L.1 M.1 (Pic0FiniteStageModelRing C L n m relation M j)
      (pic0FiniteStageModelRingSMulLM L M)
      (pic0FiniteStageModelRingSMulM C L n m relation M j)
      (pic0FiniteStageModelRingSMulL C L n m relation M j) := by
  letI : Algebra L.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingBaseAlgebra C L n m relation M j
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingAlgebra C L n m relation M j
  letI : SMul L.1 M.1 := pic0FiniteStageModelRingSMulLM L M
  letI : SMul M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingSMulM C L n m relation M j
  letI : DistribMulAction M.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingDistribMulActionM C L n m relation M j
  letI : SMul L.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingSMulL C L n m relation M j
  letI : DistribMulAction L.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingDistribMulActionL C L n m relation M j
  refine { smul_assoc := ?_ }
  intro x y z
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | add z1 z2 ih1 ih2 => rw [smul_add, smul_add, ih1, ih2, smul_add]
  | tmul a b =>
      rw [TensorProduct.smul_tmul' (x • y) a b]
      rw [TensorProduct.smul_tmul' y a b]
      rw [TensorProduct.smul_tmul' x (y • a) b]
      exact congrArg (fun q : M.1 => q ⊗ₜ[L.1] b)
        (pic0FiniteStageFinSubext_smul_assoc L M x y a)

noncomputable def pic0FiniteStageModelRestrictScalarsExplicit
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j1 j2 : Pic0FiniteStageRingIndex C)
    (f : @AlgHom M.1
      (Pic0FiniteStageModelRing C L n m relation M j1)
      (Pic0FiniteStageModelRing C L n m relation M j2)
      (inferInstance : CommSemiring M.1)
      (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
      (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
      (pic0FiniteStageModelRingAlgebra C L n m relation M j1)
      (pic0FiniteStageModelRingAlgebra C L n m relation M j2)) :
    @AlgHom L.1
      (Pic0FiniteStageModelRing C L n m relation M j1)
      (Pic0FiniteStageModelRing C L n m relation M j2)
      (inferInstance : CommSemiring L.1)
      (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
      (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
      (pic0FiniteStageModelRingBaseAlgebra C L n m relation M j1)
      (pic0FiniteStageModelRingBaseAlgebra C L n m relation M j2) := by
  exact @AlgHom.restrictScalars
    L.1 M.1
      (Pic0FiniteStageModelRing C L n m relation M j1)
      (Pic0FiniteStageModelRing C L n m relation M j2)
      (inferInstance : CommSemiring L.1)
      (inferInstance : CommSemiring M.1)
      (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
      (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
      (inferInstance : Algebra L.1 M.1)
      (pic0FiniteStageModelRingAlgebra C L n m relation M j1)
      (pic0FiniteStageModelRingAlgebra C L n m relation M j2)
      (pic0FiniteStageModelRingBaseAlgebra C L n m relation M j1)
      (pic0FiniteStageModelRingBaseAlgebra C L n m relation M j2)
      (pic0FiniteStageModelRingTowerExplicit C L n m relation M j1)
      (pic0FiniteStageModelRingTowerExplicit C L n m relation M j2)
      f

/- The outer scalar extension sees these inner tensors as dependent carriers.
   Name their canonical instances so the nested map in the theorem header does
   not synthesize a fresh, incoherent `Semiring` structure for each `q`. -/
@[reducible] noncomputable def pic0FiniteStageModelScalarExtensionSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j) :=
  @Algebra.TensorProduct.instSemiring M.1 N.1
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (pic0FiniteStageModelRingCommRing C L n m relation M j).toSemiring
    (pic0FiniteStageModelRingAlgebra C L n m relation M j)

attribute [local instance] pic0FiniteStageModelScalarExtensionSemiring

@[reducible] noncomputable def pic0FiniteStageModelScalarExtensionAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra N.1 (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j) :=
  @Algebra.TensorProduct.leftAlgebra M.1 N.1 N.1
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Semiring N.1)
    (inferInstance : Algebra M.1 N.1)
    (pic0FiniteStageModelRingCommRing C L n m relation M j).toSemiring
    (pic0FiniteStageModelRingAlgebra C L n m relation M j)
    (inferInstance : CommSemiring N.1)
    (inferInstance : Algebra N.1 N.1)
    (inferInstance : SMulCommClass M.1 N.1 N.1)

attribute [local instance] pic0FiniteStageModelScalarExtensionAlgebra
attribute [local instance] pic0FiniteStageModelScalarExtensionSemiring

noncomputable def pic0FiniteStageModelScalarExtensionMap
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j1 j2 : Pic0FiniteStageRingIndex C)
    (f : @AlgHom M.1
      (Pic0FiniteStageModelRing C L n m relation M j1)
      (Pic0FiniteStageModelRing C L n m relation M j2)
      (inferInstance : CommSemiring M.1)
      (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
      (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
      (pic0FiniteStageModelRingAlgebra C L n m relation M j1)
      (pic0FiniteStageModelRingAlgebra C L n m relation M j2)) :
    @AlgHom N.1
      (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j1)
      (N.1 ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j2)
      (inferInstance : CommSemiring N.1)
      (pic0FiniteStageModelScalarExtensionSemiring C L n m relation M N j1)
      (pic0FiniteStageModelScalarExtensionSemiring C L n m relation M N j2)
      (pic0FiniteStageModelScalarExtensionAlgebra C L n m relation M N j1)
      (pic0FiniteStageModelScalarExtensionAlgebra C L n m relation M N j2) := by
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j1) :=
    pic0FiniteStageModelRingAlgebra C L n m relation M j1
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j2) :=
    pic0FiniteStageModelRingAlgebra C L n m relation M j2
  exact @AlgebraicJacobian.scalarExtensionMapOfAlgHom
    M.1 N.1
      (Pic0FiniteStageModelRing C L n m relation M j1)
      (Pic0FiniteStageModelRing C L n m relation M j2)
      (inferInstance : CommRing M.1)
      (inferInstance : CommRing N.1)
      (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
      (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
      (inferInstance : Algebra M.1 N.1)
      (pic0FiniteStageModelRingAlgebra C L n m relation M j1)
      (pic0FiniteStageModelRingAlgebra C L n m relation M j2)
      f

noncomputable def pic0FiniteStageScalarExtensionMapOver
    {F : Type u} [Field F] [Algebra F k]
    {K : Type u} [CommRing K]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k) [Algebra M.1 K]
    (j1 j2 : Pic0FiniteStageRingIndex C)
    (f : @AlgHom M.1
      (Pic0FiniteStageModelRing C L n m relation M j1)
      (Pic0FiniteStageModelRing C L n m relation M j2)
      (inferInstance : CommSemiring M.1)
      (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
      (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
      (pic0FiniteStageModelRingAlgebra C L n m relation M j1)
      (pic0FiniteStageModelRingAlgebra C L n m relation M j2)) :
    @AlgHom K
      (K ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j1)
      (K ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j2)
      (inferInstance : CommSemiring K)
      (@Algebra.TensorProduct.instSemiring M.1 K
        (Pic0FiniteStageModelRing C L n m relation M j1)
        (inferInstance : CommSemiring M.1)
        (inferInstance : Semiring K)
        (inferInstance : Algebra M.1 K)
        (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
        (pic0FiniteStageModelRingAlgebra C L n m relation M j1))
      (@Algebra.TensorProduct.instSemiring M.1 K
        (Pic0FiniteStageModelRing C L n m relation M j2)
        (inferInstance : CommSemiring M.1)
        (inferInstance : Semiring K)
        (inferInstance : Algebra M.1 K)
        (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
        (pic0FiniteStageModelRingAlgebra C L n m relation M j2))
      (@Algebra.TensorProduct.leftAlgebra M.1 K K
        (Pic0FiniteStageModelRing C L n m relation M j1)
        (inferInstance : CommSemiring M.1)
        (inferInstance : Semiring K)
        (inferInstance : Algebra M.1 K)
        (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
        (pic0FiniteStageModelRingAlgebra C L n m relation M j1)
        (inferInstance : CommSemiring K)
        (inferInstance : Algebra K K)
        (inferInstance : SMulCommClass M.1 K K))
      (@Algebra.TensorProduct.leftAlgebra M.1 K K
        (Pic0FiniteStageModelRing C L n m relation M j2)
        (inferInstance : CommSemiring M.1)
        (inferInstance : Semiring K)
        (inferInstance : Algebra M.1 K)
        (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
        (pic0FiniteStageModelRingAlgebra C L n m relation M j2)
        (inferInstance : CommSemiring K)
        (inferInstance : Algebra K K)
        (inferInstance : SMulCommClass M.1 K K)) := by
  letI : Semiring (Pic0FiniteStageModelRing C L n m relation M j1) :=
    (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
  letI : Semiring (Pic0FiniteStageModelRing C L n m relation M j2) :=
    (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j1) :=
    pic0FiniteStageModelRingAlgebra C L n m relation M j1
  letI : Algebra M.1 (Pic0FiniteStageModelRing C L n m relation M j2) :=
    pic0FiniteStageModelRingAlgebra C L n m relation M j2
  exact @AlgebraicJacobian.scalarExtensionMapOfAlgHom
    M.1 K
      (Pic0FiniteStageModelRing C L n m relation M j1)
      (Pic0FiniteStageModelRing C L n m relation M j2)
      (inferInstance : CommRing M.1)
      (inferInstance : CommRing K)
      (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
      (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
      (inferInstance : Algebra M.1 K)
      (pic0FiniteStageModelRingAlgebra C L n m relation M j1)
      (pic0FiniteStageModelRingAlgebra C L n m relation M j2)
      f

@[reducible] noncomputable def pic0FiniteStageModelAmbientSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n j) (m j) (relation j)) :=
  @Algebra.TensorProduct.instSemiring L.1 k
    (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : CommSemiring L.1)
    (inferInstance : Semiring k)
    (inferInstance : Algebra L.1 k)
    (inferInstance : Semiring
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))
    (inferInstance : Algebra L.1
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))

attribute [local instance] pic0FiniteStageModelAmbientSemiring

@[reducible] noncomputable def pic0FiniteStageModelAmbientAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra L.1
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n j) (m j) (relation j)) :=
  @Algebra.TensorProduct.instAlgebra L.1 k
    (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : CommSemiring L.1)
    (inferInstance : Semiring k)
    (inferInstance : Algebra L.1 k)
    (inferInstance : Semiring
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))
    (inferInstance : Algebra L.1
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))

attribute [local instance] pic0FiniteStageModelAmbientAlgebra

@[reducible] noncomputable def pic0FiniteStageModelAmbientKAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra k
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n j) (m j) (relation j)) :=
  @Algebra.TensorProduct.leftAlgebra L.1 k k
    (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
    (inferInstance : CommSemiring L.1)
    (inferInstance : Semiring k)
    (inferInstance : Algebra L.1 k)
    (inferInstance : Semiring
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))
    (inferInstance : Algebra L.1
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))
    (inferInstance : CommSemiring k)
    (inferInstance : Algebra k k)
    (inferInstance : SMulCommClass L.1 k k)

attribute [local instance] pic0FiniteStageModelAmbientKAlgebra

@[reducible] noncomputable def pic0FiniteStageModelAmbientTower
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (j : Pic0FiniteStageRingIndex C) :
    IsScalarTower L.1 k
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n j) (m j) (relation j)) := by
  letI : Algebra k
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n j) (m j) (relation j)) :=
    pic0FiniteStageModelAmbientKAlgebra C L n m relation j
  letI : Algebra L.1
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n j) (m j) (relation j)) :=
    pic0FiniteStageModelAmbientAlgebra C L n m relation j
  exact @IsScalarTower.of_algebraMap_eq
    L.1 k
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n j) (m j) (relation j))
      (inferInstance : CommSemiring L.1)
      (inferInstance : CommSemiring k)
      (inferInstance : Semiring
        (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
          (n j) (m j) (relation j)))
      (inferInstance : Algebra L.1 k)
      (pic0FiniteStageModelAmbientKAlgebra C L n m relation j)
      (pic0FiniteStageModelAmbientAlgebra C L n m relation j)
      (fun _ => rfl)

noncomputable def pic0FiniteStageModelAmbientMap
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    @AlgHom L.1
      (Pic0FiniteStageModelRing C L n m relation M j)
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n j) (m j) (relation j))
      (inferInstance : CommSemiring L.1)
      (pic0FiniteStageModelRingCommRing C L n m relation M j).toSemiring
      (pic0FiniteStageModelAmbientSemiring C L n m relation j)
      (pic0FiniteStageModelRingBaseAlgebra C L n m relation M j)
      (pic0FiniteStageModelAmbientAlgebra C L n m relation j) := by
  letI : Algebra L.1 (Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelRingBaseAlgebra C L n m relation M j
  letI : Algebra L.1
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n j) (m j) (relation j)) :=
    pic0FiniteStageModelAmbientAlgebra C L n m relation j
  exact Algebra.TensorProduct.map M.1.val
    (AlgHom.id L.1
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))

noncomputable def pic0FiniteStageModelAmbientMapCompRestrict
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j1 j2 : Pic0FiniteStageRingIndex C)
    (f : @AlgHom M.1
      (Pic0FiniteStageModelRing C L n m relation M j1)
      (Pic0FiniteStageModelRing C L n m relation M j2)
      (inferInstance : CommSemiring M.1)
      (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
      (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
      (pic0FiniteStageModelRingAlgebra C L n m relation M j1)
      (pic0FiniteStageModelRingAlgebra C L n m relation M j2)) :
    @AlgHom L.1
      (Pic0FiniteStageModelRing C L n m relation M j1)
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n j2) (m j2) (relation j2))
      (inferInstance : CommSemiring L.1)
      (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
      (pic0FiniteStageModelAmbientSemiring C L n m relation j2)
      (pic0FiniteStageModelRingBaseAlgebra C L n m relation M j1)
      (pic0FiniteStageModelAmbientAlgebra C L n m relation j2) := by
  exact @AlgHom.comp L.1
    (Pic0FiniteStageModelRing C L n m relation M j1)
    (Pic0FiniteStageModelRing C L n m relation M j2)
    (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
      (n j2) (m j2) (relation j2))
    (inferInstance : CommSemiring L.1)
    (pic0FiniteStageModelRingCommRing C L n m relation M j1).toSemiring
    (pic0FiniteStageModelRingCommRing C L n m relation M j2).toSemiring
    (pic0FiniteStageModelAmbientSemiring C L n m relation j2)
    (pic0FiniteStageModelRingBaseAlgebra C L n m relation M j1)
    (pic0FiniteStageModelRingBaseAlgebra C L n m relation M j2)
    (pic0FiniteStageModelAmbientAlgebra C L n m relation j2)
    (pic0FiniteStageModelAmbientMap C L n m relation M j2)
    (pic0FiniteStageModelRestrictScalarsExplicit C L n m relation M j1 j2 f)

noncomputable def pic0FiniteStageTransportedMapRestrictScalars
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (q : Pic0FiniteStageMapIndex C) :
    @AlgHom L.1
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n (Pic0FiniteStageMapSource C q))
        (m (Pic0FiniteStageMapSource C q))
        (relation (Pic0FiniteStageMapSource C q)))
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n (Pic0FiniteStageMapTarget C q))
        (m (Pic0FiniteStageMapTarget C q))
        (relation (Pic0FiniteStageMapTarget C q)))
      (inferInstance : CommSemiring L.1)
      (pic0FiniteStageModelAmbientSemiring C L n m relation
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageModelAmbientSemiring C L n m relation
        (Pic0FiniteStageMapTarget C q))
      (pic0FiniteStageModelAmbientAlgebra C L n m relation
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageModelAmbientAlgebra C L n m relation
        (Pic0FiniteStageMapTarget C q)) := by
  letI : Algebra k
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n (Pic0FiniteStageMapSource C q))
        (m (Pic0FiniteStageMapSource C q))
        (relation (Pic0FiniteStageMapSource C q))) :=
    pic0FiniteStageModelAmbientKAlgebra C L n m relation
      (Pic0FiniteStageMapSource C q)
  letI : Algebra k
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n (Pic0FiniteStageMapTarget C q))
        (m (Pic0FiniteStageMapTarget C q))
        (relation (Pic0FiniteStageMapTarget C q))) :=
    pic0FiniteStageModelAmbientKAlgebra C L n m relation
      (Pic0FiniteStageMapTarget C q)
  exact @AlgHom.restrictScalars
    L.1 k
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n (Pic0FiniteStageMapSource C q))
        (m (Pic0FiniteStageMapSource C q))
        (relation (Pic0FiniteStageMapSource C q)))
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n (Pic0FiniteStageMapTarget C q))
        (m (Pic0FiniteStageMapTarget C q))
        (relation (Pic0FiniteStageMapTarget C q)))
      (inferInstance : CommSemiring L.1)
      (inferInstance : CommSemiring k)
      (pic0FiniteStageModelAmbientSemiring C L n m relation
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageModelAmbientSemiring C L n m relation
        (Pic0FiniteStageMapTarget C q))
      (inferInstance : Algebra L.1 k)
      (pic0FiniteStageModelAmbientKAlgebra C L n m relation
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageModelAmbientKAlgebra C L n m relation
        (Pic0FiniteStageMapTarget C q))
      (pic0FiniteStageModelAmbientAlgebra C L n m relation
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageModelAmbientAlgebra C L n m relation
        (Pic0FiniteStageMapTarget C q))
      (pic0FiniteStageModelAmbientTower C L n m relation
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageModelAmbientTower C L n m relation
        (Pic0FiniteStageMapTarget C q))
      (pic0FiniteStageTransportedMap C L n m relation e q)

noncomputable def pic0FiniteStageTransportedMapRestrictCompAmbient
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (q : Pic0FiniteStageMapIndex C) :
    @AlgHom L.1
      (Pic0FiniteStageModelRing C L n m relation M
        (Pic0FiniteStageMapSource C q))
      (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
        (n (Pic0FiniteStageMapTarget C q))
        (m (Pic0FiniteStageMapTarget C q))
        (relation (Pic0FiniteStageMapTarget C q)))
      (inferInstance : CommSemiring L.1)
      (pic0FiniteStageModelRingCommRing C L n m relation M
        (Pic0FiniteStageMapSource C q)).toSemiring
      (pic0FiniteStageModelAmbientSemiring C L n m relation
        (Pic0FiniteStageMapTarget C q))
      (pic0FiniteStageModelRingBaseAlgebra C L n m relation M
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageModelAmbientAlgebra C L n m relation
        (Pic0FiniteStageMapTarget C q)) := by
  exact @AlgHom.comp L.1
    (Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapSource C q))
    (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
      (n (Pic0FiniteStageMapSource C q))
      (m (Pic0FiniteStageMapSource C q))
      (relation (Pic0FiniteStageMapSource C q)))
    (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
      (n (Pic0FiniteStageMapTarget C q))
      (m (Pic0FiniteStageMapTarget C q))
      (relation (Pic0FiniteStageMapTarget C q)))
    (inferInstance : CommSemiring L.1)
    (pic0FiniteStageModelRingCommRing C L n m relation M
      (Pic0FiniteStageMapSource C q)).toSemiring
    (pic0FiniteStageModelAmbientSemiring C L n m relation
      (Pic0FiniteStageMapSource C q))
    (pic0FiniteStageModelAmbientSemiring C L n m relation
      (Pic0FiniteStageMapTarget C q))
    (pic0FiniteStageModelRingBaseAlgebra C L n m relation M
      (Pic0FiniteStageMapSource C q))
    (pic0FiniteStageModelAmbientAlgebra C L n m relation
      (Pic0FiniteStageMapSource C q))
    (pic0FiniteStageModelAmbientAlgebra C L n m relation
      (Pic0FiniteStageMapTarget C q))
    (pic0FiniteStageTransportedMapRestrictScalars C L n m relation e q)
    (pic0FiniteStageModelAmbientMap C L n m relation M
      (Pic0FiniteStageMapSource C q))

@[reducible] noncomputable def pic0FiniteStageFinalModelRingModule
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Module N.1 (Pic0FiniteStageFinalModelRing C L n m relation M N j) :=
  (pic0FiniteStageFinalModelRingAlgebra C L n m relation M N j).toModule

attribute [local instance] pic0FiniteStageFinalModelRingModule

/-!
The notation `k ⊗[N.1] Pic0FiniteStageFinalModelRing ...` carries the module
instance used to form the tensor product as an implicit argument.  That instance
is intentionally local while the legacy API is built, so repeating the notation
in an importing file makes typeclass search reconstruct the dependent tower (and
can time out).  This alias records the exact module witness once; public pinned
maps below use it in their result types.
-/
noncomputable abbrev Pic0FiniteStageFinalScalarExtensionCarrier
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) : Type u :=
  @TensorProduct N.1
    (inferInstance : CommSemiring N.1)
    k
    (Pic0FiniteStageFinalModelRing C L n m relation M N j)
    (inferInstance : AddCommMonoid k)
    (inferInstance : AddCommMonoid
      (Pic0FiniteStageFinalModelRing C L n m relation M N j))
    (inferInstance : Module N.1 k)
    (pic0FiniteStageFinalModelRingModule C L n m relation M N j)

@[reducible] noncomputable def pic0FiniteStageFinalScalarExtensionSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (k ⊗[N.1] Pic0FiniteStageFinalModelRing C L n m relation M N j) :=
  @Algebra.TensorProduct.instSemiring N.1 k
    (Pic0FiniteStageFinalModelRing C L n m relation M N j)
    (inferInstance : CommSemiring N.1)
    (inferInstance : Semiring k)
    (inferInstance : Algebra N.1 k)
    (pic0FiniteStageFinalModelRingCommSemiring C L n m relation M N j).toSemiring
    (pic0FiniteStageFinalModelRingAlgebra C L n m relation M N j)

attribute [local instance] pic0FiniteStageFinalScalarExtensionSemiring

@[reducible] noncomputable def pic0FiniteStageFinalScalarExtensionAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra k (k ⊗[N.1] Pic0FiniteStageFinalModelRing C L n m relation M N j) :=
  @Algebra.TensorProduct.leftAlgebra N.1 k k
    (Pic0FiniteStageFinalModelRing C L n m relation M N j)
    (inferInstance : CommSemiring N.1)
    (inferInstance : Semiring k)
    (inferInstance : Algebra N.1 k)
    (pic0FiniteStageFinalModelRingCommSemiring C L n m relation M N j).toSemiring
    (pic0FiniteStageFinalModelRingAlgebra C L n m relation M N j)
    (inferInstance : CommSemiring k)
    (inferInstance : Algebra k k)
    (inferInstance : SMulCommClass N.1 k k)

attribute [local instance] pic0FiniteStageFinalScalarExtensionAlgebra

/-! The cancellation equivalence lands in the model's direct scalar extension.
Name its two outer witnesses here so the cancellation and the model comparison share
the same `AlgEquiv` boundary instead of asking typeclass search to rebuild them. -/
set_option synthInstance.maxHeartbeats 400000 in
-- The direct model-base-change carrier is dependent on the selected quotient model.
set_option maxHeartbeats 6400000 in
@[reducible] noncomputable def pic0FiniteStageModelBaseChangeSemiring
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (k ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j) :=
  @Algebra.TensorProduct.instSemiring M.1 k
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Semiring k)
    (inferInstance : Algebra M.1 k)
    (pic0FiniteStageModelRingCommRing C L n m relation M j).toSemiring
    (pic0FiniteStageModelRingAlgebra C L n m relation M j)

attribute [local instance] pic0FiniteStageModelBaseChangeSemiring

set_option synthInstance.maxHeartbeats 400000 in
-- Reuse the semiring witness above when constructing its canonical outer algebra.
set_option maxHeartbeats 6400000 in
@[reducible] noncomputable def pic0FiniteStageModelBaseChangeAlgebra
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra k (k ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j) :=
  letI : Semiring (k ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j) :=
    pic0FiniteStageModelBaseChangeSemiring C L n m relation M j
  @Algebra.TensorProduct.leftAlgebra M.1 k k
    (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring M.1)
    (inferInstance : Semiring k)
    (inferInstance : Algebra M.1 k)
    (pic0FiniteStageModelRingCommRing C L n m relation M j).toSemiring
    (pic0FiniteStageModelRingAlgebra C L n m relation M j)
    (inferInstance : CommSemiring k)
    (inferInstance : Algebra k k)
    (inferInstance : SMulCommClass M.1 k k)

attribute [local instance] pic0FiniteStageModelBaseChangeAlgebra

noncomputable def pic0FiniteStageFinalScalarExtensionMapExplicit
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j1 j2 : Pic0FiniteStageRingIndex C)
    (f : @AlgHom N.1
      (Pic0FiniteStageFinalModelRing C L n m relation M N j1)
      (Pic0FiniteStageFinalModelRing C L n m relation M N j2)
      (inferInstance : CommSemiring N.1)
      (pic0FiniteStageFinalModelRingCommRing C L n m relation M N j1).toSemiring
      (pic0FiniteStageFinalModelRingCommRing C L n m relation M N j2).toSemiring
      (pic0FiniteStageFinalModelRingAlgebra C L n m relation M N j1)
      (pic0FiniteStageFinalModelRingAlgebra C L n m relation M N j2)) :
    @AlgHom k
      (k ⊗[N.1] Pic0FiniteStageFinalModelRing C L n m relation M N j1)
      (k ⊗[N.1] Pic0FiniteStageFinalModelRing C L n m relation M N j2)
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C L n m relation M N j1)
      (pic0FiniteStageFinalScalarExtensionSemiring C L n m relation M N j2)
      (pic0FiniteStageFinalScalarExtensionAlgebra C L n m relation M N j1)
      (pic0FiniteStageFinalScalarExtensionAlgebra C L n m relation M N j2) := by
  letI : Semiring (Pic0FiniteStageFinalModelRing C L n m relation M N j1) :=
    (pic0FiniteStageFinalModelRingCommRing C L n m relation M N j1).toSemiring
  letI : Semiring (Pic0FiniteStageFinalModelRing C L n m relation M N j2) :=
    (pic0FiniteStageFinalModelRingCommRing C L n m relation M N j2).toSemiring
  letI : Algebra N.1 (Pic0FiniteStageFinalModelRing C L n m relation M N j1) :=
    pic0FiniteStageFinalModelRingAlgebra C L n m relation M N j1
  letI : Algebra N.1 (Pic0FiniteStageFinalModelRing C L n m relation M N j2) :=
    pic0FiniteStageFinalModelRingAlgebra C L n m relation M N j2
  exact @AlgebraicJacobian.scalarExtensionMapOfAlgHom
    N.1 k
      (Pic0FiniteStageFinalModelRing C L n m relation M N j1)
      (Pic0FiniteStageFinalModelRing C L n m relation M N j2)
      (inferInstance : CommRing N.1)
      (inferInstance : CommRing k)
      (pic0FiniteStageFinalModelRingCommRing C L n m relation M N j1).toSemiring
      (pic0FiniteStageFinalModelRingCommRing C L n m relation M N j2).toSemiring
      (inferInstance : Algebra N.1 k)
      (pic0FiniteStageFinalModelRingAlgebra C L n m relation M N j1)
      (pic0FiniteStageFinalModelRingAlgebra C L n m relation M N j2)
      f

noncomputable def pic0FiniteStageCancelBaseChange
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    @AlgEquiv k
      (k ⊗[N.1] Pic0FiniteStageFinalModelRing C L n m relation M N j)
      (k ⊗[M.1] Pic0FiniteStageModelRing C L n m relation M j)
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C L n m relation M N j)
      (pic0FiniteStageModelBaseChangeSemiring C L n m relation M j)
      (pic0FiniteStageFinalScalarExtensionAlgebra C L n m relation M N j)
      (pic0FiniteStageModelBaseChangeAlgebra C L n m relation M j) :=
  @Algebra.TensorProduct.cancelBaseChange
    M.1 N.1
    (inferInstance : CommSemiring M.1)
    (inferInstance : CommSemiring N.1)
    (inferInstance : Algebra M.1 N.1)
    k k (Pic0FiniteStageModelRing C L n m relation M j)
    (inferInstance : CommSemiring k)
    (inferInstance : CommSemiring k)
    (pic0FiniteStageModelRingCommRing C L n m relation M j).toCommSemiring
    (inferInstance : Algebra M.1 k)
    (inferInstance : Algebra M.1 k)
    (pic0FiniteStageModelRingAlgebra C L n m relation M j)
    (inferInstance : Algebra k k)
    (inferInstance : IsScalarTower M.1 k k)
    (inferInstance : Algebra N.1 k)
    (inferInstance : IsScalarTower M.1 N.1 k)
    (inferInstance : Algebra N.1 k)
    (inferInstance : IsScalarTower N.1 k k)

set_option synthInstance.maxHeartbeats 400000 in
-- The comparison cancels two nested finite-subextension scalar towers.
set_option maxHeartbeats 6400000 in
/-- Scalar extension of a final finite-stage model ring recovers its exact atlas ring. -/
noncomputable def pic0FiniteStageFinalBaseChangeEquiv
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    k ⊗[N.1] Pic0FiniteStageFinalModelRing C L n m relation M N j ≃ₐ[k]
      Pic0FiniteStageRing C j :=
  (pic0FiniteStageCancelBaseChange C L n m relation M N j).trans
    (pic0FiniteStageModelBaseChangeEquiv C L n m relation e M j)

/-!
The shorthand equivalence above remains for source compatibility.  Its displayed
carrier still asks an importing file to synthesize the module hidden in the tensor
notation.  The pinned façade has a fully elaborated carrier and structure tuple in
its type, so consumers can use `@AlgEquiv.toAlgHom` without any local instances.
-/
set_option synthInstance.maxHeartbeats 400000 in
-- The pinned result type fixes the tensor carrier before the legacy composition is elaborated.
set_option maxHeartbeats 6400000 in
-- The legacy cancellation/model composition is intentionally checked once at this boundary.
noncomputable def pic0FiniteStageFinalBaseChangeEquivPinned
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    @AlgEquiv k
      (Pic0FiniteStageFinalScalarExtensionCarrier C L n m relation M N j)
      (Pic0FiniteStageRing C j)
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C L n m relation M N j)
      (instCommRingPic0FiniteStageRing C j).toSemiring
      (pic0FiniteStageFinalScalarExtensionAlgebra C L n m relation M N j)
      (instAlgebraPic0FiniteStageRing C j) :=
  pic0FiniteStageFinalBaseChangeEquiv C L n m relation e M N j

/-!
The ring-level equivalence and the package below are retained as compatibility adapters.
The package's abstract `source` carrier is not definitionally identified with
`Pic0FiniteStageFinalScalarExtensionCarrier`, so it is unsuitable for new dependent
compositions.  New consumers should use the pinned façade above and its class-free
`pic0FiniteStageFinalBaseChangeEquivPinnedFun` and
`pic0FiniteStageFinalScalarExtensionMapPinnedFun` projections; these preserve the explicit
carrier and structure witnesses at the API boundary.
-/
noncomputable opaque pic0FiniteStageFinalBaseChangeData
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Pic0FiniteStageModelBaseChangeData k :=
  Pic0FiniteStageModelBaseChangeData.of_equiv
    (pic0FiniteStageFinalBaseChangeEquiv C L n m relation e M N j)

/- The projection is intentionally exposed under a named declaration.  Its result type is
   inherited from the package, so no hidden `≃ₐ` witness is synthesized by consumers. -/
noncomputable def pic0FiniteStageFinalBaseChangeForward
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :=
  (pic0FiniteStageFinalBaseChangeData C L n m relation e M N j).forward

set_option synthInstance.maxHeartbeats 3200000 in
-- The explicit tensor witnesses avoid instance-search loops at this API boundary.
set_option maxHeartbeats 12800000 in
/-- The scalar extension of a selected finite-stage map, with the final-model ring and
algebra witnesses pinned in its result type.  Naturality consumers should use this map
instead of reconstructing `scalarExtensionMapOfAlgHom` from inferred tensor instances. -/
noncomputable def pic0FiniteStageFinalScalarExtensionMap
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
    (q : Pic0FiniteStageMapIndex C) :
    @AlgHom k
      (k ⊗[N.1] Pic0FiniteStageFinalModelRing C L n m relation M N
        (Pic0FiniteStageMapSource C q))
      (k ⊗[N.1] Pic0FiniteStageFinalModelRing C L n m relation M N
        (Pic0FiniteStageMapTarget C q))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C L n m relation M N
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageFinalScalarExtensionSemiring C L n m relation M N
        (Pic0FiniteStageMapTarget C q))
      (pic0FiniteStageFinalScalarExtensionAlgebra C L n m relation M N
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageFinalScalarExtensionAlgebra C L n m relation M N
        (Pic0FiniteStageMapTarget C q)) :=
  pic0FiniteStageFinalScalarExtensionMapExplicit C L n m relation M N
    (Pic0FiniteStageMapSource C q) (Pic0FiniteStageMapTarget C q)
    (pic0FiniteStageModelScalarExtensionMap C L n m relation M N
      (Pic0FiniteStageMapSource C q) (Pic0FiniteStageMapTarget C q) (mapM q))

/- The explicit carrier alias and structure tuple make this projection usable from
   importing modules; the legacy map above remains a compatibility adapter. -/
set_option synthInstance.maxHeartbeats 400000 in
-- The scalar-extension wrapper elaborates a dependent source and target map exactly once.
set_option maxHeartbeats 12800000 in
-- Keep the explicit structure tuple visible in the public result type.
noncomputable def pic0FiniteStageFinalScalarExtensionMapPinned
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
    (q : Pic0FiniteStageMapIndex C) :
    @AlgHom k
      (Pic0FiniteStageFinalScalarExtensionCarrier C L n m relation M N
        (Pic0FiniteStageMapSource C q))
      (Pic0FiniteStageFinalScalarExtensionCarrier C L n m relation M N
        (Pic0FiniteStageMapTarget C q))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C L n m relation M N
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageFinalScalarExtensionSemiring C L n m relation M N
        (Pic0FiniteStageMapTarget C q))
      (pic0FiniteStageFinalScalarExtensionAlgebra C L n m relation M N
        (Pic0FiniteStageMapSource C q))
      (pic0FiniteStageFinalScalarExtensionAlgebra C L n m relation M N
        (Pic0FiniteStageMapTarget C q)) :=
  pic0FiniteStageFinalScalarExtensionMap C L n m relation M mapM N q

/- The inherited `OneHom.toFun` projection of an `AlgHom` still asks importing modules
   to synthesize `One` on the dependent tensor carrier.  Export its underlying function
   separately; this projection is plain data and therefore has no class arguments at use sites. -/
noncomputable def pic0FiniteStageFinalScalarExtensionMapPinnedFun
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
    (q : Pic0FiniteStageMapIndex C) :
    Pic0FiniteStageFinalScalarExtensionCarrier C L n m relation M N
        (Pic0FiniteStageMapSource C q) →
      Pic0FiniteStageFinalScalarExtensionCarrier C L n m relation M N
        (Pic0FiniteStageMapTarget C q) :=
  fun x => pic0FiniteStageFinalScalarExtensionMapPinned C L n m relation M mapM N q x

set_option synthInstance.maxHeartbeats 400000 in
-- Converting the pinned equivalence to a hom uses its already fixed structure witnesses.
set_option maxHeartbeats 6400000 in
-- Do not ask typeclass search to infer the dependent tensor structures at a use site.
noncomputable def pic0FiniteStageFinalBaseChangeForwardPinned
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    @AlgHom k
      (Pic0FiniteStageFinalScalarExtensionCarrier C L n m relation M N j)
      (Pic0FiniteStageRing C j)
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C L n m relation M N j)
      (instCommRingPic0FiniteStageRing C j).toSemiring
      (pic0FiniteStageFinalScalarExtensionAlgebra C L n m relation M N j)
      (instAlgebraPic0FiniteStageRing C j) :=
  @AlgEquiv.toAlgHom k
    (Pic0FiniteStageFinalScalarExtensionCarrier C L n m relation M N j)
    (Pic0FiniteStageRing C j)
    (inferInstance : CommSemiring k)
    (pic0FiniteStageFinalScalarExtensionSemiring C L n m relation M N j)
    (instCommRingPic0FiniteStageRing C j).toSemiring
    (pic0FiniteStageFinalScalarExtensionAlgebra C L n m relation M N j)
    (instAlgebraPic0FiniteStageRing C j)
    (pic0FiniteStageFinalBaseChangeEquivPinned C L n m relation e M N j)

/- As with the scalar-extension map, expose a class-free pointwise projection for consumers
   that only need the comparison function.  This definition is the function-level view of
   the pinned equivalence, so naturality statements cannot silently switch boundaries. -/
noncomputable def pic0FiniteStageFinalBaseChangeEquivPinnedFun
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
  Pic0FiniteStageFinalScalarExtensionCarrier C L n m relation M N j →
      Pic0FiniteStageRing C j :=
  fun x => (pic0FiniteStageFinalBaseChangeEquivPinned C L n m relation e M N j).toFun x

/- Compatibility name for clients that think of the comparison as its forward map. -/
noncomputable def pic0FiniteStageFinalBaseChangeForwardPinnedFun
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Pic0FiniteStageFinalScalarExtensionCarrier C L n m relation M N j →
      Pic0FiniteStageRing C j :=
  pic0FiniteStageFinalBaseChangeEquivPinnedFun C L n m relation e M N j

set_option synthInstance.maxHeartbeats 400000 in
-- Naturality elaborates the cancellation and model-comparison squares together.
set_option maxHeartbeats 12800000 in
/-- The final component comparisons intertwine every scalar-extended finite-stage map
with its exact restriction or transition map. -/
theorem pic0FiniteStageFinalBaseChangeEquiv_naturality
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    [Algebra.IsAlgebraic M.1 k]
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (hmapM : forall q,
      (pic0FiniteStageModelAmbientMapCompRestrict C L n m relation M
        (Pic0FiniteStageMapSource C q)
        (Pic0FiniteStageMapTarget C q)
        (mapM q)) =
        (pic0FiniteStageTransportedMapRestrictCompAmbient C L n m relation e M q))
    (N : DatG0.FinSubext M.1 k)
    (q : Pic0FiniteStageMapIndex C) :
    (pic0FiniteStageFinalBaseChangeEquiv C L n m relation e M N
        (Pic0FiniteStageMapTarget C q)).toAlgHom.comp
        (pic0FiniteStageFinalScalarExtensionMap C L n m relation M mapM N q) =
        (pic0FiniteStageMap C q).comp
        (pic0FiniteStageFinalBaseChangeEquiv C L n m relation e M N
          (Pic0FiniteStageMapSource C q)).toAlgHom := by
  have htower := @AlgebraicJacobian.scalarExtensionMapOfAlgHom_tower
    M.1 N.1 k
    (Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapSource C q))
    (Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapTarget C q))
    (inferInstance : CommRing M.1)
    (inferInstance : CommRing N.1)
    (inferInstance : CommRing k)
    (pic0FiniteStageModelRingCommRing C L n m relation M
      (Pic0FiniteStageMapSource C q)).toSemiring
    (pic0FiniteStageModelRingCommRing C L n m relation M
      (Pic0FiniteStageMapTarget C q)).toSemiring
    (inferInstance : Algebra M.1 N.1)
    (inferInstance : Algebra M.1 k)
    (inferInstance : Algebra N.1 k)
    (inferInstance : IsScalarTower M.1 N.1 k)
    (pic0FiniteStageModelRingAlgebra C L n m relation M
      (Pic0FiniteStageMapSource C q))
    (pic0FiniteStageModelRingAlgebra C L n m relation M
      (Pic0FiniteStageMapTarget C q))
    (mapM q)
  have hcancel := @AlgebraicJacobian.cancelBaseChange_naturality
    M.1 N.1 k
    (Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapSource C q))
    (Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapTarget C q))
    (inferInstance : CommRing M.1)
    (inferInstance : CommRing N.1)
    (inferInstance : CommRing k)
    (pic0FiniteStageModelRingCommRing C L n m relation M
      (Pic0FiniteStageMapSource C q))
    (pic0FiniteStageModelRingCommRing C L n m relation M
      (Pic0FiniteStageMapTarget C q))
    (inferInstance : Algebra M.1 N.1)
    (inferInstance : Algebra M.1 k)
    (inferInstance : Algebra N.1 k)
    (inferInstance : IsScalarTower M.1 N.1 k)
    (pic0FiniteStageModelRingAlgebra C L n m relation M
      (Pic0FiniteStageMapSource C q))
    (pic0FiniteStageModelRingAlgebra C L n m relation M
      (Pic0FiniteStageMapTarget C q))
    (pic0FiniteStageModelScalarExtensionMap C L n m relation M N
      (Pic0FiniteStageMapSource C q) (Pic0FiniteStageMapTarget C q) (mapM q))
    (pic0FiniteStageScalarExtensionMapOver C L n m relation M
      (Pic0FiniteStageMapSource C q) (Pic0FiniteStageMapTarget C q) (mapM q))
    htower
  have hmodel := pic0FiniteStageModelBaseChangeEquiv_naturality
    C L n m relation e M mapM hmapM q
  apply DFunLike.ext _ _
  intro x
  change
    (pic0FiniteStageFinalBaseChangeEquiv C L n m relation e M N
        (Pic0FiniteStageMapTarget C q))
        ((pic0FiniteStageFinalScalarExtensionMap C L n m relation M mapM N q) x) =
      pic0FiniteStageMap C q
        ((pic0FiniteStageFinalBaseChangeEquiv C L n m relation e M N
          (Pic0FiniteStageMapSource C q)) x)
  change
    (pic0FiniteStageModelBaseChangeEquiv C L n m relation e M
        (Pic0FiniteStageMapTarget C q))
        ((pic0FiniteStageCancelBaseChange C L n m relation M N
          (Pic0FiniteStageMapTarget C q))
          ((pic0FiniteStageFinalScalarExtensionMap C L n m relation M mapM N q) x)) =
      pic0FiniteStageMap C q
        ((pic0FiniteStageModelBaseChangeEquiv C L n m relation e M
          (Pic0FiniteStageMapSource C q))
          ((pic0FiniteStageCancelBaseChange C L n m relation M N
            (Pic0FiniteStageMapSource C q)) x))
  have hx := DFunLike.congr_fun hcancel x
  have hm := DFunLike.congr_fun hmodel
    ((pic0FiniteStageCancelBaseChange C L n m relation M N
      (Pic0FiniteStageMapSource C q)) x)
  rw [show
      (pic0FiniteStageCancelBaseChange C L n m relation M N
          (Pic0FiniteStageMapTarget C q))
          ((pic0FiniteStageFinalScalarExtensionMap C L n m relation M mapM N q) x) =
        (AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := M.1) (K := k) (mapM q))
          ((pic0FiniteStageCancelBaseChange C L n m relation M N
            (Pic0FiniteStageMapSource C q)) x) by
    exact hx]
  exact hm

set_option synthInstance.maxHeartbeats 400000 in
-- Pointwise naturality avoids rebuilding an `AlgHom` composition from hidden tensor instances.
set_option maxHeartbeats 12800000 in
-- The pinned equivalence and scalar map are unfolded only inside this compatibility proof.
/-- Pointwise naturality for the import-safe final-stage comparison API. -/
theorem pic0FiniteStageFinalBaseChangeEquivPinned_naturality
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    [Algebra.IsAlgebraic M.1 k]
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (hmapM : forall q,
      (pic0FiniteStageModelAmbientMapCompRestrict C L n m relation M
        (Pic0FiniteStageMapSource C q)
        (Pic0FiniteStageMapTarget C q)
        (mapM q)) =
        (pic0FiniteStageTransportedMapRestrictCompAmbient C L n m relation e M q))
    (N : DatG0.FinSubext M.1 k)
    (q : Pic0FiniteStageMapIndex C)
    (x : Pic0FiniteStageFinalScalarExtensionCarrier C L n m relation M N
      (Pic0FiniteStageMapSource C q)) :
    (pic0FiniteStageFinalBaseChangeEquivPinnedFun C L n m relation e M N
      (Pic0FiniteStageMapTarget C q))
        (pic0FiniteStageFinalScalarExtensionMapPinnedFun C L n m relation M mapM N q x) =
      (pic0FiniteStageMap C q).toFun
        (pic0FiniteStageFinalBaseChangeEquivPinnedFun C L n m relation e M N
          (Pic0FiniteStageMapSource C q) x) := by
  have h := DFunLike.congr_fun
    (pic0FiniteStageFinalBaseChangeEquiv_naturality
      C L n m relation e M mapM hmapM N q) x
  simpa [pic0FiniteStageFinalBaseChangeEquivPinned,
    pic0FiniteStageFinalScalarExtensionMapPinned,
    pic0FiniteStageFinalScalarExtensionMapPinnedFun,
    pic0FiniteStageFinalBaseChangeEquivPinnedFun,
    pic0FiniteStageFinalBaseChangeForwardPinnedFun] using h

end

end AlgebraicGeometry
