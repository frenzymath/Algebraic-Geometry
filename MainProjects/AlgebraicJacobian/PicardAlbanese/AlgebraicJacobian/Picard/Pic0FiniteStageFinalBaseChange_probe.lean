/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluedOver
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelComparison

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
  exact Algebra.TensorProduct.leftAlgebra
    (R := L.1) (S := M.1) (A := M.1)
    (B := DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))

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
    Algebra.TensorProduct.leftAlgebra
      (R := L.1) (S := M.1) (A := M.1)
      (B := DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
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
    Algebra.TensorProduct.leftAlgebra
      (R := L.1) (S := M.1) (A := M.1)
      (B := DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))
  exact Algebra.TensorProduct.leftAlgebra
    (R := M.1) (S := N.1) (A := N.1)
    (B := Pic0FiniteStageModelRing C L n m relation M j)

attribute [instance 2000] pic0FiniteStageModelRingAlgebra
  pic0FiniteStageFinalModelRingAlgebra

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
    (inferInstance : Semiring
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))
    (inferInstance : Algebra L.1
      (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j)))

-- attribute [local instance] pic0FiniteStageModelRingBaseAlgebra

set_option synthInstance.maxHeartbeats 400000 in
-- Tensor-product action instances require a larger deterministic search budget.
set_option maxHeartbeats 6400000 in
@[reducible] noncomputable def pic0FiniteStageModelRingIsScalarTower
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
  refine { smul_assoc := ?_ }
  intro x y z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | tmul a b =>
      simp [Algebra.smul_def, TensorProduct.smul_tmul', ← mul_assoc]

attribute [local instance 2000] pic0FiniteStageModelRingIsScalarTower

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
    (inferInstance : Semiring
      (Pic0FiniteStageFinalModelRing C L n m relation M N j))
    (inferInstance : Algebra N.1
      (Pic0FiniteStageFinalModelRing C L n m relation M N j))

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
    (inferInstance : Semiring
      (Pic0FiniteStageFinalModelRing C L n m relation M N j))
    (inferInstance : Algebra N.1
      (Pic0FiniteStageFinalModelRing C L n m relation M N j))
    (inferInstance : CommSemiring k)
    (inferInstance : Algebra k k)
    (inferInstance : SMulCommClass N.1 k k)

attribute [local instance] pic0FiniteStageFinalScalarExtensionAlgebra

example
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (Pic0FiniteStageFinalModelRing C L n m relation M N j) := by
  infer_instance

example
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k) (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k) : IsScalarTower M.1 N.1 k := by
  infer_instance

example
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Algebra N.1 (Pic0FiniteStageFinalModelRing C L n m relation M N j) := by
  infer_instance

example
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (M : DatG0.FinSubext L.1 k)
    (N : DatG0.FinSubext M.1 k)
    (j : Pic0FiniteStageRingIndex C) :
    Semiring (k ⊗[N.1] Pic0FiniteStageFinalModelRing C L n m relation M N j) := by
  infer_instance

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
      Pic0FiniteStageRing C j := by
  exact (Algebra.TensorProduct.cancelBaseChange M.1 N.1 k k
    (Pic0FiniteStageModelRing C L n m relation M j)).trans
      (pic0FiniteStageModelBaseChangeEquiv C L n m relation e M j)

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
    (q : Pic0FiniteStageMapIndex C) :
    (pic0FiniteStageFinalBaseChangeEquiv C L n m relation e M N
        (Pic0FiniteStageMapTarget C q)).toAlgHom.comp
        (AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := N.1) (K := k)
          (AlgebraicJacobian.scalarExtensionMapOfAlgHom
            (R := M.1) (K := N.1) (mapM q))) =
      (pic0FiniteStageMap C q).comp
        (pic0FiniteStageFinalBaseChangeEquiv C L n m relation e M N
          (Pic0FiniteStageMapSource C q)).toAlgHom := by
  have hval : N.1.val = IsScalarTower.toAlgHom M.1 N.1 k := by
    ext x
    rfl
  have htower :=
    scalarExtensionMapOfAlgHom_tower_finSubext (K := k) N (mapM q)
  rw [hval] at htower
  have hcancel := AlgebraicJacobian.cancelBaseChange_naturality
    (F := M.1) (L := N.1) (K := k)
    (phiL := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := M.1) (K := N.1) (mapM q))
    (phiK := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := M.1) (K := k) (mapM q))
    htower
  have hmodel := pic0FiniteStageModelBaseChangeEquiv_naturality
    C L n m relation e M mapM hmapM q
  let eTarget := (pic0FiniteStageModelBaseChangeEquiv C L n m relation e M
    (Pic0FiniteStageMapTarget C q)).toAlgHom
  let eSource := (pic0FiniteStageModelBaseChangeEquiv C L n m relation e M
    (Pic0FiniteStageMapSource C q)).toAlgHom
  let cTarget := (Algebra.TensorProduct.cancelBaseChange M.1 N.1 k k
    (Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapTarget C q))).toAlgHom
  let cSource := (Algebra.TensorProduct.cancelBaseChange M.1 N.1 k k
    (Pic0FiniteStageModelRing C L n m relation M
      (Pic0FiniteStageMapSource C q))).toAlgHom
  let fN := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := N.1) (K := k)
    (AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := M.1) (K := N.1) (mapM q))
  let fK := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := M.1) (K := k) (mapM q)
  let g := pic0FiniteStageMap C q
  change cTarget.comp fN = fK.comp cSource at hcancel
  change eTarget.comp fK = g.comp eSource at hmodel
  change (eTarget.comp cTarget).comp fN = g.comp (eSource.comp cSource)
  calc
    _ = eTarget.comp (cTarget.comp fN) := AlgHom.comp_assoc _ _ _
    _ = eTarget.comp (fK.comp cSource) :=
      congrArg (fun f => eTarget.comp f) hcancel
    _ = (eTarget.comp fK).comp cSource := (AlgHom.comp_assoc _ _ _).symm
    _ = (g.comp eSource).comp cSource :=
      congrArg (fun f => f.comp cSource) hmodel
    _ = g.comp (eSource.comp cSource) := AlgHom.comp_assoc _ _ _

end

end AlgebraicGeometry
