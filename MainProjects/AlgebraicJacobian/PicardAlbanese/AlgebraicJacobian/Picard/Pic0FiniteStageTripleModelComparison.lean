/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.TensorProductFieldTowerMap
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleOverlapRings

/-!
# Comparing finite-stage Picard triple-overlap models

The finite-stage atlas theorem supplies presentations over `L`, models over a further
finite subextension `M`, and comparison maps after scalar extension.  This file first
cancels the tower `L -> M -> k`, producing a componentwise equivalence from the scalar
extension of every model ring to its exact section ring.  The supplied map squares become
literal naturality squares for these component equivalences.

The second step gives a reusable transport equivalence for tensor pushouts, including its
two factor-inclusion formulas.  Specializing that equivalence to the dependent Picard triple
model remains downstream: explicit ring annotations break instance coherence, while fully
inferred specialization currently exceeds the elaboration budget.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-! ## Component comparisons -/

set_option synthInstance.maxHeartbeats 200000 in
-- The component contains two dependent quotient-algebra instances.
/-- Cancel the intermediate finite subextension in a finite-presentation model and then
apply its chosen exact-ring comparison. -/
def pic0FiniteStageModelBaseChangeEquiv
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (j : Pic0FiniteStageRingIndex C) :=
  (Algebra.TensorProduct.cancelBaseChange L.1 M.1 k k
    (DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j))).trans (e j)

/-!
The comparison above is intentionally retained for source compatibility, but its inferred
tensor instances are part of the returned `AlgEquiv`.  Rebuilding a map from the displayed
carrier later can therefore select a propositionally equal, non-definitional algebra.  The
package below is the stable boundary for new consumers: pass the already elaborated
equivalence once, then carry its exact witnesses explicitly through subsequent definitions.
-/

/-- An algebra equivalence together with the exact structures in its type.

This record has no dependent `letI` fields.  In particular, projections below use explicit
`@AlgEquiv.toAlgHom` arguments, so taking a map from the package never invokes typeclass
search on a dependent tensor carrier.
-/
structure Pic0FiniteStageModelBaseChangeData (R : Type u) where
  baseSemiring : CommSemiring R
  source : Type u
  target : Type u
  sourceSemiring : Semiring source
  targetSemiring : Semiring target
  sourceAlgebra : Algebra R source
  targetAlgebra : Algebra R target
  equiv : @AlgEquiv R source target baseSemiring sourceSemiring targetSemiring
    sourceAlgebra targetAlgebra

namespace Pic0FiniteStageModelBaseChangeData

/- The explicit instance arguments are intentional: `D.equiv.toAlgHom` would ask Lean to
   synthesize the same witnesses again. -/
/-- Package an already elaborated comparison without changing any of its witnesses. -/
noncomputable def of_equiv
    {R A B : Type u}
    {baseSemiring : CommSemiring R}
    {sourceSemiring : Semiring A} {targetSemiring : Semiring B}
    {sourceAlgebra : Algebra R A} {targetAlgebra : Algebra R B}
    (equiv : @AlgEquiv R A B baseSemiring sourceSemiring targetSemiring
      sourceAlgebra targetAlgebra) :
    Pic0FiniteStageModelBaseChangeData R :=
  { baseSemiring := baseSemiring
    source := A
    target := B
    sourceSemiring := sourceSemiring
    targetSemiring := targetSemiring
    sourceAlgebra := sourceAlgebra
    targetAlgebra := targetAlgebra
    equiv := equiv }

/-- The forward map with the package's source and target structures pinned. -/
abbrev forward {R : Type u} (D : Pic0FiniteStageModelBaseChangeData R) :
    @AlgHom R D.source D.target D.baseSemiring D.sourceSemiring D.targetSemiring
      D.sourceAlgebra D.targetAlgebra :=
  @AlgEquiv.toAlgHom R D.source D.target D.baseSemiring D.sourceSemiring
    D.targetSemiring D.sourceAlgebra D.targetAlgebra D.equiv

/-- The backward map with the package's source and target structures pinned. -/
abbrev backward {R : Type u} (D : Pic0FiniteStageModelBaseChangeData R) :
    @AlgHom R D.target D.source D.baseSemiring D.targetSemiring D.sourceSemiring
      D.targetAlgebra D.sourceAlgebra :=
  @AlgEquiv.toAlgHom R D.target D.source D.baseSemiring D.targetSemiring
    D.sourceSemiring D.targetAlgebra D.sourceAlgebra
    (@AlgEquiv.symm R D.source D.target D.baseSemiring D.sourceSemiring
      D.targetSemiring D.sourceAlgebra D.targetAlgebra D.equiv)

@[simp]
theorem backward_apply_forward {R : Type u}
    (D : Pic0FiniteStageModelBaseChangeData R) (x : D.source) :
    D.backward (D.forward x) = x := by
  change D.equiv.invFun (D.equiv.toFun x) = x
  exact D.equiv.left_inv x

@[simp]
theorem forward_apply_backward {R : Type u}
    (D : Pic0FiniteStageModelBaseChangeData R) (x : D.target) :
    D.forward (D.backward x) = x := by
  change D.equiv.toFun (D.equiv.invFun x) = x
  exact D.equiv.right_inv x

end Pic0FiniteStageModelBaseChangeData

set_option synthInstance.maxHeartbeats 200000 in
-- The source and target quotient algebras depend on the finite ring tag.
set_option maxHeartbeats 1600000 in
-- Cancellation naturality and conjugation elaborate through both dependent models.
/-- The component comparisons intertwine each scalar-extended finite-stage map with the
corresponding exact restriction or transition map. -/
theorem pic0FiniteStageModelBaseChangeEquiv_naturality
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
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
    (q : Pic0FiniteStageMapIndex C) :
    (pic0FiniteStageModelBaseChangeEquiv C L n m relation e M
        (Pic0FiniteStageMapTarget C q)).toAlgHom.comp
        (AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := M.1) (K := k) (mapM q)) =
      (pic0FiniteStageMap C q).comp
        (pic0FiniteStageModelBaseChangeEquiv C L n m relation e M
          (Pic0FiniteStageMapSource C q)).toAlgHom := by
  have hval : M.1.val = IsScalarTower.toAlgHom L.1 M.1 k := by
    ext x
    rfl
  have hcancel := AlgebraicJacobian.cancelBaseChange_naturality
    (F := L.1) (L := M.1) (K := k)
    (phiL := mapM q)
    (phiK := pic0FiniteStageTransportedMap C L n m relation e q)
    (by
      rw [← hval]
      exact hmapM q)
  apply DFunLike.ext _ _
  intro x
  have hx := DFunLike.congr_fun hcancel x
  change
    (Algebra.TensorProduct.cancelBaseChange L.1 M.1 k k
      (DatG0.FiniteRelationAlgebra L.1
        (n (Pic0FiniteStageMapTarget C q))
        (m (Pic0FiniteStageMapTarget C q))
        (relation (Pic0FiniteStageMapTarget C q))))
        (AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := M.1) (K := k) (mapM q) x) =
      pic0FiniteStageTransportedMap C L n m relation e q
        ((Algebra.TensorProduct.cancelBaseChange L.1 M.1 k k
          (DatG0.FiniteRelationAlgebra L.1
            (n (Pic0FiniteStageMapSource C q))
            (m (Pic0FiniteStageMapSource C q))
            (relation (Pic0FiniteStageMapSource C q)))) x) at hx
  change
    e (Pic0FiniteStageMapTarget C q)
      ((Algebra.TensorProduct.cancelBaseChange L.1 M.1 k k
        (DatG0.FiniteRelationAlgebra L.1
          (n (Pic0FiniteStageMapTarget C q))
          (m (Pic0FiniteStageMapTarget C q))
          (relation (Pic0FiniteStageMapTarget C q))))
        (AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := M.1) (K := k) (mapM q) x)) =
      pic0FiniteStageMap C q
        (e (Pic0FiniteStageMapSource C q)
          ((Algebra.TensorProduct.cancelBaseChange L.1 M.1 k k
            (DatG0.FiniteRelationAlgebra L.1
              (n (Pic0FiniteStageMapSource C q))
              (m (Pic0FiniteStageMapSource C q))
              (relation (Pic0FiniteStageMapSource C q)))) x))
  rw [hx]
  exact (e (Pic0FiniteStageMapTarget C q)).apply_symm_apply
    (pic0FiniteStageMap C q
      (e (Pic0FiniteStageMapSource C q)
        ((Algebra.TensorProduct.cancelBaseChange L.1 M.1 k k
          (DatG0.FiniteRelationAlgebra L.1
            (n (Pic0FiniteStageMapSource C q))
            (m (Pic0FiniteStageMapSource C q))
            (relation (Pic0FiniteStageMapSource C q)))) x)))

/-! ## Transporting tensor pushouts -/

/-- Tensor-product pushouts are invariant under compatible equivalences of their base
and two factors.  The result is an equivalence over the common ground ring. -/
noncomputable def tensorPushoutAlgEquivCongr
    {R A1 A2 B1 B2 D1 D2 : Type u}
    [CommRing R] [CommRing A1] [CommRing A2]
    [CommRing B1] [CommRing B2] [CommRing D1] [CommRing D2]
    [Algebra R A1] [Algebra R A2]
    [Algebra R B1] [Algebra R B2] [Algebra R D1] [Algebra R D2]
    (f1 : A1 →ₐ[R] B1) (g1 : A1 →ₐ[R] D1)
    (f2 : A2 →ₐ[R] B2) (g2 : A2 →ₐ[R] D2)
    (eA : A1 ≃ₐ[R] A2) (eB : B1 ≃ₐ[R] B2) (eD : D1 ≃ₐ[R] D2)
    (hf : eB.toAlgHom.comp f1 = f2.comp eA.toAlgHom)
    (hg : eD.toAlgHom.comp g1 = g2.comp eA.toAlgHom) :
    letI : Algebra A1 B1 := f1.toRingHom.toAlgebra
    letI : Algebra A1 D1 := g1.toRingHom.toAlgebra
    letI : Algebra A2 B2 := f2.toRingHom.toAlgebra
    letI : Algebra A2 D2 := g2.toRingHom.toAlgebra
    letI : IsScalarTower R A1 B1 :=
      IsScalarTower.of_algebraMap_eq (fun x => (f1.commutes x).symm)
    letI : IsScalarTower R A2 B2 :=
      IsScalarTower.of_algebraMap_eq (fun x => (f2.commutes x).symm)
    B1 ⊗[A1] D1 ≃ₐ[R] B2 ⊗[A2] D2 := by
  letI : Algebra A1 B1 := f1.toRingHom.toAlgebra
  letI : Algebra A1 D1 := g1.toRingHom.toAlgebra
  letI : Algebra A2 B2 := f2.toRingHom.toAlgebra
  letI : Algebra A2 D2 := g2.toRingHom.toAlgebra
  letI : IsScalarTower R A1 B1 :=
    IsScalarTower.of_algebraMap_eq (fun x => (f1.commutes x).symm)
  letI : IsScalarTower R A2 B2 :=
    IsScalarTower.of_algebraMap_eq (fun x => (f2.commutes x).symm)
  let P1 := B1 ⊗[A1] D1
  let P2 := B2 ⊗[A2] D2
  let jB : B1 →+* P2 :=
    Algebra.TensorProduct.includeLeftRingHom.comp eB.toRingEquiv.toRingHom
  let jD : D1 →+* P2 :=
    Algebra.TensorProduct.includeRight.toRingHom.comp eD.toRingEquiv.toRingHom
  have ht : IsPushout
      (CommRingCat.ofHom f1.toRingHom) (CommRingCat.ofHom g1.toRingHom)
      (CommRingCat.ofHom jB) (CommRingCat.ofHom jD) := by
    apply (CommRingCat.isPushout_tensorProduct A2 B2 D2).of_iso'
      eA.toRingEquiv.toCommRingCatIso eB.toRingEquiv.toCommRingCatIso
      eD.toRingEquiv.toCommRingCatIso (Iso.refl (CommRingCat.of P2))
    · ext x
      exact DFunLike.congr_fun hf.symm x
    · ext x
      exact DFunLike.congr_fun hg.symm x
    · rfl
    · rfl
  have hs : IsPushout
      (CommRingCat.ofHom f1.toRingHom) (CommRingCat.ofHom g1.toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := A1) (A := B1) (B := D1)))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := A1) (A := B1) (B := D1)).toRingHom) :=
    CommRingCat.isPushout_tensorProduct A1 B1 D1
  let ie : CommRingCat.of P1 ≅ CommRingCat.of P2 :=
    hs.isoIsPushout (CommRingCat.of B1) (CommRingCat.of D1) ht
  have left_formula (b : B1) :
      ie.hom.hom (b ⊗ₜ[A1] (1 : D1)) = eB b ⊗ₜ[A2] (1 : D2) := by
    have hleft := hs.inl_isoIsPushout_hom
      (CommRingCat.of B1) (CommRingCat.of D1) ht
    have hx := congrArg
      (fun q : CommRingCat.of B1 ⟶ CommRingCat.of P2 => q.hom b) hleft
    change ie.hom.hom (b ⊗ₜ[A1] (1 : D1)) = jB b at hx
    exact hx
  let re : P1 ≃+* P2 := ie.commRingCatIsoToRingEquiv
  refine AlgEquiv.ofRingEquiv (f := re) fun x => ?_
  change ie.hom.hom (((algebraMap R B1) x) ⊗ₜ[A1] (1 : D1)) =
    ((algebraMap R B2) x) ⊗ₜ[A2] (1 : D2)
  rw [left_formula, eB.commutes]

/-- The pushout-congruence equivalence carries both tensor inclusions to the transported
factor inclusions. -/
theorem tensorPushoutAlgEquivCongr_faces
    {R A1 A2 B1 B2 D1 D2 : Type u}
    [CommRing R] [CommRing A1] [CommRing A2]
    [CommRing B1] [CommRing B2] [CommRing D1] [CommRing D2]
    [Algebra R A1] [Algebra R A2]
    [Algebra R B1] [Algebra R B2] [Algebra R D1] [Algebra R D2]
    (f1 : A1 →ₐ[R] B1) (g1 : A1 →ₐ[R] D1)
    (f2 : A2 →ₐ[R] B2) (g2 : A2 →ₐ[R] D2)
    (eA : A1 ≃ₐ[R] A2) (eB : B1 ≃ₐ[R] B2) (eD : D1 ≃ₐ[R] D2)
    (hf : eB.toAlgHom.comp f1 = f2.comp eA.toAlgHom)
    (hg : eD.toAlgHom.comp g1 = g2.comp eA.toAlgHom) :
    letI : Algebra A1 B1 := f1.toRingHom.toAlgebra
    letI : Algebra A1 D1 := g1.toRingHom.toAlgebra
    letI : Algebra A2 B2 := f2.toRingHom.toAlgebra
    letI : Algebra A2 D2 := g2.toRingHom.toAlgebra
    letI : IsScalarTower R A1 B1 :=
      IsScalarTower.of_algebraMap_eq (fun x => (f1.commutes x).symm)
    letI : IsScalarTower R A2 B2 :=
      IsScalarTower.of_algebraMap_eq (fun x => (f2.commutes x).symm)
    (forall b : B1,
      tensorPushoutAlgEquivCongr f1 g1 f2 g2 eA eB eD hf hg
          (b ⊗ₜ[A1] (1 : D1)) =
        eB b ⊗ₜ[A2] (1 : D2)) ∧
    (forall d : D1,
      tensorPushoutAlgEquivCongr f1 g1 f2 g2 eA eB eD hf hg
          ((1 : B1) ⊗ₜ[A1] d) =
        (1 : B2) ⊗ₜ[A2] eD d) := by
  letI : Algebra A1 B1 := f1.toRingHom.toAlgebra
  letI : Algebra A1 D1 := g1.toRingHom.toAlgebra
  letI : Algebra A2 B2 := f2.toRingHom.toAlgebra
  letI : Algebra A2 D2 := g2.toRingHom.toAlgebra
  letI : IsScalarTower R A1 B1 :=
    IsScalarTower.of_algebraMap_eq (fun x => (f1.commutes x).symm)
  letI : IsScalarTower R A2 B2 :=
    IsScalarTower.of_algebraMap_eq (fun x => (f2.commutes x).symm)
  let P1 := B1 ⊗[A1] D1
  let P2 := B2 ⊗[A2] D2
  let jB : B1 →+* P2 :=
    Algebra.TensorProduct.includeLeftRingHom.comp eB.toRingEquiv.toRingHom
  let jD : D1 →+* P2 :=
    Algebra.TensorProduct.includeRight.toRingHom.comp eD.toRingEquiv.toRingHom
  have ht : IsPushout
      (CommRingCat.ofHom f1.toRingHom) (CommRingCat.ofHom g1.toRingHom)
      (CommRingCat.ofHom jB) (CommRingCat.ofHom jD) := by
    apply (CommRingCat.isPushout_tensorProduct A2 B2 D2).of_iso'
      eA.toRingEquiv.toCommRingCatIso eB.toRingEquiv.toCommRingCatIso
      eD.toRingEquiv.toCommRingCatIso (Iso.refl (CommRingCat.of P2))
    · ext x
      exact DFunLike.congr_fun hf.symm x
    · ext x
      exact DFunLike.congr_fun hg.symm x
    · rfl
    · rfl
  have hs : IsPushout
      (CommRingCat.ofHom f1.toRingHom) (CommRingCat.ofHom g1.toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := A1) (A := B1) (B := D1)))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := A1) (A := B1) (B := D1)).toRingHom) :=
    CommRingCat.isPushout_tensorProduct A1 B1 D1
  let ie : CommRingCat.of P1 ≅ CommRingCat.of P2 :=
    hs.isoIsPushout (CommRingCat.of B1) (CommRingCat.of D1) ht
  constructor
  · intro b
    change ie.hom.hom (b ⊗ₜ[A1] (1 : D1)) = eB b ⊗ₜ[A2] (1 : D2)
    have hleft := hs.inl_isoIsPushout_hom
      (CommRingCat.of B1) (CommRingCat.of D1) ht
    have hx := congrArg
      (fun q : CommRingCat.of B1 ⟶ CommRingCat.of P2 => q.hom b) hleft
    change ie.hom.hom (b ⊗ₜ[A1] (1 : D1)) = jB b at hx
    exact hx
  · intro d
    change ie.hom.hom ((1 : B1) ⊗ₜ[A1] d) = (1 : B2) ⊗ₜ[A2] eD d
    have hright := hs.inr_isoIsPushout_hom
      (CommRingCat.of B1) (CommRingCat.of D1) ht
    have hx := congrArg
      (fun q : CommRingCat.of D1 ⟶ CommRingCat.of P2 => q.hom d) hright
    change ie.hom.hom ((1 : B1) ⊗ₜ[A1] d) = jD d at hx
    exact hx

/-! ## The Picard triple-model comparison -/

set_option synthInstance.maxHeartbeats 200000 in
-- Specializing the dependent combined-map family requires both quotient models.
set_option maxHeartbeats 1600000 in
-- Definitional reduction identifies the combined-map tags with the restriction leg.
/-- Component naturality for a descended left restriction map. -/
theorem pic0FiniteStageModelBaseChangeEquiv_restrictionLeft
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
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
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageModelBaseChangeEquiv C L n m relation e M
      (Sum.inr (U, V))).toAlgHom.comp
        (AlgebraicJacobian.scalarExtensionMapOfAlgHom
          (R := M.1) (K := k)
          (pic0FiniteStageRestrictionLeftModel C L n m relation M mapM U V)) =
      (pic0FiniteStageRestrictionLeft C U V).comp
        (pic0FiniteStageModelBaseChangeEquiv C L n m relation e M
          (Sum.inl U)).toAlgHom := by
  apply DFunLike.ext _ _
  intro x
  exact DFunLike.congr_fun
    (pic0FiniteStageModelBaseChangeEquiv_naturality
      C L n m relation e M mapM hmapM (Sum.inl (Sum.inl (U, V)))) x

end

end AlgebraicGeometry
