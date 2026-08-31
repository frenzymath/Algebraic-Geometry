/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Cohomology.GluedSheafDatumFibre
import AlgebraicJacobian.Picard.DivisorFamilyWindowBaseChange
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-!
# Finite-stage descent of rank-one H1 vanishing

Vanishing after extension to an arbitrary coefficient ring is witnessed by finitely many
relations when the source module is finite.  This file descends those relations to a finitely
generated intermediate subalgebra, then applies the result to the actual `H1` module of a pinned
cocycle datum.  The resulting datum is tied to the original one by the cocycle base-change tower
law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u v w

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

namespace RankOneFamilyCertificates

/-- If a finite module becomes zero after scalar extension, it already becomes zero over a
finitely generated intermediate subalgebra.

The proof descends the finitely many relations `1 ⊗ generator = 0` separately using the
direct-limit theorem for tensor products, then takes their finite supremum. -/
theorem exists_fg_subalgebra_tensor_subsingleton
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hS : Subsingleton (S ⊗[R] M)) :
    ∃ A : Subalgebra R S, A.FG ∧ Subsingleton (A ⊗[R] M) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let A0 : Subalgebra R S := ⊥
  let t : Fin n → A0 ⊗[R] M := fun i => (1 : A0) ⊗ₜ[R] s i
  have ht : ∀ i, A0.val.toLinearMap.rTensor M (t i) =
      A0.val.toLinearMap.rTensor M 0 := by
    intro i
    exact hS.elim _ _
  choose A hA0 hAfg hAzero using fun i =>
    TensorProduct.Algebra.eq_of_fg_of_subtype_eq
      (A := A0) Subalgebra.fg_bot (ht i)
  let B : Subalgebra R S := Finset.univ.sup A
  have hBfg : B.FG := by
    dsimp only [B]
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simpa using (Subalgebra.fg_bot : (⊥ : Subalgebra R S).FG)
    | @insert a q ha ih =>
        simpa [Finset.sup_insert] using (hAfg a).sup ih
  have hAB : ∀ i, A i ≤ B := by
    intro i
    exact Finset.le_sup (s := Finset.univ) (f := A) (Finset.mem_univ i)
  have hgen_zero : ∀ i, (1 : B) ⊗ₜ[R] s i = 0 := by
    intro i
    have hi := congrArg
      ((Subalgebra.inclusion (hAB i)).toLinearMap.rTensor M) (hAzero i)
    simpa [t, A0] using hi
  let f : M →ₗ[R] B ⊗[R] M := (TensorProduct.mk R B M) 1
  have hspan : Submodule.span R (Set.range s) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro m ⟨i, rfl⟩
    exact hgen_zero i
  have hf : f = 0 := by
    rw [← LinearMap.ker_eq_top]
    exact top_unique (hs ▸ hspan)
  have hone : ∀ m : M, (1 : B) ⊗ₜ[R] m = 0 := by
    intro m
    exact DFunLike.congr_fun hf m
  have hall : ∀ z : B ⊗[R] M, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul b m =>
        calc
          b ⊗ₜ[R] m = b • ((1 : B) ⊗ₜ[R] m) := by
            rw [TensorProduct.smul_tmul']
            simp
          _ = 0 := by rw [hone]; simp
    | add x y hx hy => simp [hx, hy]
  exact ⟨B, hBfg, ⟨fun x y => (hall x).trans (hall y).symm⟩⟩

end RankOneFamilyCertificates

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

namespace BasicOpenCocycleDatum

/-- Tensor vanishing of the datum pair's `H1` forces `H1` of the actual base-changed datum pair
to vanish.  This is the forward half of the Cech base-change dictionary over an arbitrary ring,
not only over residue fields. -/
theorem subsingleton_pairH1_baseChange_of_tensor
    (D : BasicOpenCocycleDatum C R pi)
    (A : Type u) [CommRing A] [Algebra k A] [Algebra R A]
    [IsScalarTower k R A]
    (h : Subsingleton ((datumPair D).H1 ⊗[R] A)) :
    Subsingleton (datumPair (D.baseChange A)).H1 := by
  have hcok := ((datumPair D).subsingleton_h1_rTensor_iff A).mp h
  have hbc : Function.Surjective ((datumPair D).diff.baseChange A) := by
    rw [← LinearMap.range_eq_top]
    exact Submodule.Quotient.subsingleton_iff.mp hcok
  have hsurj : Function.Surjective (datumPair (D.baseChange A)).diff :=
    RigidEngine.surjective_congr _ _ (D.datumDomBaseChange A)
      (D.termBaseChangeInf A) (fun x => D.datumDiffBaseChange A x) hbc
  have himg : (datumPair (D.baseChange A)).imageLattice = ⊤ := by
    rw [← (datumPair (D.baseChange A)).range_diff_eq, LinearMap.range_eq_top]
    exact hsurj
  rw [TwoLatticePair.H1, himg]
  infer_instance

/-- Refine a finitely generated coefficient stage until the actual datum pair has vanishing
`H1`.  The refined ring is finite type over the ground field, hence Noetherian, and its datum
base-changes to exactly the same datum over the ambient coefficient ring. -/
theorem exists_fg_pairH1_vanishing_stage
    {S : Type u} [CommRing S] [Algebra k S]
    (R0 : Subalgebra k S) (hR0 : R0.FG)
    (D : BasicOpenCocycleDatum C (R0 : Type u) pi)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hS : Subsingleton ((datumPair D).H1 ⊗[R0] S)) :
    ∃ A : Subalgebra (R0 : Type u) S,
      A.FG ∧ Algebra.FiniteType k A ∧ IsNoetherianRing A ∧
        Subsingleton (datumPair (D.baseChange A)).H1 ∧
        (D.baseChange A).baseChange S = D.baseChange S := by
  letI := D.moduleFinite_aeval'_pair_t₀ hpi
  letI := D.moduleFinite_aeval'_pair_t₁ hpi
  letI : Module.Finite (R0 : Type u) (datumPair D).H1 :=
    (datumPair D).moduleFinite_h1
  have hS' : Subsingleton (S ⊗[R0] (datumPair D).H1) :=
    (TensorProduct.comm (R0 : Type u) (datumPair D).H1 S).toEquiv.subsingleton_congr.mp hS
  obtain ⟨A, hAfg, hAtensor⟩ :=
    RankOneFamilyCertificates.exists_fg_subalgebra_tensor_subsingleton hS'
  have hAtensor' : Subsingleton ((datumPair D).H1 ⊗[R0] A) :=
    (TensorProduct.comm (R0 : Type u) (datumPair D).H1 A).toEquiv.subsingleton_congr.mpr
      hAtensor
  have hApair : Subsingleton (datumPair (D.baseChange A)).H1 :=
    D.subsingleton_pairH1_baseChange_of_tensor A hAtensor'
  have hR0ft : Algebra.FiniteType k R0 :=
    (Subalgebra.fg_iff_finiteType R0).mp hR0
  have hAft : Algebra.FiniteType (R0 : Type u) A :=
    (Subalgebra.fg_iff_finiteType A).mp hAfg
  have hAkt : Algebra.FiniteType k A := Algebra.FiniteType.trans hR0ft hAft
  letI : Algebra.FiniteType k A := hAkt
  have hAnoeth : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  exact ⟨A, hAfg, hAkt, hAnoeth, hApair,
    D.baseChange_baseChange C (R0 : Type u) A S⟩

end BasicOpenCocycleDatum

end AlgebraicGeometry
