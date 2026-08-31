/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import AlgebraicJacobian.Cohomology.RigidEngine2Nakayama

/-!
# Fibrewise surjectivity for finite modules

This is the small Nakayama consumer used by the universal-window persistence
arguments.  It is deliberately independent of schemes: a map between finite
modules is surjective once its right tensor with every residue field is
surjective.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace AlgebraicJacobian.RigidEngine

variable {R : Type u} [CommRing R]

/-- A finite-module map which is surjective on every residue-field fibre is
surjective.  The proof applies the finite-module vanishing engine to the
cokernel, using right exactness of `⊗`. -/
theorem surjective_of_forall_rTensor_residueField_surjective
    {U X : Type u} [AddCommGroup U] [Module R U]
    [AddCommGroup X] [Module R X] [Module.Finite R U] [Module.Finite R X]
    (φ : U →ₗ[R] X)
    (hfib : ∀ p : PrimeSpectrum R,
      Function.Surjective (φ.rTensor p.asIdeal.ResidueField)) :
    Function.Surjective φ := by
  let Q := X ⧸ LinearMap.range φ
  let q : X →ₗ[R] Q := (LinearMap.range φ).mkQ
  have hqsurj (p : PrimeSpectrum R) :
      Function.Surjective (q.rTensor p.asIdeal.ResidueField) :=
    LinearMap.rTensor_surjective _ (Submodule.mkQ_surjective _)
  have hcomp : q.comp φ = 0 := by
    ext x
    change (Submodule.Quotient.mk (φ x) : Q) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.mpr ⟨x, rfl⟩
  have hQfib : ∀ p : PrimeSpectrum R,
      Subsingleton (Q ⊗[R] p.asIdeal.ResidueField) := by
    intro p
    have hqzero : q.rTensor p.asIdeal.ResidueField = 0 := by
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := hfib p y
      rw [← LinearMap.rTensor_comp_apply, hcomp, LinearMap.rTensor_zero,
        LinearMap.zero_apply]
      simp
    refine ⟨fun y z => ?_⟩
    obtain ⟨y', rfl⟩ := hqsurj p y
    obtain ⟨z', rfl⟩ := hqsurj p z
    simp [hqzero]
  haveI : Subsingleton Q :=
    subsingleton_of_forall_subsingleton_residueField_tensor hQfib
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_iff'.2 fun x => ?_
  exact (Submodule.Quotient.mk_eq_zero _).mp (Subsingleton.elim _ _)

/-- The range form of
`surjective_of_forall_rTensor_residueField_surjective`. -/
theorem range_eq_top_of_forall_rTensor_residueField_surjective
    {U X : Type u} [AddCommGroup U] [Module R U]
    [AddCommGroup X] [Module R X] [Module.Finite R U] [Module.Finite R X]
    (φ : U →ₗ[R] X)
    (hfib : ∀ p : PrimeSpectrum R,
      Function.Surjective (φ.rTensor p.asIdeal.ResidueField)) :
    LinearMap.range φ = ⊤ :=
  LinearMap.range_eq_top.mpr
    (surjective_of_forall_rTensor_residueField_surjective φ hfib)

/-- A finite submodule whose inclusion is fibrewise surjective is the whole
ambient module. -/
theorem submodule_eq_top_of_forall_rTensor_residueField_surjective
    {X : Type u} [AddCommGroup X] [Module R X] [Module.Finite R X]
    (P : Submodule R X) [Module.Finite R ↥P]
    (hfib : ∀ p : PrimeSpectrum R,
      Function.Surjective (P.subtype.rTensor p.asIdeal.ResidueField)) :
    P = ⊤ := by
  rw [← P.range_subtype]
  exact range_eq_top_of_forall_rTensor_residueField_surjective P.subtype hfib

end AlgebraicJacobian.RigidEngine
