/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.ModuleDescent
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-!
# Faithfully flat descent of invertible modules

Let `A → B` be a faithfully flat map of commutative rings.  This file shows that the
module-theoretic properties *finite*, *finitely presented*, *flat*, *projective* and
*invertible* all descend along `A → B`: if `B ⊗[A] P` has the property over `B`, then `P`
has it over `A`.  Combined with the effectivity theorem of
`AlgebraicJacobian.Descent.ModuleDescent` this yields: a `B`-module `M` with a descent
datum descends to an `A`-module `M₀` (unique up to canonical isomorphism), and if `M` is
invertible then so is `M₀`.

The descent of invertibility is reduced, via the definition
`Module.Invertible R M ↔ Function.Bijective (contractLeft R M)`, to two ingredients:

* the *dual base-change comparison* `B ⊗[A] Dual A P → Dual B (B ⊗[A] P)` is an
  isomorphism for `P` finite projective (`Module.bijective_dualBaseChange`, proved by a
  retract argument from the finite free case, which is `IsBaseChange.linearMapLeftRight`);
* bijectivity of `A`-linear maps descends along faithfully flat maps
  (`Module.FaithfullyFlat.lTensor_bijective_iff_bijective`).

Finiteness and projectivity of `P` are themselves obtained by descent: mathlib provides
finiteness (`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`) and flatness
(`Module.Flat.of_flat_tensorProduct`); we add finite presentation
(`Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`), and
projectivity follows from flat + finitely presented.

## Main declarations

* `Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`:
  finite presentation descends along faithfully flat ring maps.
* `Module.Projective.of_projective_tensorProduct_of_faithfullyFlat`: finite projectivity
  descends along faithfully flat ring maps.
* `Module.dualBaseChange A B P : B ⊗[A] Dual A P →ₗ[B] Dual B (B ⊗[A] P)`: the dual
  base-change comparison map.
* `Module.bijective_dualBaseChange`: the comparison map is bijective for finite projective
  `P` (over an arbitrary `A`-algebra `B`).
* `Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat`: invertibility
  descends along faithfully flat ring maps.
* `Module.DescentDatum.finite_descended`, `…flat_descended`,
  `…finitePresentation_descended`, `…projective_descended`,
  `…invertible_descended`: for a descent datum on a `B`-module `M` relative to a
  faithfully flat `A → B`, the descended module inherits each property from `M`;
  in particular **an invertible module with a descent datum descends to an invertible
  module**.

All modules live in a single universe `u`.
-/

universe u

open TensorProduct

namespace Module

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-! ### Descent of finite presentation -/

/-- Finite presentation of modules descends along faithfully flat ring maps. -/
theorem FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    (P : Type u) [AddCommGroup P] [Module A P] [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B (B ⊗[A] P)] :
    Module.FinitePresentation A P := by
  have hfin : Module.Finite A P :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A P
  have hpB : Function.Surjective (p.baseChange B) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective B hp
  have hker : (LinearMap.ker (p.baseChange B)).FG :=
    Module.FinitePresentation.fg_ker (p.baseChange B) hpB
  have hexact := Module.Flat.lTensor_exact B p.exact_subtype_ker_map
  have hinj : Function.Injective ((LinearMap.ker p).subtype.baseChange B) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (LinearMap.ker p).injective_subtype
  have hrange : LinearMap.range ((LinearMap.ker p).subtype.baseChange B)
      = LinearMap.ker (p.baseChange B) := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨y, rfl⟩
      simp only [LinearMap.baseChange_eq_ltensor]
      exact hexact.apply_apply_eq_zero y
    · intro hx
      rw [LinearMap.baseChange_eq_ltensor] at hx
      obtain ⟨y, hy⟩ := (hexact x).mp hx
      exact ⟨y, by rw [LinearMap.baseChange_eq_ltensor]; exact hy⟩
  have e : (B ⊗[A] LinearMap.ker p) ≃ₗ[B] LinearMap.ker (p.baseChange B) :=
    (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have : Module.Finite B (LinearMap.ker (p.baseChange B)) := Module.Finite.iff_fg.mpr hker
  have : Module.Finite B (B ⊗[A] LinearMap.ker p) := Module.Finite.equiv e.symm
  have : Module.Finite A (LinearMap.ker p) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  exact Module.finitePresentation_of_surjective p hp (Module.Finite.iff_fg.mp this)

/-- Finite projectivity of modules descends along faithfully flat ring maps. -/
theorem Projective.of_projective_tensorProduct_of_faithfullyFlat
    (P : Type u) [AddCommGroup P] [Module A P] [Module.FaithfullyFlat A B]
    [Module.Finite B (B ⊗[A] P)] [Projective B (B ⊗[A] P)] :
    Projective A P := by
  have : Module.FinitePresentation B (B ⊗[A] P) :=
    Module.finitePresentation_of_projective B (B ⊗[A] P)
  have : Module.FinitePresentation A P :=
    FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat A B P
  have : Module.Flat A P := Module.Flat.of_flat_tensorProduct A P B
  exact Module.Flat.projective_of_finitePresentation (R := A) (M := P)

/-! ### The dual base-change comparison map -/

section DualBaseChange

variable {A B} in
/-- Two `B`-functionals on `B ⊗[A] X` that agree on the tensors `1 ⊗ₜ x` are equal. -/
private theorem dual_ext {X : Type u} [AddCommGroup X] [Module A X]
    {F G : Dual B (B ⊗[A] X)} (h : ∀ x : X, F (1 ⊗ₜ x) = G (1 ⊗ₜ x)) : F = G := by
  apply LinearMap.restrictScalars_injective A
  apply TensorProduct.ext'
  intro b x
  have hb : b ⊗ₜ[A] x = b • (1 ⊗ₜ[A] x : B ⊗[A] X) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [LinearMap.restrictScalars_apply, hb, map_smul, h]

variable (P : Type u) [AddCommGroup P] [Module A P]

/-- The canonical `B`-linear comparison map from the base change of the dual to the dual
of the base change, `b ⊗ₜ f ↦ b • (f.baseChange B)`.  It is bijective for finite
projective `P` (`Module.bijective_dualBaseChange`). -/
noncomputable def dualBaseChange : B ⊗[A] Dual A P →ₗ[B] Dual B (B ⊗[A] P) :=
  LinearMap.liftBaseChange B (Module.Dual.baseChange B)

@[simp] theorem dualBaseChange_tmul (b : B) (f : Dual A P) :
    dualBaseChange A B P (b ⊗ₜ f) = b • Module.Dual.baseChange B f := rfl

/-- Naturality of the dual base-change comparison map. -/
theorem dualBaseChange_naturality {P Q : Type u} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (g : P →ₗ[A] Q) :
    dualBaseChange A B P ∘ₗ g.dualMap.baseChange B =
      (g.baseChange B).dualMap ∘ₗ dualBaseChange A B Q := by
  apply LinearMap.restrictScalars_injective A
  apply TensorProduct.ext'
  intro b f
  simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply]
  refine dual_ext fun x => ?_
  simp [Module.Dual.baseChange_apply_tmul]

variable {A B} in
private theorem bijective_dualBaseChange_free (n : ℕ) :
    Function.Bijective (dualBaseChange A B (Fin n → A)) := by
  have j : IsBaseChange B (TensorProduct.mk A B (Fin n → A) 1) :=
    TensorProduct.isBaseChange A (Fin n → A) B
  have k : IsBaseChange B (Algebra.linearMap A B) := IsBaseChange.linearMap A B
  have hlr : IsBaseChange B (IsBaseChange.linearMapLeftRightHom j (Algebra.linearMap A B)) :=
    IsBaseChange.linearMapLeftRight j k
  have heq : Module.Dual.baseChange (R := A) B (V := Fin n → A)
      = IsBaseChange.linearMapLeftRightHom j (Algebra.linearMap A B) := by
    refine LinearMap.ext fun f => dual_ext fun x => ?_
    have h1 := IsBaseChange.linearMapLeftRightHom_comp_apply j (Algebra.linearMap A B) f x
    simpa [Algebra.algebraMap_eq_smul_one] using h1.symm
  have hlift : dualBaseChange A B (Fin n → A) = hlr.equiv.toLinearMap := by
    apply LinearMap.restrictScalars_injective A
    apply TensorProduct.ext'
    intro b f
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, dualBaseChange_tmul,
      IsBaseChange.equiv_tmul, heq]
  rw [hlift]
  exact hlr.equiv.bijective

/-- **The dual commutes with base change for finite projective modules**: the comparison
map `B ⊗[A] Dual A P → Dual B (B ⊗[A] P)` is bijective when `P` is finite projective. -/
theorem bijective_dualBaseChange [Module.Finite A P] [Projective A P] :
    Function.Bijective (dualBaseChange A B P) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' A P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hfree := bijective_dualBaseChange_free (A := A) (B := B) n
  have hnat_r := dualBaseChange_naturality A B r
  have hnat_s := dualBaseChange_naturality A B s
  -- the two retraction identities
  have hcomp : s.dualMap ∘ₗ r.dualMap = LinearMap.id := by
    ext f x
    simpa using congrArg f (LinearMap.congr_fun hs x)
  have hu : ∀ x : B ⊗[A] Dual A P,
      s.dualMap.baseChange B (r.dualMap.baseChange B x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_id,
      LinearMap.id_apply]
  have hcompB : (r.baseChange B) ∘ₗ (s.baseChange B) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hs, LinearMap.baseChange_id]
  have hv : ∀ y : Dual B (B ⊗[A] P),
      (s.baseChange B).dualMap ((r.baseChange B).dualMap y) = y := by
    intro y
    rw [← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, hcompB, LinearMap.dualMap_id,
      LinearMap.id_apply]
  constructor
  · intro x y hxy
    have h1 : dualBaseChange A B (Fin n → A) (r.dualMap.baseChange B x)
        = dualBaseChange A B (Fin n → A) (r.dualMap.baseChange B y) := by
      rw [← LinearMap.comp_apply, hnat_r, ← LinearMap.comp_apply, hnat_r]
      simp only [LinearMap.comp_apply, hxy]
    have h2 := hfree.injective h1
    rw [← hu x, ← hu y, h2]
  · intro y
    obtain ⟨z, hz⟩ := hfree.surjective ((r.baseChange B).dualMap y)
    refine ⟨s.dualMap.baseChange B z, ?_⟩
    have := LinearMap.congr_fun hnat_s z
    simp only [LinearMap.comp_apply] at this
    rw [this, hz, hv]

end DualBaseChange

/-! ### Descent of invertibility -/

/-- **Invertibility of modules descends along faithfully flat ring maps**: if `A → B` is
faithfully flat and `B ⊗[A] P` is an invertible `B`-module, then `P` is an invertible
`A`-module. -/
theorem Invertible.of_invertible_tensorProduct_of_faithfullyFlat
    (P : Type u) [AddCommGroup P] [Module A P] [Module.FaithfullyFlat A B]
    [Module.Invertible B (B ⊗[A] P)] :
    Module.Invertible A P := by
  have hfin : Module.Finite A P :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  have hproj : Projective A P :=
    Projective.of_projective_tensorProduct_of_faithfullyFlat A B P
  -- the contraction square: base change of `contractLeft A P` factors through
  -- `contractLeft B (B ⊗[A] P)` via the dual base-change comparison map
  have hsquare : (contractLeft A P).baseChange B =
      ((AlgebraTensorModule.rid A B B).symm.toLinearMap ∘ₗ contractLeft B (B ⊗[A] P) ∘ₗ
          (dualBaseChange A B P).rTensor (B ⊗[A] P)) ∘ₗ
        (AlgebraTensorModule.distribBaseChange A B (Dual A P) P).toLinearMap := by
    apply LinearMap.restrictScalars_injective A
    ext f p
    simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self, curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.baseChange_tmul, contractLeft_apply,
      LinearMap.restrictScalars_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, AlgebraTensorModule.distribBaseChange_tmul, LinearMap.rTensor_tmul,
      dualBaseChange_tmul, LinearMap.smul_apply, Dual.baseChange_apply_tmul, smul_eq_mul,
      Algebra.mul_smul_comm, mul_one, AlgebraTensorModule.rid_symm_apply]
    rw [← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, smul_eq_mul, mul_one]
  have hbij : Function.Bijective ((contractLeft A P).baseChange B) := by
    rw [hsquare]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
    exact (((AlgebraTensorModule.rid A B B).symm.bijective.comp
        (Module.Invertible.bijective (R := B) (M := B ⊗[A] P))).comp
        ((Module.Invertible.rTensor_bijective_iff (M := B ⊗[A] P)).mpr
          (bijective_dualBaseChange A B P))).comp
      (AlgebraTensorModule.distribBaseChange A B (Dual A P) P).bijective
  rw [LinearMap.baseChange_eq_ltensor] at hbij
  exact ⟨(Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B _).mp hbij⟩

/-! ### Properties of the descended module of a descent datum -/

namespace DescentDatum

variable {A B} {M : Type u} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable (D : DescentDatum A B M) [Module.FaithfullyFlat A B]

theorem finite_descended [Module.Finite B M] : Module.Finite A D.descended := by
  have : Module.Finite B (B ⊗[A] D.descended) := Module.Finite.equiv D.descentEquiv.symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

theorem flat_descended [Module.Flat B M] : Module.Flat A D.descended := by
  have : Module.Flat B (B ⊗[A] D.descended) := Module.Flat.of_linearEquiv D.descentEquiv
  exact Module.Flat.of_flat_tensorProduct A D.descended B

theorem finitePresentation_descended [Module.FinitePresentation B M] :
    Module.FinitePresentation A D.descended := by
  have : Module.FinitePresentation B (B ⊗[A] D.descended) :=
    Module.finitePresentation_of_surjective D.descentEquiv.symm.toLinearMap
      D.descentEquiv.symm.surjective
      (by simpa using Submodule.fg_bot)
  exact FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat A B
    D.descended

theorem projective_descended [Module.Finite B M] [Projective B M] :
    Projective A D.descended := by
  have : Module.Finite B (B ⊗[A] D.descended) := Module.Finite.equiv D.descentEquiv.symm
  have : Projective B (B ⊗[A] D.descended) := Projective.of_equiv D.descentEquiv.symm
  exact Projective.of_projective_tensorProduct_of_faithfullyFlat A B D.descended

/-- **Faithfully flat descent of invertible modules**: if `M` is an invertible `B`-module
with a descent datum relative to a faithfully flat `A → B`, then the descended `A`-module
is invertible.  Together with `Module.DescentDatum.descentEquiv` (which exhibits
`B ⊗[A] M₀ ≃ M`) and `Module.DescentDatum.equivDescended` (uniqueness), this is the
descent theorem for the Picard group. -/
theorem invertible_descended [Module.Invertible B M] : Module.Invertible A D.descended := by
  have : Module.Invertible B (B ⊗[A] D.descended) := .congr D.descentEquiv.symm
  exact Invertible.of_invertible_tensorProduct_of_faithfullyFlat A B D.descended

end DescentDatum

end Module
