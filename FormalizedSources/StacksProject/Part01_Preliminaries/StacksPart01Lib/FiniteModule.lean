/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Finite and cyclic modules

The finiteness lemmas in this file package the scalar-tower arguments used in
the Stacks Project's discussion of finite modules (Tags 0560, 00GJ, and 00KZ).
-/

namespace StacksPart01

/-- If an `R`-module is finite, then it is finite over any larger scalar ring
`S` acting through a scalar tower (Stacks, Tag 0560). -/
theorem finite_over_subring
    {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R M] [Module S M] [SMul R S] [IsScalarTower R S M]
    [Module.Finite R M] :
    Module.Finite S M := by
  exact Module.Finite.of_restrictScalars_finite R S M

/-- For a finite scalar extension, finiteness of a module over the two scalar
rings is equivalent (Stacks, Tag 00GJ). -/
theorem finite_module_iff_of_finite_extension
    {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R S] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite R S] :
    Module.Finite R M ↔ Module.Finite S M := by
  constructor
  · intro h
    letI : Module.Finite R M := h
    exact Module.Finite.of_restrictScalars_finite R S M
  · intro h
    letI : Module.Finite S M := h
    exact Module.Finite.trans S M

/-- A tensor product of two finite modules is finite (Stacks, Tag 05G5). -/
theorem finite_module_tensorProduct
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N] :
    Module.Finite R (TensorProduct R M N) := by
  infer_instance

/-- Base change of a finite module is finite over the base-change algebra
(Stacks, Tag 05G5). -/
theorem finite_module_baseChange
    {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    Module.Finite A (TensorProduct R A M) := by
  exact Module.Finite.base_change R A M

/-- A finite product of finite modules is finite. -/
theorem finite_module_pi
    {R ι : Type*} [Semiring R] [Finite ι]
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)]
    [(i : ι) → Module R (M i)] [(i : ι) → Module.Finite R (M i)] :
    Module.Finite R ((i : ι) → M i) := by
  exact Module.Finite.pi

/-- Quotients of finite modules by submodules are finite. -/
theorem finite_module_quotient
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M) :
    Module.Finite R (M ⧸ N) := by
  exact Module.Finite.quotient R N

/-- For a finite algebra, module finite presentation is equivalent to algebra
finite presentation. -/
theorem finite_presentation_iff_algebra_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] :
    Module.FinitePresentation R S ↔ Algebra.FinitePresentation R S := by
  exact Module.FinitePresentation.iff_finitePresentation_of_finite R S

/-- A cyclic module is linearly equivalent to the quotient of its scalar ring
by an ideal.  The ideal is the kernel of the map sending a scalar to its
multiple of the chosen generator. -/
theorem exists_ideal_quotient_equiv_of_cyclic
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (h : ∃ m : M, Function.Surjective
      (LinearMap.toSpanSingleton R M m)) :
    ∃ I : Ideal R, Nonempty ((R ⧸ I) ≃ₗ[R] M) := by
  obtain ⟨m, hm⟩ := h
  let f := LinearMap.toSpanSingleton R M m
  exact ⟨LinearMap.ker f, ⟨f.quotKerEquivOfSurjective hm⟩⟩

/-- The quotient obtained by adjoining one generator to a submodule is cyclic.

This is the one-step construction used in the finite-module filtration lemma
(Stacks, Tag 00KZ). -/
theorem exists_ideal_quotient_equiv_sup_span
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (x : M) :
    ∃ I : Ideal R, Nonempty (((↥((R ∙ x : Submodule R M) ⊔ N)) ⧸
      Submodule.comap ((R ∙ x : Submodule R M) ⊔ N).subtype N) ≃ₗ[R] (R ⧸ I)) := by
  let P : Submodule R M := (R ∙ x : Submodule R M) ⊔ N
  let p : Submodule R M := R ∙ x
  let f₀ : R →ₗ[R] p :=
    LinearMap.toSpanSingleton R p ⟨x, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩
  let D : Submodule R p :=
    Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype N
  let q : p →ₗ[R] p ⧸ D := Submodule.mkQ D
  let f : R →ₗ[R] p ⧸ D := q.comp f₀
  have hf₀ : Function.Surjective f₀ := by
    intro y
    rcases (Submodule.mem_span_singleton.mp y.property) with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    simpa [f₀, LinearMap.toSpanSingleton_apply] using ha
  have hq : Function.Surjective q := Submodule.mkQ_surjective D
  have hf : Function.Surjective f := hq.comp hf₀
  let e : (p ⧸ D) ≃ₗ[R]
      (↥P ⧸ Submodule.comap P.subtype N) :=
    by simpa [P, D] using (LinearMap.quotientInfEquivSupQuotient p N)
  let e₀ : (R ⧸ LinearMap.ker f) ≃ₗ[R]
      (↥P ⧸ Submodule.comap P.subtype N) :=
    (f.quotKerEquivOfSurjective hf).trans e
  exact ⟨LinearMap.ker f, ⟨e₀.symm⟩⟩

/- A finite cyclic filtration relation records finite stages and the ideal
quotient appearing at each successive step. -/
inductive CyclicFiltration {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] : Submodule R M → Submodule R M → Prop where
  | refl {N : Submodule R M} (hN : N.FG) :
      CyclicFiltration N N
  | step {N P Q : Submodule R M} (h : CyclicFiltration N P)
      (hQ : Q.FG) (hPQ : P ≤ Q) {I : Ideal R}
      (e : ((↥Q) ⧸ Submodule.comap Q.subtype P) ≃ₗ[R] (R ⧸ I)) :
      CyclicFiltration N Q

/-- A finite module admits a finite filtration by finitely generated
submodules whose successive quotients are cyclic (Stacks, Tag 00KZ). -/
theorem finite_module_cyclic_filtration
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    CyclicFiltration (⊥ : Submodule R M) (⊤ : Submodule R M) := by
  let motive : ∀ N : Submodule R M, N.FG → Prop :=
    fun N _ => CyclicFiltration (⊥ : Submodule R M) N
  apply Submodule.fg_sup_span_induction (motive := motive)
  · exact CyclicFiltration.refl Submodule.fg_bot
  · intro N x hN ih
    have hstep : CyclicFiltration (⊥ : Submodule R M) ((R ∙ x) ⊔ N) := by
      obtain ⟨I, hI⟩ := exists_ideal_quotient_equiv_sup_span N x
      rcases hI with ⟨e⟩
      refine CyclicFiltration.step ih ?_ le_sup_right e
      exact (Submodule.fg_span_singleton x).sup hN
    simpa [sup_comm] using hstep
  · exact Module.Finite.fg_top

end StacksPart01
