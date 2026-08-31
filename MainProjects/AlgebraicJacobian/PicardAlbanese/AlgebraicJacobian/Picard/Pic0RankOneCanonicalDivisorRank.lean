/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Descending constant rank along an injective base change

A finite projective module whose scalar extension has rank one at every prime already has
rank one at every prime when the coefficient map is injective.  The image on spectra is dense,
while the stalk-rank function is locally constant.
-/

set_option autoImplicit false

universe u

open TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Rank one descends from a scalar extension along an injective ring map. -/
theorem rankAtStalk_eq_one_of_injective_baseChange
    {R S M N : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module S N]
    (hinj : Function.Injective (algebraMap R S))
    (e : S ⊗[R] M ≃ₗ[S] N)
    (hrank : ∀ q : PrimeSpectrum S, Module.rankAtStalk N q = 1) :
    ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1 := by
  letI : Module.FinitePresentation R M :=
    Module.finitePresentation_of_projective _ _
  have hlc : IsLocallyConstant (Module.rankAtStalk (R := R) M) :=
    Module.isLocallyConstant_rankAtStalk
  have hdense : DenseRange (PrimeSpectrum.comap (algebraMap R S)) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have himg : ∀ q : PrimeSpectrum S,
      Module.rankAtStalk M (q.comap (algebraMap R S)) = 1 := by
    intro q
    rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv e]
    exact hrank q
  intro p
  by_contra hp
  obtain ⟨q, hq⟩ := hdense.exists_mem_open (hlc ({1}ᶜ : Set ℕ)) ⟨p, hp⟩
  exact hq (himg q)

end AlgebraicGeometry
