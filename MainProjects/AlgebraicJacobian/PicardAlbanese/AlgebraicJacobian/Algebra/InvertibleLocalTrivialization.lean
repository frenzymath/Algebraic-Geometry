/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Invertible modules are Zariski-locally trivial

Let `A` be a commutative ring and `N` an invertible `A`-module.  This file proves the
commutative-algebra form of the statement "an invertible module is Zariski-locally free":

* `Module.Free.tensor_of_localizedModule_away`: if the standard localized module
  `LocalizedModule.Away r N` is free over `Localization.Away r`, then `S ⊗[A] N` is free
  over `S` for **any** localization model `S` of `A` away from `r`.
* `Module.Invertible.exists_notMem_tensor_free`: for every prime `p` of `A` there is an
  `f ∉ p` such that `N` trivializes away from `f`.  This is the local-to-global heart:
  invertible modules are finitely presented, their localization at `p` is free over the
  local ring `A_p` (finite flat over local is free), and freeness spreads out from the
  prime to a principal open neighbourhood
  (`Module.FinitePresentation.exists_free_localizedModule_powers`).
* `Module.Invertible.span_tensor_free_eq_top`: the trivializing elements `f` span the
  unit ideal, i.e. the principal opens `D(f)` on which `N` trivializes cover `Spec A`.

This is the "invertible modules are Zariski-locally trivial" brick feeding the
surjectivity half of the Čech–Picard dictionary in
`AlgebraicJacobian.Picard.CechPicSurjective`: it produces the finite localization cover
on which an invertible module admits trivializations, whose transition units
(`AlgebraicJacobian.Algebra.BaseChangeTrivialization`) form the Čech 1-cocycle
presenting its class.

**Extraction candidate.**  This file is mathlib-PR-shaped: it discharges the TODO in
`Mathlib.RingTheory.PicardGroup` that invertible modules are Zariski-locally free, using
only `Mathlib.RingTheory.Localization.Free` and the Picard-group instances.

Everything is pinned to a single universe `u`, matching the descent development in
`AlgebraicJacobian.Descent.ModuleDescent`.
-/

universe u

open TensorProduct

namespace Module

variable {A : Type u} [CommRing A] (N : Type u) [AddCommGroup N] [Module A N]

/-- Transport of freeness from the standard localized module `LocalizedModule.Away r N`
to the base change `S ⊗[A] N` for ANY localization model `S` of `A` away from `r`. -/
theorem Free.tensor_of_localizedModule_away (r : A)
    [Module.Free (Localization.Away r) (LocalizedModule.Away r N)]
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away r S] :
    Module.Free S (S ⊗[A] N) := by
  letI : Algebra (Localization.Away r) S :=
    (IsLocalization.algEquiv (Submonoid.powers r)
      (Localization.Away r) S).toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower A (Localization.Away r) S :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      ((IsLocalization.algEquiv (Submonoid.powers r)
        (Localization.Away r) S).commutes a).symm
  haveI : Module.Free (Localization.Away r) (Localization.Away r ⊗[A] N) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) N)
  exact Module.Free.of_equiv
    (AlgebraTensorModule.cancelBaseChange A (Localization.Away r) S S N)

/-- An invertible module becomes free away from some element outside any given prime. -/
theorem Invertible.exists_notMem_tensor_free [Module.Invertible A N]
    (p : Ideal A) [p.IsPrime] :
    ∃ f ∉ p, ∀ (S : Type u) [CommRing S] [Algebra A S], IsLocalization.Away f S →
      Module.Free S (S ⊗[A] N) := by
  haveI : Module.FinitePresentation A N := Module.finitePresentation_of_projective A N
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl N) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl N) (Localization.AtPrime p)
  exact ⟨r, hr, fun S _ _ hS ↦ by
    haveI := hS
    haveI := hfree
    exact Free.tensor_of_localizedModule_away N r S⟩

/-- The trivializing sections of an invertible module span the unit ideal. -/
theorem Invertible.span_tensor_free_eq_top [Module.Invertible A N] :
    Ideal.span {f : A | ∀ (S : Type u) [CommRing S] [Algebra A S], IsLocalization.Away f S →
      Module.Free S (S ⊗[A] N)} = ⊤ := by
  by_contra h
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ h
  haveI := hmax.isPrime
  obtain ⟨f, hf, hfree⟩ := Invertible.exists_notMem_tensor_free N m
  exact hf (hle (Ideal.subset_span hfree))

end Module
