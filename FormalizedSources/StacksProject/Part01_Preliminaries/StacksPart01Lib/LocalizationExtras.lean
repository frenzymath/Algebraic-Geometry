/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Etale.Basic

/-!
# The zero localization criterion

The localization of a ring is the zero ring exactly when zero belongs to the
chosen multiplicative system (Stacks, Tag 00CQ).
-/

namespace StacksPart01

/-- A localization is subsingleton exactly when its denominator submonoid
contains zero (Stacks, Tag 00CQ). -/
theorem localization_subsingleton_iff
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S] :
    Subsingleton S ↔ 0 ∈ M := by
  exact IsLocalization.subsingleton_iff

/-- The canonical map into a localization is formally etale (Stacks, Tag 04EG). -/
theorem localization_formallyEtale
    {R : Type*} [CommRing R] (M : Submonoid R) :
    Algebra.FormallyEtale R (Localization M) := by
  exact Algebra.FormallyEtale.of_isLocalization M

/-! ### Localization models and fraction criteria

The equivalence below packages the universal-property comparison of two
localization models (Stacks, Tags 00CP and 02C6).
-/

/-- Two rings satisfying the same localization predicate are canonically
isomorphic as algebras over the base ring. -/
noncomputable def localizationAlgEquiv
    {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (M : Submonoid R) [Algebra R S] [Algebra R T]
    [IsLocalization M S] [IsLocalization M T] :
    S ≃ₐ[R] T :=
  IsLocalization.algEquiv M S T

/-- The localization equivalence sends a fraction to the fraction with the
same numerator and denominator in the target model. -/
@[simp]
theorem localizationAlgEquiv_mk'
    {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (M : Submonoid R) [Algebra R S] [Algebra R T]
    [IsLocalization M S] [IsLocalization M T]
    (x : R) (y : M) :
    localizationAlgEquiv M (IsLocalization.mk' S x y) =
      IsLocalization.mk' T x y := by
  exact IsLocalization.algEquiv_mk' x y

/-- An element maps to zero in the canonical localization exactly when some
denominator kills it (Stacks, Tag 00CQ). -/
theorem localization_map_eq_zero_iff
    {R : Type*} [CommSemiring R] (M : Submonoid R) (r : R) :
    algebraMap R (Localization M) r = 0 ↔
      ∃ m : M, (m : R) * r = 0 := by
  exact IsLocalization.map_eq_zero_iff M (Localization M) r

/-- In the localization away from `f`, an element vanishes exactly when a
power of `f` annihilates it (Stacks, Tag 00CQ). -/
theorem localization_away_map_eq_zero_iff
    {R : Type*} [CommSemiring R] (f r : R) :
    algebraMap R (Localization.Away f) r = 0 ↔
      ∃ n : ℕ, f ^ n * r = 0 := by
  rw [localization_map_eq_zero_iff (Submonoid.powers f) r]
  constructor
  · rintro ⟨m, hm⟩
    rcases (Submonoid.mem_powers_iff (m : R) f).mp m.property with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    exact hn.symm ▸ hm
  · rintro ⟨n, hn⟩
    have hmem : f ^ n ∈ Submonoid.powers f :=
      (Submonoid.mem_powers_iff (f ^ n) f).mpr ⟨n, rfl⟩
    exact ⟨⟨f ^ n, hmem⟩, hn⟩

/-- A canonical localization fraction is zero exactly when some denominator
kills its numerator (Stacks, Tag 00CQ). -/
theorem localization_mk'_eq_zero_iff
    {R : Type*} [CommSemiring R] (M : Submonoid R) (x : R) (s : M) :
    IsLocalization.mk' (Localization M) x s = 0 ↔
      ∃ m : M, (m : R) * x = 0 := by
  exact IsLocalization.mk'_eq_zero_iff x s

/-! ### Localized ideals and submodules

These identities express extension of ideals/submodules along a localization,
including compatibility with finite intersections and generated submodules.
-/

theorem ideal_localized_eq_map
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R) :
    Submodule.localized' S M (Algebra.linearMap R S) I =
      I.map (algebraMap R S) := by
  exact Ideal.localized'_eq_map S M I

theorem submodule_localized_inf
    {R S M N : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Algebra R S] [Module S N] [IsScalarTower R S N]
    (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N)
    [IsLocalizedModule p f] (N₁ N₂ : Submodule R M) :
    Submodule.localized' S p f (N₁ ⊓ N₂) =
      Submodule.localized' S p f N₁ ⊓ Submodule.localized' S p f N₂ := by
  exact Submodule.localized'_inf S p f N₁ N₂

theorem submodule_localized_iSup
    {R S M N ι : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Algebra R S] [Module S N] [IsScalarTower R S N]
    (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N)
    [IsLocalizedModule p f] (N₁ : ι → Submodule R M) :
    Submodule.localized' S p f (⨆ i, N₁ i) =
      ⨆ i, Submodule.localized' S p f (N₁ i) := by
  exact Submodule.localized'_iSup S p f N₁

theorem submodule_localized_span
    {R S M N : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Algebra R S] [Module S N] [IsScalarTower R S N]
    (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N)
    [IsLocalizedModule p f] (s : Set M) :
    Submodule.localized' S p f (Submodule.span R s) =
      Submodule.span S (f '' s) := by
  exact Submodule.localized'_span S p f s

end StacksPart01
