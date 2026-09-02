/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization of modules

The Stacks Project's localization chapter uses the localization of modules as
an exact functor.  This module exposes the corresponding Mathlib API under the
project namespace, together with the canonical-map identities used in the
universal-property arguments.
-/

namespace StacksPart01

open Function IsLocalizedModule
open scoped TensorProduct

variable {R : Type*} [CommSemiring R]

/-!
The canonical tensor description of a localized module is the formulation used
in Stacks, Tag 00DK.  Mathlib provides the inverse orientation (from the
localized module to the tensor product); the wrapper below presents the map in
the direction used by the source.
-/
noncomputable def tensorLocalizationEquiv
    (S : Submonoid R) (M : Type*) [AddCommMonoid M] [Module R M] :
    Localization S ⊗[R] M ≃ₗ[Localization S] LocalizedModule S M :=
  (LocalizedModule.equivTensorProduct S M).symm

/- The map sends a fraction tensor to the corresponding localized numerator. -/
@[simp]
theorem tensorLocalizationEquiv_tmul
    (S : Submonoid R) (M : Type*) [AddCommMonoid M] [Module R M]
    (r : R) (s : S) (m : M) :
    tensorLocalizationEquiv S M (Localization.mk r s ⊗ₜ[R] m) =
      r • LocalizedModule.mk m s := by
  exact LocalizedModule.equivTensorProduct_symm_apply_tmul S m r s

@[simp]
theorem tensorLocalizationEquiv_one_tmul
    (S : Submonoid R) (M : Type*) [AddCommMonoid M] [Module R M]
    (m : M) :
    tensorLocalizationEquiv S M (1 ⊗ₜ[R] m) = LocalizedModule.mk m 1 := by
  exact LocalizedModule.equivTensorProduct_symm_apply_tmul_one S m

/-!
The canonical localization map sends an element to the fraction with
denominator `1`, and the localized map agrees with it on such elements.
-/
@[simp]
theorem localizedModule_map_mk (S : Submonoid R) {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (g : M →ₗ[R] N) (m : M) :
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S N) g
        (LocalizedModule.mkLinearMap S M m) =
      LocalizedModule.mkLinearMap S N (g m) := by
  exact IsLocalizedModule.map_apply S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) g m

/-!
Localization preserves composition of module maps.
-/
theorem localizedModule_map_comp (S : Submonoid R)
    {M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S P) (h.comp g) =
      (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N)
        (LocalizedModule.mkLinearMap S P) h).comp
        (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) g) := by
  exact IsLocalizedModule.map_comp' S
    (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N)
    (LocalizedModule.mkLinearMap S P) g h

/-!
The localized module has the expected universal property: maps out of it are
uniquely determined by their restriction along the canonical map whenever the
elements of `S` act invertibly on the target.
-/
theorem localizedModule_universal (S : Submonoid R)
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (g : M →ₗ[R] N)
    (h : ∀ s : S, IsUnit ((algebraMap R (Module.End R N)) s)) :
    ∃! l : LocalizedModule S M →ₗ[R] N,
      l.comp (LocalizedModule.mkLinearMap S M) = g := by
  exact IsLocalizedModule.is_universal S
    (LocalizedModule.mkLinearMap S M) g h

/-!
The localized identity map is the identity, a useful normalization for
iterated localization constructions.
-/
@[simp]
theorem localizedModule_map_id (S : Submonoid R) (M : Type*)
    [AddCommMonoid M] [Module R M] :
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S M) LinearMap.id = LinearMap.id := by
  exact IsLocalizedModule.map_id S (LocalizedModule.mkLinearMap S M)

/-!
Kernels and ranges of localized maps are the localizations of the original
kernels and ranges.  These identities are the submodule form of exactness.
-/
theorem localizedModule_ker_map (S : Submonoid R)
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (g : M →ₗ[R] N) :
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) g).ker =
      Submodule.localized₀ S (LocalizedModule.mkLinearMap S M) g.ker := by
  exact LinearMap.ker_localizedMap_eq_localized₀_ker S
    (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) g

theorem localizedModule_range_map (S : Submonoid R)
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (g : M →ₗ[R] N) :
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) g).range =
      Submodule.localized₀ S (LocalizedModule.mkLinearMap S N) g.range := by
  exact LinearMap.range_localizedMap_eq_localized₀_range S
    (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) g

/-!
Localization preserves exactness of a sequence of module maps.  This is the
formal counterpart of Stacks Tag 00CS.
-/
theorem localization_exact (S : Submonoid R)
    {M₀ M₁ M₂ : Type*}
    [AddCommMonoid M₀] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂)
    (hex : Function.Exact g h) :
    Function.Exact
      (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M₀)
        (LocalizedModule.mkLinearMap S M₁) g)
      (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M₁)
        (LocalizedModule.mkLinearMap S M₂) h) := by
  exact LocalizedModule.map_exact S g h hex

/-- Localization preserves injectivity of a linear map. -/
theorem localizedModule_map_injective (S : Submonoid R)
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (g : M →ₗ[R] N) (hg : Function.Injective g) :
    Function.Injective
      (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S N) g) := by
  exact LocalizedModule.map_injective S g hg

/-- Localization preserves surjectivity of a linear map. -/
theorem localizedModule_map_surjective (S : Submonoid R)
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (g : M →ₗ[R] N) (hg : Function.Surjective g) :
    Function.Surjective
      (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S N) g) := by
  exact LocalizedModule.map_surjective S g hg

/-!
The kernel of the canonical map is precisely the submodule of elements killed
by some denominator.  This is the elementwise form of the localization
equivalence relation.
-/
theorem localizedModule_mem_ker_iff
    {A : Type*} [CommRing A] (S : Submonoid A)
    {M : Type*} [AddCommMonoid M] [Module A M] {m : M} :
    m ∈ (LocalizedModule.mkLinearMap S M).ker ↔
      ∃ r : A, r ∈ S ∧ r • m = 0 := by
  exact LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := m)

/- The localization of a quotient module agrees with the quotient of the
localized module (Stacks, Tag 02C8 and the surrounding construction). -/
noncomputable def localizedModule_quotient_equiv
    {A : Type*} [CommRing A] (S : Submonoid A) {M : Type*}
    [AddCommGroup M] [Module A M] (N : Submodule A M) :
    (LocalizedModule S M ⧸ Submodule.localized S N) ≃ₗ[Localization S]
      LocalizedModule S (M ⧸ N) :=
  localizedQuotientEquiv S N

/- Finite generation is preserved by localization. -/
theorem localizedModule_finite (S : Submonoid R)
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    Module.Finite (Localization S) (LocalizedModule S M) := by
  infer_instance

theorem localizedModule_finite_of_isLocalized
    (S : Submonoid R) {Rₚ : Type*} [CommSemiring Rₚ] [Algebra R Rₚ]
    [IsLocalization S Rₚ] {M : Type*} [AddCommMonoid M] [Module R M]
    {Mₚ : Type*} [AddCommMonoid Mₚ] [Module R Mₚ] [Module Rₚ Mₚ]
    [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ)
    [IsLocalizedModule S f] [Module.Finite R M] :
    Module.Finite Rₚ Mₚ := by
  exact Module.Finite.of_isLocalizedModule S f

/-- The ring-level universal property of localization (Stacks, Tag 00CP). -/
theorem existsUnique_localization_lift
    {A B : Type*} [CommSemiring A] [CommSemiring B]
    (S : Submonoid A) (f : A →+* B)
    (hf : ∀ s : S, IsUnit (f s)) :
    ∃! g : Localization S →+* B,
      g.comp (algebraMap A (Localization S)) = f := by
  refine ⟨IsLocalization.lift hf, IsLocalization.lift_comp hf, ?_⟩
  intro g hg
  exact (IsLocalization.lift_unique (S := Localization S) hf
    (RingHom.congr_fun hg)).symm

end StacksPart01
