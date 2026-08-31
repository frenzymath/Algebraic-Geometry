/-
Copyright (c) 2026 The StacksPart02Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart02Lib Contributors
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Standard opens and their localization maps

The standard open `D(f)` on an affine open is represented on sections by the
localization away from `f`.  This file exposes that fact and the induced map
between such localizations under a ring homomorphism.
-/

namespace StacksPart02

open AlgebraicGeometry

universe u

/-- Sections on a standard open of an affine open are the localization away
from the defining section (Stacks, Tag 01HS(1)). -/
theorem affineOpen_standardOpen_isLocalization
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsLocalization.Away f Γ(X, X.basicOpen f) := by
  exact hU.isLocalization_basicOpen f

/-- The corresponding statement for an affine scheme and a global section. -/
theorem affineScheme_standardOpen_isLocalization
    (X : Scheme.{u}) [IsAffine X] (f : Γ(X, ⊤)) :
    IsLocalization.Away f Γ(X, X.basicOpen f) := by
  infer_instance

section RingMap

variable {R S Rf Sf : Type*}
variable [CommSemiring R] [CommSemiring S]
variable [CommSemiring Rf] [CommSemiring Sf]
variable [Algebra R Rf] [Algebra S Sf]

/-- The canonical map between localizations induced by a ring map.

If `Rf` is `R` localized away from `f` and `Sf` is `S` localized away from
`φ(f)`, this is the map supplied by the universal property of localization.
-/
noncomputable def standardOpenLocalizationMap
    (φ : R →+* S) (f : R)
    [IsLocalization.Away f Rf]
    [IsLocalization.Away (φ f) Sf] :
    Rf →+* Sf :=
  IsLocalization.Away.map Rf Sf φ f

@[simp]
theorem standardOpenLocalizationMap_algebraMap
    (φ : R →+* S) (f : R)
    [IsLocalization.Away f Rf]
    [IsLocalization.Away (φ f) Sf] (a : R) :
    standardOpenLocalizationMap φ f (algebraMap R Rf a) =
      algebraMap S Sf (φ a) := by
  have h : Submonoid.powers f ≤ (Submonoid.powers (φ f)).comap φ := by
    rintro x ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  change IsLocalization.map Sf φ h (algebraMap R Rf a) = algebraMap S Sf (φ a)
  exact IsLocalization.map_eq h a

/-- Ring-hom form of `standardOpenLocalizationMap_algebraMap`. -/
theorem standardOpenLocalizationMap_comp_algebraMap
    (φ : R →+* S) (f : R)
    [IsLocalization.Away f Rf]
    [IsLocalization.Away (φ f) Sf] :
    (standardOpenLocalizationMap φ f).comp (algebraMap R Rf) =
      (algebraMap S Sf).comp φ := by
  ext a
  exact standardOpenLocalizationMap_algebraMap φ f a

end RingMap

section Inclusion

variable {R : Type*} [CommSemiring R]

/-- The containment `D(g) ⊆ D(f)` is equivalent to an exponent relation
`g^n = a f` (Stacks, Tag 01HS(1)(b)). -/
theorem standardOpen_subset_iff_exists_pow_eq_mul {f g : R}
    (hsub : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ∃ n : ℕ, ∃ a : R, g ^ n = a * f := by
  have h' := (PrimeSpectrum.basicOpen_le_basicOpen_iff g f).mp hsub
  rw [Ideal.mem_radical_iff] at h'
  obtain ⟨n, hn⟩ := h'
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hn
  exact ⟨n, a, by simpa [mul_comm] using ha.symm⟩

/-- The defining element of a larger standard open is invertible after
localizing at a smaller standard open. -/
theorem standardOpen_isUnit_of_subset {f g : R}
    (hsub : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    IsUnit (algebraMap R (Localization.Away g) f) := by
  exact (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
    (S := Localization.Away g) (f := g) (g := f)).mp hsub

/-- The canonical localization map associated to an inclusion of standard
opens `D(g) ⊆ D(f)`. -/
noncomputable def standardOpenLocalizationMapOfSubset {f g : R}
    (hsub : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    Localization.Away f →+* Localization.Away g :=
  IsLocalization.Away.lift f
    (g := algebraMap R (Localization.Away g))
    (standardOpen_isUnit_of_subset hsub)

@[simp]
theorem standardOpenLocalizationMapOfSubset_algebraMap {f g : R}
    (hsub : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) (a : R) :
    standardOpenLocalizationMapOfSubset hsub (algebraMap R (Localization.Away f) a) =
      algebraMap R (Localization.Away g) a := by
  exact IsLocalization.Away.lift_eq f (standardOpen_isUnit_of_subset hsub) a

/-- Inclusion maps of standard opens compose along inclusions. -/
theorem standardOpenLocalizationMapOfSubset_comp {f g h : R}
    (hfg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (hgh : PrimeSpectrum.basicOpen h ≤ PrimeSpectrum.basicOpen g) :
    (standardOpenLocalizationMapOfSubset hgh).comp
        (standardOpenLocalizationMapOfSubset hfg) =
      standardOpenLocalizationMapOfSubset (hgh.trans hfg) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp [standardOpenLocalizationMapOfSubset]

end Inclusion

section ModuleInclusion

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Powers of `f` act by units on the module localized away from `g` whenever
`D(g) ⊆ D(f)`. -/
theorem standardOpen_module_isUnit_of_subset {f g : R}
    (hsub : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ∀ x : Submonoid.powers f,
      IsUnit (algebraMap R (Module.End R (LocalizedModule.Away g M)) (x : R)) := by
  have hf : IsUnit (algebraMap R (Localization.Away g) f) :=
    standardOpen_isUnit_of_subset hsub
  have hfend :
      IsUnit (algebraMap R (Module.End R (LocalizedModule.Away g M)) f) := by
    rw [show algebraMap R (Module.End R (LocalizedModule.Away g M)) f =
        Algebra.lsmul R R (LocalizedModule.Away g M)
          (algebraMap R (Localization.Away g) f) by
          ext m
          simp]
    exact hf.map (Algebra.lsmul R R (LocalizedModule.Away g M)).toMonoidHom
  rintro ⟨x, hx⟩
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x f).mp hx
  simpa only [map_pow] using hfend.pow n

/-- The canonical map between module localizations associated to an inclusion
of standard opens. -/
noncomputable def standardOpenLocalizedModuleMapOfSubset {f g : R}
    (hsub : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away g M :=
  IsLocalizedModule.lift (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
    (standardOpen_module_isUnit_of_subset hsub)

@[simp]
theorem standardOpenLocalizedModuleMapOfSubset_mkLinearMap {f g : R}
    (hsub : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) (m : M) :
    standardOpenLocalizedModuleMapOfSubset hsub
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers g) M m := by
  exact IsLocalizedModule.lift_apply
    (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
    (standardOpen_module_isUnit_of_subset hsub) m

/-- The canonical module maps compose along inclusions of standard opens. -/
theorem standardOpenLocalizedModuleMapOfSubset_comp {f g h : R}
    (hfg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (hgh : PrimeSpectrum.basicOpen h ≤ PrimeSpectrum.basicOpen g) :
    (standardOpenLocalizedModuleMapOfSubset (M := M) hgh).comp
        (standardOpenLocalizedModuleMapOfSubset (M := M) hfg) =
      standardOpenLocalizedModuleMapOfSubset (M := M) (hgh.trans hfg) := by
  refine IsLocalizedModule.ext
    (S := Submonoid.powers f)
    (M := M)
    (M' := LocalizedModule.Away f M)
    (M'' := LocalizedModule.Away h M)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (standardOpen_module_isUnit_of_subset (M := M) (hgh.trans hfg)) ?_
  rw [LinearMap.comp_assoc]
  apply LinearMap.ext
  intro m
  change (standardOpenLocalizedModuleMapOfSubset (M := M) hgh)
      ((standardOpenLocalizedModuleMapOfSubset (M := M) hfg)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m)) =
    standardOpenLocalizedModuleMapOfSubset (M := M) (hgh.trans hfg)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M m)
  simp only [standardOpenLocalizedModuleMapOfSubset_mkLinearMap]

end ModuleInclusion

/-! ### Covers of a standard open -/

/-- A family of standard opens covers `D(f)` exactly when its defining
sections generate the unit ideal after localizing away from `f` (Stacks,
Tag 01HS(3)). -/
theorem standardOpen_subset_iUnion_iff_span_eq_top_localization
    {R : Type*} [CommSemiring R] {ι : Type*}
    (f : R) (g : ι → R) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
        ⋃ i, (PrimeSpectrum.basicOpen (g i) : Set (PrimeSpectrum R)) ↔
      Ideal.span (Set.range (fun i =>
        algebraMap R (Localization.Away f) (g i))) = ⊤ := by
  let c : PrimeSpectrum (Localization.Away f) → PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (Localization.Away f))
  have hc (x : ι) :
      c ⁻¹' (PrimeSpectrum.basicOpen (g x) : Set (PrimeSpectrum R)) =
        (PrimeSpectrum.basicOpen
          (algebraMap R (Localization.Away f) (g x)) :
            Set (PrimeSpectrum (Localization.Away f))) := by
    exact congrArg
      (fun U : TopologicalSpace.Opens (PrimeSpectrum (Localization.Away f)) =>
        (U : Set (PrimeSpectrum (Localization.Away f))))
      (PrimeSpectrum.comap_basicOpen (algebraMap R (Localization.Away f)) (g x))
  have hrange : Set.range c = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  constructor
  · intro h
    have htop : (⨆ i, PrimeSpectrum.basicOpen
        (algebraMap R (Localization.Away f) (g i))) = ⊤ := by
      apply TopologicalSpace.Opens.ext
      apply Set.ext
      intro q
      constructor
      · intro _
        trivial
      · intro _
        have hq : c q ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
          rw [← hrange]
          exact ⟨q, rfl⟩
        rcases Set.mem_iUnion.mp (h hq) with ⟨i, hi⟩
        change q ∈ (⨆ i, PrimeSpectrum.basicOpen
          (algebraMap R (Localization.Away f) (g i)))
        rw [TopologicalSpace.Opens.mem_iSup]
        refine ⟨i, ?_⟩
        change q ∈ c ⁻¹' (PrimeSpectrum.basicOpen (g i) : Set (PrimeSpectrum R))
        rw [hc i]
        exact hi
    exact PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp htop
  · intro h
    have htop : (⨆ i, PrimeSpectrum.basicOpen
        (algebraMap R (Localization.Away f) (g i))) = ⊤ :=
      PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr h
    intro p hp
    rw [← hrange] at hp
    rcases hp with ⟨q, rfl⟩
    rcases TopologicalSpace.Opens.mem_iSup.mp (htop.ge (Set.mem_univ q)) with ⟨i, hi⟩
    apply Set.mem_iUnion.mpr ⟨i, ?_⟩
    change q ∈ c ⁻¹' (PrimeSpectrum.basicOpen (g i) : Set (PrimeSpectrum R))
    rw [hc i]
    exact hi

end StacksPart02
