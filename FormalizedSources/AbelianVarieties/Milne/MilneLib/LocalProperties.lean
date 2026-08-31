/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

import MilneLib.Nakayama

/-!
# Local exactness

Exactness of a sequence of modules can be checked after localizing at every
maximal ideal.  This is the local-global principle used in Milne's discussion
of coherent modules and exact sequences.
-/

open IsLocalizedModule

namespace MilneLib

variable {R M N L : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  [AddCommMonoid L] [Module R L]

open TensorProduct

open CategoryTheory MorphismProperty
open AlgebraicGeometry

/-- Quasi-finiteness descends from a faithfully flat base change. -/
theorem quasiFinite_of_faithfullyFlat_baseChange
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Module.FaithfullyFlat R A]
    [Algebra.QuasiFinite A (A ⊗[R] S)] :
    Algebra.QuasiFinite R S := by
  refine ⟨fun p hp => ?_⟩
  obtain ⟨P, hP, hPover⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := R) (B := A) p
  letI : P.IsPrime := hP
  letI : P.LiesOver p := hPover
  letI := Localization.AtPrime.algebraOfLiesOver p P
  have hfin : Module.Finite P.ResidueField (P.Fiber (A ⊗[R] S)) := inferInstance
  let e : P.Fiber (A ⊗[R] S) ≃ₐ[P.ResidueField]
      P.ResidueField ⊗[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  have hfin' : Module.Finite P.ResidueField
      (P.ResidueField ⊗[p.ResidueField] (p.Fiber S)) := by
    letI : Module.Finite P.ResidueField (P.Fiber (A ⊗[R] S)) := hfin
    exact Module.Finite.equiv e.toLinearEquiv
  letI : Module.Finite P.ResidueField
      (P.ResidueField ⊗[p.ResidueField] (p.Fiber S)) := hfin'
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat P.ResidueField

/-- The RingHom QuasiFinite property codescends along faithfully flat maps. -/
theorem quasiFinite_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.QuasiFinite RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.QuasiFinite.respectsIso ?_
  intro R S T _ _ _ _ _ h h'
  rw [RingHom.quasiFinite_algebraMap] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact quasiFinite_of_faithfullyFlat_baseChange (R := R) (S := T) (A := S)

/-- Scheme-theoretic local quasi-finiteness descends along an fpqc cover. -/
theorem locallyQuasiFinite_descendsAlong_faithfullyFlat :
    DescendsAlong @LocallyQuasiFinite
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat
    quasiFinite_codescendsAlong_faithfullyFlat

/-
The canonical `LocalizedModule` maps keep the statement independent of a
chosen model for the localization at a maximal ideal.
-/
theorem LinearMap.exact_of_localized_at_maximal
    (f : M →ₗ[R] N) (g : N →ₗ[R] L)
    (h : ∀ (J : Ideal R) [J.IsMaximal],
      Function.Exact
        (IsLocalizedModule.map J.primeCompl
          (LocalizedModule.mkLinearMap J.primeCompl M)
          (LocalizedModule.mkLinearMap J.primeCompl N) f)
        (IsLocalizedModule.map J.primeCompl
          (LocalizedModule.mkLinearMap J.primeCompl N)
          (LocalizedModule.mkLinearMap J.primeCompl L) g)) :
    Function.Exact f g := by
  exact exact_of_localized_maximal f g h

/-- A map of modules is surjective when its canonical localizations at all
maximal ideals are surjective. -/
theorem LinearMap.surjective_of_localized_at_maximal
    (f : M →ₗ[R] N)
    (h : ∀ (J : Ideal R) [J.IsMaximal],
      Function.Surjective
        (IsLocalizedModule.map J.primeCompl
          (LocalizedModule.mkLinearMap J.primeCompl M)
          (LocalizedModule.mkLinearMap J.primeCompl N) f)) :
    Function.Surjective f := by
  exact surjective_of_localized_maximal f h

/-- A map to a finite module is surjective if its reductions modulo every
maximal ideal are surjective. -/
theorem LinearMap.surjective_of_surjective_residue_at_maximal
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N)
    (h : ∀ (J : Ideal R) [J.IsMaximal],
      Function.Surjective (((J • (⊤ : Submodule R N)).mkQ) ∘ₗ f)) :
    Function.Surjective f := by
  apply LinearMap.surjective_of_localized_at_maximal f
  intro J hJ
  change Function.Surjective
    (LinearMap.extendScalarsOfIsLocalization J.primeCompl
      (Localization J.primeCompl)
      (IsLocalizedModule.map J.primeCompl
        (LocalizedModule.mkLinearMap J.primeCompl M)
        (LocalizedModule.mkLinearMap J.primeCompl N) f))
  letI : Module.Finite (Localization J.primeCompl) (LocalizedModule J.primeCompl N) :=
    Module.Finite.of_isLocalizedModule J.primeCompl
      (LocalizedModule.mkLinearMap J.primeCompl N)
  apply LinearMap.surjective_of_surjective_residue
  have hrange : J • (⊤ : Submodule R N) ⊔ f.range = ⊤ := by
    rw [← Submodule.map_mkQ_eq_top, ← LinearMap.range_comp]
    exact LinearMap.range_eq_top.mpr (h J)
  have hlocal := congrArg
    (Submodule.localized'FrameHom (Localization J.primeCompl) J.primeCompl
      (LocalizedModule.mkLinearMap J.primeCompl N)) hrange
  rw [map_sup] at hlocal
  simp only [Submodule.IsLocalizedModule.localized'FrameHom_apply] at hlocal
  rw [LinearMap.localized'_range_eq_range_localizedMap
    (Localization J.primeCompl) J.primeCompl
    (LocalizedModule.mkLinearMap J.primeCompl M)
    (LocalizedModule.mkLinearMap J.primeCompl N) f] at hlocal
  apply LinearMap.range_eq_top.mp
  rw [LinearMap.range_comp, Submodule.map_mkQ_eq_top]
  simpa only [Submodule.localized'_smul, Ideal.localized'_eq_map,
    Localization.AtPrime.map_eq_maximalIdeal, Submodule.localized'_top] using hlocal

/-- Exactness of a module complex can be tested after localizing at every
maximal ideal.  The reverse implication is the local-global step used in the
coherent-sheaf arguments, while the forward implication is preservation of
exactness by localization. -/
theorem LinearMap.exact_iff_exact_localized_at_maximal
    {R M N L : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid L] [Module R L]
    (f : M →ₗ[R] N) (g : N →ₗ[R] L) :
    Function.Exact f g ↔
      ∀ (J : Ideal R) [J.IsMaximal],
        Function.Exact (LocalizedModule.map J.primeCompl f)
          (LocalizedModule.map J.primeCompl g) := by
  constructor
  · intro h J hJ
    exact LocalizedModule.map_exact J.primeCompl f g h
  · exact LinearMap.exact_of_localized_at_maximal f g

end MilneLib
