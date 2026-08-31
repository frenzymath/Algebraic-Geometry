/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Dimension infrastructure

These lemmas isolate the commutative-algebra part of Milne's dimension
arguments.  The affine-scheme adapter is deliberately conditional; the
proper abelian-variety case still needs a separate global dimension theorem.
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  MorphismProperty
open AlgebraicGeometry

namespace MilneLib

/-- An injective integral extension preserves Krull dimension. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hfin : f.IsIntegral)
    (hinj : Function.Injective f) :
    ringKrullDim S = ringKrullDim R := by
  letI : Algebra R S := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hfin⟩
  let c : PrimeSpectrum S → PrimeSpectrum R := PrimeSpectrum.comap f
  have hc_strict : StrictMono c := by
    intro I J hIJ
    change I.asIdeal < J.asIdeal at hIJ
    change Ideal.comap f I.asIdeal < Ideal.comap f J.asIdeal
    exact Ideal.IsIntegral.comap_lt_comap hIJ
  have hcoheight (I : PrimeSpectrum S) :
      Order.coheight I = Order.coheight (c I) := by
    apply Order.coheight_eq_of_strictMono c hc_strict
    intro a b hab
    obtain ⟨Q, haQ, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
        b.asIdeal a.asIdeal hab.le
    let q : PrimeSpectrum S := ⟨Q, hQprime⟩
    refine ⟨q, ?_, ?_⟩
    · change a.asIdeal < Q
      refine lt_of_le_of_ne haQ ?_
      intro hEq
      have hcEq : c a = b := by
        apply PrimeSpectrum.ext
        change Ideal.comap f a.asIdeal = b.asIdeal
        simpa [hEq, RingHom.algebraMap_toAlgebra] using hQcomap
      exact (ne_of_lt hab) hcEq
    · apply PrimeSpectrum.ext
      change Ideal.comap f Q = b.asIdeal
      simpa only [RingHom.algebraMap_toAlgebra] using hQcomap
  change Order.krullDim (PrimeSpectrum S) =
    Order.krullDim (PrimeSpectrum R)
  apply le_antisymm
  · exact Order.krullDim_le_of_strictMono c hc_strict
  · rw [Order.krullDim_eq_iSup_coheight,
        Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro p
    obtain ⟨q, hq⟩ := hfin.comap_surjective hinj p
    rw [← hq, ← hcoheight q]
    exact le_iSup
      (fun q : PrimeSpectrum S =>
        (Order.coheight q : WithBot ℕ∞)) q

/-- A finite surjective morphism to an affine reduced scheme preserves
Krull dimension.  Finiteness makes the source affine, so the assertion is
reduced to the integral injective map on global sections. -/
theorem topologicalKrullDim_eq_of_isFinite_surjective_of_isAffineTarget
    {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] [IsReduced Y] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  rw [IsHomeomorph.topologicalKrullDim_eq X.isoSpec.hom
        X.isoSpec.hom.homeomorph.isHomeomorph,
      IsHomeomorph.topologicalKrullDim_eq Y.isoSpec.hom
        Y.isoSpec.hom.homeomorph.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum Γ(X, ⊤)) =
    topologicalKrullDim (PrimeSpectrum Γ(Y, ⊤))
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_eq_of_isIntegral_of_injective
    (f.appTop).hom f.finite_appTop.to_isIntegral (f.app_injective ⊤)

end MilneLib
