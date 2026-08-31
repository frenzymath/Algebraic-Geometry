/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1Curves
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Hartshorne Chapter I: local rings of smooth curves

This file connects standard smooth affine charts of relative dimension one to
Dedekind domains. It then identifies the local rings of an integral smooth
curve: the generic stalk is a field, while every non-generic stalk is a
discrete valuation ring. The resulting height-one specialization statements
are the finiteness substrate for principal divisors.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace Hartshorne

/-!
## Dedekind algebras
-/

/-- A finite-type, formally unramified domain over a Dedekind domain is
Dedekind in the local-DVR sense. Quasi-finiteness supplies incomparability of
primes without requiring the algebra to be module-finite. -/
theorem isDedekindDomainDvr_of_formallyUnramified_of_finiteType
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [IsDedekindDomain A] [IsDomain B] [Algebra.FormallyUnramified A B] :
    IsDedekindDomainDvr B where
  __ := Algebra.FiniteType.isNoetherianRing A B
  is_dvr_at_nonzero_prime := by
    intro q hq hqp
    let q' := IsLocalRing.maximalIdeal (Localization.AtPrime q)
    suffices q'.IsPrincipal from ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q)
      (IsLocalization.AtPrime.not_isField B hq (Localization.AtPrime q))).out 4 0).mp this
    let p := q.under A
    let _ := Localization.AtPrime.algebraOfLiesOver p q
    have hp : p ≠ ⊥ := by
      intro hp0
      refine hq (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) ⊥ q bot_le ?_).symm
      exact (le_bot_iff.mp (hp0 ▸ Ideal.comap_mono bot_le)).trans hp0.symm
    have : p.IsMaximal := (hqp.under A).isMaximal hp
    let _ : Field (A ⧸ p) := Ideal.Quotient.field p
    have : Module.Finite (A ⧸ p) (B ⧸ p.map (algebraMap A B)) :=
      Algebra.FormallyUnramified.finite_of_free _ _
    have := IsArtinianRing.of_finite (A ⧸ p) (B ⧸ p.map (algebraMap A B))
    suffices q' = (p.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q)) by
      rw [this, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq A (Localization.AtPrime p) (Localization.AtPrime q),
        ← Ideal.map_map]
      infer_instance
    rw [← (Algebra.FormallyUnramified.isRadical_map_isMaximal A B p).radical,
      IsLocalization.map_radical q.primeCompl,
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime q) q,
      Localization.AtPrime.map_eq_maximalIdeal]
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q.map (Ideal.Quotient.mk (p.map (algebraMap A B))),
      IsArtinianRing.mem_minimalPrimes bot_le, Ideal.comap_map_mk Ideal.map_comap_le⟩

/-- A finite-type, formally unramified domain over a Dedekind domain is a
Dedekind domain. -/
theorem isDedekindDomain_of_formallyUnramified_of_finiteType
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [IsDedekindDomain A] [IsDomain B] [Algebra.FormallyUnramified A B] :
    IsDedekindDomain B :=
  have := isDedekindDomainDvr_of_formallyUnramified_of_finiteType A B
  inferInstance

/-- The polynomial ring in one multivariate variable over a field is a
principal ideal ring. -/
theorem mvPolynomial_isPrincipalIdealRing_fin_one (k : Type*) [Field k] :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) k) := by
  have e : Polynomial k ≃+* MvPolynomial (Fin 1) k :=
    (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.toRingEquiv
  exact IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective

/-- The polynomial ring in one multivariate variable over a field is a
Dedekind domain. -/
theorem mvPolynomial_isDedekindDomain_fin_one (k : Type*) [Field k] :
    IsDedekindDomain (MvPolynomial (Fin 1) k) :=
  have := mvPolynomial_isPrincipalIdealRing_fin_one k
  inferInstance

/-- A standard smooth domain of relative dimension one over a field is a
Dedekind domain. -/
theorem standardSmoothOne_isDedekindDomain
    (k B : Type*) [Field k] [CommRing B] [Algebra k B] [IsDomain B]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k B] : IsDedekindDomain B := by
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 k B
  algebraize [g.toRingHom]
  have : Algebra.Etale (MvPolynomial (Fin 1) k) B := hg.toAlgebra
  have := mvPolynomial_isDedekindDomain_fin_one k
  exact isDedekindDomain_of_formallyUnramified_of_finiteType
    (MvPolynomial (Fin 1) k) B

/-!
## Affine Dedekind charts
-/

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The stalk of an integral scheme at a point of an affine Dedekind chart is
a valuation ring. At the zero prime it is a fraction field; otherwise it is a
discrete valuation ring. -/
theorem affineOpen_stalk_valuationRing [IsIntegral X] {V : X.Opens}
    (hV : IsAffineOpen V) (hD : IsDedekindDomain Γ(X, V)) {x : X} (hx : x ∈ V) :
    ValuationRing (X.presheaf.stalk x) := by
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hV.isLocalization_stalk ⟨x, hx⟩
  set q := hV.primeIdealOf ⟨x, hx⟩ with hq
  by_cases hbot : q.asIdeal = ⊥
  · have hsub : q.asIdeal.primeCompl = nonZeroDivisors Γ(X, V) := by
      ext z
      simp [Ideal.primeCompl, hbot, mem_nonZeroDivisors_iff_ne_zero]
    have hfrac : IsLocalization (nonZeroDivisors Γ(X, V))
        (X.presheaf.stalk x) := by
      rw [← hsub]
      exact hloc
    letI : Field (X.presheaf.stalk x) := IsFractionRing.toField Γ(X, V)
    infer_instance
  · have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        Γ(X, V) hbot _
    infer_instance

/-- On an irreducible scheme, a generalization of a point in an affine
Dedekind chart is either the generic point or the point itself. -/
theorem affineOpen_specializes_eq_genericPoint_or_eq [IrreducibleSpace X]
    {V : X.Opens} (hV : IsAffineOpen V) (hD : IsDedekindDomain Γ(X, V))
    {x y : X} (hx : x ∈ V) (h : y ⤳ x) : y = genericPoint X ∨ y = x := by
  have hy : y ∈ V := h.mem_open V.2 hx
  set py := hV.primeIdealOf ⟨y, hy⟩ with hpy
  set px := hV.primeIdealOf ⟨x, hx⟩ with hpx
  have hyx : hV.fromSpec.base py = y := hV.fromSpec_primeIdealOf ⟨y, hy⟩
  have hxx : hV.fromSpec.base px = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  have hspec : py ⤳ px := by
    refine hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp ?_
    rw [hyx, hxx]
    exact h
  have hle : py.asIdeal ≤ px.asIdeal :=
    (PrimeSpectrum.le_iff_specializes py px).mpr hspec
  by_cases hbot : py.asIdeal = ⊥
  · left
    have hgen : (genericPoint (Spec Γ(X, V)) : Spec Γ(X, V)) = py := by
      rw [genericPoint_eq_bot_of_affine]
      exact (PrimeSpectrum.ext hbot).symm
    rw [← hyx, ← hgen, genericPoint_eq_of_isOpenImmersion hV.fromSpec]
  · right
    have hmax : py.asIdeal.IsMaximal := py.isPrime.isMaximal hbot
    have : py.asIdeal = px.asIdeal := hmax.eq_of_le px.isPrime.ne_top hle
    rw [← hyx, ← hxx, PrimeSpectrum.ext this]

/-- A non-generic point is closed when every strict generalization is the
generic point. -/
theorem closed_singleton_of_curve_specializations [IrreducibleSpace X]
    (hgen : ∀ x y : X, y ⤳ x → y = genericPoint X ∨ y = x) {x : X}
    (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  have : closure ({x} : Set X) ⊆ {x} := by
    intro y hy
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
    rcases hgen y x hxy with h | h
    · exact absurd h hx
    · exact h ▸ rfl
  exact closure_subset_iff_isClosed.mp this

/-- A closed subset of a Noetherian curve-like scheme which avoids the
generic point is finite. -/
theorem finite_closed_of_avoids_genericPoint [IrreducibleSpace X]
    [TopologicalSpace.NoetherianSpace X]
    (hgen : ∀ x y : X, y ⤳ x → y = genericPoint X ∨ y = x)
    {Z : Set X} (hZ : IsClosed Z) (hxi : genericPoint X ∉ Z) : Z.Finite := by
  obtain ⟨S, hSfin, hScl, hSirr, hSsup⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hSsup]
  refine Set.Finite.sUnion hSfin fun t ht => ?_
  obtain ⟨z, hz⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
  have hzZ : z ∈ Z := hSsup ▸ Set.mem_sUnion.mpr ⟨t, ht, hz.mem⟩
  have hzxi : z ≠ genericPoint X := fun h => hxi (h ▸ hzZ)
  have hcl : IsClosed ({z} : Set X) :=
    closed_singleton_of_curve_specializations hgen hzxi
  have : t = {z} := by
    rw [← hz.def, hcl.closure_eq]
  rw [this]
  exact Set.finite_singleton z

/-!
## Smooth curves
-/

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- Every point of an integral smooth curve over a field lies in an affine
open whose ring of sections is a Dedekind domain. -/
theorem smoothCurve_exists_dedekind_affineOpen
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ IsDedekindDomain Γ(X, V) := by
  obtain ⟨U, hU, V, hV, hxV, e, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := f) x
  have hUtop : U = ⊤ := by
    have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum k))
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_)
    exact Subsingleton.elim (f.base x) y ▸ e hxV
  subst hUtop
  letI : Field Γ(Spec (CommRingCat.of k), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  algebraize [(f.appLE ⊤ V e).hom]
  exact ⟨V, hV, hxV,
    standardSmoothOne_isDedekindDomain
      Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V)⟩

/-- Every stalk of an integral smooth curve over a field is a valuation ring. -/
theorem smoothCurve_stalk_valuationRing
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] (x : X) :
    ValuationRing (X.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, hD⟩ := smoothCurve_exists_dedekind_affineOpen f x
  exact affineOpen_stalk_valuationRing hV hD hxV

/-- At a non-generic point of an affine Dedekind chart, the stalk is a
discrete valuation ring. -/
theorem affineOpen_stalk_isDiscreteValuationRing [IsIntegral X] {V : X.Opens}
    (hV : IsAffineOpen V) (hD : IsDedekindDomain Γ(X, V)) {x : X}
    (hx : x ∈ V) (hxg : x ≠ genericPoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hV.isLocalization_stalk ⟨x, hx⟩
  set q := hV.primeIdealOf ⟨x, hx⟩ with hq
  have hbot : q.asIdeal ≠ ⊥ := by
    intro h
    apply hxg
    have h1 : hV.fromSpec.base q = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
    have hgen : (genericPoint (Spec Γ(X, V)) : Spec Γ(X, V)) = q := by
      rw [genericPoint_eq_bot_of_affine]
      exact (PrimeSpectrum.ext h).symm
    rw [← h1, ← hgen, genericPoint_eq_of_isOpenImmersion hV.fromSpec]
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    Γ(X, V) hbot _

/-- The stalk of an integral smooth curve at a non-generic point is a
discrete valuation ring. -/
theorem smoothCurve_stalk_isDiscreteValuationRing
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X}
    (hx : x ≠ genericPoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, hD⟩ := smoothCurve_exists_dedekind_affineOpen f x
  exact affineOpen_stalk_isDiscreteValuationRing hV hD hxV hx

/-- The stalk of an integral smooth curve at a non-generic point is a
Dedekind domain. -/
theorem smoothCurve_stalk_isDedekindDomain
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X}
    (hx : x ≠ genericPoint X) : IsDedekindDomain (X.presheaf.stalk x) := by
  haveI := smoothCurve_stalk_isDiscreteValuationRing f hx
  infer_instance

/-- On an integral smooth curve, a generalization of a point is either the
generic point or the point itself. -/
theorem smoothCurve_specializes_eq_genericPoint_or_eq
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x y : X} (h : y ⤳ x) :
    y = genericPoint X ∨ y = x := by
  obtain ⟨V, hV, hxV, hD⟩ := smoothCurve_exists_dedekind_affineOpen f x
  exact affineOpen_specializes_eq_genericPoint_or_eq hV hD hxV h

/-- Every non-generic point of an integral smooth curve is closed. -/
theorem smoothCurve_isClosed_singleton_of_ne_genericPoint
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X}
    (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) :=
  closed_singleton_of_curve_specializations
    (fun _ _ h => smoothCurve_specializes_eq_genericPoint_or_eq f h) hx

end Hartshorne
