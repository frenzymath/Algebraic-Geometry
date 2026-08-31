/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Standard smooth algebras of relative dimension one over a field are Dedekind domains

The commutative-algebra bricks for "the local rings of a smooth curve are discrete valuation
rings":

* `IsDedekindDomainDvr.of_formallyUnramified_of_finiteType` /
  `IsDedekindDomain.of_formallyUnramified_of_finiteType`: a domain which is unramified and of
  finite type over a Dedekind domain is a Dedekind domain.  This generalizes Mathlib's
  `isDedekindDomain.of_formallyUnramified` from module-finite to finite-type algebras: the
  incomparability of primes, which for finite algebras comes from integrality, here comes from
  quasi-finiteness (`Algebra.QuasiFinite`, satisfied by any unramified algebra essentially of
  finite type).
* `Algebra.IsStandardSmoothOfRelativeDimension.isDedekindDomain`: a domain which is standard
  smooth of relative dimension `1` over a field is a Dedekind domain.  By the structure theorem
  for standard smooth algebras (Stacks 00T7,
  `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`), such an algebra is
  étale over the polynomial ring `k[t]`, which is a principal ideal domain; étale maps are
  unramified and of finite type, so the previous brick applies.
* `Algebra.IsStandardSmoothOfRelativeDimension.exists_transcendental`: a nontrivial standard
  smooth algebra of relative dimension `1` over a field contains an element transcendental over
  the field, namely the étale coordinate: étale algebras are flat, hence torsion-free over
  `k[t]`, so the coordinate satisfies no nonzero polynomial.

Everything in this file is stated in Mathlib generality and is a candidate for upstreaming.
-/

set_option autoImplicit false

section Unramified

/-- A domain which is unramified and of finite type over a Dedekind domain is a Dedekind
domain in the DVR sense: it is Noetherian, and its localization at every nonzero prime is a
discrete valuation ring.

This generalizes `isDedekindDomainDvr.of_formallyUnramified` (which assumes the algebra to be
module-finite) to finite-type algebras: the incomparability of primes over a common prime of
the base, which for finite algebras follows from integrality, here follows from
quasi-finiteness of unramified algebras (`Algebra.QuasiFinite.eq_of_le_of_under_eq`). -/
theorem IsDedekindDomainDvr.of_formallyUnramified_of_finiteType
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
    -- Incomparability from quasi-finiteness: a nonzero prime of `B` contracts to a nonzero
    -- prime of `A`.
    have hp : p ≠ ⊥ := by
      intro hp0
      refine hq (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) ⊥ q bot_le ?_).symm
      exact (le_bot_iff.mp (hp0 ▸ Ideal.comap_mono bot_le)).trans hp0.symm
    have : p.IsMaximal := (hqp.under A).isMaximal hp
    let _ : Field (A ⧸ p) := Ideal.Quotient.field p
    -- The fiber ring over `p` is finite over the residue field `A ⧸ p` by unramifiedness.
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

/-- A domain which is unramified and of finite type over a Dedekind domain is a Dedekind
domain. -/
theorem IsDedekindDomain.of_formallyUnramified_of_finiteType
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [IsDedekindDomain A] [IsDomain B] [Algebra.FormallyUnramified A B] :
    IsDedekindDomain B :=
  have := IsDedekindDomainDvr.of_formallyUnramified_of_finiteType A B
  inferInstance

end Unramified

section StandardSmooth

variable (k : Type*) [Field k]

/-- The polynomial ring in one (multivariate) variable over a field is a principal ideal
ring, by transport from `Polynomial k`. -/
theorem MvPolynomial.isPrincipalIdealRing_fin_one :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) k) := by
  have e : Polynomial k ≃+* MvPolynomial (Fin 1) k :=
    (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.toRingEquiv
  exact IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective

/-- The polynomial ring in one (multivariate) variable over a field is a Dedekind domain. -/
theorem MvPolynomial.isDedekindDomain_fin_one : IsDedekindDomain (MvPolynomial (Fin 1) k) :=
  have := MvPolynomial.isPrincipalIdealRing_fin_one k
  inferInstance

variable (B : Type*) [CommRing B] [Algebra k B]

/-- A domain which is standard smooth of relative dimension `1` over a field is a Dedekind
domain: by the structure theorem for standard smooth algebras (Stacks 00T7) it is étale over
the principal ideal domain `k[t]`, and unramified finite-type algebras over Dedekind domains
are Dedekind. -/
theorem Algebra.IsStandardSmoothOfRelativeDimension.isDedekindDomain [IsDomain B]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k B] : IsDedekindDomain B := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 k B
  algebraize [g.toRingHom]
  have : Algebra.Etale (MvPolynomial (Fin 1) k) B := hg.toAlgebra
  have := MvPolynomial.isDedekindDomain_fin_one k
  exact IsDedekindDomain.of_formallyUnramified_of_finiteType (MvPolynomial (Fin 1) k) B

/-- A nontrivial standard smooth algebra of relative dimension `1` over a field contains an
element transcendental over the field: the étale coordinate given by the structure theorem for
standard smooth algebras.  Its transcendence comes from flatness of étale maps: `B` is a
torsion-free `k[t]`-module, so no nonzero polynomial annihilates `1`. -/
theorem Algebra.IsStandardSmoothOfRelativeDimension.exists_transcendental [Nontrivial B]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k B] :
    ∃ t : B, Transcendental k t := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 k B
  algebraize [g.toRingHom]
  have : Algebra.Etale (MvPolynomial (Fin 1) k) B := hg.toAlgebra
  -- `B` is flat over `k[t]`, hence torsion-free, hence the algebra map is injective.
  have hinj : Function.Injective g := by
    intro a b hab
    by_contra hne
    have hmem : a - b ∈ nonZeroDivisors (MvPolynomial (Fin 1) k) :=
      mem_nonZeroDivisors_of_ne_zero (sub_ne_zero_of_ne hne)
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) hmem
    have : (a - b) • (1 : B) = (a - b) • (0 : B) := by
      rw [smul_zero, Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra, map_sub,
        sub_eq_zero]
      exact hab
    exact one_ne_zero (hreg this)
  refine ⟨g (MvPolynomial.X 0), fun hX => ?_⟩
  -- If the coordinate were algebraic, `X 0` would be algebraic in `k[t]` itself.
  have : IsAlgebraic k (MvPolynomial.X 0 : MvPolynomial (Fin 1) k) := by
    obtain ⟨P, hP, hPeval⟩ := hX
    refine ⟨P, hP, hinj ?_⟩
    rw [map_zero, ← hPeval]
    exact (Polynomial.aeval_algHom_apply g (MvPolynomial.X 0) P).symm
  exact MvPolynomial.transcendental_X k (0 : Fin 1) this

end StandardSmooth
