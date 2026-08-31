/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.DedekindColength

/-!
# Dedekind colength through localization at a prime (G-D5(b), SB-3b algebra face)

The multiplicity face of the chart colength dictionary
(`informal/deg-d5b-worksheet.md` §4 SB-3b), stated in pure commutative algebra: for a
Dedekind domain `B` over a field `K` and a nonzero `f : B`, the colength
`finrank K (B ⧸ (f))` is computed per prime factor through the localization at that prime —
**never** through the false principal-prime shortcut of
`finrank_quotient_span_eq_sum_ord` (whose `hprin` hypothesis fails on general Dedekind
charts).

The two mathlib pieces this glues are `IsLocalization.AtPrime.equivQuotMaximalIdealPow`
(`B ⧸ p^n ≃ₐ[B] S ⧸ m^n` for `S` a localization of `B` at the maximal prime `p`) and the
landed prime-power engine `AlgebraicJacobian.Algebra.DedekindColength`
(`finrank_quotient_span_pow`, `finrank_quotient_eq_sum_factors_pow`), applied in the
localization `S` — a discrete valuation ring, where the maximal ideal *is* principal.

## Main declarations

* `AlgebraicGeometry.moduleFinite_quotient_pow_of_isPrincipal` — dévissage: if `B ⧸ I` is a
  finite `K`-module and `I` is principal nonzero, so is every `B ⧸ Iⁿ`.
* `AlgebraicGeometry.intValuation_eq_exp_neg_count` — the `p`-adic valuation of `f` is
  `exp (−count p (factors (f)))`: the bridge between the `factors` multiset of the landed
  engine and mathlib's `HeightOneSpectrum.intValuation`.
* `AlgebraicGeometry.mem_pow_iff_le_count` — `f ∈ pⁿ ↔ n ≤ count p (factors (f))`.
* `AlgebraicGeometry.count_factors_span_algebraMap` — **multiplicities are preserved by
  localization at the prime**: `count m (factors (f·S)) = count p (factors (f))` for `S` a
  localization of `B` at `p` with maximal ideal `m`.
* `AlgebraicGeometry.quotPowLinearEquiv`, `AlgebraicGeometry.residueQuotLinearEquiv` —
  `K`-linear forms of the localization isomorphisms `B ⧸ pⁿ ≃ S ⧸ mⁿ`, `B ⧸ p ≃ S ⧸ m`.
* `AlgebraicGeometry.moduleFinite_quotient_pow_atPrime`,
  `AlgebraicGeometry.finrank_quotient_pow_atPrime` — the per-prime colength collapse
  `finrank K (B ⧸ pⁿ) = n * finrank K (B ⧸ p)`, via the DVR `S`.
* `AlgebraicGeometry.moduleFinite_quotient_span`,
  `AlgebraicGeometry.finrank_quotient_span_eq_sum_count` — the honest Dedekind colength
  formula `finrank K (B ⧸ (f)) = ∑_{p ∣ (f)} count p (factors (f)) * finrank K (B ⧸ p)`,
  with no principality hypothesis.  This is the engine of the fiber-degree identity (†) and
  of the deferred E-i pushforward-rank node.
-/

set_option autoImplicit false

open Module (finrank)
open UniqueFactorizationMonoid IsLocalRing IsDedekindDomain

namespace AlgebraicGeometry

/-! ### Dévissage of module finiteness along principal prime powers -/

section Devissage

variable {K : Type*} [Field K] {B : Type*} [CommRing B] [IsDomain B] [Algebra K B]

/-- **Finiteness dévissage.** If `B ⧸ I` is a finite `K`-module for a nonzero principal
ideal `I`, then so is `B ⧸ Iⁿ` for every `n`: induct along the filtration
`Iⁿ ⧸ Iⁿ⁺¹ ≅ B ⧸ I` (the landed `quotEquivMapPow`), using that module finiteness is closed
under extensions (`Module.Finite.of_submodule_quotient`). 


 * Provenance: CUSTOM.
-/
theorem moduleFinite_quotient_pow_of_isPrincipal {I : Ideal B} (h : I.IsPrincipal)
    (h' : I ≠ ⊥) [Module.Finite K (B ⧸ I)] (n : ℕ) : Module.Finite K (B ⧸ I ^ n) := by
  induction n with
  | zero =>
    have hle : I ≤ I ^ 0 := by rw [pow_zero, Ideal.one_eq_top]; exact le_top
    exact Module.Finite.of_surjective (Ideal.Quotient.factorₐ K hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  | succ n ih =>
    set g : (B ⧸ I ^ (n + 1)) →ₗ[K] (B ⧸ I ^ n) :=
      (Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right n.le_succ)).toLinearMap with hg_def
    have hg : Function.Surjective g :=
      Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right n.le_succ)
    have hker : LinearMap.ker g =
        Submodule.restrictScalars K (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)) := by
      apply SetLike.ext
      intro x
      rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, hg_def, AlgHom.toLinearMap_apply,
        Ideal.Quotient.factorₐ_apply, ← RingHom.mem_ker, Ideal.Quotient.factor_ker]
    haveI : Module.Finite K (LinearMap.ker g) := by
      rw [hker]
      exact Module.Finite.equiv (quotEquivMapPow h h' n)
    haveI := ih
    haveI : Module.Finite K ((B ⧸ I ^ (n + 1)) ⧸ LinearMap.ker g) :=
      Module.Finite.equiv (g.quotKerEquivOfSurjective hg).symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

end Devissage

/-! ### Multiplicities and the adic valuation -/

section Count

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

/-- The `p`-adic valuation of a nonzero `f : B` is `exp (−count p (factors (f)))`: mathlib's
`intValuation` is defined by the `Associates` count, which agrees with the `Multiset` count
of the `factors` multiset used by the landed colength engine. 


 * Provenance: CUSTOM.
-/
theorem intValuation_eq_exp_neg_count (v : HeightOneSpectrum B) {f : B} (hf : f ≠ 0) :
    v.intValuation f
      = WithZero.exp (-(Multiset.count v.asIdeal (factors (Ideal.span {f})) : ℤ)) := by
  have hsp : Ideal.span {f} ≠ (0 : Ideal B) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact hf
  rw [v.intValuation_if_neg hf, factors_eq_normalizedFactors,
    ← Ideal.count_associates_factors_eq hsp v.isPrime v.ne_bot]

/-- **Membership in prime powers reads off the multiplicity**: `f ∈ pⁿ` if and only if
`n ≤ count p (factors (f))`. 


 * Provenance: CUSTOM.
-/
theorem mem_pow_iff_le_count (v : HeightOneSpectrum B) {f : B} (hf : f ≠ 0) (n : ℕ) :
    f ∈ v.asIdeal ^ n ↔ n ≤ Multiset.count v.asIdeal (factors (Ideal.span {f})) := by
  rw [← v.intValuation_le_pow_iff_mem, intValuation_eq_exp_neg_count v hf,
    WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]

/-- **Multiplicities are preserved by localization at the prime** (the "least-trodden
bridge" of the worksheet, dissolved): for a localization `S` of the Dedekind domain `B` at
the nonzero prime `p` and a nonzero `f : B`, the multiplicity of the maximal ideal of `S`
in the factorization of `f·S` equals the multiplicity of `p` in the factorization of
`(f) ⊆ B`.  Both multiplicities are characterized by membership in prime powers
(`mem_pow_iff_le_count`), and those memberships correspond along the localization
(`IsLocalization.AtPrime.under_maximalIdeal_pow`). 


 * Provenance: CUSTOM.
-/
theorem count_factors_span_algebraMap (S : Type*) [CommRing S] [IsDedekindDomain S]
    [Algebra B S] {p : Ideal B} [hp : p.IsPrime] (hp0 : p ≠ ⊥) [IsLocalization.AtPrime S p]
    [IsLocalRing S] {f : B} (hf : f ≠ 0) :
    Multiset.count (maximalIdeal S) (factors (Ideal.span {algebraMap B S f}))
      = Multiset.count p (factors (Ideal.span {f})) := by
  haveI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hp0 S
  haveI : p.IsMaximal := hp.isMaximal hp0
  set vB : HeightOneSpectrum B := ⟨p, hp, hp0⟩ with hvB
  set vS : HeightOneSpectrum S :=
    ⟨maximalIdeal S, (maximalIdeal.isMaximal S).isPrime,
      IsDiscreteValuationRing.not_a_field S⟩ with hvS
  have hinj : Function.Injective (algebraMap B S) :=
    IsLocalization.injective S p.primeCompl_le_nonZeroDivisors
  have hfS : algebraMap B S f ≠ 0 := fun h0 => hf (hinj (by rw [h0, map_zero]))
  have key : ∀ n : ℕ, algebraMap B S f ∈ maximalIdeal S ^ n ↔ f ∈ p ^ n := by
    intro n
    conv_rhs => rw [← IsLocalization.AtPrime.under_maximalIdeal_pow p S n]
    rw [Ideal.mem_under]
  have hiff : ∀ n : ℕ,
      (n ≤ Multiset.count (maximalIdeal S) (factors (Ideal.span {algebraMap B S f}))
        ↔ n ≤ Multiset.count p (factors (Ideal.span {f}))) := by
    intro n
    rw [← mem_pow_iff_le_count vS hfS n, ← mem_pow_iff_le_count vB hf n]
    exact key n
  exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)

end Count

/-! ### The per-prime colength collapse through the localization -/

section AtPrime

variable {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B]
  (S : Type*) [CommRing S] [Algebra K S] [Algebra B S] [IsScalarTower K B S]
  (p : Ideal B) [p.IsMaximal] [IsLocalization.AtPrime S p] [IsLocalRing S]

/-- The localization isomorphism `B ⧸ pⁿ ≃ Rₚ ⧸ mⁿ`
(`IsLocalization.AtPrime.equivQuotMaximalIdealPow`), as a `K`-linear equivalence. 


 * Provenance: CUSTOM.
-/
noncomputable def quotPowLinearEquiv (n : ℕ) :
    (B ⧸ p ^ n) ≃ₗ[K] S ⧸ maximalIdeal S ^ n :=
  ((IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n).toLinearEquiv).restrictScalars K

/-- The residue-field isomorphism `B ⧸ p ≃ S ⧸ m`
(`IsLocalization.AtPrime.equivQuotMaximalIdeal`), as a `K`-linear equivalence. 


 * Provenance: CUSTOM.
-/
noncomputable def residueQuotLinearEquiv : (B ⧸ p) ≃ₗ[K] S ⧸ maximalIdeal S :=
  (AlgEquiv.ofRingEquiv (f := IsLocalization.AtPrime.equivQuotMaximalIdeal p S)
    (fun c : K => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap,
        IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
        ← IsScalarTower.algebraMap_apply K B S])).toLinearEquiv

variable {S p}

/-- **Per-prime finiteness**: if the residue `B ⧸ p` is a finite `K`-module, so is every
`B ⧸ pⁿ` — transported through the localization `S`, where the maximal ideal is principal
(`S` is a DVR when `B` is Dedekind), and dévissaged there. 


 * Provenance: CUSTOM.
-/
theorem moduleFinite_quotient_pow_atPrime [IsDedekindDomain B] [IsDomain S] (hp0 : p ≠ ⊥)
    [Module.Finite K (B ⧸ p)] (n : ℕ) : Module.Finite K (B ⧸ p ^ n) := by
  haveI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hp0 S
  haveI : Module.Finite K (S ⧸ maximalIdeal S) :=
    Module.Finite.equiv (residueQuotLinearEquiv S p)
  haveI : Module.Finite K (S ⧸ maximalIdeal S ^ n) :=
    moduleFinite_quotient_pow_of_isPrincipal
      (IsPrincipalIdealRing.principal (maximalIdeal S))
      (IsDiscreteValuationRing.not_a_field S) n
  exact Module.Finite.equiv (quotPowLinearEquiv S p n).symm

/-- **The per-prime colength collapse**: `finrank K (B ⧸ pⁿ) = n * finrank K (B ⧸ p)` for a
nonzero prime `p` of a Dedekind domain with `K`-finite residue.  Proved in the localization
`S` at `p` — a DVR, where the maximal ideal is principal and the landed
`finrank_quotient_span_pow` applies. 


 * Provenance: CUSTOM.
-/
theorem finrank_quotient_pow_atPrime [IsDedekindDomain B] [IsDomain S] (hp0 : p ≠ ⊥)
    [Module.Finite K (B ⧸ p)] (n : ℕ) :
    finrank K (B ⧸ p ^ n) = n * finrank K (B ⧸ p) := by
  haveI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hp0 S
  haveI : Module.Finite K (S ⧸ maximalIdeal S) :=
    Module.Finite.equiv (residueQuotLinearEquiv S p)
  haveI : Module.Finite K (S ⧸ maximalIdeal S ^ n) :=
    moduleFinite_quotient_pow_of_isPrincipal
      (IsPrincipalIdealRing.principal (maximalIdeal S))
      (IsDiscreteValuationRing.not_a_field S) n
  rw [(quotPowLinearEquiv S p n).finrank_eq,
    finrank_quotient_span_pow (IsPrincipalIdealRing.principal (maximalIdeal S))
      (IsDiscreteValuationRing.not_a_field S) n,
    (residueQuotLinearEquiv S p).finrank_eq, smul_eq_mul]

end AtPrime

/-! ### The honest Dedekind colength formula -/

section Master

variable {K : Type*} [Field K] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra K B]

/-- Every prime factor of `(f)` is a nonzero prime ideal containing `f`. 


 * Provenance: CUSTOM.
-/
theorem prime_factor_span (f : B) {P : Ideal B}
    (hP : P ∈ (factors (Ideal.span {f})).toFinset) : P.IsPrime ∧ P ≠ ⊥ ∧ f ∈ P := by
  have hprime : Prime P := prime_of_factor _ (Multiset.mem_toFinset.mp hP)
  refine ⟨Ideal.isPrime_of_prime hprime, hprime.ne_zero, ?_⟩
  rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le]
  exact dvd_of_mem_factors (Multiset.mem_toFinset.mp hP)

/-- The canonical localization of `B` at a prime factor, with its `K`-algebra structure by
composition.  Bundled as `haveI`-style helpers inside the master proofs. -/
private theorem master_aux {f : B}
    [hfin : ∀ P : (factors (Ideal.span {f})).toFinset, Module.Finite K (B ⧸ (P : Ideal B))]
    (P : (factors (Ideal.span {f})).toFinset) :
    Module.Finite K
        (B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (factors (Ideal.span {f})))
      ∧ finrank K
          (B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (factors (Ideal.span {f})))
        = Multiset.count (P : Ideal B) (factors (Ideal.span {f}))
            * finrank K (B ⧸ (P : Ideal B)) := by
  obtain ⟨hPprime, hP0, -⟩ := prime_factor_span f P.2
  haveI := hPprime
  haveI : (P : Ideal B).IsMaximal := hPprime.isMaximal hP0
  haveI : IsDomain (Localization.AtPrime (P : Ideal B)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (P : Ideal B).primeCompl_le_nonZeroDivisors
  haveI := hfin P
  exact ⟨moduleFinite_quotient_pow_atPrime (S := Localization.AtPrime (P : Ideal B)) hP0 _,
    finrank_quotient_pow_atPrime (S := Localization.AtPrime (P : Ideal B)) hP0 _⟩

/-- **Finiteness of the Dedekind colength module**: for a nonzero `f` in a Dedekind domain
over `K` with `K`-finite residues at the prime factors of `(f)`, the quotient `B ⧸ (f)` is
a finite `K`-module.  (Via the landed Chinese-remainder decomposition
`quotAlgEquivPiFactors` and per-prime dévissage.) 


 * Provenance: CUSTOM.
-/
theorem moduleFinite_quotient_span {f : B} (hf : f ≠ 0)
    [∀ P : (factors (Ideal.span {f})).toFinset, Module.Finite K (B ⧸ (P : Ideal B))] :
    Module.Finite K (B ⧸ Ideal.span {f}) := by
  have hI : Ideal.span {f} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  haveI : ∀ P : (factors (Ideal.span {f})).toFinset,
      Module.Finite K
        (B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (factors (Ideal.span {f}))) :=
    fun P => (master_aux P).1
  exact Module.Finite.equiv (quotAlgEquivPiFactors (k := K) hI).toLinearEquiv.symm

/-- **The honest Dedekind colength formula** (SB-3b's algebra keystone; the generalization
of the landed `finrank_quotient_span_eq_sum_ord` with the false principality hypothesis
removed): for `f ≠ 0` in a Dedekind domain `B` over `K` with `K`-finite residues at the
prime factors,

`finrank K (B ⧸ (f)) = ∑_{P ∣ (f)} count P (factors (f)) * finrank K (B ⧸ P)`.

Each prime-power block collapses through the localization at `P` — a discrete valuation
ring — where the maximal ideal is principal. 


 * Provenance: CUSTOM.
-/
theorem finrank_quotient_span_eq_sum_count {f : B} (hf : f ≠ 0)
    [∀ P : (factors (Ideal.span {f})).toFinset, Module.Finite K (B ⧸ (P : Ideal B))] :
    finrank K (B ⧸ Ideal.span {f})
      = ∑ P : (factors (Ideal.span {f})).toFinset,
          Multiset.count (P : Ideal B) (factors (Ideal.span {f}))
            * finrank K (B ⧸ (P : Ideal B)) := by
  have hI : Ideal.span {f} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  haveI : ∀ P : (factors (Ideal.span {f})).toFinset,
      Module.Finite K
        (B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (factors (Ideal.span {f}))) :=
    fun P => (master_aux P).1
  rw [finrank_quotient_eq_sum_factors_pow hI]
  exact Finset.sum_congr rfl fun P _ => (master_aux P).2

end Master

end AlgebraicGeometry
