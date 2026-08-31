/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.AuslanderBuchsbaum

/-!
# Cohen–Macaulay equidimensionality: Ischebeck's bound and (K) at height one

The pure-algebra brick of Milne Lemma 3.3, substep 4b-transport
(`informal/m33-spec.md` D7). Main results, for a Noetherian local ring
`(R, 𝔪)`:

* `RingTheory.Module.depth_le_coheight_of_isAssociatedPrime` —
  **Ischebeck's bound** (consumer form, Stacks 00LK): for a finite nontrivial
  `R`-module `M` and `p ∈ Ass M`, `depth M ≤ coheight p (= dim R/p)`.
  The proof is Ext-free: induction on `n ≤ depth M` through the `p`-torsion
  submodule `T` — for an `M`-regular `x ∈ 𝔪` one has `T ∩ xM = xT`, so
  Nakayama produces `t ∈ T ∖ xM` whose class in `M/xM` is a nonzero
  `(p + x)`-torsion element; any associated prime `q ⊇ ann(t̄)` of `M/xM`
  then satisfies `p < q`, and `depth(M/xM) ≥ depth M − 1` closes the
  induction.
* `RingTheory.CohenMacaulay.coheight_eq_ringKrullDim_of_isAssociatedPrime`,
  `…ringKrullDim_quotient_eq_of_isAssociatedPrime` — **CM unmixedness**:
  over a Cohen–Macaulay local ring, every associated prime `p` of `R` has
  `dim R/p = dim R`; hence (`…mem_minimalPrimes_of_isAssociatedPrime`)
  `Ass R = Min R`.
* `RingTheory.CohenMacaulay.ringKrullDim_quotient_add_one_of_height_eq_one` —
  **(K) at height one**: in a Cohen–Macaulay local ring, a prime of height 1
  has `dim R/p + 1 = dim R`. Route (spec D7, the only case the 4b-transport
  consumes): prime avoidance against the finitely many (minimal, by
  unmixedness) associated primes yields a nonzerodivisor `y ∈ p ∩ 𝔪`; `p` is
  minimal over `(y) = ann(R/y)`, so `p ∈ Ass_R(R/y)` and Ischebeck applied to
  the **module** `R/y` gives `dim R ≤ coheight p + 1`; the converse
  inequality is `coheight` strict antitonicity below a minimal prime.
  **No ring change and no chain surgery** are needed.

Supporting API: `Module.maximalIdeal_smul_top_ne_top`,
`Module.nontrivial_quotSMulTop_of_mem_maximalIdeal`,
`Module.exists_isSMulRegular_of_one_le_depth`,
`Module.depth_le_depth_quotSMulTop_add_one` (via the landed
`depth_of_short_exact`), and the dimension bridge
`ringKrullDim_quotient_eq_coheight`.

Blueprint reference: `lem:milne_codim1_indeterminacy` (Milne, *Abelian
Varieties* §I.3 Lemma 3.3; Matsumura, *Commutative ring theory* §17).
-/

set_option autoImplicit false

universe u v

open IsLocalRing Pointwise

namespace RingTheory

namespace Module

/-! ## §1. Depth via regular sequences: the sSup toolkit -/

/-- Unfold `Module.depth` on the substantive branch. -/
private lemma depth_eq_sSup_of_ne_top {R : Type u} [CommRing R] {I : Ideal R}
    {M : Type v} [AddCommGroup M] [Module R M]
    (h : I • (⊤ : Submodule R M) ≠ ⊤) :
    Module.depth I M = sSup { n : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = n ∧
      (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs } := by
  unfold Module.depth
  rw [if_neg h]

/-- **Nakayama, top-smul form**: over a local ring, `𝔪M ≠ M` for a finite
nontrivial module. -/
lemma maximalIdeal_smul_top_ne_top {R : Type u} [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
  intro h
  have hbot : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) ⊤
      ((Module.finite_def (R := R) (M := M)).mp inferInstance) h.symm.le
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  exact hm (by simpa using hbot.le (Submodule.mem_top (x := m)))

/-- The quotient `M/xM` of a finite nontrivial module by `x ∈ 𝔪` is
nontrivial (Nakayama). -/
lemma nontrivial_quotSMulTop_of_mem_maximalIdeal {R : Type u} [CommRing R]
    [IsLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] :
    Nontrivial (QuotSMulTop x M) := by
  rcases subsingleton_or_nontrivial (QuotSMulTop x M) with hsub | hnt
  · exfalso
    have htop : x • (⊤ : Submodule R M) = ⊤ :=
      Submodule.Quotient.subsingleton_iff.mp hsub
    refine maximalIdeal_smul_top_ne_top (R := R) M (le_antisymm le_top ?_)
    calc (⊤ : Submodule R M) = x • ⊤ := htop.symm
      _ ≤ IsLocalRing.maximalIdeal R • ⊤ := by
          rintro u hu
          obtain ⟨v, -, rfl⟩ :=
            (Submodule.mem_smul_pointwise_iff_exists u x ⊤).mp hu
          exact Submodule.smul_mem_smul hx Submodule.mem_top
  · exact hnt

/-- Extract an `M`-regular element of `𝔪` from `1 ≤ depth M`. -/
lemma exists_isSMulRegular_of_one_le_depth {R : Type u} [CommRing R]
    [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M]
    (h : (1 : ℕ∞) ≤ Module.depth (IsLocalRing.maximalIdeal R) M) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, IsSMulRegular M x := by
  rw [depth_eq_sSup_of_ne_top (maximalIdeal_smul_top_ne_top M)] at h
  by_contra hcon
  push Not at hcon
  -- every regular sequence in `𝔪` is empty, so the supremum is `0 < 1`
  have hzero : ∀ n ∈ { n : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = n ∧
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular M rs }, n ≤ 0 := by
    rintro n ⟨rs, rfl, hmem, hreg⟩
    match rs with
    | [] => simp
    | x :: tl =>
      exfalso
      obtain ⟨hxreg, -⟩ := (RingTheory.Sequence.isRegular_cons_iff M x tl).mp hreg
      exact hcon x (hmem x (List.mem_cons_self)) hxreg
  exact absurd (h.trans (sSup_le hzero)) (by simp)

/-- **Depth drop, upper bound**: for an `M`-regular `x ∈ 𝔪`,
`depth M ≤ depth (M/xM) + 1` — the second inequality of
`depth_of_short_exact` on `0 → M → M → M/xM → 0`. -/
lemma depth_le_depth_quotSMulTop_add_one {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {M : Type u} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Nontrivial M] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) :
    Module.depth (IsLocalRing.maximalIdeal R) M
      ≤ Module.depth (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 := by
  haveI : Nontrivial (QuotSMulTop x M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal hx M
  have hexact : Function.Exact (LinearMap.lsmul R M x)
      (x • (⊤ : Submodule R M)).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
    ext u
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply]
    exact ⟨fun hu => by
        obtain ⟨v, -, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists u x ⊤).mp hu
        exact ⟨v, hv⟩,
      fun ⟨v, hv⟩ => (Submodule.mem_smul_pointwise_iff_exists u x ⊤).mpr
        ⟨v, trivial, hv⟩⟩
  have hses := depth_of_short_exact (LinearMap.lsmul R M x)
    (x • (⊤ : Submodule R M)).mkQ hreg (Submodule.mkQ_surjective _) hexact
  have h2 := hses.2.1
  rw [min_le_iff] at h2
  rcases h2 with h2 | h2
  · exact h2.trans le_self_add
  · exact tsub_le_iff_right.mp h2

/-! ## §2. Ischebeck's bound (consumer form, Ext-free) -/

/-- Induction core for Ischebeck's bound: `n ≤ depth M ⟹ n ≤ coheight p`
for `p ∈ Ass M`. -/
private theorem natCast_le_coheight_of_isAssociatedPrime_of_le_depth
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] {p : Ideal R} (hp : IsAssociatedPrime p M)
    (hn : (n : ℕ∞) ≤ Module.depth (IsLocalRing.maximalIdeal R) M) :
    (n : ℕ∞) ≤ Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) := by
  induction n generalizing M p with
  | zero => simp
  | succ n ih =>
    -- unpack the associated prime as an annihilator
    obtain ⟨hprime, m, hmeq⟩ := isAssociatedPrime_iff.mp hp
    have hm0 : m ≠ 0 := by
      rintro rfl
      refine hprime.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_)
      rw [hmeq, Submodule.mem_colon_singleton]
      simp
    -- an `M`-regular element `x ∈ 𝔪`
    obtain ⟨x, hx𝔪, hxreg⟩ := exists_isSMulRegular_of_one_le_depth
      (le_trans (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n))
        hn)
    have hxp : x ∉ p := by
      intro hxp
      have hx' : x • m = 0 := by
        rw [hmeq, Submodule.mem_colon_singleton] at hxp
        simpa using hxp
      exact hm0 (hxreg (by simp [hx']))
    -- the `p`-torsion submodule
    set T : Submodule R M := Submodule.torsionBySet R M ↑p with hTdef
    have hmT : m ∈ T := by
      rw [hTdef, Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      have ha' : a ∈ p := ha
      rw [hmeq, Submodule.mem_colon_singleton] at ha'
      simpa using ha'
    -- Nakayama through `T ∩ xM = xT`: some `t ∈ T` survives modulo `xM`
    have hTx : ¬ T ≤ x • (⊤ : Submodule R M) := by
      intro hle
      have hsub : T ≤ IsLocalRing.maximalIdeal R • T := by
        intro u hu
        obtain ⟨v, -, rfl⟩ :=
          (Submodule.mem_smul_pointwise_iff_exists u x ⊤).mp (hle hu)
        have hvT : v ∈ T := by
          rw [hTdef, Submodule.mem_torsionBySet_iff] at hu ⊢
          rintro ⟨a, ha⟩
          have h1 := hu ⟨a, ha⟩
          have h2 : x • ((⟨a, ha⟩ : (↑p : Set R)) : R) • v = 0 := by
            rw [smul_comm]
            simpa using h1
          exact hxreg (by simpa using h2)
        exact Submodule.smul_mem_smul hx𝔪 hvT
      have hTbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
        (IsLocalRing.maximalIdeal R) T (IsNoetherian.noetherian T) hsub
        (IsLocalRing.maximalIdeal_le_jacobson ⊥)
      rw [hTbot] at hmT
      exact hm0 (by simpa using hmT)
    obtain ⟨t, htT, htx⟩ := SetLike.not_le_iff_exists.mp hTx
    -- its class in `M/xM` is a nonzero `(p + x)`-torsion element
    have htb : (x • (⊤ : Submodule R M)).mkQ t ≠ 0 := by
      rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    haveI : Module.Finite R (QuotSMulTop x M) :=
      Module.Finite.of_surjective (x • (⊤ : Submodule R M)).mkQ
        (Submodule.mkQ_surjective _)
    haveI : Nontrivial (QuotSMulTop x M) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal hx𝔪 M
    obtain ⟨q, hq, hcolon⟩ :=
      exists_le_isAssociatedPrime_of_isNoetherianRing R _ htb
    -- `p < q`
    have hpq : p ≤ q := by
      refine le_trans ?_ hcolon
      intro a ha
      have hat : a • t = 0 := by
        rw [hTdef, Submodule.mem_torsionBySet_iff] at htT
        simpa using htT ⟨a, ha⟩
      rw [Submodule.mem_colon_singleton, ← map_smul, hat, map_zero]
      exact Submodule.zero_mem ⊥
    have hxq : x ∈ q := by
      refine hcolon ?_
      have hxt : x • t ∈ x • (⊤ : Submodule R M) :=
        (Submodule.mem_smul_pointwise_iff_exists _ x ⊤).mpr ⟨t, trivial, rfl⟩
      rw [Submodule.mem_colon_singleton, ← map_smul, Submodule.mkQ_apply,
        Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact hxt
    have hlt : p < q := lt_of_le_of_ne hpq fun h => hxp (h ▸ hxq)
    -- induction at `M/xM`, `q`
    have hdepthQ : (n : ℕ∞) ≤
        Module.depth (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) := by
      have hstep := depth_le_depth_quotSMulTop_add_one hx𝔪 hxreg
      have hcast : ((n : ℕ∞) + 1) ≤
          Module.depth (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 := by
        refine le_trans ?_ hstep
        exact_mod_cast hn
      exact (WithTop.add_le_add_iff_right WithTop.one_ne_top).mp hcast
    have hIH := ih hq hdepthQ
    -- one strict specialisation step in `Spec R`
    have hcoh : Order.coheight (⟨q, hq.isPrime⟩ : PrimeSpectrum R) + 1
        ≤ Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) :=
      Order.coheight_add_one_le (by exact_mod_cast hlt)
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ Order.coheight (⟨q, hq.isPrime⟩ : PrimeSpectrum R) + 1 := by gcongr
      _ ≤ Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) := hcoh

/-- **Ischebeck's bound, consumer form** (Stacks 00LK): for a finite
nontrivial module `M` over a Noetherian local ring and an associated prime
`p ∈ Ass M`, the depth of `M` is at most the coheight of `p` in `Spec R`
(that is, `dim R/p`; see `ringKrullDim_quotient_eq_coheight`). -/
theorem depth_le_coheight_of_isAssociatedPrime
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] {p : Ideal R} (hp : IsAssociatedPrime p M) :
    Module.depth (IsLocalRing.maximalIdeal R) M
      ≤ Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) := by
  rw [← ENat.forall_natCast_le_iff_le]
  intro n hn
  exact natCast_le_coheight_of_isAssociatedPrime_of_le_depth n hp hn

end Module

/-! ## §3. The dimension bridge: `dim R/p = coheight p` -/

/-- The Krull dimension of `R/p` is the coheight of `p` in `Spec R`:
`Spec (R/p)` is order-isomorphic to the closed set `V(p) = Ici p`. -/
lemma _root_.ringKrullDim_quotient_eq_coheight {R : Type u} [CommRing R]
    (p : Ideal R) [hp : p.IsPrime] :
    ringKrullDim (R ⧸ p) =
      (Order.coheight (⟨p, hp⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
  have hset : (PrimeSpectrum.zeroLocus (R := R) ↑p) =
      Set.Ici (⟨p, hp⟩ : PrimeSpectrum R) := by
    ext q
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  have e : PrimeSpectrum (R ⧸ p) ≃o Set.Ici (⟨p, hp⟩ : PrimeSpectrum R) :=
    (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p).trans
      (OrderIso.setCongr _ _ hset)
  calc ringKrullDim (R ⧸ p) = Order.krullDim (PrimeSpectrum (R ⧸ p)) := rfl
    _ = Order.krullDim (Set.Ici (⟨p, hp⟩ : PrimeSpectrum R)) :=
        Order.krullDim_eq_of_orderIso e
    _ = (Order.coheight (⟨p, hp⟩ : PrimeSpectrum R) : WithBot ℕ∞) :=
        (Order.coheight_eq_krullDim_Ici _).symm

/-! ## §4. Cohen–Macaulay: unmixedness and (K) at height one -/

namespace CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **CM unmixedness, coheight form**: over a Cohen–Macaulay local ring,
every associated prime of `R` has coheight equal to `dim R`. -/
theorem coheight_eq_ringKrullDim_of_isAssociatedPrime [CohenMacaulay R]
    {p : Ideal R} (hp : IsAssociatedPrime p R) :
    (Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) : WithBot ℕ∞)
      = ringKrullDim R := by
  refine le_antisymm (Order.coheight_le_krullDim _) ?_
  calc ringKrullDim R
      = (Module.depth (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) :=
        (CohenMacaulay.depth_eq_krullDim).symm
    _ ≤ (Order.coheight (⟨p, hp.isPrime⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
        exact_mod_cast Module.depth_le_coheight_of_isAssociatedPrime hp

/-- **CM unmixedness, quotient-dimension form**: `dim R/p = dim R` for every
associated prime `p` of a Cohen–Macaulay local ring. -/
theorem ringKrullDim_quotient_eq_of_isAssociatedPrime [CohenMacaulay R]
    {p : Ideal R} (hp : IsAssociatedPrime p R) :
    ringKrullDim (R ⧸ p) = ringKrullDim R := by
  haveI := hp.isPrime
  rw [ringKrullDim_quotient_eq_coheight p]
  exact coheight_eq_ringKrullDim_of_isAssociatedPrime hp

/-- Over a Cohen–Macaulay local ring, every associated prime of `R` is a
minimal prime: a strictly smaller prime would push the coheight above
`dim R`. -/
theorem mem_minimalPrimes_of_isAssociatedPrime [CohenMacaulay R]
    {q : Ideal R} (hq : IsAssociatedPrime q R) : q ∈ minimalPrimes R := by
  haveI := hq.isPrime
  by_contra hqm
  obtain ⟨q₀, hq₀min, hq₀le⟩ := Ideal.exists_minimalPrimes_le (bot_le (a := q))
  haveI : q₀.IsPrime := hq₀min.1.1
  have hlt : q₀ < q := hq₀le.lt_of_ne fun h => hqm (h ▸ hq₀min)
  have hstep : Order.coheight (⟨q, hq.isPrime⟩ : PrimeSpectrum R) + 1
      ≤ Order.coheight (⟨q₀, ‹q₀.IsPrime›⟩ : PrimeSpectrum R) :=
    Order.coheight_add_one_le (by exact_mod_cast hlt)
  have hbase := coheight_eq_ringKrullDim_of_isAssociatedPrime hq
  have hcap : (Order.coheight (⟨q₀, ‹q₀.IsPrime›⟩ : PrimeSpectrum R)
      : WithBot ℕ∞) ≤ ringKrullDim R := Order.coheight_le_krullDim _
  have hne_top : Order.coheight (⟨q, hq.isPrime⟩ : PrimeSpectrum R) ≠ ⊤ := by
    intro h
    apply ringKrullDim_ne_top (R := R)
    rw [← hbase, h]
    rfl
  have hle : Order.coheight (⟨q₀, ‹q₀.IsPrime›⟩ : PrimeSpectrum R)
      ≤ Order.coheight (⟨q, hq.isPrime⟩ : PrimeSpectrum R) := by
    have h := hcap.trans_eq hbase.symm
    exact_mod_cast h
  exact lt_irrefl _ ((ENat.add_one_le_iff hne_top).mp (hstep.trans hle))

/-- **(K) at height one** (spec D7, the case consumed by the 4b-transport):
in a Cohen–Macaulay local ring, a prime `p` of height 1 satisfies
`dim R/p + 1 = dim R`. -/
theorem ringKrullDim_quotient_add_one_of_height_eq_one [CohenMacaulay R]
    {p : Ideal R} [hpr : p.IsPrime] (hht : p.height = 1) :
    ringKrullDim (R ⧸ p) + 1 = ringKrullDim R := by
  rw [ringKrullDim_quotient_eq_coheight p]
  refine le_antisymm ?_ ?_
  · -- `coheight p + 1 ≤ dim R`: `p` is not minimal, so it strictly contains
    -- a minimal prime.
    have hpnotmin : p ∉ minimalPrimes R := by
      intro hmin
      have h0 := Ideal.height_eq_zero_iff.mpr hmin
      rw [hht] at h0
      exact one_ne_zero h0
    obtain ⟨q₀, hq₀min, hq₀le⟩ := Ideal.exists_minimalPrimes_le (bot_le (a := p))
    haveI : q₀.IsPrime := hq₀min.1.1
    have hlt : q₀ < p := hq₀le.lt_of_ne fun h => hpnotmin (h ▸ hq₀min)
    have hstep : Order.coheight (⟨p, hpr⟩ : PrimeSpectrum R) + 1
        ≤ Order.coheight (⟨q₀, ‹q₀.IsPrime›⟩ : PrimeSpectrum R) :=
      Order.coheight_add_one_le (by exact_mod_cast hlt)
    calc (Order.coheight (⟨p, hpr⟩ : PrimeSpectrum R) : WithBot ℕ∞) + 1
        = ((Order.coheight (⟨p, hpr⟩ : PrimeSpectrum R) + 1 : ℕ∞)
            : WithBot ℕ∞) := by norm_cast
      _ ≤ (Order.coheight (⟨q₀, ‹q₀.IsPrime›⟩ : PrimeSpectrum R)
            : WithBot ℕ∞) := by exact_mod_cast hstep
      _ ≤ ringKrullDim R := Order.coheight_le_krullDim _
  · -- `dim R ≤ coheight p + 1` through Ischebeck at the module `R/(y)`.
    -- Step 1: prime avoidance — a nonzerodivisor `y ∈ p`.
    have hAssFin := associatedPrimes.finite R R
    have hnotsub : ¬ (p : Set R) ⊆ ⋃ q ∈ associatedPrimes R R, (q : Set R) := by
      intro hsub
      have hsub' : (p : Set R) ⊆ ⋃ q ∈ hAssFin.toFinset, (q : Set R) := by
        intro a ha
        have := hsub ha
        simp only [Set.mem_iUnion] at this ⊢
        obtain ⟨q, hqm, hq⟩ := this
        exact ⟨q, hAssFin.mem_toFinset.mpr hqm, hq⟩
      have hex := (Ideal.subset_union_prime (⊥ : Ideal R) (⊥ : Ideal R)
        (fun q hqm _ _ =>
          (AssociatedPrimes.mem_iff.mp (hAssFin.mem_toFinset.mp hqm)).isPrime)).mp
        hsub'
      obtain ⟨q, hqmem, hpq⟩ := hex
      have hqass : IsAssociatedPrime q R :=
        AssociatedPrimes.mem_iff.mp (hAssFin.mem_toFinset.mp hqmem)
      -- `q` is minimal, so `p ≤ q` forces `p = q`, of height 0 ≠ 1
      haveI := hqass.isPrime
      have hqmin := mem_minimalPrimes_of_isAssociatedPrime hqass
      have hqp : q ≤ p := hqmin.2 ⟨hpr, bot_le⟩ hpq
      have heq : p = q := le_antisymm hpq hqp
      have hzero := Ideal.height_eq_zero_iff.mpr hqmin
      rw [← heq, hht] at hzero
      exact one_ne_zero hzero
    obtain ⟨y, hyp, hyunion⟩ := Set.not_subset.mp hnotsub
    have hyNZD : y ∈ nonZeroDivisors R := by
      by_contra hy
      refine hyunion ?_
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors R]
      exact hy
    have hy𝔪 : y ∈ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hpr.ne_top hyp
    -- Step 2: `p` is minimal over `(y)`.
    have hspan_ne_top : Ideal.span ({y} : Set R) ≠ ⊤ :=
      Ideal.span_singleton_ne_top fun hu =>
        IsLocalRing.notMem_maximalIdeal.mpr hu hy𝔪
    have hpmin : p ∈ (Ideal.span ({y} : Set R)).minimalPrimes := by
      constructor
      · exact ⟨hpr, (Ideal.span_singleton_le_iff_mem p).mpr hyp⟩
      · rintro q ⟨hqpr, hyq⟩ hqp
        haveI : q.IsPrime := hqpr
        -- `q` contains the nonzerodivisor `y`, so it is not minimal in `R`
        have hqnotmin : q ∉ minimalPrimes R := by
          intro hqmin
          have hann : Module.annihilator R R = ⊥ := by
            refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
            simpa using Module.mem_annihilator.mp ha 1
          have hqass : q ∈ associatedPrimes R R :=
            Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
              R R (by rwa [hann])
          have hyzd : y ∈ ⋃ q' ∈ associatedPrimes R R, (q' : Set R) :=
            Set.mem_biUnion hqass (hyq (Ideal.mem_span_singleton_self y))
          rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors R] at hyzd
          exact hyzd hyNZD
        have hq1 : 1 ≤ q.height := by
          rcases eq_or_ne q.height 0 with h0 | h0
          · exact absurd (Ideal.height_eq_zero_iff.mp h0) hqnotmin
          · exact Order.one_le_iff_ne_zero.mpr h0
        -- `q < p` would force `ht p ≥ 2`
        rcases eq_or_lt_of_le hqp with heq | hlt2
        · exact heq.ge
        · exfalso
          have hh := Ideal.height_add_one_le_of_lt_of_isPrime hlt2
          rw [hht] at hh
          have h0 : q.height ≤ 0 := by
            have h1' : q.height + 1 ≤ 0 + 1 := by simpa using hh
            exact (WithTop.add_le_add_iff_right WithTop.one_ne_top).mp h1'
          have hcontra := hq1.trans h0
          norm_num at hcontra
    -- Step 3: `p ∈ Ass_R (R/(y))` and Ischebeck.
    haveI : Module.Finite R (R ⧸ Ideal.span ({y} : Set R)) :=
      Module.Finite.of_surjective
        (Ideal.span ({y} : Set R)).mkQ (Submodule.mkQ_surjective _)
    haveI : Nontrivial (R ⧸ Ideal.span ({y} : Set R)) :=
      Ideal.Quotient.nontrivial_iff.mpr hspan_ne_top
    have hpass : IsAssociatedPrime p (R ⧸ Ideal.span ({y} : Set R)) := by
      refine AssociatedPrimes.mem_iff.mp
        (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
          R (R ⧸ Ideal.span ({y} : Set R)) ?_)
      rwa [Ideal.annihilator_quotient]
    have hIsch := Module.depth_le_coheight_of_isAssociatedPrime hpass
    -- Step 4: `depth_R (R/(y)) ≥ depth R − 1 = dim R − 1`.
    have hyreg : IsSMulRegular R y :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors hyNZD
    have hdrop := Module.depth_le_depth_quotSMulTop_add_one hy𝔪 hyreg (M := R)
    have hspan_smul : Ideal.span ({y} : Set R) = y • (⊤ : Ideal R) := by
      simp [← Submodule.ideal_span_singleton_smul]
    have htransport : Module.depth (IsLocalRing.maximalIdeal R)
        (QuotSMulTop y R) = Module.depth (IsLocalRing.maximalIdeal R)
          (R ⧸ Ideal.span ({y} : Set R)) :=
      Module.depth_eq_of_linearEquiv _
        (Submodule.quotEquivOfEq _ _ hspan_smul.symm)
    rw [htransport] at hdrop
    -- Step 5: assemble in `WithBot ℕ∞`.
    have hfinal : Module.depth (IsLocalRing.maximalIdeal R)
        (R ⧸ Ideal.span ({y} : Set R)) + 1
        ≤ Order.coheight (⟨p, hpr⟩ : PrimeSpectrum R) + 1 := by gcongr
    calc ringKrullDim R
        = (Module.depth (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) :=
          (CohenMacaulay.depth_eq_krullDim).symm
      _ ≤ ((Module.depth (IsLocalRing.maximalIdeal R)
            (R ⧸ Ideal.span ({y} : Set R)) + 1 : ℕ∞) : WithBot ℕ∞) := by
          exact_mod_cast hdrop
      _ ≤ ((Order.coheight (⟨p, hpr⟩ : PrimeSpectrum R) + 1 : ℕ∞)
            : WithBot ℕ∞) := by exact_mod_cast hfinal
      _ = (Order.coheight (⟨p, hpr⟩ : PrimeSpectrum R) : WithBot ℕ∞) + 1 := by
          norm_cast

end CohenMacaulay

end RingTheory
