/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.ABRegularQuotient

/-!
# Regular local rings are domains (Stacks 00NP)

Seventh file of the Auslander–Buchsbaum package.

* `RingTheory.CohenMacaulay.isDomain_of_regularLocal` — every regular local
  Noetherian ring is an integral domain (Stacks tag 00NP; proof of 00NQ-style
  by induction on `spanFinrank 𝔪`). Mathlib at the pin does not expose this
  implication; this file is the gap-fill.

The proof is a strong induction on `spanFinrank 𝔪` (generalising the ring):
the base case `spanFinrank 𝔪 = 0` makes `R` a field; in the inductive step,
pick `x ∈ 𝔪 \ 𝔪²` (Nakayama), so `R/(x)` is regular local of one smaller
dimension (`ABRegularQuotient`), hence a domain by induction, hence `(x)` is
prime. Take a minimal prime `𝔭 ⊆ (x)`: if `x ∉ 𝔭`, then `𝔭 ⊆ x𝔭` and Nakayama
gives `𝔭 = ⊥`, so `R` is a domain; the case `x ∈ 𝔭` (i.e. `(x)` a minimal
prime) is refuted by re-running the argument with a fresh witness
`x' ∈ 𝔪 \ (𝔪² ∪ ⋃ minimalPrimes R)` obtained by prime avoidance.
-/

set_option autoImplicit false
-- The ported signatures keep the source's explicit `[IsLocalRing R]` /
-- `[IsNoetherianRing R]` binders alongside `[IsRegularLocalRing R]` (which
-- implies both); silence the overlapping-instances style linter rather than
-- churn the audited proofs.
set_option linter.overlappingInstances false

universe u v

open CategoryTheory

namespace RingTheory

namespace CohenMacaulay

/-! ### The base case: `spanFinrank 𝔪 = 0` makes `R` a field

For a Noetherian local ring `R` with `(maximalIdeal R).spanFinrank = 0`, the
ring `R` is a field, hence a domain. The maximal ideal collapses to `⊥` via
`Submodule.spanFinrank_eq_zero_iff_eq_bot` (under FG), and
`IsLocalRing.isField_iff_maximalIdeal_eq` upgrades the resulting field-by-
trivial-maximal-ideal characterisation to `IsField R`, from which
`IsField.isDomain` gives `IsDomain R`. -/
private lemma isDomain_of_isLocalRing_of_spanFinrank_maximalIdeal_eq_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : (IsLocalRing.maximalIdeal R).spanFinrank = 0) : IsDomain R := by
  have h𝔪_fg : (IsLocalRing.maximalIdeal R).FG :=
    Ideal.fg_of_isNoetherianRing _
  have h𝔪_bot : IsLocalRing.maximalIdeal R = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot h𝔪_fg).mp h
  have hField : IsField R :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mpr h𝔪_bot
  exact hField.isDomain

/-! ### Zero-divisor witness from a minimal prime

For a commutative ring `R` and a minimal prime `𝔭 ∈ minimalPrimes R`, every
element of `𝔭` is a zero-divisor in `R`. Concretely: for any `x ∈ 𝔭`, there
exists `y ∈ R, y ≠ 0` with `x * y = 0`.

Proof: minimal primes are disjoint from non-zero-divisors via
`Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes`, so `x ∈ 𝔭` ⟹
`x ∉ nonZeroDivisors R` ⟹ `∃ y ≠ 0, x * y = 0`. -/
private lemma exists_ne_zero_mul_eq_zero_of_mem_minimalPrimes
    {R : Type u} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭 ∈ minimalPrimes R)
    {x : R} (hx : x ∈ 𝔭) :
    ∃ y : R, y ≠ 0 ∧ x * y = 0 := by
  have hdisj : Disjoint (𝔭 : Set R) (nonZeroDivisors R : Set R) :=
    Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔭
  have hxNot : x ∉ nonZeroDivisors R := fun hxNZD =>
    (Set.disjoint_left.mp hdisj) hx hxNZD
  have hExistsZD : ¬ ∀ z, x * z = 0 → z = 0 := fun h => hxNot <| by
    rw [mem_nonZeroDivisors_iff]
    refine ⟨h, fun z hz => h z (by rw [mul_comm]; exact hz)⟩
  push Not at hExistsZD
  obtain ⟨y, hxy, hy⟩ := hExistsZD
  exact ⟨y, hy, hxy⟩

/-- **`(x)` is not a minimal prime in the regular-local inductive step.** For a
regular local Noetherian ring `R` of `spanFinrank 𝔪 = k + 1` and
`x ∈ 𝔪 \ 𝔪²`, the ideal `Ideal.span {x}` is *not* a minimal prime of `R`.

The strong-induction hypothesis `hIH` is taken as an explicit argument
(universally quantified over the ring `R'` at dimension `k`), so the lemma can
be invoked inside `isDomain_of_regularLocal`'s `succ` arm without requiring
`IsDomain R` (which is the goal being proved there). -/
private lemma notMem_minimalPrimes_of_regularLocal_succ
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsRegularLocalRing R] {k : ℕ}
    (hdim : (IsLocalRing.maximalIdeal R).spanFinrank = k + 1)
    (x : R) (hxMem : x ∈ IsLocalRing.maximalIdeal R)
    (hxNotSq : x ∉ (IsLocalRing.maximalIdeal R) ^ 2)
    (hIH : ∀ (R' : Type u) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
            [IsRegularLocalRing R'],
            (IsLocalRing.maximalIdeal R').spanFinrank = k → IsDomain R') :
    Ideal.span ({x} : Set R) ∉ minimalPrimes R := by
  intro hmin
  -- Step 1: x is a zero-divisor in R.
  have hxIn : x ∈ Ideal.span ({x} : Set R) :=
    Ideal.subset_span (Set.mem_singleton x)
  obtain ⟨y, hy_ne, hxy⟩ :=
    exists_ne_zero_mul_eq_zero_of_mem_minimalPrimes hmin hxIn
  -- Step 2: bring `R/(x)` into scope as a regular local ring of `spanFinrank = k`,
  -- and apply IH to obtain `IsDomain (R/(x))`.
  obtain ⟨hNT, hLR, hRLR, hdim_quot⟩ :=
    regularLocal_quotient_isRegularLocal_of_notMemSq hdim x hxMem hxNotSq
  haveI : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := hNT
  haveI : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) := hLR
  haveI : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := hRLR
  haveI hDomain_quot : IsDomain (R ⧸ Ideal.span ({x} : Set R)) :=
    hIH (R ⧸ Ideal.span ({x} : Set R)) hdim_quot
  -- Prime-avoidance route: use the IH-as-universal-quantifier-over-rings
  -- hypothesis to prove `IsDomain R` directly, then derive a contradiction
  -- from `(x) ∈ minimalPrimes R` + `x ∉ 𝔪²`.
  --
  -- Concretely: pick a *fresh* witness `x' ∈ 𝔪 \ (𝔪² ∪ ⋃ minimalPrimes R)`
  -- via prime avoidance (`Ideal.subset_union_prime_finite`).  Then:
  --   * `R/(x')` is regular local of `spanFinrank = k` via
  --     `regularLocal_quotient_isRegularLocal_of_notMemSq`,
  --   * `IsDomain (R/(x'))` via `hIH`,
  --   * `(x')` is prime,
  --   * a minimal prime `𝔭' ⊆ (x')` exists (`Ideal.exists_minimalPrimes_le`),
  --     and `x' ∉ 𝔭'` (since `x'` avoids all minimal primes), so for `y ∈ 𝔭'
  --     ⊆ (x')` we get `y = x' · z` with `z ∈ 𝔭'`, hence `𝔭' ⊆ x' · 𝔭' ⊆
  --     jacobson R · 𝔭'`,
  --   * Nakayama yields `𝔭' = ⊥`, so `⊥ ∈ minimalPrimes R` is prime, hence
  --     `IsDomain R`.
  -- In a domain, `(⊥ : Ideal R).minimalPrimes = {⊥}`, so `hmin` forces
  -- `Ideal.span {x} = ⊥`, hence `x = 0 ∈ 𝔪²`, contradicting `hxNotSq`.
  classical
  set 𝔪 : Ideal R := IsLocalRing.maximalIdeal R with h𝔪_def
  -- spanFinrank-positivity follows from hdim.
  have hpos : 0 < 𝔪.spanFinrank := by rw [h𝔪_def, hdim]; omega
  -- Step P1: enumerate the avoidance set `S = {𝔪²} ∪ minimalPrimes R`.
  have hMP_fin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  let S : Set (Ideal R) := insert (𝔪 ^ 2) (minimalPrimes R)
  have hS_fin : S.Finite := hMP_fin.insert _
  -- Step P2: each element of S other than `𝔪²` is prime.
  have hp : ∀ i ∈ S, i ≠ (𝔪 ^ 2) → i ≠ (𝔪 ^ 2) → i.IsPrime := by
    intro i hi h₁ _
    simp only [S, Set.mem_insert_iff] at hi
    rcases hi with hi | hi
    · exact absurd hi h₁
    · exact _root_.IsMinimalPrime.isPrime hi
  -- Step P3: `𝔪` is not contained in any element of `S`.
  have h_nle : ∀ i ∈ S, ¬ ((𝔪 : Set R) ⊆ (i : Set R)) := by
    intro i hi habs
    simp only [S, Set.mem_insert_iff] at hi
    rcases hi with rfl | hi
    · -- 𝔪 ⊆ 𝔪² contradicts hpos via `exists_notMemSq_of_spanFinrank_pos`.
      obtain ⟨x₀, hx₀Mem, hx₀NotSq⟩ := exists_notMemSq_of_spanFinrank_pos hpos
      exact hx₀NotSq (habs hx₀Mem)
    · -- i ∈ minimalPrimes R, 𝔪 ⊆ i ⟹ i = 𝔪 (since i ⊆ 𝔪 always), then 𝔪
      -- is a minimal prime ⟹ primeHeight 𝔪 = 0 ⟹ ringKrullDim R = 0,
      -- contradicting `IsRegularLocalRing.spanFinrank_maximalIdeal` + hdim.
      haveI hi_prime : i.IsPrime := _root_.IsMinimalPrime.isPrime hi
      have hi_eq : i = 𝔪 := by
        apply le_antisymm
        · exact IsLocalRing.le_maximalIdeal hi_prime.ne_top
        · exact habs
      have h_min : 𝔪 ∈ minimalPrimes R := hi_eq ▸ hi
      have h_ph_zero : 𝔪.height = 0 := Ideal.height_eq_zero_iff.mpr h_min
      have h_ph_dim : 𝔪.height = ringKrullDim R :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      have h_dim_zero : (ringKrullDim R : WithBot ℕ∞) = 0 :=
        h_ph_dim ▸ (h_ph_zero ▸ rfl)
      have h_dim_eq : (𝔪.spanFinrank : WithBot ℕ∞) = ringKrullDim R := by
        have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
        exact_mod_cast this
      have h_span_zero : 𝔪.spanFinrank = 0 := by
        have h := h_dim_eq.trans h_dim_zero
        exact_mod_cast h
      omega
  -- Step P4: apply prime avoidance to deduce `𝔪 ⊄ ⋃ S`.
  have h_not_subset : ¬ ((𝔪 : Set R) ⊆ ⋃ i ∈ S, (i : Set R)) := by
    intro habs
    obtain ⟨i, hi_S, hi_le⟩ :=
      (Ideal.subset_union_prime_finite (f := id) hS_fin (𝔪 ^ 2) (𝔪 ^ 2) hp).mp habs
    exact h_nle i hi_S hi_le
  -- Step P5: extract `x' ∈ 𝔪 \ ⋃ S`.
  obtain ⟨x', hx'Mem, hx'NotIn⟩ := Set.not_subset.mp h_not_subset
  have hx'NotSq : x' ∉ 𝔪 ^ 2 := by
    intro h
    refine hx'NotIn ?_
    exact Set.mem_biUnion (Set.mem_insert _ _) h
  have hx'NotMinPrime : ∀ 𝔭 ∈ minimalPrimes R, x' ∉ 𝔭 := by
    intro 𝔭 h𝔭 hx𝔭
    refine hx'NotIn ?_
    exact Set.mem_biUnion (Set.mem_insert_of_mem _ h𝔭) hx𝔭
  -- Step P6: `R/(x')` is regular local of `spanFinrank = k`, hence a domain
  -- by `hIH`. Then `(x')` is prime.
  obtain ⟨hNT', hLR', hRLR', hdim_quot'⟩ :=
    regularLocal_quotient_isRegularLocal_of_notMemSq hdim x' hx'Mem hx'NotSq
  haveI : Nontrivial (R ⧸ Ideal.span ({x'} : Set R)) := hNT'
  haveI : IsLocalRing (R ⧸ Ideal.span ({x'} : Set R)) := hLR'
  haveI : IsRegularLocalRing (R ⧸ Ideal.span ({x'} : Set R)) := hRLR'
  haveI hDomain_quot' : IsDomain (R ⧸ Ideal.span ({x'} : Set R)) :=
    hIH (R ⧸ Ideal.span ({x'} : Set R)) hdim_quot'
  haveI hPrime_x' : (Ideal.span ({x'} : Set R)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hDomain_quot'
  -- Step P7: pick a minimal prime `𝔭' ⊆ (x')`; since `x'` avoids minimal
  -- primes, `x' ∉ 𝔭'`.
  obtain ⟨𝔭', h𝔭'_min, h𝔭'_le⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal R)) (J := Ideal.span ({x'} : Set R)) bot_le
  haveI h𝔭'_prime : 𝔭'.IsPrime := _root_.IsMinimalPrime.isPrime h𝔭'_min
  have hx'_notIn_𝔭' : x' ∉ 𝔭' := hx'NotMinPrime _ h𝔭'_min
  -- Step P8: `𝔭' ⊆ jacobson R · 𝔭'` via the standard `y = x' · z` step.
  have h𝔭'_sub_smul :
      (𝔭' : Submodule R R) ≤ Ring.jacobson R • (𝔭' : Submodule R R) := by
    intro y hy
    have hy_in_x' : y ∈ Ideal.span ({x'} : Set R) := h𝔭'_le hy
    rw [Ideal.mem_span_singleton] at hy_in_x'
    obtain ⟨z, rfl⟩ := hy_in_x'
    have hz_in : z ∈ 𝔭' := by
      rcases h𝔭'_prime.mem_or_mem hy with hx'_in | hz_in
      · exact absurd hx'_in hx'_notIn_𝔭'
      · exact hz_in
    have hx'Jac : x' ∈ Ring.jacobson R := by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact hx'Mem
    have hsmul := Submodule.smul_mem_smul (I := Ring.jacobson R)
      (N := (𝔭' : Submodule R R)) hx'Jac hz_in
    simpa [smul_eq_mul] using hsmul
  -- Step P9: by Nakayama `𝔭' = ⊥`, hence `⊥` is prime, hence `IsDomain R`.
  have h𝔭'_fg : (𝔭' : Submodule R R).FG := Ideal.fg_of_isNoetherianRing _
  have h𝔭'_bot_sub : (𝔭' : Submodule R R) = ⊥ :=
    Submodule.FG.eq_bot_of_le_jacobson_smul h𝔭'_fg h𝔭'_sub_smul
  have h𝔭'_bot : 𝔭' = (⊥ : Ideal R) := by
    ext z
    constructor
    · intro hz
      exact h𝔭'_bot_sub.le hz
    · rintro (rfl : z = 0)
      exact 𝔭'.zero_mem
  haveI h_bot_prime : (⊥ : Ideal R).IsPrime := h𝔭'_bot ▸ h𝔭'_prime
  haveI hDomain_R : IsDomain R := IsDomain.of_bot_isPrime R
  -- Step P10: in a domain, `(⊥ : Ideal R).minimalPrimes = {⊥}`, so `hmin`
  -- forces `Ideal.span {x} = ⊥`, hence `x = 0`, contradicting `hxNotSq`.
  have h_minP_singleton : minimalPrimes R = {(⊥ : Ideal R)} := by
    change (⊥ : Ideal R).minimalPrimes = _
    exact Ideal.minimalPrimes_eq_subsingleton_self
  have hx_min_eq_bot : Ideal.span ({x} : Set R) = (⊥ : Ideal R) := by
    rw [h_minP_singleton] at hmin
    exact hmin
  have hx_eq_zero : x = 0 := by
    have hx_in_bot : x ∈ (⊥ : Ideal R) := by
      rw [← hx_min_eq_bot]
      exact Ideal.subset_span (Set.mem_singleton x)
    exact (Submodule.mem_bot _).mp hx_in_bot
  apply hxNotSq
  rw [hx_eq_zero]
  exact zero_mem _

/-- **Regular local Noetherian rings are domains** (Stacks tag 00NP). Every
regular local Noetherian ring is an integral domain.

This is the consumer-facing implication needed to close
`exists_isRegular_of_regularLocal` (and through it `CohenMacaulay.of_regular`).

The body is a strong induction on `spanFinrank 𝔪 R`:

* Base case `n = 0` → `isDomain_of_isLocalRing_of_spanFinrank_maximalIdeal_eq_zero`
  (𝔪 collapses to `⊥`, `R` is a field, hence a domain).
* Inductive step `n = k + 1`: pick `x ∈ 𝔪 \ 𝔪²` via
  `exists_notMemSq_of_spanFinrank_pos`; then `R/(x)` is regular local of
  `spanFinrank = k` (`regularLocal_quotient_isRegularLocal_of_notMemSq`), hence
  a domain by the IH, hence `(x)` is prime. Take a minimal prime `𝔭 ⊆ (x)`:
  the `x ∉ 𝔭` branch closes via `𝔭 ⊆ x·𝔭` + Nakayama (`𝔭 = ⊥`, so `⊥` is
  prime); the `x ∈ 𝔭` branch is refuted by
  `notMem_minimalPrimes_of_regularLocal_succ`. 






 * Provenance: REFERENCE.
-/
lemma isDomain_of_regularLocal
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsRegularLocalRing R] : IsDomain R := by
  -- Strong induction on `spanFinrank 𝔪`, generalising `R` so the IH applies
  -- to the quotient `R/(x)` at smaller dim.
  suffices haux : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R]
      [IsNoetherianRing R] [IsRegularLocalRing R],
      (IsLocalRing.maximalIdeal R).spanFinrank = n → IsDomain R by
    exact haux _ R rfl
  intro n
  induction n with
  | zero =>
    intros R _ _ _ _ hdim
    exact isDomain_of_isLocalRing_of_spanFinrank_maximalIdeal_eq_zero hdim
  | succ k ih =>
    intros R _ _ _ _ hdim
    -- Step 1: pick `x ∈ 𝔪 \ 𝔪²` via Nakayama.
    have hpos : 0 < (IsLocalRing.maximalIdeal R).spanFinrank := by omega
    obtain ⟨x, hxMem, hxNotSq⟩ := exists_notMemSq_of_spanFinrank_pos hpos
    -- Step 2: instances + IsRegularLocalRing on R/(x) via the axiom-clean helper.
    obtain ⟨hNT, hLR, hRLR, hdim_quot⟩ :=
      regularLocal_quotient_isRegularLocal_of_notMemSq hdim x hxMem hxNotSq
    -- Step 3: IH on R/(x) at spanFinrank = k.
    have hDomain_R' : IsDomain (R ⧸ Ideal.span ({x} : Set R)) :=
      ih (R ⧸ Ideal.span ({x} : Set R)) hdim_quot
    -- Step 4: (x) is prime in R (R/(x) is a domain).
    haveI hPrime_x : (Ideal.span ({x} : Set R)).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp hDomain_R'
    -- Step 5: pick minimal prime 𝔭 ≤ (x).
    obtain ⟨𝔭, h𝔭_min, h𝔭_le⟩ := Ideal.exists_minimalPrimes_le
      (I := (⊥ : Ideal R)) (J := Ideal.span ({x} : Set R)) bot_le
    haveI h𝔭_prime : 𝔭.IsPrime := _root_.IsMinimalPrime.isPrime h𝔭_min
    -- Step 6: case split on x ∈ 𝔭 vs x ∉ 𝔭.
    by_cases hxIn : x ∈ 𝔭
    · -- Case `x ∈ 𝔭`: then `𝔭 = (x)` is a minimal prime of `R`, which
      -- `notMem_minimalPrimes_of_regularLocal_succ` refutes.
      have h𝔭_eq : 𝔭 = Ideal.span ({x} : Set R) := by
        apply le_antisymm h𝔭_le
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hxIn
      have hmin : Ideal.span ({x} : Set R) ∈ minimalPrimes R := h𝔭_eq ▸ h𝔭_min
      exact absurd hmin
        (notMem_minimalPrimes_of_regularLocal_succ R hdim x hxMem hxNotSq
          (fun R' _ _ _ _ h => ih R' h))
    · -- Case `x ∉ 𝔭`: `𝔭 ⊆ 𝔪·𝔭` by the `y = x·z, z ∈ 𝔭` argument; Nakayama
      -- (`Submodule.FG.eq_bot_of_le_jacobson_smul`) gives `𝔭 = ⊥`, so `(0)`
      -- is a prime ideal of `R`, hence `IsDomain R`.
      have h𝔭_sub_smul : (𝔭 : Submodule R R) ≤
          Ring.jacobson R • (𝔭 : Submodule R R) := by
        intro y hy
        -- y ∈ 𝔭 ≤ (x), so x | y, so y = x*z for some z.
        have hy_in_x : y ∈ Ideal.span ({x} : Set R) := h𝔭_le hy
        rw [Ideal.mem_span_singleton] at hy_in_x
        obtain ⟨z, rfl⟩ := hy_in_x
        -- Goal: x * z ∈ jacobson R • 𝔭. We have y = x * z ∈ 𝔭 prime, x ∉ 𝔭,
        -- so z ∈ 𝔭.
        have hz_in : z ∈ 𝔭 := by
          rcases h𝔭_prime.mem_or_mem hy with hx_in | hz_in
          · exact absurd hx_in hxIn
          · exact hz_in
        have hxJac : x ∈ Ring.jacobson R := by
          rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
          exact hxMem
        have hsmul := Submodule.smul_mem_smul (I := Ring.jacobson R)
          (N := (𝔭 : Submodule R R)) hxJac hz_in
        -- hsmul : x • z ∈ jacobson R • 𝔭. Goal: x * z ∈ jacobson R • 𝔭.
        -- These are equal since x • z = x * z (smul = mul for R-module R).
        simpa [smul_eq_mul] using hsmul
      have h𝔭_fg : (𝔭 : Submodule R R).FG := Ideal.fg_of_isNoetherianRing _
      have h𝔭_bot_sub : (𝔭 : Submodule R R) = ⊥ :=
        Submodule.FG.eq_bot_of_le_jacobson_smul h𝔭_fg h𝔭_sub_smul
      have h𝔭_bot : 𝔭 = (⊥ : Ideal R) := by
        ext y
        constructor
        · intro hy
          have hy' : y ∈ (⊥ : Submodule R R) := h𝔭_bot_sub.le hy
          exact hy'
        · rintro (rfl : y = 0)
          exact 𝔭.zero_mem
      haveI h_bot_prime : (⊥ : Ideal R).IsPrime := h𝔭_bot ▸ h𝔭_prime
      exact IsDomain.of_bot_isPrime R

end CohenMacaulay

end RingTheory
