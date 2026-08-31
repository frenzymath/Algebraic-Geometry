/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Algebra.ABRegularCM

/-!
# Pole-divisor purity: the commutative-algebra layer

This file proves the ring-theoretic core of the **purity of the polar locus**
of a function-field element (the scheme-level wrapper is
`Albanese/PolePurity.lean`): in a Noetherian domain `R` all of whose
localizations at primes are regular, if `b ≠ 0` and the denominator ideal
`((b) : a)` is contained in a prime `𝔭`, then some prime `𝔮 ≤ 𝔭` of height
exactly `1` still contains `((b) : a)`:

* `exists_height_one_prime_colon_le`.

Geometrically: if `a/b` is not regular at `𝔭`, it already has a pole along a
codimension-one prime through `𝔭`.

## Mathematical route (deliberately avoiding Serre / Auslander–Buchsbaum UFD)

The classical proof runs through "regular ⟹ normal ⟹ Krull-domain
intersection `R = ⋂_{ht 𝔭 = 1} R_𝔭`". Neither "regular local ⟹ UFD"
(Auslander–Buchsbaum) nor Serre's normality criterion is available in Mathlib
at v4.31.0, and both are heavy builds. Instead we use a completely elementary
chain:

1. **Swap lemma** (`mem_span_singleton_of_swap_pair`): in a domain, if `u, v`
   is a "swap pair" (`u ≠ 0` and `v` is regular modulo `u`) and both
   `u * x ∈ (b)` and `v * x ∈ (b)`, then `x ∈ (b)`. Pure `dvd` arithmetic:
   from `u x = b s`, `v x = b t` one gets `b (u t - v s) = 0`, hence
   `u t = v s`, hence `u ∣ s`, hence `x ∈ (b)`. This replaces the
   determinant-trick/integral-closedness step of the classical argument.
2. **Swap pairs exist** in a regular local ring of dimension `≥ 2`
   (`IsRegularLocalRing.exists_swap_pair_of_two_le_ringKrullDim`): take
   `u ∈ 𝔪 ∖ 𝔪²`; then `R/(u)` is again regular local of positive dimension
   (project lemma `regularLocal_quotient_isRegularLocal_of_notMemSq` in
   `Algebra/ABRegularQuotient.lean`), hence a domain by Stacks 00NP (project
   lemma `isDomain_of_regularLocal` in `Algebra/ABRegularDomain.lean`), and
   any `v ∈ 𝔪` with `v ∉ (u)` is regular modulo `u`.
3. **Height bound** (`Ideal.height_le_one_of_colon_span_singleton`): if a
   prime `Q` of a Noetherian domain is the annihilator `((b) : y)` of a
   nonzero element of `A/(b)` (`b ≠ 0`) and `A_Q` is regular, then
   `ht Q ≤ 1`. Otherwise `dim A_Q ≥ 2` yields a swap pair inside the maximal
   ideal `𝔪_Q = ((b) : y) A_Q`, and the swap lemma forces `y ∈ (b) A_Q`,
   contradicting properness of the colon. (This is the elementary form of
   "principal ideals are unmixed in a normal domain", localized so that only
   regularity of the *one* local ring `A_Q` enters.)
4. **Main ring theorem** (`exists_height_one_prime_colon_le`): for `b ≠ 0`
   with denominator ideal `((b) : a) ≤ 𝔭`, there is a prime `𝔮 ≤ 𝔭` of
   height exactly `1` with `((b) : a) ≤ 𝔮`. Run the associated-prime
   existence theorem for `A/(b)` over the localization `A = R_𝔭` (so that
   the produced prime automatically sits below `𝔭`), apply step 3 there,
   and descend heights along `IsLocalization.height_under`.

The fraction-field translation (step 5, "regular at a point" =
"the denominator ideal avoids the corresponding prime") and the scheme-level
wrapper live in `Albanese/PolePurity.lean`.

Blueprint reference: `lem:pole_divisor_purity` (feeding
`lem:milne_codim1_indeterminacy`; Milne, *Abelian Varieties*, §I.3 p. 17,
and Hartshorne, *Algebraic Geometry*, II.6.3A / AG 9.2 for the classical
normality route this replaces).
-/

set_option autoImplicit false
-- Carried in-file (inbox I-0161): the lakefile sets `maxSynthPendingDepth 3`
-- but `lake env lean` does not apply lakefile leanOptions; without it the
-- `Algebra.smul_def` rewrite in `exists_height_one_prime_colon_le`'s colon
-- bridge matches the wrong `•` occurrence.
set_option maxSynthPendingDepth 3

universe u

open IsLocalRing

/-! ## §1. The swap lemma

The elementary replacement for the determinant trick: a length-two "regular
sequence style" pair transports membership in a principal ideal across a
colon. Only domain arithmetic is used. -/

/-- **Swap lemma.** In a domain, let `u ≠ 0` and let `v` be regular modulo
`(u)` (i.e. `v * s ∈ (u) → s ∈ (u)`). If both `u * x` and `v * x` lie in
`(b)`, then `x ∈ (b)`.

Proof: write `u * x = b * s`, `v * x = b * t`. Then
`b * (u * t) = u * (v * x) = v * (u * x) = b * (v * s)`, so (cancelling `b`;
the case `b = 0` is immediate from `u ≠ 0`) `u * t = v * s`, hence
`v * s ∈ (u)`, hence `s = u * s'`, hence `u * x = b * u * s'` and cancelling
`u` gives `x = b * s' ∈ (b)`. -/
theorem mem_span_singleton_of_swap_pair {A : Type*} [CommRing A] [IsDomain A]
    {u v b x : A} (hu : u ≠ 0)
    (hv : ∀ s : A, v * s ∈ Ideal.span ({u} : Set A) → s ∈ Ideal.span ({u} : Set A))
    (hux : u * x ∈ Ideal.span ({b} : Set A))
    (hvx : v * x ∈ Ideal.span ({b} : Set A)) :
    x ∈ Ideal.span ({b} : Set A) := by
  rw [Ideal.mem_span_singleton] at hux hvx ⊢
  obtain ⟨s, hs⟩ := hux
  obtain ⟨t, ht⟩ := hvx
  rcases eq_or_ne b 0 with rfl | hb
  · -- `b = 0`: then `u * x = 0` and `u ≠ 0` force `x = 0`.
    rw [zero_mul] at hs
    rcases mul_eq_zero.mp hs with h | h
    · exact absurd h hu
    · simp [h]
  · -- `b ≠ 0`: cancel `b` in `b * (u * t) = b * (v * s)`.
    have hbut : b * (u * t) = b * (v * s) := by
      calc b * (u * t) = u * (b * t) := by ring
        _ = u * (v * x) := by rw [← ht]
        _ = v * (u * x) := by ring
        _ = v * (b * s) := by rw [← hs]
        _ = b * (v * s) := by ring
    have hut : u * t = v * s := mul_left_cancel₀ hb hbut
    -- `v * s ∈ (u)`, so `s ∈ (u)`.
    obtain ⟨s', hs'⟩ := Ideal.mem_span_singleton.mp
      (hv s (Ideal.mem_span_singleton.mpr ⟨t, hut.symm⟩))
    -- cancel `u` in `u * x = b * (u * s')`.
    refine ⟨s', mul_left_cancel₀ hu ?_⟩
    calc u * x = b * s := hs
      _ = b * (u * s') := by rw [hs']
      _ = u * (b * s') := by ring

/-! ## §2. Swap pairs exist in a regular local ring of dimension `≥ 2`

We combine the project's Stacks 00NP assets from the Auslander–Buchsbaum
package (`Algebra/ABRegularQuotient.lean`, `Algebra/ABRegularDomain.lean`):

* `RingTheory.CohenMacaulay.regularLocal_quotient_isRegularLocal_of_notMemSq`
  (`R/(u)` is regular local of one lower `spanFinrank` for `u ∈ 𝔪 ∖ 𝔪²`);
* `RingTheory.CohenMacaulay.isDomain_of_regularLocal` (Stacks 00NP: a
  regular local ring is a domain);
* `RingTheory.CohenMacaulay.exists_notMemSq_of_spanFinrank_pos` (Nakayama
  witness: an element of `𝔪 ∖ 𝔪²` exists when `spanFinrank 𝔪 > 0`). -/

/-- **Swap pairs exist in a regular local ring of Krull dimension `≥ 2`.**
There are `u, v ∈ 𝔪` with `u ≠ 0` and `v` regular modulo `(u)`.

Take `u ∈ 𝔪 ∖ 𝔪²`; then `R/(u)` is regular local with
`spanFinrank 𝔪' = spanFinrank 𝔪 - 1 ≥ 1` (project Stacks 00NU prep lemma),
hence a nontrivial domain by Stacks 00NP with `𝔪' ≠ ⊥`; any lift `v ∈ 𝔪` of
a nonzero `v̄ ∈ 𝔪'` is regular modulo `(u)` because `A/(u)` is a domain. -/
theorem IsRegularLocalRing.exists_swap_pair_of_two_le_ringKrullDim
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (h2 : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    ∃ u v : A, u ∈ maximalIdeal A ∧ v ∈ maximalIdeal A ∧ u ≠ 0 ∧
      ∀ s : A, v * s ∈ Ideal.span ({u} : Set A) → s ∈ Ideal.span ({u} : Set A) := by
  -- `spanFinrank 𝔪 = ringKrullDim A ≥ 2`.
  have hspan : 2 ≤ (maximalIdeal A).spanFinrank := by
    have heq := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [← heq] at h2
    exact_mod_cast h2
  obtain ⟨u, huMem, huSq⟩ :=
    RingTheory.CohenMacaulay.exists_notMemSq_of_spanFinrank_pos (R := A) (by omega)
  obtain ⟨hNT, hLR, hRLR, hdimq⟩ :=
    RingTheory.CohenMacaulay.regularLocal_quotient_isRegularLocal_of_notMemSq
      (R := A) (k := (maximalIdeal A).spanFinrank - 1) (by omega) u huMem huSq
  haveI := hNT; haveI := hLR; haveI := hRLR
  haveI : IsDomain (A ⧸ Ideal.span ({u} : Set A)) :=
    RingTheory.CohenMacaulay.isDomain_of_regularLocal _
  -- the quotient's maximal ideal is nonzero since its `spanFinrank` is `≥ 1`.
  have hmq_ne_bot : maximalIdeal (A ⧸ Ideal.span ({u} : Set A)) ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.spanFinrank_bot] at hdimq
    omega
  obtain ⟨vbar, hvbarMem, hvbar0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmq_ne_bot
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective vbar
  refine ⟨u, v, huMem, ?_, fun h0 => huSq (h0 ▸ (Ideal.zero_mem _ : (0 : A) ∈ _)), ?_⟩
  · -- `v ∈ 𝔪`: a unit `v` would map to a unit, contradicting membership in `𝔪'`.
    by_contra hvNot
    have hvUnit : IsUnit v := by
      by_contra hnu
      exact hvNot (fun h => hnu h)
    exact (IsLocalRing.notMem_maximalIdeal.mpr (hvUnit.map _)) hvbarMem
  · -- regularity of `v` modulo `(u)`: `A/(u)` is a domain and `v̄ ≠ 0`.
    intro s hs
    have hmul : (Ideal.Quotient.mk (Ideal.span ({u} : Set A)) v)
        * (Ideal.Quotient.mk (Ideal.span ({u} : Set A)) s) = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hs
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hvbar0
    · exact Ideal.Quotient.eq_zero_iff_mem.mp h

/-! ## §3. Height bound for colon primes of principal ideals

If a prime `Q` of a Noetherian domain equals `((b) : y)` with `b ≠ 0` and the
localization `A_Q` is a regular local ring, then `ht Q ≤ 1` — the elementary
substitute for "associated primes of principal ideals in a normal domain have
height one". -/

/-- Descend divisibility along a localization with injective structure map:
`algebraMap a ∈ (algebraMap b)` upstairs yields `s * a ∈ (b)` downstairs for
some `s` in the inverted submonoid. -/
private lemma exists_smul_mem_span_of_algebraMap_mem_span
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    (hinj : Function.Injective (algebraMap R A))
    {a b : R} (h : algebraMap R A a ∈ Ideal.span ({algebraMap R A b} : Set A)) :
    ∃ s ∈ M, s * a ∈ Ideal.span ({b} : Set R) := by
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp h
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.mk'_surjective M c'
  refine ⟨s, s.2, Ideal.mem_span_singleton.mpr ⟨c, hinj ?_⟩⟩
  have hspec : IsLocalization.mk' A c s * algebraMap R A s = algebraMap R A c :=
    IsLocalization.mk'_spec A c s
  calc algebraMap R A ((s : R) * a)
      = algebraMap R A s * algebraMap R A a := by rw [map_mul]
    _ = algebraMap R A s * (algebraMap R A b * c') := by rw [hc']
    _ = algebraMap R A b * (IsLocalization.mk' A c s * algebraMap R A s) := by
        rw [← hcs]; ring
    _ = algebraMap R A b * algebraMap R A c := by rw [hspec]
    _ = algebraMap R A (b * c) := by rw [map_mul]

/-- **Height bound for colon primes of principal ideals.** Let `A` be a
Noetherian domain and let the prime `Q = ((b) : y)` be the annihilator of
`y mod (b)`. If `A_Q` is a regular local ring then `ht Q ≤ 1`.

If `ht Q ≥ 2` then `dim A_Q ≥ 2`, so `A_Q` contains a swap pair `u, v` inside
its maximal ideal `𝔪_Q`. But `𝔪_Q = ((b) : y) A_Q` is again a colon:
`𝔪_Q = ((b/1) : (y/1))` in `A_Q`. Hence `u * (y/1), v * (y/1) ∈ (b/1)` and the
swap lemma gives `y/1 ∈ (b/1)`, i.e. `((b/1) : (y/1)) = ⊤ = 𝔪_Q`,
a contradiction. -/
theorem Ideal.height_le_one_of_colon_span_singleton
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {b y : A} {Q : Ideal A} [hQp : Q.IsPrime]
    (hQ : Q = (Ideal.span ({b} : Set A)).colon {y})
    (hreg : IsRegularLocalRing (Localization.AtPrime Q)) :
    Q.height ≤ 1 := by
  by_contra hgt
  -- `2 ≤ ht Q`, hence `2 ≤ ringKrullDim A_Q`.
  have h2 : (2 : ℕ∞) ≤ Q.height := by
    have h1 : (1 : ℕ∞) < Q.height := lt_of_not_ge hgt
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ Q.height := Order.add_one_le_of_lt h1
  have h2dim : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime Q) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)]
    simpa using WithBot.coe_le_coe.mpr h2
  haveI := hreg
  haveI : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_localization Q.primeCompl_le_nonZeroDivisors
  obtain ⟨u, v, huMem, hvMem, hu0, hv⟩ :=
    IsRegularLocalRing.exists_swap_pair_of_two_le_ringKrullDim
      (A := Localization.AtPrime Q) h2dim
  set φ := algebraMap A (Localization.AtPrime Q) with hφ
  have hinj : Function.Injective φ :=
    IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors
  -- `y/1 ∉ (b/1)`: otherwise some `s ∉ Q` has `s * y ∈ (b)`, i.e. `s ∈ Q`.
  have hy' : φ y ∉ Ideal.span ({φ b} : Set (Localization.AtPrime Q)) := by
    intro hmem
    obtain ⟨s, hsM, hsy⟩ :=
      exists_smul_mem_span_of_algebraMap_mem_span Q.primeCompl hinj hmem
    refine hsM (hQ ▸ Submodule.mem_colon_singleton.mpr ?_)
    rw [smul_eq_mul]
    exact hsy
  -- the maximal ideal of `A_Q` is the colon `((b/1) : (y/1))`.
  have hm_eq : maximalIdeal (Localization.AtPrime Q)
      = (Ideal.span ({φ b} : Set (Localization.AtPrime Q))).colon {φ y} := by
    apply le_antisymm
    · -- `𝔪_Q = Q.map φ ≤ colon`.
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      have hry : r • y ∈ Ideal.span ({b} : Set A) :=
        Submodule.mem_colon_singleton.mp (hQ ▸ hr)
      rw [smul_eq_mul] at hry
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hry
      refine Ideal.mem_comap.mpr (Submodule.mem_colon_singleton.mpr ?_)
      have : φ r * φ y = φ b * φ d := by rw [← map_mul, ← map_mul, hd]
      rw [smul_eq_mul, this]
      exact Ideal.mem_span_singleton.mpr ⟨φ d, rfl⟩
    · -- the colon is proper, hence contained in the maximal ideal.
      apply IsLocalRing.le_maximalIdeal
      intro htop
      have h1 : (1 : Localization.AtPrime Q) ∈
          (Ideal.span ({φ b} : Set (Localization.AtPrime Q))).colon {φ y} := by
        rw [htop]; trivial
      have h2' := Submodule.mem_colon_singleton.mp h1
      rw [smul_eq_mul, one_mul] at h2'
      exact hy' h2'
  -- swap lemma: `y/1 ∈ (b/1)`, contradiction.
  refine hy' (mem_span_singleton_of_swap_pair hu0 hv ?_ ?_)
  · have hmm := Submodule.mem_colon_singleton.mp (hm_eq ▸ huMem)
    rwa [smul_eq_mul] at hmm
  · have hmm := Submodule.mem_colon_singleton.mp (hm_eq ▸ hvMem)
    rwa [smul_eq_mul] at hmm

/-! ## §4. The main ring theorem -/

/-- **Existence of a height-one pole prime.** Let `R` be a Noetherian domain
whose localizations at primes are all regular. If `b ≠ 0` and the denominator
ideal `((b) : a)` is contained in a prime `𝔭`, then there is a prime
`𝔮 ≤ 𝔭` of height exactly `1` still containing `((b) : a)`.

(Geometrically: if `a/b` is not regular at `𝔭`, it already has a pole along a
codimension-one prime through `𝔭`.) -/
theorem exists_height_one_prime_colon_le
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hreg : ∀ (q : Ideal R) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q))
    {a b : R} (hb : b ≠ 0) {p : Ideal R} [hp : p.IsPrime]
    (hle : (Ideal.span ({b} : Set R)).colon {a} ≤ p) :
    ∃ q : Ideal R, q.IsPrime ∧ q.height = 1 ∧ q ≤ p ∧
      (Ideal.span ({b} : Set R)).colon {a} ≤ q := by
  -- Work over `A := R_𝔭` so the associated prime automatically sits below `𝔭`.
  set A := Localization.AtPrime p with hA
  haveI : IsDomain A :=
    IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing A :=
    IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  set φ := algebraMap R A with hφ
  have hinj : Function.Injective φ :=
    IsLocalization.injective A p.primeCompl_le_nonZeroDivisors
  have hb' : φ b ≠ 0 := fun h => hb (hinj (by simpa using h))
  -- `a/1 ∉ (b/1)`, i.e. `a mod (b/1)` is a nonzero element of `A ⧸ (b/1)`.
  have ha' : φ a ∉ Ideal.span ({φ b} : Set A) := by
    intro hmem
    obtain ⟨s, hsM, hsa⟩ :=
      exists_smul_mem_span_of_algebraMap_mem_span p.primeCompl hinj hmem
    refine hsM (hle (Submodule.mem_colon_singleton.mpr ?_))
    rw [smul_eq_mul]
    exact hsa
  have hxne : (Ideal.Quotient.mk (Ideal.span ({φ b} : Set A)) (φ a)) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact ha'
  -- associated prime `Q ⊇ Ann(a mod (b/1))`.
  obtain ⟨Q, hQass, hQge⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing
      (R := A) (Ideal.Quotient.mk (Ideal.span ({φ b} : Set A)) (φ a)) hxne
  haveI hQp : Q.IsPrime := hQass.isPrime
  -- colon bridge in the quotient module: `Ann(x mod I) = (I : x)`.
  have colon_bridge : ∀ x : A,
      (⊥ : Submodule A (A ⧸ Ideal.span ({φ b} : Set A))).colon
          {Ideal.Quotient.mk (Ideal.span ({φ b} : Set A)) x}
        = (Ideal.span ({φ b} : Set A)).colon {x} := by
    intro x
    ext r
    rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton,
      Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
  -- `Q` is itself a colon `((b/1) : y)` of a single element.
  obtain ⟨-, ybar, hQeq0⟩ := isAssociatedPrime_iff.mp hQass
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  have hQeq : Q = (Ideal.span ({φ b} : Set A)).colon {y} := by
    rw [hQeq0, colon_bridge]
  -- regularity of `A_Q` transported from `R_{𝔮}` with `𝔮 = Q ∩ R`.
  haveI hqcomap : (Q.comap (algebraMap R (Localization p.primeCompl))).IsPrime :=
    Ideal.IsPrime.comap _
  haveI : IsRegularLocalRing
      (Localization.AtPrime (Q.comap (algebraMap R (Localization p.primeCompl)))) :=
    hreg _
  have hregQ : IsRegularLocalRing (Localization.AtPrime Q) :=
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        p.primeCompl Q).toRingEquiv
  -- height bound and lower bound.
  have hht_le : Q.height ≤ 1 :=
    Ideal.height_le_one_of_colon_span_singleton hQeq hregQ
  have hbQ : φ b ∈ Q := by
    rw [hQeq]
    refine Submodule.mem_colon_singleton.mpr ?_
    rw [smul_eq_mul]
    exact Ideal.mem_span_singleton.mpr ⟨y, rfl⟩
  have hQ_ne_bot : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hbQ
    exact hb' hbQ
  have hht_ge : 1 ≤ Q.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff]
    intro hmin
    exact hQ_ne_bot (le_bot_iff.mp (hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le))
  have hQht : Q.height = 1 := le_antisymm hht_le hht_ge
  -- descend to `𝔮 := Q ∩ R`.
  refine ⟨Q.under R, hqcomap, ?_, ?_, ?_⟩
  · -- `ht 𝔮 = ht Q = 1` via `IsLocalization.height_under`.
    rw [IsLocalization.height_under p.primeCompl (A := A) Q]
    exact hQht
  · -- `𝔮 ≤ 𝔭` since `Q ≤ 𝔪_A` and `𝔪_A ∩ R = 𝔭`.
    intro r hr
    have hrm : algebraMap R A r ∈ maximalIdeal A :=
      IsLocalRing.le_maximalIdeal hQp.ne_top (Ideal.mem_comap.mp hr)
    have hmem : r ∈ (maximalIdeal A).under R := Ideal.mem_comap.mpr hrm
    have hmp : (maximalIdeal A).under R = p := Localization.AtPrime.under_maximalIdeal
    rwa [hmp] at hmem
  · -- `((b) : a) ≤ 𝔮`.
    intro r hr
    have hra : r • a ∈ Ideal.span ({b} : Set R) := Submodule.mem_colon_singleton.mp hr
    rw [smul_eq_mul] at hra
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hra
    have hmemcolon : φ r ∈ (Ideal.span ({φ b} : Set A)).colon {φ a} := by
      refine Submodule.mem_colon_singleton.mpr ?_
      have heq : φ r * φ a = φ b * φ d := by rw [← map_mul, ← map_mul, hd]
      rw [smul_eq_mul, heq]
      exact Ideal.mem_span_singleton.mpr ⟨φ d, rfl⟩
    refine Ideal.mem_comap.mpr (hQge ?_)
    rw [colon_bridge]
    exact hmemcolon
