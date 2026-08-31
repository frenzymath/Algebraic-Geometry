/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.FunctionField
import AlgebraicJacobian.Albanese.AuslanderBuchsbaum
import AlgebraicJacobian.Albanese.CoheightBridge

/-!
# Pole-divisor purity on a locally Noetherian integral scheme with regular stalks

This file proves the **purity of the polar locus** of a function-field element:
on a locally Noetherian integral scheme `X` all of whose stalks are regular
local rings (e.g. a scheme smooth over a field, via
`isRegularLocalRing_stalk_of_smooth`), an element `h ∈ K(X)` that is *not*
regular at a point `P` (i.e. `h` is not in the image of `𝒪_{X,P} → K(X)`)
fails to be regular already at some *codimension-one* generisation `z ⤳ P`:

* `AlgebraicGeometry.Scheme.exists_specializes_coheight_eq_one_of_notMem_stalk_range`.

This is the scheme-level "pole divisors are pure codimension 1" input to
Milne's *Abelian Varieties* §I.3 Lemma 3.3 (Substep 4 of the plan recorded at
`indeterminacy_pure_codim_one_into_grpScheme` in
`Albanese/CodimOneExtension.lean`): the polar locus of each pulled-back
regular function on the smooth variety `X × X` is pure codim 1 through every
of its points, in exactly the "specialises from a coheight-1 point of the
locus" form needed by the Lemma 3.3 disjunct.

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
   (project lemma `regularLocal_quotient_isRegularLocal_of_notMemSq`), hence
   a domain by Stacks 00NP (project lemma `isDomain_of_regularLocal`), and
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
5. **Scheme wrapper**: choose an affine open `U ∋ P`, identify
   `𝒪_{X,P} = Γ(U)_𝔭` and `K(X) = Frac Γ(U)`, translate "regular at a
   point" into "the denominator ideal is not contained in the corresponding
   prime" (`div_mem_range_algebraMap_iff`), and convert the height-1 prime
   back into a point `z ⤳ P` with `Order.coheight z = 1` via
   `IsAffineOpen.fromSpec` and the project's coheight bridge
   (`ringKrullDim_stalk_eq_coheight`).

Blueprint reference: `lem:pole_divisor_purity` (feeding
`lem:milne_codim1_indeterminacy`; Milne, *Abelian Varieties*, §I.3 p. 17,
and Hartshorne, *Algebraic Geometry*, II.6.3A / AG 9.2 for the classical
normality route this replaces).
-/

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

We combine the project's Stacks 00NP assets from
`Albanese/AuslanderBuchsbaum.lean`:

* `RingTheory.CohenMacaulay.regularLocal_quotient_isRegularLocal_of_notMemSq`
  (`R/(u)` is regular local of one lower `spanFinrank` for `u ∈ 𝔪 ∖ 𝔪²`);
* `RingTheory.CohenMacaulay.isDomain_of_regularLocal` (Stacks 00NP: a
  regular local ring is a domain). -/

/-- Nakayama witness: a Noetherian local ring with `spanFinrank 𝔪 > 0` has an
element of `𝔪 ∖ 𝔪²`. (Public replica of the `private` helper
`exists_notMemSq_of_spanFinrank_pos` in `Albanese/AuslanderBuchsbaum.lean`.) -/
private lemma exists_mem_notMemSq_of_spanFinrank_pos
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : 0 < (maximalIdeal R).spanFinrank) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 := by
  by_contra h_neg
  push Not at h_neg
  have h_le_sq : maximalIdeal R ≤ (maximalIdeal R) ^ 2 := h_neg
  have hsq : (maximalIdeal R : Submodule R R) ^ 2
      = (maximalIdeal R) • (maximalIdeal R : Submodule R R) := by
    rw [sq, ← Ideal.smul_eq_mul]
  have hfg : (maximalIdeal R : Submodule R R).FG := Ideal.fg_of_isNoetherianRing _
  have hjac : maximalIdeal R ≤ (⊥ : Ideal R).jacobson :=
    IsLocalRing.maximalIdeal_le_jacobson _
  have h_le_smul : (maximalIdeal R : Submodule R R)
      ≤ ⊥ ⊔ (maximalIdeal R) • (maximalIdeal R : Submodule R R) := by
    rw [bot_sup_eq, ← hsq]; exact h_le_sq
  have h_bot : (maximalIdeal R : Submodule R R) ≤ ⊥ :=
    Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac h_le_smul
  have h_eq_bot : maximalIdeal R = ⊥ := le_bot_iff.mp h_bot
  have h_span : (maximalIdeal R).spanFinrank = 0 := by
    rw [h_eq_bot]; exact Submodule.spanFinrank_bot
  omega

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
  obtain ⟨u, huMem, huSq⟩ := exists_mem_notMemSq_of_spanFinrank_pos (R := A) (by omega)
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

/-! ## §5. Fraction-field membership as a colon condition -/

/-- Over a localization `S = R_𝔮` sitting inside the fraction field `K` of a
domain `R`, the fraction `a / b` (with `b ≠ 0`) lies in the image of `S → K`
iff the denominator ideal `((b) : a)` is *not* contained in `𝔮`. -/
private lemma div_mem_range_algebraMap_iff
    {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K]
    (S : Type*) [CommRing S] [Algebra R S] [Algebra S K] [IsScalarTower R S K]
    {q : Ideal R} [hq : q.IsPrime] [IsLocalization.AtPrime S q]
    {a b : R} (hb : b ≠ 0) :
    algebraMap R K a / algebraMap R K b ∈ (algebraMap S K).range ↔
      ¬ ((Ideal.span ({b} : Set R)).colon {a} ≤ q) := by
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hbK : algebraMap R K b ≠ 0 := fun h => hb (hinjK (by simpa using h))
  constructor
  · rintro ⟨g, hg⟩ hcolon
    obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.mk'_surjective q.primeCompl g
    replace hcs : IsLocalization.mk' S c s = g := hcs
    -- push `mk'_spec` down to `K` along the scalar tower.
    have hspec : algebraMap S K g * algebraMap R K (s : R) = algebraMap R K c := by
      have h0 : IsLocalization.mk' S c s * algebraMap R S (s : R) = algebraMap R S c :=
        IsLocalization.mk'_spec S c s
      have h1 := congrArg (algebraMap S K) h0
      rw [map_mul, hcs] at h1
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    -- `g * b = a` in `K`.
    have hg' : algebraMap S K g * algebraMap R K b = algebraMap R K a := by
      rw [hg, div_mul_cancel₀ _ hbK]
    -- `s * a = b * c` in `R`.
    have hKey : algebraMap R K ((s : R) * a) = algebraMap R K (b * c) := by
      rw [map_mul, map_mul, ← hg', ← hspec]
      ring
    have hcross : (s : R) * a = b * c := hinjK hKey
    have hsColon : (s : R) ∈ (Ideal.span ({b} : Set R)).colon {a} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      exact Ideal.mem_span_singleton.mpr ⟨c, hcross⟩
    exact s.2 (hcolon hsColon)
  · intro hnot
    obtain ⟨s, hsColon, hsq⟩ := SetLike.not_le_iff_exists.mp hnot
    have hs0 : s ≠ 0 := fun h => hsq (h ▸ q.zero_mem)
    have hsa : s • a ∈ Ideal.span ({b} : Set R) := Submodule.mem_colon_singleton.mp hsColon
    rw [smul_eq_mul] at hsa
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hsa
    have hsq' : s ∈ q.primeCompl := hsq
    refine ⟨IsLocalization.mk' S c ⟨s, hsq'⟩, ?_⟩
    have hspec : algebraMap S K (IsLocalization.mk' S c ⟨s, hsq'⟩)
        * algebraMap R K s = algebraMap R K c := by
      have h0 : IsLocalization.mk' S c ⟨s, hsq'⟩ * algebraMap R S s = algebraMap R S c :=
        IsLocalization.mk'_spec S c ⟨s, hsq'⟩
      have h1 := congrArg (algebraMap S K) h0
      rw [map_mul] at h1
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    have hsK : algebraMap R K s ≠ 0 := fun h => hs0 (hinjK (by simpa using h))
    have hcb : c * b = a * s := by
      rw [mul_comm c b, ← hc]
      exact mul_comm _ _
    rw [eq_div_iff hbK]
    apply mul_right_cancel₀ hsK
    calc algebraMap S K (IsLocalization.mk' S c ⟨s, hsq'⟩) * algebraMap R K b
          * algebraMap R K s
        = (algebraMap S K (IsLocalization.mk' S c ⟨s, hsq'⟩) * algebraMap R K s)
          * algebraMap R K b := by ring
      _ = algebraMap R K c * algebraMap R K b := by rw [hspec]
      _ = algebraMap R K (c * b) := by rw [map_mul]
      _ = algebraMap R K (a * s) := by rw [hcb]
      _ = algebraMap R K a * algebraMap R K s := by rw [map_mul]

/-! ## §6. The scheme-level pole-divisor purity theorem -/

namespace AlgebraicGeometry

open TopologicalSpace

/-- **Pole-divisor purity.** Let `X` be a locally Noetherian integral scheme
all of whose stalks are regular local rings (e.g. `X` smooth over a field).
If `h ∈ K(X)` is not regular at a point `P` — i.e. `h` does not lie in the
image of `𝒪_{X,P} → K(X)` — then `h` is already non-regular at some
codimension-one point `z` specialising to `P`:

`∃ z, z ⤳ P ∧ coheight z = 1 ∧ h ∉ im (𝒪_{X,z} → K(X))`.

In particular the polar locus `{x | h ∉ im (𝒪_{X,x} → K(X))}` of a
function-field element is of *pure codimension one* in the "every point
specialises from a coheight-one point of the locus" sense — exactly the shape
of the Milne Lemma 3.3 disjunct (`indeterminacy_pure_codim_one_into_grpScheme`
in `Albanese/CodimOneExtension.lean`).

Blueprint reference: `lem:pole_divisor_purity` (Hartshorne II.6.3A;
Milne, *Abelian Varieties*, §I.3 p. 17). -/
theorem Scheme.exists_specializes_coheight_eq_one_of_notMem_stalk_range
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (P : X) (h : X.functionField)
    (hP : h ∉ (algebraMap (X.presheaf.stalk P) X.functionField).range) :
    ∃ z : X, z ⤳ P ∧ Order.coheight z = 1 ∧
      h ∉ (algebraMap (X.presheaf.stalk z) X.functionField).range := by
  -- Choose an affine chart `U ∋ P` and set `R := Γ(X, U)`.
  obtain ⟨U, hU, hPU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := P) (U := ⊤) (by trivial)
  haveI : Nonempty U := ⟨⟨P, hPU⟩⟩
  haveI hNoeth : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI hFR : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  -- The stalk at `P` as the localization of `R` at `𝔭`.
  set p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨P, hPU⟩ with hp_def
  letI : Algebra Γ(X, U) (X.presheaf.stalk P) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPU⟩
  haveI hlocP : IsLocalization.AtPrime (X.presheaf.stalk P) p.asIdeal :=
    hU.isLocalization_stalk ⟨P, hPU⟩
  haveI := functionField_isScalarTower X U ⟨P, hPU⟩
  -- Write `h = a / b` as a fraction of sections over `U`.
  obtain ⟨⟨a, b⟩, hmk⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Γ(X, U)) h
  replace hmk : IsLocalization.mk' X.functionField a b = h := hmk
  have hb0 : (b : Γ(X, U)) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hdiv : h = algebraMap Γ(X, U) X.functionField a
      / algebraMap Γ(X, U) X.functionField b := by
    rw [← hmk, IsFractionRing.mk'_eq_div]
  -- Non-regularity at `P` says the denominator ideal sits inside `𝔭`.
  have hle : (Ideal.span ({(b : Γ(X, U))} : Set Γ(X, U))).colon {a} ≤ p.asIdeal := by
    have hnn := (div_mem_range_algebraMap_iff (K := X.functionField)
      (X.presheaf.stalk P) (q := p.asIdeal) hb0).not.mp (hdiv ▸ hP)
    exact not_not.mp hnn
  -- Every localization of `R` at a prime is regular: transport stalk
  -- regularity along the chart.
  have hregR : ∀ (q : Ideal Γ(X, U)) [q.IsPrime],
      IsRegularLocalRing (Localization.AtPrime q) := by
    intro q hq
    have hzU' : hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)) ∈ U := by
      have h1 : hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U))
          ∈ Set.range hU.fromSpec.base := ⟨⟨q, hq⟩, rfl⟩
      rw [hU.range_fromSpec] at h1
      exact h1
    letI : Algebra Γ(X, U)
        (X.presheaf.stalk (hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)))) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hzU'⟩
    haveI hlocz : IsLocalization.AtPrime
        (X.presheaf.stalk (hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)))) q :=
      hU.isLocalization_stalk' ⟨q, hq⟩ hzU'
    haveI := hreg (hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)))
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl
        (X.presheaf.stalk (hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U))))
        (Localization.AtPrime q)).toRingEquiv
  -- Main ring theorem: a height-one prime `𝔮 ≤ 𝔭` containing the
  -- denominator ideal.
  obtain ⟨q, hqprime, hqht, hqle, hqcolon⟩ :=
    exists_height_one_prime_colon_le hregR hb0 (p := p.asIdeal) hle
  haveI := hqprime
  -- The corresponding point `z ∈ U ⊆ X`.
  have hzU : hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)) ∈ U := by
    have h1 : hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U))
        ∈ Set.range hU.fromSpec.base := ⟨⟨q, hqprime⟩, rfl⟩
    rw [hU.range_fromSpec] at h1
    exact h1
  letI : Algebra Γ(X, U)
      (X.presheaf.stalk (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)))) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hzU⟩
  haveI hlocz : IsLocalization.AtPrime
      (X.presheaf.stalk (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)))) q :=
    hU.isLocalization_stalk' ⟨q, hqprime⟩ hzU
  haveI := functionField_isScalarTower X U ⟨_, hzU⟩
  refine ⟨hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)), ?_, ?_, ?_⟩
  · -- `z ⤳ P` from `𝔮 ≤ 𝔭` via the chart.
    have hle' : (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)) ≤ p := hqle
    have hspec2 : (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)) ⤳ p :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hle'
    have hmap := hspec2.map hU.fromSpec.continuous
    have hPeq : hU.fromSpec p = P := by
      rw [hp_def]
      exact hU.fromSpec_primeIdealOf ⟨P, hPU⟩
    rwa [hPeq] at hmap
  · -- `coheight z = 1` via the coheight–Krull-dimension bridge.
    have hbridge := AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_coheight X
      (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)))
    have hdim : ringKrullDim
        (X.presheaf.stalk (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U))))
        = ((1 : ℕ∞) : WithBot ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q
        (X.presheaf.stalk (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U))))]
      exact_mod_cast hqht
    rw [hbridge] at hdim
    exact_mod_cast hdim
  · -- non-regularity at `z` from `((b) : a) ≤ 𝔮`.
    rw [hdiv]
    rw [div_mem_range_algebraMap_iff (K := X.functionField)
      (X.presheaf.stalk (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U))))
      (q := q) hb0]
    exact fun hn => hn hqcolon

end AlgebraicGeometry
