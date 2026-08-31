/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.ABFormula

/-!
# Cohen–Macaulay local rings and regular quotients (Stacks 00N8, 00NU-prep)

Sixth file of the Auslander–Buchsbaum package.

* `RingTheory.CohenMacaulay` — the Cohen–Macaulay predicate for a Noetherian
  local ring, `depth(R) = ringKrullDim R`, packaged as a `Prop`-valued class
  (Stacks tag 00N8). Mathlib at the pin has no Cohen–Macaulay predicate; this
  is the gap-fill.
* `RingTheory.CohenMacaulay.finrank_cotangentSpace_quot_span_singleton_succ` —
  the cotangent dim-drop: for `x ∈ 𝔪 \ 𝔪²` over a Noetherian local ring,
  `finrank κ' (CotangentSpace (R/(x))) + 1 = finrank κ (CotangentSpace R)`.
* `RingTheory.CohenMacaulay.exists_notMemSq_of_spanFinrank_pos` — the Nakayama
  witness `x ∈ 𝔪 \ 𝔪²` when `spanFinrank 𝔪 ≥ 1`.
* `RingTheory.CohenMacaulay.regularLocal_quotient_isRegularLocal_of_notMemSq` —
  for a regular local `R` with `spanFinrank 𝔪 = k + 1` and `x ∈ 𝔪 \ 𝔪²`, the
  quotient `R/(x)` is regular local with `spanFinrank 𝔪' = k` (via the
  cotangent dim-drop and the Krull-height bound
  `ringKrullDim_le_ringKrullDim_quotient_add_encard`, which does *not* need `x`
  to be a non-zero-divisor).

These are the inputs for `ABRegularDomain` (Stacks 00NP: regular local rings
are domains) and `ABRegularCM` (Stacks 00NQ: regular local rings are
Cohen–Macaulay).
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

/-! ## Cohen–Macaulay local rings

A Noetherian local ring `(R, 𝔪)` is **Cohen–Macaulay** if its depth equals
its Krull dimension (Stacks tag 00N8). Mathlib at the pin has neither the
predicate nor the class — this is the gap-fill. -/

/-- A Noetherian local ring `(R, 𝔪)` is **Cohen–Macaulay** if its depth
equals its Krull dimension: `depth(R) = dim R` (Stacks tag 00N8).

Encoded as a `Prop`-valued type class so downstream consumers can write
`[CohenMacaulay R]` and use Cohen–Macaulay as a hypothesis. 


 * Provenance: REFERENCE.
-/
class CohenMacaulay (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : Prop where
  /-- The Cohen–Macaulay equation: `depth(R) = ringKrullDim R`. The numeric
  comparison is in `WithBot ℕ∞` after coercion of the `ℕ∞`-valued depth. -/
  depth_eq_krullDim :
    (Module.depth (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) = ringKrullDim R

/-! ## Towards "regular local rings are Cohen–Macaulay"

Every regular Noetherian local ring is Cohen–Macaulay (Stacks tag 00NQ;
`ABRegularCM`). The proof picks a minimal generating set `x_1, …, x_d` of `𝔪`
(where `d = dim R`), uses that `R` is a domain (Stacks 00NP; `ABRegularDomain`)
to start an `R`-regular sequence, and inducts on dimension — each
`R/(x_1, …, x_c)` is again regular of dimension `d - c`. This file provides the
per-step engine: the cotangent dim-drop and the regularity of the quotient
`R/(x)` for `x ∈ 𝔪 \ 𝔪²`. -/

namespace CohenMacaulay

/-- **Cotangent dim-drop on `R ⧸ (x)`.** For a Noetherian local ring `(R, 𝔪)`
and `x ∈ 𝔪 \ 𝔪²`, the cotangent space of `R / (x)` has dimension one less
than that of `R`:
```
finrank κ' (CotangentSpace (R/(x))) + 1 = finrank κ (CotangentSpace R)
```
where `κ = R / 𝔪` and `κ' = (R/(x)) / 𝔪'` are the two residue fields.

Both sides reduce to `spanFinrank` of the maximal ideal via
`IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`, and the
`spanFinrank` equation is proved by two inequalities:
* `≤`: Steinitz exchange — in a minimal generating finset `V` of `𝔪`, the
  expansion of `x` has a unit coefficient at some `v₀ ∈ V` (else `x ∈ 𝔪²`),
  so `(V \ {v₀}) ∪ {x}` still generates and its image generates `𝔪'`, with
  `x` dying in `R/(x)`;
* `≥`: lift-and-cons — a minimal generating finset of `𝔪'` lifts along the
  surjection `R → R/(x)` and, together with `x`, generates `𝔪`.

This is the building block that upgrades `R/(x)` back to `IsRegularLocalRing`
in `regularLocal_quotient_isRegularLocal_of_notMemSq` below. 





 * Provenance: CUSTOM.
-/
theorem finrank_cotangentSpace_quot_span_singleton_succ
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hxnotsq : x ∉ IsLocalRing.maximalIdeal R ^ 2)
    [Nontrivial (R ⧸ Ideal.span {x})]
    [IsLocalRing (R ⧸ Ideal.span {x})]
    [IsNoetherianRing (R ⧸ Ideal.span {x})] :
    Module.finrank (IsLocalRing.ResidueField (R ⧸ Ideal.span {x}))
        (IsLocalRing.CotangentSpace (R ⧸ Ideal.span {x})) + 1 =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  -- Reduce the κ-finrank statement to a spanFinrank statement (both sides go
  -- through `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`).
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R,
      ← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace
          (R ⧸ Ideal.span {x})]
  -- Goal: (𝔪 (R/(x))).spanFinrank + 1 = (𝔪 R).spanFinrank,
  -- via (≥) lift-and-cons + (≤) Steinitz exchange.
  refine le_antisymm ?_ ?_
  · -- (≤): (𝔪 (R/(x))).spanFinrank + 1 ≤ (𝔪 R).spanFinrank.
    classical
    -- Get min gen finset V of 𝔪 R.
    have h𝔪_fg : (IsLocalRing.maximalIdeal R).FG := Ideal.fg_of_isNoetherianRing _
    obtain ⟨V, hV_card, hV_span⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank h𝔪_fg
    -- Step 1: spanFinrank 𝔪 R ≥ 1 (since x ∉ 𝔪² implies x ≠ 0, hence 𝔪 ≠ ⊥).
    have h_n_ge_1 : 1 ≤ Submodule.spanFinrank (IsLocalRing.maximalIdeal R) := by
      rw [← hV_card]
      by_contra h
      push Not at h
      have hV_empty : V.card = 0 := Nat.lt_one_iff.mp h
      have hV_eq : V = ∅ := Finset.card_eq_zero.mp hV_empty
      have h𝔪_bot : IsLocalRing.maximalIdeal R = ⊥ := by
        rw [← hV_span, hV_eq, Finset.coe_empty, Submodule.span_empty]
      apply hxnotsq
      have hx_bot : x ∈ (⊥ : Ideal R) := h𝔪_bot ▸ hx
      rw [Submodule.mem_bot] at hx_bot
      rw [hx_bot]; exact zero_mem _
    -- Step 2: x ∈ Submodule.span R V, extract coefficients via mem_span_finset.
    have hx_mem : x ∈ Submodule.span R (V : Set R) := hV_span ▸ hx
    obtain ⟨c, _hc_supp, hc_sum⟩ := Submodule.mem_span_finset.mp hx_mem
    -- Step 3 (axiom-clean): ∃ v₀ ∈ V with c v₀ ∉ 𝔪 R, i.e., c v₀ is a unit.
    -- If all c v ∈ 𝔪, then x = Σ c v • v ∈ 𝔪 · 𝔪 = 𝔪². Contradicts hxnotsq.
    have hexists_unit : ∃ v₀ ∈ V, c v₀ ∉ IsLocalRing.maximalIdeal R := by
      by_contra h
      push Not at h
      apply hxnotsq
      rw [pow_two, ← hc_sum]
      refine Submodule.sum_mem _ ?_
      intro v hvV
      have hcv_mem : c v ∈ IsLocalRing.maximalIdeal R := h v hvV
      have hv_mem : v ∈ IsLocalRing.maximalIdeal R := by
        rw [← hV_span]; exact Submodule.subset_span (by exact_mod_cast hvV)
      have hmul : c v • v ∈ (IsLocalRing.maximalIdeal R : Submodule R R) *
          IsLocalRing.maximalIdeal R := by
        rw [smul_eq_mul]
        exact Ideal.mul_mem_mul hcv_mem hv_mem
      simpa [Ideal.smul_eq_mul] using hmul
    obtain ⟨v₀, hv₀_V, hv₀_notmem⟩ := hexists_unit
    have hv₀_unit : IsUnit (c v₀) := IsLocalRing.notMem_maximalIdeal.mp hv₀_notmem
    obtain ⟨u, hu⟩ := hv₀_unit
    -- Step 4: v₀ = ↑u⁻¹ * x - Σ_{v ∈ V.erase v₀} ↑u⁻¹ * c v * v.
    have hsum_split : c v₀ * v₀ + ∑ v ∈ V.erase v₀, c v * v = x := by
      rw [← Finset.sum_erase_add _ _ hv₀_V] at hc_sum
      simp only [smul_eq_mul] at hc_sum
      linear_combination hc_sum
    have hu_inv : (↑u⁻¹ : R) * c v₀ = 1 := by rw [← hu]; exact Units.inv_mul u
    have h_sum_eq : (↑u⁻¹ : R) * ∑ v ∈ V.erase v₀, c v * v =
        ∑ v ∈ V.erase v₀, (↑u⁻¹ : R) * c v * v := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    have hv₀_eq : v₀ = (↑u⁻¹ : R) * x -
        ∑ v ∈ V.erase v₀, (↑u⁻¹ : R) * c v * v := by
      have h1 : (↑u⁻¹ : R) * (c v₀ * v₀ + ∑ v ∈ V.erase v₀, c v * v) =
          (↑u⁻¹ : R) * x := by rw [hsum_split]
      rw [mul_add, ← mul_assoc, hu_inv, one_mul, h_sum_eq] at h1
      linear_combination h1
    have hv₀_in_new : v₀ ∈ Submodule.span R (insert x (V.erase v₀ : Set R)) := by
      -- Prove the membership via the explicit linear combination, then
      -- substitute the LHS via hv₀_eq.
      have key : (↑u⁻¹ : R) * x - ∑ v ∈ V.erase v₀, (↑u⁻¹ : R) * c v * v ∈
          Submodule.span R (insert x (V.erase v₀ : Set R)) := by
        apply Submodule.sub_mem
        · exact Submodule.smul_mem _ _
            (Submodule.subset_span (Set.mem_insert _ _))
        · apply Submodule.sum_mem
          intro v hvErase
          exact Submodule.smul_mem _ _
            (Submodule.subset_span (Set.mem_insert_of_mem _
              (by exact_mod_cast hvErase)))
      -- `rw [← hv₀_eq] at key` only rewrites the LHS occurrence (the V.erase v₀
      -- in the RHS uses v₀ directly, not the explicit expr).
      rwa [← hv₀_eq] at key
    -- Step 5: Submodule.span R (insert x (V.erase v₀)) = 𝔪 R.
    have h𝔪R_new : Submodule.span R (insert x (V.erase v₀ : Set R)) =
        IsLocalRing.maximalIdeal R := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro y hy
        rcases hy with rfl | hy
        · exact hx
        · have hy_V : y ∈ V := Finset.mem_of_mem_erase (by exact_mod_cast hy)
          rw [← hV_span]
          exact Submodule.subset_span (by exact_mod_cast hy_V)
      · rw [← hV_span, Submodule.span_le]
        intro v hv
        by_cases hv_eq : v = v₀
        · rw [hv_eq]; exact hv₀_in_new
        · refine Submodule.subset_span ?_
          right
          exact_mod_cast Finset.mem_erase.mpr ⟨hv_eq, by exact_mod_cast hv⟩
    -- Step 6: 𝔪 R' = Ideal.span (mkx '' (V.erase v₀)).
    -- First, 𝔪 R' = Ideal.map mkx 𝔪 R, and mkx x = 0.
    set mkx : R →+* (R ⧸ Ideal.span {x}) := Ideal.Quotient.mk _ with hmkx_def
    have h_mkx_x : mkx x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_span_singleton_self x)
    have hcomap_eq : Ideal.comap mkx
        (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})) =
        IsLocalRing.maximalIdeal R := by
      have hmax : (Ideal.comap mkx
          (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}))).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      exact (IsLocalRing.isMaximal_iff R).mp hmax
    have h𝔪R'_eq_map : IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}) =
        Ideal.map mkx (IsLocalRing.maximalIdeal R) := by
      conv_rhs => rw [← hcomap_eq]
      exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
    -- Now 𝔪 R' = Ideal.map mkx (span (insert x (V.erase v₀)))
    --         = Ideal.span (mkx '' (insert x (V.erase v₀)))
    --         = Ideal.span (insert 0 (mkx '' (V.erase v₀)))
    --         ≤ Submodule.span R' (mkx '' (V.erase v₀)).
    -- For the spanFinrank bound it suffices to show the inequality
    -- spanFinrank 𝔪 R' ≤ |V.erase v₀|.
    have h_bound : Submodule.spanFinrank
        (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})) ≤ V.card - 1 := by
      have h𝔪R'_span : IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}) =
          Ideal.span (mkx '' (V.erase v₀ : Set R)) := by
        rw [h𝔪R'_eq_map, ← h𝔪R_new, Ideal.map_span,
            Set.image_insert_eq, h_mkx_x]
        -- Goal: Ideal.span (insert 0 (mkx '' V.erase v₀)) =
        --        Ideal.span (mkx '' V.erase v₀).
        -- 0 ∈ Ideal.span A for any A, so adding 0 doesn't change span.
        apply le_antisymm
        · rw [Ideal.span_le]
          rintro y (rfl | hy)
          · exact Submodule.zero_mem _
          · exact Submodule.subset_span hy
        · exact Ideal.span_mono (Set.subset_insert _ _)
      calc Submodule.spanFinrank
            (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}))
          = Submodule.spanFinrank
              (Ideal.span (mkx '' (V.erase v₀ : Set R))) := by rw [h𝔪R'_span]
        _ = Submodule.spanFinrank
              (Submodule.span _ (mkx '' (V.erase v₀ : Set R))) := rfl
        _ ≤ (mkx '' (V.erase v₀ : Set R)).ncard :=
            Submodule.spanFinrank_span_le_ncard_of_finite
              ((V.erase v₀).finite_toSet.image _)
        _ ≤ (V.erase v₀ : Set R).ncard :=
            Set.ncard_image_le (V.erase v₀).finite_toSet
        _ = (V.erase v₀).card := Set.ncard_coe_finset _
        _ = V.card - 1 := Finset.card_erase_of_mem hv₀_V
    -- Step 7: conclude using h_n_ge_1.
    omega
  · -- (≥): (𝔪 R).spanFinrank ≤ (𝔪 (R/(x))).spanFinrank + 1.
    -- Lift-and-cons strategy: a min gen set T of 𝔪 (R/(x)) lifts to T_lift ⊆
    -- 𝔪 R via `Function.surjInv` of `Ideal.Quotient.mk_surjective`; the union
    -- `T_lift ∪ {x}` generates 𝔪 R since 𝔪 R = (Ideal.span {x}) ⊔ (lift of 𝔪').
    classical
    set R' : Type u := R ⧸ Ideal.span {x} with hR'_def
    let mkx : R →+* R' := Ideal.Quotient.mk _
    let g : R' → R := Function.surjInv Ideal.Quotient.mk_surjective
    have hg : ∀ y, mkx (g y) = y := Function.surjInv_eq _
    -- Get min gen finset of 𝔪'.
    have h𝔪'_fg : (IsLocalRing.maximalIdeal R').FG := Ideal.fg_of_isNoetherianRing _
    obtain ⟨T, hT_card, hT_span⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank h𝔪'_fg
    -- T : Finset R', T.card = spanFinrank 𝔪', span R' T = 𝔪'.
    let T_lift : Finset R := T.image g
    let U : Finset R := insert x T_lift
    -- Step A: U generates 𝔪 R via the comap identification.
    -- Comap mkx (𝔪 R') = 𝔪 R, since R is local and mkx is surjective.
    have hcomap_eq : Ideal.comap mkx (IsLocalRing.maximalIdeal R') =
        IsLocalRing.maximalIdeal R := by
      have hmax : (Ideal.comap mkx (IsLocalRing.maximalIdeal R')).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      exact (IsLocalRing.isMaximal_iff R).mp hmax
    have hker_eq : RingHom.ker mkx = Ideal.span {x} := Ideal.mk_ker
    -- Step B: 𝔪 R = (Ideal.span T_lift) ⊔ (Ideal.span {x}).
    -- Compute: comap mkx (map mkx (Ideal.span T_lift)) = Ideal.span T_lift ⊔ ker mkx.
    have hmap_T_lift : Ideal.map mkx (Ideal.span (T_lift : Set R)) =
        IsLocalRing.maximalIdeal R' := by
      rw [Ideal.map_span]
      -- mkx '' T_lift = T (as sets).
      have him : mkx '' (T_lift : Set R) = (T : Set R') := by
        ext y
        simp only [Set.mem_image, Finset.coe_image, T_lift]
        refine ⟨?_, ?_⟩
        · rintro ⟨a, ⟨b, hbT, rfl⟩, rfl⟩
          rw [hg b]; exact hbT
        · intro hyT
          exact ⟨g y, ⟨y, hyT, rfl⟩, hg y⟩
      rw [him]; exact hT_span
    have h𝔪R_decomp : IsLocalRing.maximalIdeal R =
        Ideal.span (T_lift : Set R) ⊔ Ideal.span {x} := by
      calc IsLocalRing.maximalIdeal R
          = Ideal.comap mkx (IsLocalRing.maximalIdeal R') := hcomap_eq.symm
        _ = Ideal.comap mkx (Ideal.map mkx (Ideal.span (T_lift : Set R))) := by
              rw [hmap_T_lift]
        _ = Ideal.span (T_lift : Set R) ⊔ RingHom.ker mkx := by
              rw [Ideal.comap_map_of_surjective' mkx Ideal.Quotient.mk_surjective]
        _ = Ideal.span (T_lift : Set R) ⊔ Ideal.span {x} := by rw [hker_eq]
    -- Step C: span R U = Ideal.span T_lift ⊔ Ideal.span {x}.
    have hU_span_eq : Submodule.span R (↑U : Set R) =
        Ideal.span (T_lift : Set R) ⊔ Ideal.span {x} := by
      have hUeq : (↑U : Set R) = (↑T_lift : Set R) ∪ {x} := by
        change ((insert x T_lift : Finset R) : Set R) = _
        rw [Finset.coe_insert, Set.insert_eq, Set.union_comm]
      rw [hUeq, Submodule.span_union]
    -- Step D: spanFinrank 𝔪 R ≤ U.card ≤ T.card + 1.
    calc Submodule.spanFinrank (IsLocalRing.maximalIdeal R)
        = Submodule.spanFinrank (Submodule.span R (↑U : Set R)) := by
          rw [hU_span_eq, ← h𝔪R_decomp]
      _ ≤ (↑U : Set R).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite U.finite_toSet
      _ = U.card := by simp
      _ ≤ T_lift.card + 1 := by
          have := Finset.card_insert_le x T_lift
          simpa [U] using this
      _ ≤ T.card + 1 := by
          have hle : T_lift.card ≤ T.card := Finset.card_image_le
          omega
      _ = Submodule.spanFinrank (IsLocalRing.maximalIdeal R') + 1 := by
          rw [hT_card]

/-- **Nakayama witness.** For a Noetherian local ring `(R, 𝔪)` with
`spanFinrank 𝔪 ≥ 1`, there exists `x ∈ 𝔪` with `x ∉ 𝔪²`.

This is the "cotangent space is nonzero" content: by Nakayama, if `𝔪 ⊆ 𝔪²`
then `𝔪 = 0` (so `spanFinrank 𝔪 = 0`), contradicting the hypothesis. 





 * Provenance: CUSTOM.
-/
lemma exists_notMemSq_of_spanFinrank_pos
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : 0 < (IsLocalRing.maximalIdeal R).spanFinrank) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, x ∉ (IsLocalRing.maximalIdeal R) ^ 2 := by
  -- By contradiction: assume 𝔪 ⊆ 𝔪², then by Nakayama 𝔪 = 0, but spanFinrank 𝔪 ≥ 1.
  by_contra h_neg
  push Not at h_neg
  have h𝔪_le_sq : IsLocalRing.maximalIdeal R ≤ (IsLocalRing.maximalIdeal R) ^ 2 := h_neg
  -- 𝔪² = 𝔪 • 𝔪.
  have hsq : (IsLocalRing.maximalIdeal R : Submodule R R) ^ 2
      = (IsLocalRing.maximalIdeal R) • (IsLocalRing.maximalIdeal R : Submodule R R) := by
    rw [sq, ← Ideal.smul_eq_mul]
  have h𝔪_fg : (IsLocalRing.maximalIdeal R : Submodule R R).FG :=
    Ideal.fg_of_isNoetherianRing _
  -- Use Submodule.le_of_le_smul_of_le_jacobson_bot with N = ⊥.
  have hjac : (IsLocalRing.maximalIdeal R) ≤ (⊥ : Ideal R).jacobson :=
    IsLocalRing.maximalIdeal_le_jacobson _
  have h_le_smul : (IsLocalRing.maximalIdeal R : Submodule R R)
      ≤ ⊥ ⊔ (IsLocalRing.maximalIdeal R) •
        (IsLocalRing.maximalIdeal R : Submodule R R) := by
    rw [bot_sup_eq, ← hsq]; exact h𝔪_le_sq
  have h𝔪_bot : (IsLocalRing.maximalIdeal R : Submodule R R) ≤ ⊥ :=
    Submodule.le_of_le_smul_of_le_jacobson_bot h𝔪_fg hjac h_le_smul
  have h𝔪_eq_bot : (IsLocalRing.maximalIdeal R) = ⊥ := le_bot_iff.mp h𝔪_bot
  have h_span : (IsLocalRing.maximalIdeal R).spanFinrank = 0 := by
    rw [h𝔪_eq_bot]; exact Submodule.spanFinrank_bot
  omega

/-! ### The regular quotient step (Stacks 00NU prep)

For a regular local Noetherian ring `R` of `spanFinrank 𝔪 = k + 1` and
`x ∈ 𝔪 \ 𝔪²`, the quotient `R ⧸ Ideal.span {x}` is again a regular local
ring of `spanFinrank 𝔪' = k`.

This is the **axiom-clean** counterpart of
`exists_isSMulRegular_quotient_isRegularLocal_succ`: it avoids the
`IsSMulRegular R x` hypothesis (which depends on `isDomain_of_regularLocal`)
by routing the dimension lower bound through
`ringKrullDim_le_ringKrullDim_quotient_add_encard` — a Krull-height bound
that does NOT require `x` to be a non-zero-divisor — instead of
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`. -/
/-- Provenance: CUSTOM. -/
lemma regularLocal_quotient_isRegularLocal_of_notMemSq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsRegularLocalRing R] {k : ℕ}
    (hdim : (IsLocalRing.maximalIdeal R).spanFinrank = k + 1)
    (x : R) (hxMem : x ∈ IsLocalRing.maximalIdeal R)
    (hxNotSq : x ∉ (IsLocalRing.maximalIdeal R) ^ 2) :
    ∃ _ : Nontrivial (R ⧸ Ideal.span ({x} : Set R)),
    ∃ _ : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)),
    ∃ _ : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)),
      (IsLocalRing.maximalIdeal (R ⧸ Ideal.span ({x} : Set R))).spanFinrank = k := by
  -- Step 1: instances on R/(x).
  have hxNonunit : ¬ IsUnit x := fun hu =>
    (IsLocalRing.notMem_maximalIdeal.mpr hu) hxMem
  have hspan_ne_top : (Ideal.span ({x} : Set R)) ≠ ⊤ :=
    Ideal.span_singleton_ne_top hxNonunit
  haveI hNT : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) :=
    Ideal.Quotient.nontrivial_iff.mpr hspan_ne_top
  haveI hLR : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  -- Step 2: cotangent dim drop → spanFinrank drop on R/(x).
  have hcot := finrank_cotangentSpace_quot_span_singleton_succ x hxMem hxNotSq
  have hR_cot_eq :
      Module.finrank (IsLocalRing.ResidueField R)
          (IsLocalRing.CotangentSpace R) = k + 1 := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R]
    exact hdim
  have hR'_cot_eq :
      Module.finrank (IsLocalRing.ResidueField (R ⧸ Ideal.span ({x} : Set R)))
          (IsLocalRing.CotangentSpace (R ⧸ Ideal.span ({x} : Set R))) = k := by
    have h := hcot
    rw [hR_cot_eq] at h
    omega
  have hspan_R'_eq_k :
      (IsLocalRing.maximalIdeal (R ⧸ Ideal.span ({x} : Set R))).spanFinrank = k := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace
        (R ⧸ Ideal.span ({x} : Set R))]
    exact hR'_cot_eq
  -- Step 3: Krull height theorem: ringKrullDim R ≤ ringKrullDim R/(x) + 1.
  have hxJac : x ∈ Ring.jacobson R := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact hxMem
  have h_x_subset_jac : ({x} : Set R) ⊆ Ring.jacobson R := by
    intro y hy
    rcases hy with rfl
    exact hxJac
  have hKrullDimLE : ringKrullDim R ≤
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 := by
    have h := ringKrullDim_le_ringKrullDim_quotient_add_encard
                ({x} : Set R) h_x_subset_jac
    simpa using h
  have hR_dim : ringKrullDim R = ((k + 1 : ℕ) : WithBot ℕ∞) := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at h
    exact_mod_cast h.symm
  -- Step 4: extract `ringKrullDim R/(x) = k` from hKrullDimLE + upper bound.
  -- Upper bound: `ringKrullDim R/(x) ≤ spanFinrank 𝔪' = k`.
  have h_dim_upper : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ≤
      ((k : ℕ) : WithBot ℕ∞) := by
    refine le_trans (ringKrullDim_le_spanFinrank_maximalIdeal _) ?_
    rw [hspan_R'_eq_k]
  -- Adding 1 to both sides of h_dim_upper:
  -- `ringKrullDim R/(x) + 1 ≤ (k:WithBot) + 1 = (k+1:WithBot) = ringKrullDim R`.
  have h_add_le : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 ≤
      ((k + 1 : ℕ) : WithBot ℕ∞) := by
    calc ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1
        ≤ ((k : ℕ) : WithBot ℕ∞) + 1 := by gcongr
      _ = ((k + 1 : ℕ) : WithBot ℕ∞) := by push_cast; ring
  -- Combined with hKrullDimLE via hR_dim → equation in WithBot.
  have h_add_eq : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1
      = ((k + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hR_dim] at hKrullDimLE
    exact le_antisymm h_add_le hKrullDimLE
  -- Extract `ringKrullDim R/(x) = k : WithBot ℕ∞` via `WithBot.add_eq_coe`.
  have hR'_dim_eq : ringKrullDim (R ⧸ Ideal.span ({x} : Set R))
      = ((k : ℕ) : WithBot ℕ∞) := by
    obtain ⟨a', b', ha', hb', hab⟩ := WithBot.add_eq_coe.mp h_add_eq
    rw [← ha']
    have hb_eq : b' = (1 : ℕ∞) := by
      have h1 : ((b' : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := by
        rw [hb']; simp
      exact_mod_cast h1
    have ha_eq : a' = (k : ℕ∞) := by
      rw [hb_eq] at hab
      have hcast2 : a' + 1 = (k : ℕ∞) + 1 := by exact_mod_cast hab
      have hne_top : (1 : ℕ∞) ≠ ⊤ := by simp
      exact WithTop.add_right_cancel hne_top hcast2
    exact_mod_cast ha_eq
  -- Step 5: spanFinrank 𝔪' = k = ringKrullDim R/(x) → IsRegularLocalRing R/(x).
  have hRLR : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [hspan_R'_eq_k, hR'_dim_eq]
  exact ⟨hNT, hLR, hRLR, hspan_R'_eq_k⟩

end CohenMacaulay

end RingTheory
