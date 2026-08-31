/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.ABRegularDomain

/-!
# Regular local rings are Cohen–Macaulay (Stacks 00NQ)

Final file of the Auslander–Buchsbaum package.

* `RingTheory.CohenMacaulay.exists_isRegular_of_regularLocal` — a regular local
  Noetherian ring admits an `R`-regular sequence in `𝔪` of length
  `spanFinrank 𝔪 = dim R` (a regular system of parameters is a regular
  sequence), by induction on the dimension through the regular quotients
  `R/(x)` of `ABRegularQuotient`, with `isDomain_of_regularLocal` providing the
  non-zero-divisors.
* `RingTheory.CohenMacaulay.of_regular` — every regular Noetherian local ring
  is Cohen–Macaulay (Stacks tag 00NQ), as an instance: `depth(R) ≥ dim R` from
  the regular sequence above, `depth(R) ≤ dim R` from
  `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`.

This is the consumer-facing input for the pole-purity/codim-1-extension chapter
(`Albanese/PolePurity` and beyond): the local ring of a regular surface at a
closed point is regular of Krull dimension 2, hence Cohen–Macaulay of depth 2.
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

/-! ### Length-bound on regular sequences

For a Noetherian local ring `R`, every `R`-regular sequence has length at most
`ringKrullDim R`. This is the **upper bound** half of Stacks 00NQ: it is the
specialisation of the equality
`ringKrullDim (R / ofList rs) + rs.length = ringKrullDim R`
(`ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`) to the observation that
`ringKrullDim (R / ofList rs) ≥ 0` whenever the quotient is nontrivial, which it
is precisely because `IsRegular` rules out `rs • ⊤ = ⊤`. -/
private lemma length_le_ringKrullDim_of_isRegular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {rs : List R} (h : RingTheory.Sequence.IsRegular R rs) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim R := by
  have heq := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs h
  have hntq : Nontrivial (R ⧸ Ideal.ofList rs) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro habs
    apply h.top_ne_smul
    change (⊤ : Submodule R R) = (Ideal.ofList rs) • ⊤
    rw [habs]; simp
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.ofList rs) :=
    ringKrullDim_nonneg_of_nontrivial
  calc (rs.length : WithBot ℕ∞)
      = 0 + (rs.length : WithBot ℕ∞) := by simp
    _ ≤ ringKrullDim (R ⧸ Ideal.ofList rs) + (rs.length : WithBot ℕ∞) := by gcongr
    _ = ringKrullDim R := heq

/-- For a regular local ring `(R, 𝔪)` of Krull dimension `k + 1`, there exists
`x ∈ 𝔪 \ 𝔪²` that is additionally an `R`-regular element.

The Nakayama witness is `exists_notMemSq_of_spanFinrank_pos`; the
`IsSMulRegular` upgrade uses that in a domain (`isDomain_of_regularLocal`)
every nonzero element is a non-zero-divisor (`IsSMulRegular.of_ne_zero`). -/
private lemma exists_isSMulRegular_notMemSq_of_regularLocal_succ
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsRegularLocalRing R] {k : ℕ}
    (hdim : (IsLocalRing.maximalIdeal R).spanFinrank = k + 1) :
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧
      x ∉ (IsLocalRing.maximalIdeal R) ^ 2 ∧ IsSMulRegular R x := by
  have hpos : 0 < (IsLocalRing.maximalIdeal R).spanFinrank := by omega
  obtain ⟨x, hxMem, hxNotSq⟩ := exists_notMemSq_of_spanFinrank_pos hpos
  have hx_ne_zero : x ≠ 0 := by
    intro hx0
    apply hxNotSq
    rw [hx0]; exact Submodule.zero_mem _
  haveI : IsDomain R := isDomain_of_regularLocal R
  haveI : Module.IsTorsionFree R R := inferInstance
  exact ⟨x, hxMem, hxNotSq, IsSMulRegular.of_ne_zero hx_ne_zero⟩

/-- **Stacks 00NQ inductive substrate.**
For a regular local ring `(R, 𝔪)` of Krull dimension `k + 1`, there exists
`x ∈ 𝔪` that is `R`-regular (a non-zero-divisor on `R`) such that the quotient
`R ⧸ Ideal.span {x}` is again a regular local ring of Krull dimension `k`
(equivalently: its maximal ideal has `spanFinrank = k`).

Assembly path (after `exists_isSMulRegular_notMemSq_of_regularLocal_succ`
provides `x ∈ 𝔪 \ 𝔪²` that is `R`-regular):
1. Build `[Nontrivial (R/(x))]`, `[IsLocalRing (R/(x))]`,
   `[IsNoetherianRing (R/(x))]` instances from `Ideal.span_singleton_ne_top`
   (since `x ∈ 𝔪` is a nonunit) + `IsLocalRing.of_surjective'` of the
   quotient map + `Ideal.Quotient.isNoetherianRing` automatic.
2. Cotangent dim-drop via `finrank_cotangentSpace_quot_span_singleton_succ`:
   `finrank κ' (CotangentSpace (R/(x))) + 1 = finrank κ (CotangentSpace R)`.
3. Translate κ-finrank to spanFinrank via
   `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` (Mathlib);
   combine with `hdim : spanFinrank 𝔪 R = k+1` to get
   `spanFinrank 𝔪 (R/(x)) = k`.
4. Krull dim drop via
   `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`: since `x` is
   `R`-regular and `x ∈ 𝔪`,
   `ringKrullDim (R/(x)) + 1 = ringKrullDim R`. By `IsRegularLocalRing`'s
   defining equation `ringKrullDim R = spanFinrank 𝔪 R = k+1`, so
   `ringKrullDim (R/(x)) = k`.
5. Conclude `IsRegularLocalRing (R/(x))` via
   `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` (the inequality
   becomes the equation `spanFinrank = k = ringKrullDim`). -/
private lemma exists_isSMulRegular_quotient_isRegularLocal_succ
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsRegularLocalRing R] {k : ℕ}
    (hdim : (IsLocalRing.maximalIdeal R).spanFinrank = k + 1) :
    ∃ (x : R), x ∈ IsLocalRing.maximalIdeal R ∧ IsSMulRegular R x ∧
      ∃ _ : IsRegularLocalRing (R ⧸ Ideal.span {x}),
        (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = k := by
  -- Step 1: extract `x ∈ 𝔪 \ 𝔪²` that is `R`-regular.
  obtain ⟨x, hxMem, hxNotSq, hxReg⟩ :=
    exists_isSMulRegular_notMemSq_of_regularLocal_succ (k := k) hdim
  refine ⟨x, hxMem, hxReg, ?_⟩
  -- Step 2: assemble the structural instances on `R/(x)`.
  have hxNonunit : ¬ IsUnit x := fun hu =>
    (IsLocalRing.notMem_maximalIdeal.mpr hu) hxMem
  have hspan_ne_top : (Ideal.span ({x} : Set R)) ≠ ⊤ :=
    Ideal.span_singleton_ne_top hxNonunit
  haveI : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) :=
    Ideal.Quotient.nontrivial_iff.mpr hspan_ne_top
  haveI : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  -- IsNoetherianRing (R ⧸ I) is automatic via `Ideal.Quotient.isNoetherianRing`.
  -- Step 3: cotangent dim-drop.
  have hcot := finrank_cotangentSpace_quot_span_singleton_succ x hxMem hxNotSq
  -- Step 4: translate κ-finrank to spanFinrank on both R and R/(x).
  have hR_cot_eq :
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = k + 1 := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R]
    exact hdim
  have hR'_cot_eq :
      Module.finrank (IsLocalRing.ResidueField (R ⧸ Ideal.span ({x} : Set R)))
          (IsLocalRing.CotangentSpace (R ⧸ Ideal.span ({x} : Set R))) = k := by
    -- from `hcot : LHS + 1 = RHS` and `hR_cot_eq : RHS = k + 1` we get `LHS = k`.
    have h := hcot
    rw [hR_cot_eq] at h
    omega
  have hspan_R'_eq_k :
      (IsLocalRing.maximalIdeal (R ⧸ Ideal.span ({x} : Set R))).spanFinrank = k := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace
        (R ⧸ Ideal.span ({x} : Set R))]
    exact hR'_cot_eq
  -- Step 5: Krull dim drop on R/(x).  `ringKrullDim (R/(x)) + 1 = ringKrullDim R`.
  have hKrullDimDrop : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxReg hxMem
  -- `ringKrullDim R = (k+1 : ℕ)` by `IsRegularLocalRing`'s defining equation.
  have hR_dim : ringKrullDim R = ((k + 1 : ℕ) : WithBot ℕ∞) := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at h
    -- h : ((k+1 : ℕ) : WithBot ℕ∞) = ringKrullDim R (after coercion through ℕ∞)
    exact_mod_cast h.symm
  -- Solve `ringKrullDim (R/(x)) = (k : ℕ)` from the additive equation.
  have hR'_dim : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) = ((k : ℕ) : WithBot ℕ∞) := by
    rw [hR_dim] at hKrullDimDrop
    -- hKrullDimDrop : ringKrullDim (R/(x)) + 1 = ((k+1 : ℕ) : WithBot ℕ∞).
    -- Use `WithBot.add_eq_coe` to extract finite witnesses `a', b' : ℕ∞`, then
    -- cancel `+ 1` in `ℕ∞` via `WithTop.add_right_cancel` (since `1 ≠ ⊤`).
    obtain ⟨a', b', ha', hb', hab⟩ := WithBot.add_eq_coe.mp hKrullDimDrop
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
  -- Step 6: conclude `IsRegularLocalRing (R/(x))` via `of_spanFinrank_maximalIdeal_le`.
  have hRegLR : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ <| by
      rw [hspan_R'_eq_k, hR'_dim]
  exact ⟨hRegLR, hspan_R'_eq_k⟩

/-- Packages the inductive step of Stacks 00NQ: given a regular local ring `R`
of dimension `k + 1`, plus the inductive hypothesis at dimension `k`
(universally quantified in the ring), produce a regular sequence of length
`k + 1` in the maximal ideal of `R`. Assembly path:

1. `exists_isSMulRegular_quotient_isRegularLocal_succ` extracts `x ∈ 𝔪` with
   `IsSMulRegular R x` AND `IsRegularLocalRing
   (R⧸(x))` of `spanFinrank = k`.
2. IH applied on `R ⧸ Ideal.span {x}` produces a regular sequence
   `rs'_q : List (R ⧸ (x))` of length `k` in the maximal ideal there.
3. Lift `rs'_q` to `rs : List R` via `Function.surjInv` of
   `Ideal.Quotient.mk_surjective`; the section property gives
   `rs.map (Ideal.Quotient.mk _) = rs'_q`.
4. Members of `rs` lie in `𝔪` because the maximal ideal of `R⧸(x)` is the
   image of `𝔪` (`IsLocalRing.le_maximalIdeal` applied to the comap chain).
5. Cons via `RingTheory.Sequence.IsRegular.cons'` to form the length-`(k+1)`
   sequence `x :: rs`. -/
private lemma regularLocal_inductive_step {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsRegularLocalRing R] {k : ℕ}
    (hdim : (IsLocalRing.maximalIdeal R).spanFinrank = k + 1)
    (IH : ∀ (R' : Type u) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
            [IsRegularLocalRing R'],
            (IsLocalRing.maximalIdeal R').spanFinrank = k →
            ∃ rs : List R', rs.length = k ∧
              (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R') ∧
              RingTheory.Sequence.IsRegular R' rs) :
    ∃ rs : List R, rs.length = k + 1 ∧
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular R rs := by
  -- Step 1: extract `x ∈ 𝔪` regular on `R` with `R ⧸ (x)` regular local of
  -- `spanFinrank = k`.
  obtain ⟨x, hxMem, hxReg, hRLR, hdim_quot⟩ :=
    exists_isSMulRegular_quotient_isRegularLocal_succ hdim
  -- Step 2: apply IH on `R ⧸ (x)` — this gives a regular sequence of length
  -- `k` on the quotient, valued in its maximal ideal.
  obtain ⟨rs'_q, hlen_q, hmem_q, hreg_q⟩ := IH (R ⧸ Ideal.span {x}) hdim_quot
  -- Step 3: lift `rs'_q : List (R ⧸ (x))` to `rs' : List R` via the right
  -- inverse of the (surjective) quotient ring hom.
  let mkq : R →+* R ⧸ Ideal.span {x} := Ideal.Quotient.mk _
  let g : R ⧸ Ideal.span {x} → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hg : ∀ y, mkq (g y) = y := Function.surjInv_eq _
  let rs' : List R := rs'_q.map g
  have hlen_rs' : rs'.length = k := by simp [rs', hlen_q]
  have hmkmap : rs'.map mkq = rs'_q := by
    change (rs'_q.map g).map mkq = rs'_q
    rw [List.map_map]
    conv_rhs => rw [← List.map_id rs'_q]
    exact List.map_congr_left fun y _ => hg y
  -- Step 4: each element of `rs'` lies in `𝔪 R` via the comap of `𝔪 (R⧸(x))`.
  -- The maximal ideal of `R ⧸ (x)` comaps back to `𝔪 R` (it's the *unique*
  -- maximal ideal of `R` containing `Ideal.span {x} ⊆ 𝔪`).
  have hmem_rs' : ∀ r ∈ rs', r ∈ IsLocalRing.maximalIdeal R := by
    intro r hr
    simp only [rs', List.mem_map] at hr
    obtain ⟨y, hy_mem, rfl⟩ := hr
    -- The comap of `𝔪 (R⧸(x))` under the surjective `mkq` is a maximal ideal
    -- of `R`; since `R` is local, it equals `𝔪 R`.  Hence `g y ∈ comap mkq 𝔪'`
    -- iff `g y ∈ 𝔪 R`.
    have hmax_comap : (Ideal.comap mkq
        (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have heq : Ideal.comap mkq
        (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}))
        = IsLocalRing.maximalIdeal R :=
      (IsLocalRing.isMaximal_iff R).mp hmax_comap
    rw [← heq, Ideal.mem_comap]
    exact (hg y).symm ▸ hmem_q y hy_mem
  -- Step 5: cons `x` onto `rs'` to form the length-`(k+1)` regular sequence.
  refine ⟨x :: rs', ?_, ?_, ?_⟩
  · simp [hlen_rs']
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr_in
    · exact hxMem
    · exact hmem_rs' r hr_in
  · -- `IsRegular R (x :: rs')` via `IsRegular.cons'`.
    -- Need `IsSMulRegular R x` (have `hxReg`) AND
    -- `IsRegular (QuotSMulTop x R) (rs'.map (Ideal.Quotient.mk (Ideal.span {x})))`.
    refine RingTheory.Sequence.IsRegular.cons' hxReg ?_
    -- After `cons'`: goal is `IsRegular (QuotSMulTop x R) (rs'.map mkq)`
    -- = `IsRegular (QuotSMulTop x R) rs'_q` (by `hmkmap`), implicit ring
    -- `R ⧸ Ideal.span {x}` (inferred from list type).
    rw [hmkmap]
    -- Goal: `IsRegular (QuotSMulTop x R) rs'_q` (implicit ring `R ⧸ (x)`).
    -- IH provides: `IsRegular (R ⧸ Ideal.span {x}) rs'_q` (same implicit
    -- ring, but M differs: `R ⧸ Ideal.span {x}` vs `QuotSMulTop x R = R ⧸ (x • ⊤)`).
    --
    -- The two M's are *equal as sets* — both are the quotient of `R` by the
    -- principal ideal `(x)`, written two different ways. The bridge is an
    -- explicit `R⧸(x)`-linear equiv between the two quotients, then
    -- `LinearEquiv.isRegular_congr` transports `hreg_q` across.  The two
    -- `mapQ` halves use `LinearMap.id` with `heq.le` / `heq.ge`, and
    -- `map_smul'` reduces to `rfl` after `Quotient.inductionOn` on the scalar
    -- (the `R⧸(x)`-action on both sides is `[s] • [r] = [s * r]`
    -- definitionally).
    open scoped Pointwise in
    have heq : (x • (⊤ : Submodule R R)) = (Ideal.span {x} : Submodule R R) := by
      ext y
      simp [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton,
        eq_comm, Dvd.dvd]
    let e : (R ⧸ (x • (⊤ : Submodule R R))) ≃ₗ[R ⧸ Ideal.span {x}]
        (R ⧸ Ideal.span {x}) := {
      toFun := Submodule.mapQ _ _ LinearMap.id heq.le
      invFun := Submodule.mapQ _ _ LinearMap.id heq.ge
      left_inv := by rintro ⟨r⟩; rfl
      right_inv := by rintro ⟨r⟩; rfl
      map_add' := map_add _
      map_smul' := by
        rintro q ⟨r⟩
        induction q using Quotient.inductionOn with
        | _ s => rfl
    }
    exact (LinearEquiv.isRegular_congr e.symm rs'_q).mp hreg_q

/-- Provenance: CUSTOM. -/
lemma exists_isRegular_of_regularLocal
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsRegularLocalRing R] :
    ∃ rs : List R, rs.length = (IsLocalRing.maximalIdeal R).spanFinrank
        ∧ (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
        ∧ RingTheory.Sequence.IsRegular R rs := by
  -- Strong induction on `n = spanFinrank R`, generalising `R` so the inductive
  -- hypothesis can be applied to the quotient `R/(x)` at smaller dimension.
  suffices haux : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R]
      [IsNoetherianRing R] [IsRegularLocalRing R],
      (IsLocalRing.maximalIdeal R).spanFinrank = n →
      ∃ rs : List R, rs.length = n ∧
        (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular R rs by
    exact haux _ R rfl
  intro n
  induction n with
  | zero =>
    -- Base case `dim 0`: spanFinrank = 0, hence `maximalIdeal R = ⊥` (so `R` is
    -- a field). The empty list is trivially `R`-regular on the nonzero ring `R`.
    intros R _ _ _ _ _hdim
    refine ⟨[], rfl, by simp, ?_⟩
    exact RingTheory.Sequence.IsRegular.nil R R
  | succ k ih =>
    -- Inductive case `dim (k + 1)`: delegate to `regularLocal_inductive_step`,
    -- supplying the inductive hypothesis at dimension `k`. The helper handles
    -- the substantive NZD-extraction + quotient-regularity + cons assembly.
    intros R _ _ _ _ hdim
    exact regularLocal_inductive_step (k := k) hdim (fun R' _ _ _ _ h => ih R' h)

/-- **Regular local rings are Cohen–Macaulay.** Every regular Noetherian
local ring is Cohen–Macaulay: a minimal generating set of `𝔪` is an
`R`-regular sequence of length `dim R`, so `depth(R) ≥ dim R`; combined
with the standard upper bound `depth(R) ≤ dim R` (Stacks 00LK) this gives
`depth(R) = dim R`.

This is the consumer-facing input for the codim-1 extension of a rational map
across a codim-2 closed point on a regular projective surface (pole purity):
the local ring `O_{S,x}` of a regular projective surface at a closed point is
regular of Krull dimension `2`, hence Cohen–Macaulay, hence has depth `2`,
which is exactly the input the local-cohomology vanishing `H^i_x(O_S) = 0` for
`i < 2` needs (Stacks 0AVF; see Hartshorne III.7).

The body combines `length_le_ringKrullDim_of_isRegular` (the upper bound) and
`exists_isRegular_of_regularLocal` (the lower bound) into
`depth = ringKrullDim`. 






 * Provenance: REFERENCE.
-/
instance of_regular (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsRegularLocalRing R] : CohenMacaulay R where
  depth_eq_krullDim := by
    -- Step 1: simplify `Module.depth` via the `else` branch
    --   (since `𝔪 • ⊤ = 𝔪 ≠ ⊤` for a local ring's maximal ideal).
    have h𝔪 : (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R R)
        ≠ (⊤ : Submodule R R) := by
      have heq : (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R R)
          = IsLocalRing.maximalIdeal R := by simp
      rw [heq]
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    rw [Module.depth, if_neg h𝔪]
    -- Step 2: convert RHS to the spanFinrank using
    -- `IsRegularLocalRing.spanFinrank_maximalIdeal`.
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
    -- Goal: ((sSup {n | …} : ℕ∞) : WithBot ℕ∞)
    --         = ((spanFinrank 𝔪 : ℕ) : WithBot ℕ∞)
    -- Step 3: it suffices to show the sSup equals spanFinrank as ℕ∞,
    -- via antisymmetry: upper bound from Helper 1, lower bound from Helper 2.
    have h1 : (sSup { n : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = n ∧
        (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
          ∧ RingTheory.Sequence.IsRegular R rs }
        : ℕ∞) = ((IsLocalRing.maximalIdeal R).spanFinrank : ℕ∞) := by
      apply le_antisymm
      · -- Upper bound: every element of the sSup-set is at most spanFinrank.
        apply sSup_le
        rintro n ⟨rs, rfl, _, hreg⟩
        have hub := length_le_ringKrullDim_of_isRegular hreg
        rw [← IsRegularLocalRing.spanFinrank_maximalIdeal] at hub
        exact_mod_cast hub
      · -- Lower bound: spanFinrank is achieved by Helper 2's regular sequence.
        obtain ⟨rs, hlen, hmem, hreg⟩ := exists_isRegular_of_regularLocal R
        apply le_sSup
        refine ⟨rs, ?_, hmem, hreg⟩
        exact_mod_cast hlen
    rw [h1]
    -- Final coercion: `((n : ℕ∞) : WithBot ℕ∞) = ((n : ℕ) : WithBot ℕ∞)`
    -- is the standard `Nat.cast`-tower commutation.
    rfl

end CohenMacaulay

end RingTheory
