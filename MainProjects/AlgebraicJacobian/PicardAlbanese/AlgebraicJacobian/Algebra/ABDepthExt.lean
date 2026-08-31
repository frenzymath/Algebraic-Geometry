/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.ABDepth

/-!
# Depth via the Ext characterisation (Stacks 00LW)

Second file of the Auslander–Buchsbaum package. For a Noetherian local ring
`(R, 𝔪)` with residue field `κ = R/𝔪` and a nonzero finite `R`-module `M`, the
depth of `M` equals the smallest index `i` at which `Ext^i_R(κ, M)` is nonzero
(Stacks tag 00LW).

* `RingTheory.Module.ext_smul_eq_zero_of_mem_annihilator` — `x ∈ Ann(N)` kills
  the `R`-action on `Ext^i_R(N, M)`.
* `RingTheory.Module.depth_eq_smallest_ext_index` — the depth-bound form of
  Stacks 00LW: `n ≤ depth 𝔪 M ↔ ∀ i < n, Ext^i_R(κ, M) = 0`.

The characterisation is stated via the depth-bound `↔` Ext-vanishing-below —
logically equivalent to "`depth M` is the smallest `i` with `Ext^i(κ, M) ≠ 0`"
and the form most convenient for the inductive proofs downstream.
-/

set_option autoImplicit false

universe u v

open CategoryTheory

namespace RingTheory

namespace Module

/-- **`Ann`-killing of Ext via R-linearity.** For any `R`-modules `N, M` and any
`x : R` in the annihilator of `N`, the `R`-action `x • e` on `e : Ext^i_R(N, M)`
is zero.

Proof: `x • e = (mk₀ (x • 𝟙_N)).comp e (zero_add i)` (by R-linearity:
`mk₀_smul + smul_comp + mk₀_id_comp`). For `x ∈ Ann(N)` the morphism
`x • 𝟙_N : N ⟶ N` is the zero map, so `mk₀ (x • 𝟙_N) = mk₀ 0 = 0`
(`mk₀_zero`), and `0.comp e = 0` (`zero_comp`).

This is the precise statement of the Stacks-00LW "`x ∈ 𝔪` annihilates
`Ext^*(κ, -)`" trick, lifted to the more general `x ∈ Ann(N)` form so it covers
both `N = κ` and `N = R/(x_1,…,x_k)`. It is reused by the matrix-collapse
argument of `ABSyzygy`. 






 * Provenance: CUSTOM.
-/
lemma ext_smul_eq_zero_of_mem_annihilator
    {R : Type u} [CommRing R]
    {N M : ModuleCat.{u} R} {i : ℕ} (e : Abelian.Ext.{u} N M i)
    {x : R} (hx : x ∈ Module.annihilator R (N : Type u)) :
    x • e = 0 := by
  -- Step 1: x • 𝟙_N = 0 in ModuleCat (the underlying linear map sends m ↦ x • m,
  -- which is 0 since x ∈ Ann(N)).
  have hkill : (x • (𝟙 N : N ⟶ N)) = (0 : N ⟶ N) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro n
    change x • n = 0
    exact Module.mem_annihilator.mp hx n
  -- Step 2: x • e = (mk₀ (x • 𝟙_N)).comp e (zero_add i) by R-linearity.
  have hreflect :
      (CategoryTheory.Abelian.Ext.mk₀ (x • (𝟙 N : N ⟶ N))).comp e (zero_add i)
        = x • e := by
    have hmk : (CategoryTheory.Abelian.Ext.mk₀ (x • (𝟙 N : N ⟶ N))
                : Abelian.Ext.{u} N N 0)
        = x • CategoryTheory.Abelian.Ext.mk₀ (𝟙 N) :=
      CategoryTheory.Abelian.Ext.mk₀_smul (R := R) x (𝟙 N)
    rw [hmk, CategoryTheory.Abelian.Ext.smul_comp,
        CategoryTheory.Abelian.Ext.mk₀_id_comp]
  -- Step 3: substitute hkill to collapse mk₀ … to mk₀ 0 = 0, then zero_comp.
  rw [← hreflect, hkill, CategoryTheory.Abelian.Ext.mk₀_zero,
      CategoryTheory.Abelian.Ext.zero_comp]

/-- **Depth via Ext characterisation.** For a Noetherian local ring `(R, 𝔪)`
with residue field `κ = R/𝔪` and a nonzero finite `R`-module `M`, the
depth-bound `n ≤ depth(M)` is equivalent to the vanishing of `Ext^i_R(κ, M)`
for all `i < n`. Equivalently, `depth(M)` is the smallest `i` at which
`Ext^i_R(κ, M)` is nonzero.

The body proceeds by induction on `n` (generalising `M`, so the inductive
hypothesis applies recursively to `M/xM`) via the long exact sequence of
`Ext^*(κ, -)` applied to `0 → M → M → M/xM → 0` for a non-zero-divisor
`x ∈ 𝔪`:

* the **forward** direction extracts an `M`-regular sequence of length `n+1`
  from the depth supremum (Nakayama rules out the `𝔪M = M` branch under
  `Nontrivial M`), cons-decomposes it via `isRegular_cons_iff`, and chases the
  LES of `Ext^*(κ, -)` on `IsSMulRegular.smulShortComplex_shortExact`, killing
  the multiplication-by-`x` maps with `ext_smul_eq_zero_of_mem_annihilator`;
* the **backward** direction derives `Subsingleton (κ →ₗ[R] M)` from
  `Ext^0(κ, M) = 0` (via `mk₀_eq_zero_iff` + `ModuleCat.hom_ext_iff`), invokes
  `IsSMulRegular.subsingleton_linearMap_iff` + `Ideal.annihilator_quotient` to
  obtain `x ∈ 𝔪` with `IsSMulRegular M x`, chases the LES to get Ext-vanishing
  on `M/xM` below `n`, applies the inductive hypothesis on `M/xM` (nontrivial
  by `nontrivial_quotSMulTop_of_mem_maximalIdeal`), and conses `x` onto the
  resulting regular sequence via `isRegular_cons_iff` + `le_sSup`. 






 * Provenance: REFERENCE.
-/
theorem depth_eq_smallest_ext_index
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [_root_.Module.Finite R M]
    [Nontrivial M] (n : ℕ) :
    (n : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) M ↔
      ∀ i : ℕ, i < n →
        ∀ e : Abelian.Ext.{u}
            (ModuleCat.of R (IsLocalRing.ResidueField R))
            (ModuleCat.of R M) i, e = 0 := by
  -- We generalize `M` so the inductive hypothesis is universally quantified
  -- over the module — this lets the induction step recursively apply the IH
  -- to the quotient `M / xM` (a *different* module of the same shape).
  induction n generalizing M with
  | zero =>
    -- LHS: `(0 : ℕ∞) ≤ depth M` is `bot_le`.
    -- RHS: `∀ i < 0, …` is vacuous since no `i` satisfies `i < 0`.
    exact ⟨fun _ i hi _ => absurd hi (Nat.not_lt_zero i), fun _ => bot_le⟩
  | succ n ih =>
    -- The Stacks 00LW inductive step. The blueprint sketch is:
    --
    -- (⇒) Assume `(n+1 : ℕ∞) ≤ depth M`. Then `Nontrivial M` rules out
    --     `𝔪 • ⊤ = ⊤` (Nakayama), so `depth M` is the supremum and we can
    --     extract an `M`-regular sequence `rs = x :: rs'` of length `n+1` in
    --     `𝔪`. The cons-decomposition `RingTheory.Sequence.isRegular_cons_iff`
    --     gives `IsSMulRegular M x` and `IsRegular (QuotSMulTop x M) rs'`.
    --     For `i = 0`: `Hom(κ, M) ↪ Hom(κ, M)` via `[x]` is `[x]` on the
    --     domain `Hom(κ, M)`, but `x ∈ 𝔪 = Ann(κ)` kills this on the κ side,
    --     so `Hom(κ, M) = 0`. Pass to `Ext^0` via `addEquiv₀`.
    --     For `1 ≤ i ≤ n`: the SES `0 → M →[x] M → M/xM → 0` (built via
    --     `IsSMulRegular.smulShortComplex_shortExact`) plus the fact that
    --     `[x]_*` is zero on `Ext^i(κ, M)` (because `x ∈ Ann κ` ⇒
    --     `x • 𝟙_κ = 0`, hence by `precomp_smul = smul_precomp` the
    --     R-action on `Ext^i(κ, M)` is annihilated by `x`) lets the
    --     LES connecting map `Ext^{i-1}(κ, M/xM) ↠ Ext^i(κ, M)` be
    --     surjective.  By IH applied to `M/xM` (we get `n ≤ depth (M/xM)`,
    --     so `Ext^j(κ, M/xM) = 0` for `j < n`) we conclude
    --     `Ext^i(κ, M) = 0` for `1 ≤ i ≤ n`.
    --
    -- (⇐) Assume `∀ i < n+1, ∀ e ∈ Ext^i(κ, M), e = 0`.
    --     Specialise at `i = 0` and use `Ext.addEquiv₀` to extract
    --     `Subsingleton (κ →ₗ[R] M)`.  Apply
    --     `IsSMulRegular.subsingleton_linearMap_iff` (Mathlib) with
    --     `N := ResidueField R` and `Module.annihilator R (ResidueField R) =
    --     maximalIdeal R` to obtain `x ∈ 𝔪` with `IsSMulRegular M x`.
    --     The SES + same "x annihilates Ext^*(κ, ·)" fact give
    --     `Ext^j(κ, M/xM) = 0` for `j < n` (via the LES at indices `j ≤ n-1`).
    --     `M/xM := QuotSMulTop x M` is `Nontrivial` by
    --     `nontrivial_quotSMulTop_of_mem_maximalIdeal` and `Module.Finite`
    --     as a quotient.  Apply `ih` on `M/xM` at index `n` to get a
    --     regular sequence `rs'` of length `n` in `𝔪` on `M/xM`.  Then
    --     `x :: rs'` is a regular sequence of length `n+1` in `𝔪` on `M`
    --     by `RingTheory.Sequence.isRegular_cons_iff`. This gives
    --     `(n+1 : ℕ∞) ≤ depth M` via `le_sSup` on the depth supremum.
    --
    -- The helper `ext_smul_eq_zero_of_mem_annihilator` above closes the
    -- substantive piece "`x ∈ Ann N` annihilates `Ext^i(N, M)`"; this is the
    -- algebraic fact under both directions of the iff. The remaining pieces
    -- are LES-of-Ext bookkeeping + supremum-extraction.
    refine ⟨?_, ?_⟩
    · -- (⇒) Forward direction: `(n+1 : ℕ∞) ≤ depth M → ∀ i ≤ n, Ext^i(κ, M) = 0`,
      -- via Nakayama-driven `depth = sSup` extraction + cons-decomposition +
      -- LES chase using `ext_smul_eq_zero_of_mem_annihilator` +
      -- `covariant_sequence_exact₁`.
      intro _hdepth i _hi _e
      -- Step 1: unfold `depth M = sSup S_M` (Nakayama rules out `𝔪 • ⊤ = ⊤`).
      have hne_M : (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) ≠ ⊤ :=
        Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson _))
      have hdepth_M_unfold :
          depth (IsLocalRing.maximalIdeal R) M
            = sSup { k : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = k ∧
              (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
              ∧ RingTheory.Sequence.IsRegular M rs } := by
        rw [depth, if_neg hne_M]
      -- Step 2: extract a regular sequence rs of length > n in 𝔪 on M.
      have hlt : (n : ℕ∞) < depth (IsLocalRing.maximalIdeal R) M := by
        calc (n : ℕ∞)
            < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
          _ ≤ _ := _hdepth
      rw [hdepth_M_unfold] at hlt
      obtain ⟨k, ⟨rs, hrs_len, hrs_mem, hrs_reg⟩, hk_lt⟩ := lt_sSup_iff.mp hlt
      have hrs_len_gt : n < rs.length := by
        rw [← hrs_len] at hk_lt
        exact_mod_cast hk_lt
      -- Step 3: rs is non-empty (length > n ≥ 0); decompose rs = x :: rs_tail.
      rcases rs with _ | ⟨x, rs_tail⟩
      · -- impossible: empty list has length 0, not > n.
        simp at hrs_len_gt
      have hxMem : x ∈ IsLocalRing.maximalIdeal R := hrs_mem x List.mem_cons_self
      have htail_mem : ∀ r ∈ rs_tail, r ∈ IsLocalRing.maximalIdeal R := fun r hr =>
        hrs_mem r (List.mem_cons_of_mem _ hr)
      have hcons := (RingTheory.Sequence.isRegular_cons_iff M x rs_tail).mp hrs_reg
      have hxReg : IsSMulRegular M x := hcons.1
      have hrs_tail_reg : RingTheory.Sequence.IsRegular (QuotSMulTop x M) rs_tail :=
        hcons.2
      have htail_len_ge : n ≤ rs_tail.length := by
        have h1 : n < (x :: rs_tail).length := hrs_len_gt
        simp [List.length_cons] at h1
        omega
      -- Step 4: `x ∈ Ann(κ)` via `Ideal.annihilator_quotient`.
      have hannih : Module.annihilator R (IsLocalRing.ResidueField R) =
          IsLocalRing.maximalIdeal R := Ideal.annihilator_quotient
      have hxAnnih : x ∈ Module.annihilator R (IsLocalRing.ResidueField R) :=
        hannih ▸ hxMem
      -- Step 5: build MxM and show depth MxM ≥ n via the prefix rs_tail.take n.
      let MxM : Type u := QuotSMulTop x M
      haveI : Nontrivial MxM :=
        nontrivial_quotSMulTop_of_mem_maximalIdeal M hxMem
      haveI : _root_.Module.Finite R MxM := inferInstance
      have hne_MxM : (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R MxM) ≠ ⊤ :=
        Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson _))
      let rs_n := rs_tail.take n
      have hrs_n_len : rs_n.length = n := by
        change (rs_tail.take n).length = n
        rw [List.length_take]
        omega
      have hrs_n_mem : ∀ r ∈ rs_n, r ∈ IsLocalRing.maximalIdeal R := fun r hr =>
        htail_mem r (List.mem_of_mem_take hr)
      have hrs_n_reg : RingTheory.Sequence.IsRegular MxM rs_n := by
        change RingTheory.Sequence.IsRegular MxM (rs_tail.take n)
        have hsplit : rs_tail = rs_tail.take n ++ rs_tail.drop n :=
          (List.take_append_drop _ _).symm
        have hwr : RingTheory.Sequence.IsWeaklyRegular MxM rs_tail :=
          hrs_tail_reg.toIsWeaklyRegular
        rw [hsplit] at hwr
        have hwr_n : RingTheory.Sequence.IsWeaklyRegular MxM (rs_tail.take n) :=
          ((RingTheory.Sequence.isWeaklyRegular_append_iff MxM _ _).mp hwr).1
        exact (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
          hrs_n_mem).mpr hwr_n
      have hdepth_MxM : (n : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) MxM := by
        rw [depth, if_neg hne_MxM]
        apply le_sSup
        refine ⟨rs_n, ?_, hrs_n_mem, hrs_n_reg⟩
        exact_mod_cast hrs_n_len
      -- Step 6: apply ih (M := MxM) at index n.
      have hMxM_vanish : ∀ j < n, ∀ e : Abelian.Ext.{u}
          (ModuleCat.of R (IsLocalRing.ResidueField R))
          (ModuleCat.of R MxM) j, e = 0 :=
        (ih (M := MxM)).mp hdepth_MxM
      -- Step 7: LES chase. Set up SES.
      let S : ShortComplex (ModuleCat.{u} R) :=
        ModuleCat.smulShortComplex (ModuleCat.of R M) x
      have hS : S.ShortExact := hxReg.smulShortComplex_shortExact
      -- `S.f = x • 𝟙_M` (definitional), hence `mk₀ S.f = x • mk₀ 𝟙`, hence
      -- `_e.comp (mk₀ S.f) (add_zero i) = x • _e = 0` (by helper at `x ∈ Ann κ`).
      have hSf_eq_smul : S.f = x • (𝟙 (ModuleCat.of R M) : _ ⟶ _) := rfl
      have hSf_kill :
          _e.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero i) = 0 := by
        have hcomp :
            _e.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero i) = x • _e := by
          rw [hSf_eq_smul]
          exact (CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀ _e x).symm
        rw [hcomp]
        exact ext_smul_eq_zero_of_mem_annihilator _e hxAnnih
      -- Split on i = 0 vs i ≥ 1.
      rcases Nat.eq_zero_or_pos i with hi0 | hi_pos
      · subst hi0
        -- Use mono S.f (since hxReg) + postcomp_mk₀_injective_of_mono.
        haveI hmono : CategoryTheory.Mono S.f := by
          rw [ModuleCat.mono_iff_injective]
          exact hxReg
        have hinj := CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono
          (ModuleCat.of R (IsLocalRing.ResidueField R)) S.f
        apply hinj
        change _e.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 0)
          = (0 : Abelian.Ext.{u} (ModuleCat.of R (IsLocalRing.ResidueField R))
              (ModuleCat.of R M) 0).comp (CategoryTheory.Abelian.Ext.mk₀ S.f)
              (add_zero 0)
        rw [CategoryTheory.Abelian.Ext.zero_comp]
        exact hSf_kill
      · -- i ≥ 1: write i = j + 1, then j < n and use covariant_sequence_exact₁.
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.pos_iff_ne_zero.mp hi_pos)
        have hj : j < n := by omega
        obtain ⟨x₃, hx₃⟩ :=
          CategoryTheory.Abelian.Ext.covariant_sequence_exact₁
            (ModuleCat.of R (IsLocalRing.ResidueField R)) hS _e hSf_kill rfl
        have hx₃_zero : x₃ = 0 := hMxM_vanish j hj _
        rw [hx₃_zero] at hx₃
        rw [← hx₃]; simp; rfl
    · -- (⇐) Backward direction: `(∀ i ≤ n, Ext^i(κ, M) = 0) → (n+1 : ℕ∞) ≤ depth M`.
      intro hext
      -- Step 1: From Ext^0(κ, M) = 0, extract `Subsingleton (κ →ₗ[R] M)`.
      -- For all R-linear maps `f g : κ →ₗ[R] M`, `mk₀ (ofHom f) = 0` in Ext^0
      -- (by `hext 0`), so via `mk₀_eq_zero_iff` the morphism `ofHom f = 0`,
      -- hence `f = 0`.  Both `f = 0 = g`.
      have hext0 : ∀ e : Abelian.Ext.{u}
          (ModuleCat.of R (IsLocalRing.ResidueField R))
          (ModuleCat.of R M) 0, e = 0 := hext 0 (Nat.succ_pos n)
      have hsubsing : Subsingleton (IsLocalRing.ResidueField R →ₗ[R] M) := by
        refine ⟨fun f g => ?_⟩
        have hf : (ModuleCat.ofHom f : ModuleCat.of R _ ⟶ ModuleCat.of R M) = 0 :=
          (CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff (ModuleCat.ofHom f)).mp
            (hext0 _)
        have hg : (ModuleCat.ofHom g : ModuleCat.of R _ ⟶ ModuleCat.of R M) = 0 :=
          (CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff (ModuleCat.ofHom g)).mp
            (hext0 _)
        have hf' : f = 0 := ModuleCat.hom_ext_iff.mp hf
        have hg' : g = 0 := ModuleCat.hom_ext_iff.mp hg
        rw [hf', hg']
      -- Step 2: Apply `subsingleton_linearMap_iff` to extract a regular element.
      -- The annihilator of `R ⧸ maximalIdeal R = ResidueField R` is `maximalIdeal R`
      -- by `Ideal.annihilator_quotient` (under the two-sided instance — automatic
      -- for commutative R).
      have hannih : Module.annihilator R (IsLocalRing.ResidueField R) =
          IsLocalRing.maximalIdeal R :=
        Ideal.annihilator_quotient
      have ⟨x, hxAnnih, hxReg⟩ :=
        IsSMulRegular.subsingleton_linearMap_iff.mp hsubsing
      have hxMem : x ∈ IsLocalRing.maximalIdeal R := hannih ▸ hxAnnih
      -- Step 3: Pass to `M/xM := QuotSMulTop x M` and apply IH at index n
      -- (LES chase to derive Ext-vanishing on M/xM, application of IH, and
      -- `isRegular_cons_iff` assembly).
      let MxM : Type u := QuotSMulTop x M
      haveI : Nontrivial MxM :=
        nontrivial_quotSMulTop_of_mem_maximalIdeal M hxMem
      -- `Module.Finite R (M / xM)` is automatic via `Module.Finite.quotient`.
      haveI : _root_.Module.Finite R MxM := inferInstance
      -- Step A: derive `∀ j < n, Ext^j(κ, MxM) = 0` from `hext` via the
      --   LES of `Ext^*(κ, ·)` on the SES `0 → M →[x] M → MxM → 0`.
      let S : ShortComplex (ModuleCat.{u} R) :=
        ModuleCat.smulShortComplex (ModuleCat.of R M) x
      have hS : S.ShortExact := hxReg.smulShortComplex_shortExact
      set κ : ModuleCat.{u} R := ModuleCat.of R (IsLocalRing.ResidueField R)
        with hκ
      have hMxM_vanish : ∀ j < n, ∀ e : Abelian.Ext.{u} κ
          (ModuleCat.of R MxM) j, e = 0 := by
        intro j hj e
        -- `e.comp hS.extClass rfl : Ext κ M (j+1) = 0` by `hext` at `j+1`.
        have he_ext : e.comp hS.extClass (rfl : j + 1 = j + 1) = 0 :=
          hext (j + 1) (by omega) _
        obtain ⟨x₂, hx₂⟩ :=
          CategoryTheory.Abelian.Ext.covariant_sequence_exact₃ κ hS e rfl he_ext
        -- `x₂ : Ext κ M j = 0` by `hext` at `j`.
        have hx₂_zero : x₂ = 0 := hext j (by omega) _
        rw [hx₂_zero] at hx₂
        rw [← hx₂]; simp; rfl
      -- Step B: apply `ih (M := MxM)` at index `n`.
      have hdepth_MxM : (n : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) MxM :=
        (ih (M := MxM)).mpr hMxM_vanish
      -- Step C: unfold `depth MxM = sSup`-clause and extract a witness rs'
      --   of length ≥ n on MxM in 𝔪 (when n ≥ 1; the n = 0 case uses []).
      have hne_MxM : (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R MxM) ≠ ⊤ :=
        Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson _))
      have hdepth_MxM_unfold :
          depth (IsLocalRing.maximalIdeal R) MxM
            = sSup { k : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = k ∧
              (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
              ∧ RingTheory.Sequence.IsRegular MxM rs } := by
        rw [depth, if_neg hne_MxM]
      obtain ⟨rs', hrs'_len_ge, hrs'_mem, hrs'_reg⟩ :
          ∃ rs' : List R, n ≤ rs'.length ∧
            (∀ r ∈ rs', r ∈ IsLocalRing.maximalIdeal R) ∧
            RingTheory.Sequence.IsRegular MxM rs' := by
        rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
        · subst hn0
          exact ⟨[], by simp, by simp,
            RingTheory.Sequence.IsRegular.nil R MxM⟩
        · have hlt : ((n - 1 : ℕ) : ℕ∞) <
              depth (IsLocalRing.maximalIdeal R) MxM := by
            have h1 : ((n - 1 : ℕ) : ℕ∞) < (n : ℕ∞) := by
              exact_mod_cast Nat.sub_lt hn_pos Nat.one_pos
            exact h1.trans_le hdepth_MxM
          rw [hdepth_MxM_unfold] at hlt
          obtain ⟨k, ⟨rs', hrs'_len_eq, hrs'_mem, hrs'_reg⟩, hk_lt⟩ :=
            lt_sSup_iff.mp hlt
          have hrs'_len_gt : n - 1 < rs'.length := by
            rw [← hrs'_len_eq] at hk_lt
            exact_mod_cast hk_lt
          refine ⟨rs', ?_, hrs'_mem, hrs'_reg⟩
          omega
      -- Step D: truncate rs' to length n; resulting sequence is M-regular.
      let rs_n := rs'.take n
      have hrs_n_len : rs_n.length = n := by
        change (rs'.take n).length = n
        rw [List.length_take]
        omega
      have hrs_n_mem : ∀ r ∈ rs_n, r ∈ IsLocalRing.maximalIdeal R := fun r hr =>
        hrs'_mem r (List.mem_of_mem_take hr)
      have hrs_n_reg : RingTheory.Sequence.IsRegular MxM rs_n := by
        change RingTheory.Sequence.IsRegular MxM (rs'.take n)
        have hsplit : rs' = rs'.take n ++ rs'.drop n :=
          (List.take_append_drop _ _).symm
        have hwr : RingTheory.Sequence.IsWeaklyRegular MxM rs' :=
          hrs'_reg.toIsWeaklyRegular
        rw [hsplit] at hwr
        have hwr_n : RingTheory.Sequence.IsWeaklyRegular MxM (rs'.take n) :=
          ((RingTheory.Sequence.isWeaklyRegular_append_iff MxM _ _).mp hwr).1
        exact (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
          hrs_n_mem).mpr hwr_n
      -- Step E: cons x to form a length-(n+1) M-regular sequence in 𝔪.
      have hrs_M_reg : RingTheory.Sequence.IsRegular M (x :: rs_n) :=
        (RingTheory.Sequence.isRegular_cons_iff M x rs_n).mpr ⟨hxReg, hrs_n_reg⟩
      have hrs_M_mem : ∀ r ∈ (x :: rs_n), r ∈ IsLocalRing.maximalIdeal R := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hxMem
        · exact hrs_n_mem r hr
      have hrs_M_len : (x :: rs_n).length = n + 1 := by simp [hrs_n_len]
      -- Step F: conclude `(n+1 : ℕ∞) ≤ depth M` via `le_sSup`.
      have hne_M : (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) ≠ ⊤ :=
        Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson _))
      rw [depth, if_neg hne_M]
      apply le_sSup
      refine ⟨x :: rs_n, ?_, hrs_M_mem, hrs_M_reg⟩
      exact_mod_cast hrs_M_len

end Module

end RingTheory
