/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.ABDepthExt

/-!
# Depth on short exact sequences and depth transport (Stacks 00LX)

Third file of the Auslander–Buchsbaum package.

* `RingTheory.Module.depth_of_short_exact` — the three crosswise depth
  inequalities on a short exact sequence `0 → N' → N → N'' → 0` of nonzero
  finite modules over a Noetherian local ring (Stacks tag 00LX), each a direct
  read-off of the long exact `Ext^*(κ, -)` sequence and the depth-via-Ext
  characterisation of `ABDepthExt`.
* `RingTheory.Module.depth_eq_of_linearEquiv` — depth is invariant under
  `R`-linear equivalence.
* `RingTheory.Module.ideal_smul_top_pi_const` and
  `RingTheory.Module.depth_pi_const_eq_depth_of_nonempty` — the depth of a
  constant Pi module `ι → M` (nonempty finite `ι`) equals the depth of `M`;
  the substrate identifying `depth(R^k) = depth(R)` for finite free modules in
  the Auslander–Buchsbaum base case.
-/

set_option autoImplicit false
-- The ported pi-const depth lemmas keep the source's `[Fintype ι] [DecidableEq ι]`
-- binders (used in the proofs via `Pi.single`/`Finset.univ`); silence the
-- style linters that suggest `[Finite ι]` + `classical` (precedent:
-- `Algebra/LocalizationCocycleBaseChange.lean`).
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

universe u v

open CategoryTheory

namespace RingTheory

namespace Module

/-! ## Depth on a short exact sequence

For a short exact sequence `0 → N' → N → N'' → 0` of nonzero finite modules
over a Noetherian local ring, the three modules' depths satisfy three
crosswise inequalities (Stacks tag 00LX), each a direct read-off of the
long exact `Ext^*(κ, -)` sequence and the depth-via-Ext characterisation
of `ABDepthExt`. -/

/-! ### Helper A: Ext-vanishing from strict depth bound

For a Noetherian local ring `(R, 𝔪)` and a nonzero finite `R`-module `M`,
if `(i : ℕ∞) < depth M` then every element of `Ext^i_R(κ, M)` is zero.

This packages `depth_eq_smallest_ext_index` for the LES chase: the
`n ≤ depth M` form with `n := i + 1` instantiates the `∀ j < i + 1`
quantifier at `j = i`. -/
private lemma ext_vanish_of_natCast_lt_depth
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [_root_.Module.Finite R M]
    [Nontrivial M] {i : ℕ}
    (h : (i : ℕ∞) < depth (IsLocalRing.maximalIdeal R) M)
    (e : CategoryTheory.Abelian.Ext.{u}
        (ModuleCat.of R (IsLocalRing.ResidueField R))
        (ModuleCat.of R M) i) : e = 0 := by
  have h' : ((i + 1 : ℕ) : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) M := by
    have hcast : ((i + 1 : ℕ) : ℕ∞) = (i : ℕ∞) + 1 := by push_cast; ring
    rw [hcast]; exact Order.add_one_le_of_lt h
  exact (depth_eq_smallest_ext_index (M := M) (i + 1)).mp h' i (Nat.lt_succ_self i) e

/-! ### Helper B: `ℕ∞` tsub bridge

If `(a : ℕ) ≤ d - 1` in `ℕ∞` and `1 ≤ a` (in `ℕ`), then
`((a + 1 : ℕ) : ℕ∞) ≤ d`.

Case-split on `d = ⊤` (trivial) and `d = ↑n` (drop to `ℕ` arithmetic).
Used for the `depth N' - 1` shift in the second SES inequality. -/
private lemma natCast_add_one_le_of_le_sub_one
    {d : ℕ∞} {a : ℕ} (ha : 1 ≤ a) (h : (a : ℕ∞) ≤ d - 1) :
    ((a + 1 : ℕ) : ℕ∞) ≤ d := by
  rcases eq_or_ne d ⊤ with hd | hd
  · simp [hd]
  · obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp hd
    -- Reduce to ℕ: turn `↑a ≤ ↑n - 1` into `a ≤ n - 1`, then `a + 1 ≤ n`.
    have h₂ : (a : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := by
      refine h.trans (le_of_eq ?_)
      rcases n with _ | n
      · rfl
      · push_cast; rfl
    have han : a ≤ n - 1 := by exact_mod_cast h₂
    have hle : a + 1 ≤ n := by omega
    exact Nat.cast_le.mpr hle

/-- Provenance: REFERENCE. -/
theorem depth_of_short_exact
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {N' N N'' : Type u}
    [AddCommGroup N'] [Module R N'] [_root_.Module.Finite R N'] [Nontrivial N']
    [AddCommGroup N] [Module R N] [_root_.Module.Finite R N] [Nontrivial N]
    [AddCommGroup N''] [Module R N''] [_root_.Module.Finite R N''] [Nontrivial N'']
    (f : N' →ₗ[R] N) (g : N →ₗ[R] N'')
    (_hf : Function.Injective f) (_hg : Function.Surjective g)
    (_hex : Function.Exact f g) :
    min (depth (IsLocalRing.maximalIdeal R) N')
        (depth (IsLocalRing.maximalIdeal R) N'')
      ≤ depth (IsLocalRing.maximalIdeal R) N
    ∧ min (depth (IsLocalRing.maximalIdeal R) N)
          (depth (IsLocalRing.maximalIdeal R) N' - 1)
        ≤ depth (IsLocalRing.maximalIdeal R) N''
    ∧ min (depth (IsLocalRing.maximalIdeal R) N)
          (depth (IsLocalRing.maximalIdeal R) N'' + 1)
        ≤ depth (IsLocalRing.maximalIdeal R) N' := by
  -- Package the SES as a `ShortComplex.ShortExact` in `ModuleCat.{u} R`.
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (by ext x; simpa using _hex.apply_apply_eq_zero x)
  have hS : S.ShortExact :=
    ModuleCat.shortComplex_shortExact S _hex _hf _hg
  -- The residue field as a ModuleCat object.
  set κ : ModuleCat.{u} R := ModuleCat.of R (IsLocalRing.ResidueField R) with hκ
  refine ⟨?_, ?_, ?_⟩
  · -- (1) min(depth N', depth N'') ≤ depth N
    rw [← ENat.forall_natCast_le_iff_le]
    intro a ha
    rw [le_min_iff] at ha
    obtain ⟨haN', haN''⟩ := ha
    rw [depth_eq_smallest_ext_index]
    intro i hi e
    -- `e : Ext κ S.X₂ i = Ext κ (of R N) i`; goal `e = 0`.
    have hicast : (i : ℕ∞) < (a : ℕ∞) := by exact_mod_cast hi
    have hiN' : (i : ℕ∞) < depth (IsLocalRing.maximalIdeal R) N' := hicast.trans_le haN'
    have hiN'' : (i : ℕ∞) < depth (IsLocalRing.maximalIdeal R) N'' := hicast.trans_le haN''
    -- `e ∘ S.g ∈ Ext κ (of R N'') i = 0`.
    have heg : e.comp (CategoryTheory.Abelian.Ext.mk₀ S.g) (add_zero i) = 0 :=
      ext_vanish_of_natCast_lt_depth hiN'' _
    obtain ⟨x₁, hx₁⟩ :=
      CategoryTheory.Abelian.Ext.covariant_sequence_exact₂ κ hS e heg
    -- `x₁ ∈ Ext κ (of R N') i = 0`.
    have hx₁_zero : x₁ = 0 := ext_vanish_of_natCast_lt_depth hiN' _
    rw [hx₁_zero] at hx₁
    simpa using hx₁.symm
  · -- (2) min(depth N, depth N' - 1) ≤ depth N''
    rw [← ENat.forall_natCast_le_iff_le]
    intro a ha
    rw [le_min_iff] at ha
    obtain ⟨haN, haN'sub⟩ := ha
    rw [depth_eq_smallest_ext_index]
    intro i hi e
    -- `e : Ext κ S.X₃ i = Ext κ (of R N'') i`; goal `e = 0`.
    have hicast : (i : ℕ∞) < (a : ℕ∞) := by exact_mod_cast hi
    have hiN : (i : ℕ∞) < depth (IsLocalRing.maximalIdeal R) N := hicast.trans_le haN
    -- `↑(i+1) < depth N'`: use Helper B with `a` and the inequality `hi : i + 1 ≤ a`.
    have hia : 1 ≤ a := by omega
    have ha1 : ((a + 1 : ℕ) : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) N' :=
      natCast_add_one_le_of_le_sub_one hia haN'sub
    have hsucc : ((i + 1 : ℕ) : ℕ∞) < depth (IsLocalRing.maximalIdeal R) N' := by
      have : ((i + 1 : ℕ) : ℕ∞) < ((a + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.add_lt_add_right hi 1
      exact this.trans_le ha1
    -- `e ∘ extClass ∈ Ext κ (of R N') (i + 1) = 0`.
    have hext : e.comp hS.extClass rfl = 0 :=
      ext_vanish_of_natCast_lt_depth hsucc _
    obtain ⟨x₂, hx₂⟩ :=
      CategoryTheory.Abelian.Ext.covariant_sequence_exact₃ κ hS e rfl hext
    -- `x₂ ∈ Ext κ (of R N) i = 0`.
    have hx₂_zero : x₂ = 0 := ext_vanish_of_natCast_lt_depth hiN _
    rw [hx₂_zero] at hx₂
    simpa using hx₂.symm
  · -- (3) min(depth N, depth N'' + 1) ≤ depth N'
    rw [← ENat.forall_natCast_le_iff_le]
    intro a ha
    rw [le_min_iff] at ha
    obtain ⟨haN, haN''add⟩ := ha
    rw [depth_eq_smallest_ext_index]
    intro i hi e
    -- `e : Ext κ S.X₁ i = Ext κ (of R N') i`; goal `e = 0`.
    have hicast : (i : ℕ∞) < (a : ℕ∞) := by exact_mod_cast hi
    have hiN : (i : ℕ∞) < depth (IsLocalRing.maximalIdeal R) N := hicast.trans_le haN
    -- `e ∘ S.f ∈ Ext κ (of R N) i = 0`.
    have hef : e.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero i) = 0 :=
      ext_vanish_of_natCast_lt_depth hiN _
    -- Split on `i = 0` vs `i ≥ 1`. For `i ≥ 1`, use `covariant_sequence_exact₁`.
    -- For `i = 0`, postcomposition by `S.f` is injective (since `S.f` is mono).
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      -- `e : Ext κ S.X₁ 0`; postcomp by `S.f` is injective; image is `e ∘ S.f = 0`,
      -- so `e = 0`.
      have hmono : CategoryTheory.Mono S.f :=
        (ModuleCat.mono_iff_injective _).mpr _hf
      have hinj := CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono κ S.f
      apply hinj
      simpa using hef
    · -- `i ≥ 1`. Let `i = j + 1` and use `covariant_sequence_exact₁` at
      -- `n₀ = j, n₁ = i = j + 1`.
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi0)
      -- `e : Ext κ (of R N') (j + 1)`. We need `Ext κ (of R N'') j = 0`.
      -- From `↑(j+2) ≤ ↑a ≤ depth N'' + 1`, get `↑j + 1 ≤ depth N''`, so `↑j < depth N''`.
      have hjN'' : (j : ℕ∞) < depth (IsLocalRing.maximalIdeal R) N'' := by
        have hja : j + 2 ≤ a := by omega
        have h_j2 : ((j + 2 : ℕ) : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) N'' + 1 := by
          refine le_trans ?_ haN''add
          exact_mod_cast hja
        have hcast : ((j + 2 : ℕ) : ℕ∞) = ((j + 1 : ℕ) : ℕ∞) + 1 := by push_cast; ring
        rw [hcast] at h_j2
        have h_canc : ((j + 1 : ℕ) : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) N'' :=
          (ENat.add_le_add_iff_right (by norm_num : (1 : ℕ∞) ≠ ⊤)).mp h_j2
        have hcast2 : ((j + 1 : ℕ) : ℕ∞) = (j : ℕ∞) + 1 := by push_cast; ring
        rw [hcast2] at h_canc
        exact (ENat.add_one_le_iff (by simp : (j : ℕ∞) ≠ ⊤)).mp h_canc
      obtain ⟨x₃, hx₃⟩ :=
        CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ κ hS e hef rfl
      -- `x₃ ∈ Ext κ (of R N'') j = 0`.
      have hx₃_zero : x₃ = 0 := ext_vanish_of_natCast_lt_depth hjN'' _
      rw [hx₃_zero] at hx₃
      simpa using hx₃.symm

/-- **Depth is preserved under `R`-linear equivalence.** For a commutative ring
`R`, an ideal `I ⊆ R`, and two `R`-modules `M, M'` with an `R`-linear
equivalence `e : M ≃ₗ[R] M'`, we have `depth I M = depth I M'`.

This is the standard "depth is an invariant of the isomorphism class" fact;
the proof has two steps: (1) the side-condition `I • ⊤ = ⊤` is preserved
under linear equivalence, and (2) the regular-sequence supremum sets agree
via `LinearEquiv.isRegular_congr`.

Together with `depth_pi_const_eq_depth_of_nonempty` below it identifies
`depth(M)` with `depth(R)` for `M` finite free, which closes the `pd(M) = 0`
base case of the Auslander–Buchsbaum formula. 






 * Provenance: CUSTOM.
-/
lemma depth_eq_of_linearEquiv {R : Type u} [CommRing R] (I : Ideal R)
    {M M' : Type v} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') :
    depth I M = depth I M' := by
  -- Step 1: `I • ⊤ = ⊤` is preserved under the linear equivalence.
  have hcond : (I • (⊤ : Submodule R M) = ⊤) ↔ (I • (⊤ : Submodule R M') = ⊤) := by
    have e_top : Submodule.map (e : M →ₗ[R] M') (⊤ : Submodule R M) = ⊤ := by
      rw [Submodule.map_top]; exact LinearEquiv.range e
    have e_symm_top :
        Submodule.map (e.symm : M' →ₗ[R] M) (⊤ : Submodule R M') = ⊤ := by
      rw [Submodule.map_top]; exact LinearEquiv.range e.symm
    refine ⟨?_, ?_⟩
    · intro h
      have hmap :=
        Submodule.map_smul'' I (⊤ : Submodule R M) (e : M →ₗ[R] M')
      rw [h, e_top] at hmap
      exact hmap.symm
    · intro h
      have hmap :=
        Submodule.map_smul'' I (⊤ : Submodule R M') (e.symm : M' →ₗ[R] M)
      rw [h, e_symm_top] at hmap
      exact hmap.symm
  -- Step 2: the `sSup` sets agree via `LinearEquiv.isRegular_congr`.
  unfold depth
  by_cases h : I • (⊤ : Submodule R M) = ⊤
  · simp [if_pos h, if_pos (hcond.mp h)]
  · rw [if_neg h, if_neg (mt hcond.mpr h)]
    congr 1
    ext n
    refine ⟨?_, ?_⟩
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem, (LinearEquiv.isRegular_congr e rs).mp hreg⟩
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem, (LinearEquiv.isRegular_congr e rs).mpr hreg⟩

/-! ### Depth of a constant Pi module equals the depth of the fiber

For a commutative ring `R`, ideal `I`, module `M`, and nonempty finite type `ι`,
`depth I (ι → M) = depth I M`. The proof goes through the regular-sequence
characterization: each `r`-action on `ι → M` is pointwise (so an `r ∈ R` is
regular on `ι → M` iff regular on `M`), and the quotient `(ι → M)/r·⊤`
identifies with `ι → M/r·⊤` via `Submodule.quotientPi`. The side condition
`I • ⊤ = ⊤` agrees on both sides via a `Pi.single` lifting argument.

This is the substrate needed to close the `pd_R(M) = 0` case of the
Auslander–Buchsbaum formula (where `M ≃ₗ[R] Fin k → R` via a basis). -/

/-- For any commutative ring `R`, ideal `I`, finite index `ι`, and module `M`,
the ideal-action `I • ⊤_{ι → M}` equals the pi-submodule of fibre `I • ⊤_M`s.
(Non-private: reused by the minimality argument in `ABFormula`.) 






 * Provenance: CUSTOM.
-/
lemma ideal_smul_top_pi_const
    {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) {M : Type v} [AddCommGroup M] [Module R M] :
    (I • (⊤ : Submodule R (ι → M))) =
      Submodule.pi (Set.univ : Set ι) (fun (_ : ι) => I • (⊤ : Submodule R M)) := by
  apply le_antisymm
  · intro f hf i _
    refine Submodule.smul_induction_on hf ?_ ?_
    · intro a hain x _
      change a • x i ∈ I • (⊤ : Submodule R M)
      exact Submodule.smul_mem_smul hain trivial
    · intro x y hx hy
      change (x + y) i ∈ _
      exact Submodule.add_mem _ hx hy
  · intro f hf
    rw [show f = ∑ j, Pi.single j (f j) from (Finset.univ_sum_single f).symm]
    refine Submodule.sum_mem _ ?_
    intro j _
    have hfj : f j ∈ I • (⊤ : Submodule R M) := hf j (Set.mem_univ j)
    have hmap :
        Pi.single j (f j) ∈
          Submodule.map (LinearMap.single R (fun (_ : ι) => M) j)
            (I • (⊤ : Submodule R M)) :=
      Submodule.mem_map.mpr ⟨f j, hfj, rfl⟩
    rw [Submodule.map_smul''] at hmap
    exact Submodule.smul_mono le_rfl le_top hmap

/-- The side condition `I • ⊤ = ⊤` agrees on `ι → M` and `M` for nonempty
finite `ι`: a free product of fibre `I•⊤_M`-witnesses combines to a
`I•⊤_{ι → M}`-witness (via `Pi.single`-lifting), and conversely a
`Pi.single j m`-projection at `j` reads off the witness on the fibre. -/
private lemma ideal_smul_top_pi_const_eq_top_iff
    {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (I : Ideal R) {M : Type v} [AddCommGroup M] [Module R M] :
    I • (⊤ : Submodule R (ι → M)) = ⊤ ↔ I • (⊤ : Submodule R M) = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro m _
    obtain ⟨j⟩ := ‹Nonempty ι›
    have hsingle_mem :
        (Pi.single j m : ι → M) ∈ I • (⊤ : Submodule R (ι → M)) := by
      rw [h]; trivial
    rw [ideal_smul_top_pi_const] at hsingle_mem
    have := hsingle_mem j (Set.mem_univ j)
    rwa [Pi.single_eq_same] at this
  · intro h
    rw [ideal_smul_top_pi_const, eq_top_iff]
    intro f _ i _
    rw [h]
    trivial

/-- `QuotSMulTop r (ι → M) ≃ₗ[R] ι → QuotSMulTop r M` for finite `ι`,
obtained by rewriting `r • ⊤ = Ideal.span {r} • ⊤` and using
`Submodule.quotientPi`. -/
private noncomputable def quotSMulTopPiConstLinearEquiv
    {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] (r : R)
    {M : Type v} [AddCommGroup M] [Module R M] :
    QuotSMulTop r (ι → M) ≃ₗ[R] (ι → QuotSMulTop r M) := by
  refine (Submodule.quotEquivOfEq _ _ ?_).trans (Submodule.quotientPi _)
  rw [← Submodule.ideal_span_singleton_smul r (⊤ : Submodule R (ι → M))]
  rw [ideal_smul_top_pi_const]
  congr 1
  funext _
  exact Submodule.ideal_span_singleton_smul r ⊤

/-- For nonempty finite `ι`, a list `rs : List R` is `(ι → M)`-regular iff it
is `M`-regular. Proof by induction on `rs`: the empty case reduces to
`Nontrivial (ι → M) ↔ Nontrivial M`; the cons case uses `Pi.isSMulRegular_iff`
(for the SMul-regular conjunct) plus `quotSMulTopPiConstLinearEquiv` +
`LinearEquiv.isRegular_congr` (to bridge the quotient regularity to the IH on
`QuotSMulTop r M`). -/
private lemma isRegular_pi_const_iff_of_nonempty
    {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rs : List R) :
    ∀ {M : Type v} [AddCommGroup M] [Module R M],
      RingTheory.Sequence.IsRegular (ι → M) rs ↔
        RingTheory.Sequence.IsRegular M rs := by
  induction rs with
  | nil =>
    intro M _ _
    refine ⟨?_, ?_⟩
    · rintro ⟨_, hPi_top⟩
      refine ⟨.nil R M, ?_⟩
      rw [Ideal.ofList_nil, Submodule.bot_smul] at hPi_top ⊢
      intro habs
      apply hPi_top
      rw [Submodule.eq_bot_iff] at habs ⊢
      intro f _
      funext i
      exact habs (f i) trivial
    · rintro ⟨_, hM_top⟩
      refine ⟨.nil R (ι → M), ?_⟩
      rw [Ideal.ofList_nil, Submodule.bot_smul] at hM_top ⊢
      obtain ⟨j⟩ := ‹Nonempty ι›
      intro habs
      apply hM_top
      rw [Submodule.eq_bot_iff] at habs ⊢
      intro m _
      have hsingle : (Pi.single j m : ι → M) = 0 := habs _ trivial
      have heval := congr_fun hsingle j
      rwa [Pi.single_eq_same, Pi.zero_apply] at heval
  | cons r rs' ih =>
    intro M _ _
    rw [RingTheory.Sequence.isRegular_cons_iff, RingTheory.Sequence.isRegular_cons_iff]
    refine and_congr ?_ ?_
    · constructor
      · intro h
        obtain ⟨j⟩ := ‹Nonempty ι›
        exact Pi.isSMulRegular_iff.mp h j
      · intro h
        exact Pi.isSMulRegular_iff.mpr fun _ => h
    · rw [LinearEquiv.isRegular_congr
        (quotSMulTopPiConstLinearEquiv (R := R) (ι := ι) r (M := M)) rs']
      exact ih (M := QuotSMulTop r M)

/-- **Depth of a constant Pi module.** For any commutative ring `R`, ideal `I`,
`R`-module `M`, and nonempty finite type `ι`, the depth of the Pi module
`ι → M` equals the depth of `M`:
```
  depth I (ι → M) = depth I M.
```
This is the substrate for the `pd_R(M) = 0` case of the Auslander–Buchsbaum
formula: a finite free module `M ≃ₗ[R] Fin k → R` has `depth(M) = depth(R)`,
so `0 + depth(M) = depth(R)` holds. 






 * Provenance: CUSTOM.
-/
lemma depth_pi_const_eq_depth_of_nonempty
    {R : Type u} [CommRing R] (I : Ideal R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {M : Type v} [AddCommGroup M] [Module R M] :
    depth I (ι → M) = depth I M := by
  unfold depth
  by_cases h : I • (⊤ : Submodule R (ι → M)) = ⊤
  · rw [if_pos h, if_pos ((ideal_smul_top_pi_const_eq_top_iff I).mp h)]
  · rw [if_neg h, if_neg (mt (ideal_smul_top_pi_const_eq_top_iff I).mpr h)]
    congr 1
    ext n
    refine ⟨?_, ?_⟩
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem, (isRegular_pi_const_iff_of_nonempty rs).mp hreg⟩
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem, (isRegular_pi_const_iff_of_nonempty rs).mpr hreg⟩

end Module

end RingTheory
