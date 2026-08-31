/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.ABSyzygy

/-!
# The Auslander–Buchsbaum formula (Stacks 090V)

Fifth file of the Auslander–Buchsbaum package: for a nonzero finite module `M`
of finite projective dimension over a Noetherian local ring `(R, 𝔪)`,

* `RingTheory.auslander_buchsbaum_formula` —
  `pd_R(M) + depth_R(M) = depth(R)` (Stacks tag 090V), with the finite
  projective dimension encoded by an explicit `n : ℕ` with
  `Module.projectiveDimension R M = n`;
* `RingTheory.auslander_buchsbaum_formula_succ_pd` — the `pd_R(M) = k + 1` case,
  proved by Nat-induction on `k` (generalising `M`) along minimal surjections
  `R^n ↠ M`: the inductive step combines the syzygy descent of `ABSyzygy` with
  the two Stacks-00LX inequalities; the base case `pd M = 1` is the
  matrix-collapse argument on the free kernel `ker f ≅ R^k ↪ R^n` (whose matrix
  entries lie in `𝔪` by minimality).
-/

set_option autoImplicit false

universe u v

open CategoryTheory

namespace RingTheory

/-! ## The Auslander–Buchsbaum formula

For a nonzero finite module `M` of finite projective dimension over a
Noetherian local ring `(R, 𝔪)`, the **Auslander–Buchsbaum formula** reads
```
  pd_R(M) + depth(M) = depth(R)
```
(Stacks tag 090V). Unlike the Stacks proof (induction on `depth(M)` along
minimal resolutions), the proof formalised here inducts on `pd_R(M)` along
minimal surjections `R^n ↠ M`: the inductive step applies the induction
hypothesis to the syzygy `ker f` (with `pd(ker f) = pd(M) - 1` exactly, by the
descent/ascent bridges of `ABSyzygy`) and combines the two Stacks-00LX
inequalities arithmetically; the base case `pd M = 1` is a matrix-collapse
argument on the free kernel. -/

/-! ### ℕ∞ combine for the inductive step of Auslander–Buchsbaum

Pure arithmetic in `ℕ∞ = WithTop ℕ`: packages the inductive hypothesis
`j + depth(K) = depth(R)` together with the two `depth_of_short_exact`
inequalities (parts (2) and (3)) on the SES `0 → K → R^n → M → 0` — after
identifying `depth(R^n) = depth(R)` — into the conclusion
`(j+1) + depth(M) = depth(R)`. Valid for `j ≥ 1` (the inductive step
`pd M ≥ 2`); the `j = 0` / `pd M = 1` base case is handled separately via
matrix-collapse since part (3) is then vacuous. -/
private lemma enat_ab_inductive_combine {j : ℕ} {d dK dM : ℕ∞}
    (hIH : (j : ℕ∞) + dK = d)
    (h2 : min d (dK - 1) ≤ dM)
    (h3 : min d (dM + 1) ≤ dK)
    (hj : 1 ≤ j) :
    ((j + 1 : ℕ) : ℕ∞) + dM = d := by
  subst hIH
  cases dK with
  | top =>
    -- `dK = ⊤`: part (2) forces `dM = ⊤`, both sides are `⊤`.
    have hdM : dM = ⊤ := by
      have : (⊤ : ℕ∞) ≤ dM := by simpa using h2
      simpa using top_le_iff.mp this
    subst hdM; simp
  | coe K =>
    cases dM with
    | top =>
      -- `dM = ⊤`: part (3) gives `↑(j+K) ≤ ↑K`, i.e. `j ≤ 0`, contradiction.
      exfalso
      have : (j : ℕ∞) + (K : ℕ∞) ≤ (K : ℕ∞) := by simpa using h3
      rw [← Nat.cast_add, Nat.cast_le] at this
      omega
    | coe m =>
      -- All finite: reduce parts (2),(3) to `ℕ` disjunctions and finish with `omega`.
      have h2' : min ((j : ℕ∞) + (K : ℕ∞)) ((K : ℕ∞) - 1) ≤ (m : ℕ∞) := h2
      have h3' : min ((j : ℕ∞) + (K : ℕ∞)) ((m : ℕ∞) + 1) ≤ (K : ℕ∞) := h3
      rw [show ((K : ℕ∞) - 1) = ((K - 1 : ℕ) : ℕ∞) by
            cases K with
            | zero => simp
            | succ K => push_cast; rfl,
          ← Nat.cast_add] at h2'
      rw [show ((m : ℕ∞) + 1) = ((m + 1 : ℕ) : ℕ∞) by push_cast; rfl,
          ← Nat.cast_add] at h3'
      simp only [min_le_iff, Nat.cast_le] at h2' h3'
      rw [← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj]
      omega

/-! ### Exact projective dimension of the syzygy `ker f`

For a surjection `f : R^n ↠ M` with `pd_R M = k+2`, the kernel satisfies
`pd_R (ker f) = k+1` exactly. The upper bound `≤ k+1` is the syzygy-descent
helper `hasProjectiveDimensionLT_ker_of_surjection` packaged through
`projectiveDimension_le_iff`; the lower bound `≥ k+1` is the contrapositive of
the ascent helper `hasProjectiveDimensionLT_succ_of_hasProjectiveDimensionLT_ker`
through `projectiveDimension_ge_iff` (if `pd(ker f) < k+1` then `pd M < k+2`,
contradiction). This is the exact-pd input the inductive step needs to invoke
its induction hypothesis on `ker f`. -/
private lemma projectiveDimension_ker_eq_of_surjection
    {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    {n : ℕ} (f : (Fin n → R) →ₗ[R] M) (hf : Function.Surjective f)
    {k : ℕ}
    (hpdM : _root_.Module.projectiveDimension R M = ((k + 2 : ℕ) : WithBot ℕ∞)) :
    _root_.Module.projectiveDimension R (LinearMap.ker f) = ((k + 1 : ℕ) : WithBot ℕ∞) := by
  have hM3 : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 2 + 1) :=
    Module.hasProjectiveDimensionLT_succ_of_projectiveDimension_eq hpdM
  have hK2 : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker f)) (k + 2) :=
    Module.hasProjectiveDimensionLT_ker_of_surjection f hf (k := k + 1) hM3
  have hle : _root_.Module.projectiveDimension R (LinearMap.ker f)
      ≤ ((k + 1 : ℕ) : WithBot ℕ∞) := by
    rw [show _root_.Module.projectiveDimension R (LinearMap.ker f)
          = CategoryTheory.projectiveDimension (ModuleCat.of R (LinearMap.ker f)) from rfl,
        CategoryTheory.projectiveDimension_le_iff]
    exact hK2
  have hge : ((k + 1 : ℕ) : WithBot ℕ∞)
      ≤ _root_.Module.projectiveDimension R (LinearMap.ker f) := by
    rw [show _root_.Module.projectiveDimension R (LinearMap.ker f)
          = CategoryTheory.projectiveDimension (ModuleCat.of R (LinearMap.ker f)) from rfl,
        CategoryTheory.projectiveDimension_ge_iff]
    intro hK1
    have hM2 : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 2) :=
      Module.hasProjectiveDimensionLT_succ_of_hasProjectiveDimensionLT_ker f hf (k := k) hK1
    have hlt : CategoryTheory.projectiveDimension (ModuleCat.of R M)
        < ((k + 2 : ℕ) : WithBot ℕ∞) :=
      CategoryTheory.projectiveDimension_lt_iff.mpr hM2
    rw [show CategoryTheory.projectiveDimension (ModuleCat.of R M)
          = _root_.Module.projectiveDimension R M from rfl, hpdM] at hlt
    exact absurd hlt (lt_irrefl _)
  exact le_antisymm hle hge

/-- **The `pd_R(M) = k + 1` case of the Auslander–Buchsbaum formula.**

Proof by Nat-induction on `k`, generalising `M`:

* **Base case `pd M = 1`** (matrix-collapse). Take a minimal surjection
  `f : R^n ↠ M` (`exists_minimalSurjection_finite_localRing`); its kernel has
  `pd = 0`, hence is finite free, say `ker f ≅ R^k` with `k ≥ 1`, and the
  inclusion `A : R^k ↪ R^n` has all matrix entries in `𝔪` (minimality). For
  `≤`: with `depth R = D` finite, pick a nonzero class `α ∈ Ext^D(κ, R^k)`
  (`exists_ne_zero_ext_of_depth_eq`); the matrix-collapse
  `ext_comp_mk₀_ofHom_eq_zero_of_entries_mem_annihilator` kills `α ∘ mk₀ A`, so
  the LES of `Ext^*(κ, -)` on `0 → R^k → R^n → M → 0` produces a nonzero class
  in `Ext^{D-1}(κ, M)`, forcing `depth M + 1 ≤ D`. For `≥`: part (2) of
  `depth_of_short_exact` gives `depth R - 1 ≤ depth M`.

* **Inductive step `pd M = k + 2`.** For a minimal surjection `f : R^n ↠ M`,
  `pd (ker f) = k + 1` exactly (`projectiveDimension_ker_eq_of_surjection`);
  the induction hypothesis on `ker f` plus the two Stacks-00LX inequalities
  (`depth_ses_ineqs_of_surjection_finite_localRing`) combine arithmetically via
  `enat_ab_inductive_combine`. 






 * Provenance: REFERENCE.
-/
lemma auslander_buchsbaum_formula_succ_pd
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [_root_.Module.Finite R M]
    [Nontrivial M] (k : ℕ)
    (_hpd : _root_.Module.projectiveDimension R M
        = ((k + 1 : ℕ) : WithBot ℕ∞)) :
    ((k + 1 : ℕ) : ℕ∞) + Module.depth (IsLocalRing.maximalIdeal R) M
      = Module.depth (IsLocalRing.maximalIdeal R) R := by
  -- Nat-induction on `k`, generalizing `M`. The inductive step `pd M = k+2`
  -- is closed via the syzygy descent (IH on `ker f` with exact
  -- `pd (ker f) = k+1`) plus the two `depth_of_short_exact` inequalities,
  -- combined arithmetically by `enat_ab_inductive_combine`. The base case
  -- `pd M = 1` is the matrix-collapse argument, using
  -- `ext_comp_mk₀_ofHom_eq_zero_of_entries_mem_annihilator` + an LES chase.
  induction k generalizing M with
  | zero =>
    -- **Base case `pd M = 1`** (Path B matrix-collapse).
    -- The minimal surjection `f : R^n ↠ M` has free kernel `K = ker f`
    -- (pd K = 0); writing `K ≅ R^k`, the inclusion `A : R^k ↪ R^n` has
    -- entries in `𝔪`. The matrix-collapse forces the LES of `Ext^*(κ, -)` to
    -- give `depth M + 1 = depth R`; combined with `depth_of_short_exact (2)`.
    obtain ⟨n, f, hf_surj, _hn_eq, hf_min⟩ :=
      Module.exists_minimalSurjection_finite_localRing R M
    -- `ker f` is projective (pd < 1), finite, hence free over the local ring.
    have hM_lt : HasProjectiveDimensionLT (ModuleCat.of R M) 2 :=
      Module.hasProjectiveDimensionLT_succ_of_projectiveDimension_eq _hpd
    haveI hK_lt : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker f)) 1 :=
      Module.hasProjectiveDimensionLT_ker_of_surjection f hf_surj (k := 0) hM_lt
    haveI hKproj : CategoryTheory.Projective (ModuleCat.of R (LinearMap.ker f)) :=
      inferInstance
    haveI : _root_.Module.Projective R (LinearMap.ker f) :=
      (IsProjective.iff_projective _).mpr hKproj
    haveI : _root_.Module.Flat R (LinearMap.ker f) := _root_.Module.Flat.of_projective
    haveI : _root_.Module.Finite R (LinearMap.ker f) := Module.IsNoetherian.finite R _
    haveI : _root_.Module.Free R (LinearMap.ker f) :=
      _root_.Module.free_of_flat_of_isLocalRing
    -- `ker f` is nonzero: else `f` is an iso and `M` would be free (pd 0 ≠ 1).
    haveI hKnt : Nontrivial (LinearMap.ker f) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      have hbot : LinearMap.ker f = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Submodule.mem_bot]
        exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker f) 0)
      have hfinj : Function.Injective f := LinearMap.ker_eq_bot.mp hbot
      let e : (Fin n → R) ≃ₗ[R] M := LinearEquiv.ofBijective f ⟨hfinj, hf_surj⟩
      haveI : _root_.Module.Free R M := _root_.Module.Free.of_equiv e
      haveI hMproj : CategoryTheory.Projective (ModuleCat.of R M) :=
        (IsProjective.iff_projective M).mp inferInstance
      have hMlt1 : HasProjectiveDimensionLT (ModuleCat.of R M) 1 := inferInstance
      have hlt : CategoryTheory.projectiveDimension (ModuleCat.of R M) < ((1 : ℕ) : WithBot ℕ∞) :=
        CategoryTheory.projectiveDimension_lt_iff.mpr hMlt1
      rw [show CategoryTheory.projectiveDimension (ModuleCat.of R M)
            = _root_.Module.projectiveDimension R M from rfl, _hpd] at hlt
      simp at hlt
    -- `n ≥ 1`.
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso; subst h0
        exact not_subsingleton M (Function.Surjective.subsingleton hf_surj)
      · exact h
    -- The free kernel as `R^k`.
    set k := _root_.Module.finrank R (LinearMap.ker f) with hk_def
    let φ : (Fin k → R) ≃ₗ[R] LinearMap.ker f :=
      (_root_.Module.finBasis R (LinearMap.ker f)).equivFun.symm
    -- `k ≥ 1`: else `Fin k → R` is subsingleton, so `ker f` is too (via `φ`).
    haveI hNEk : Nonempty (Fin k) := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      haveI : Subsingleton (Fin k → R) := inferInstance
      exact (not_subsingleton (LinearMap.ker f))
        (Equiv.subsingleton φ.symm.toEquiv)
    have hk : 1 ≤ k := Fin.pos_iff_nonempty.mpr hNEk
    haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    haveI : Inhabited (Fin n) := ⟨⟨0, hn⟩⟩
    haveI : Inhabited (Fin k) := Classical.inhabited_of_nonempty hNEk
    haveI : Nontrivial (Fin n → R) := Pi.nontrivial
    haveI : Nontrivial (Fin k → R) := Pi.nontrivial
    let A : (Fin k → R) →ₗ[R] (Fin n → R) :=
      (LinearMap.ker f).subtype ∘ₗ (φ : (Fin k → R) →ₗ[R] LinearMap.ker f)
    have hAinj : Function.Injective A :=
      (Subtype.val_injective).comp φ.injective
    have hfA : ∀ x, f (A x) = 0 := fun x =>
      LinearMap.mem_ker.mp (φ x).2
    have hexact : Function.Exact A f := by
      rw [LinearMap.exact_iff]
      rw [show LinearMap.range A
            = Submodule.map (LinearMap.ker f).subtype (LinearMap.range
                (φ : (Fin k → R) →ₗ[R] LinearMap.ker f)) from LinearMap.range_comp _ _]
      rw [LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
    -- depths of the free pieces.
    have hdRn : Module.depth (IsLocalRing.maximalIdeal R) (Fin n → R)
        = Module.depth (IsLocalRing.maximalIdeal R) R :=
      Module.depth_pi_const_eq_depth_of_nonempty _
    have hdRk : Module.depth (IsLocalRing.maximalIdeal R) (Fin k → R)
        = Module.depth (IsLocalRing.maximalIdeal R) R :=
      Module.depth_pi_const_eq_depth_of_nonempty _
    -- Direction (A): `depth R - 1 ≤ depth M` from `depth_of_short_exact (2)`.
    have htriple := Module.depth_of_short_exact A f hAinj hf_surj hexact
    have hpart2 : Module.depth (IsLocalRing.maximalIdeal R) R - 1
        ≤ Module.depth (IsLocalRing.maximalIdeal R) M := by
      have h := htriple.2.1
      rw [hdRn, hdRk, min_eq_right tsub_le_self] at h
      exact h
    -- Entries of `A` lie in `𝔪 = Ann κ`.
    have hannih : _root_.Module.annihilator R (IsLocalRing.ResidueField R)
        = IsLocalRing.maximalIdeal R := Ideal.annihilator_quotient
    have hA_entries : ∀ (i : Fin n) (j : Fin k),
        A (Pi.single j 1) i ∈ _root_.Module.annihilator R
          ((ModuleCat.of R (IsLocalRing.ResidueField R) : ModuleCat.{u} R) : Type u) := by
      intro i j
      have hvec : A (Pi.single j 1)
          ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R (Fin n → R)) :=
        hf_min (φ (Pi.single j 1)).2
      rw [Module.ideal_smul_top_pi_const] at hvec
      have hcoord : A (Pi.single j 1) i
          ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R R) := hvec i (Set.mem_univ i)
      have hle : (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R R)
          ≤ IsLocalRing.maximalIdeal R := by
        rw [Submodule.smul_le]
        intro a ha b _
        rw [smul_eq_mul]
        exact Ideal.mul_mem_right b _ ha
      have : A (Pi.single j 1) i ∈ IsLocalRing.maximalIdeal R := hle hcoord
      rw [show _root_.Module.annihilator R
            ((ModuleCat.of R (IsLocalRing.ResidueField R) : ModuleCat.{u} R) : Type u)
            = IsLocalRing.maximalIdeal R from hannih]
      exact this
    -- The SES `0 → R^k →[A] R^n →[f] M → 0` as a `ShortComplex`.
    let S : ShortComplex (ModuleCat.{u} R) :=
      ShortComplex.mk (ModuleCat.ofHom A) (ModuleCat.ofHom f)
        (by
          rw [← ModuleCat.ofHom_comp, show f ∘ₗ A = 0 from LinearMap.ext hfA]
          rfl)
    have hS : S.ShortExact :=
      ModuleCat.shortComplex_shortExact S hexact hAinj hf_surj
    set κ : ModuleCat.{u} R := ModuleCat.of R (IsLocalRing.ResidueField R) with hκ
    -- Final equation `1 + depth M = depth R`.
    change ((1 : ℕ) : ℕ∞) + Module.depth (IsLocalRing.maximalIdeal R) M
        = Module.depth (IsLocalRing.maximalIdeal R) R
    rw [Nat.cast_one]
    refine le_antisymm ?_ ?_
    · -- Direction (B): `1 + depth M ≤ depth R` via the matrix-collapse LES.
      rcases eq_or_ne (Module.depth (IsLocalRing.maximalIdeal R) R) ⊤ with htop | hfin
      · rw [htop]; exact le_top
      · obtain ⟨D, hD_eq⟩ := WithTop.ne_top_iff_exists.mp hfin
        -- nonzero class in `Ext^D(κ, R^k)`.
        obtain ⟨α, hα⟩ :=
          Module.exists_ne_zero_ext_of_depth_eq (M := (Fin k → R)) (D := D)
            (by rw [hdRk]; exact hD_eq.symm)
        have hcollapse : α.comp (CategoryTheory.Abelian.Ext.mk₀ (ModuleCat.ofHom A))
            (add_zero D) = 0 :=
          Module.ext_comp_mk₀_ofHom_eq_zero_of_entries_mem_annihilator A hA_entries α
        rcases D with _ | D'
        · -- `D = 0`: `S.f` mono forces `α = 0`, contradicting `α ≠ 0`.
          exfalso
          haveI hmono : CategoryTheory.Mono (ModuleCat.ofHom A) := by
            rw [ModuleCat.mono_iff_injective]; exact hAinj
          apply hα
          apply CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono κ
            (ModuleCat.ofHom A)
          change α.comp (CategoryTheory.Abelian.Ext.mk₀ (ModuleCat.ofHom A)) (add_zero 0)
              = (0 : Abelian.Ext.{u} κ (ModuleCat.of R (Fin k → R)) 0).comp
                  (CategoryTheory.Abelian.Ext.mk₀ (ModuleCat.ofHom A)) (add_zero 0)
          rw [CategoryTheory.Abelian.Ext.zero_comp]
          exact hcollapse
        · -- `D = D'+1`: the connecting map yields a nonzero `Ext^{D'}(κ, M)`.
          obtain ⟨x₃, hx₃⟩ :=
            CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ κ hS α hcollapse
              (n₀ := D') rfl
          have hx₃ne : x₃ ≠ 0 := by
            intro h
            rw [h, CategoryTheory.Abelian.Ext.zero_comp] at hx₃
            exact hα hx₃.symm
          have hnotle : ¬ ((D' + 1 : ℕ) : ℕ∞)
              ≤ Module.depth (IsLocalRing.maximalIdeal R) M := by
            rw [Module.depth_eq_smallest_ext_index (M := M) (D' + 1)]
            intro hcontra
            exact hx₃ne (hcontra D' (Nat.lt_succ_self D') x₃)
          calc (1 : ℕ∞) + Module.depth (IsLocalRing.maximalIdeal R) M
              = Module.depth (IsLocalRing.maximalIdeal R) M + 1 := add_comm _ _
            _ ≤ ((D' + 1 : ℕ) : ℕ∞) := Order.add_one_le_of_lt (not_le.mp hnotle)
            _ = Module.depth (IsLocalRing.maximalIdeal R) R := hD_eq
    · -- Direction (A).
      calc Module.depth (IsLocalRing.maximalIdeal R) R
          ≤ Module.depth (IsLocalRing.maximalIdeal R) R - 1 + 1 := le_tsub_add
        _ ≤ Module.depth (IsLocalRing.maximalIdeal R) M + 1 := by gcongr
        _ = 1 + Module.depth (IsLocalRing.maximalIdeal R) M := add_comm _ _
  | succ k ih =>
    -- **Inductive step `pd M = k+2`.** No matrix-collapse needed.
    obtain ⟨n, f, hf_surj, _hn_eq, _hf_min⟩ :=
      Module.exists_minimalSurjection_finite_localRing R M
    -- `pd (ker f) = k+1` exactly.
    have hpdK : _root_.Module.projectiveDimension R (LinearMap.ker f)
        = ((k + 1 : ℕ) : WithBot ℕ∞) :=
      projectiveDimension_ker_eq_of_surjection f hf_surj (k := k) _hpd
    -- `ker f` is nonzero (else `pd (ker f) = ⊥ ≠ k+1`).
    haveI hKnt : Nontrivial (LinearMap.ker f) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      have hbot : _root_.Module.projectiveDimension R (LinearMap.ker f) = ⊥ := by
        rw [show _root_.Module.projectiveDimension R (LinearMap.ker f)
              = CategoryTheory.projectiveDimension
                  (ModuleCat.of R (LinearMap.ker f)) from rfl,
            CategoryTheory.projectiveDimension_eq_bot_iff]
        exact (ModuleCat.isZero_of_subsingleton _)
      rw [hpdK] at hbot
      exact absurd hbot (by simp)
    -- `n ≥ 1` (else `R^0 ≅ 0` surjects onto the nonzero `M`).
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso
        subst h0
        haveI : Subsingleton (Fin 0 → R) := inferInstance
        have hMsub : Subsingleton M := Function.Surjective.subsingleton hf_surj
        exact not_subsingleton M hMsub
      · exact h
    -- IH on `ker f`: `(k+1) + depth (ker f) = depth R`.
    have hIH : ((k + 1 : ℕ) : ℕ∞)
        + Module.depth (IsLocalRing.maximalIdeal R) (LinearMap.ker f)
        = Module.depth (IsLocalRing.maximalIdeal R) R :=
      ih hpdK
    -- The two SES inequalities (parts (2),(3)).
    obtain ⟨h2, h3⟩ :=
      Module.depth_ses_ineqs_of_surjection_finite_localRing hn f hf_surj
    -- Combine arithmetically.
    have hcombine := enat_ab_inductive_combine hIH h2 h3 (Nat.le_add_left 1 k)
    simpa using hcombine

/-- **The Auslander–Buchsbaum formula.** Let `(R, 𝔪)` be a Noetherian local
ring and let `M` be a nonzero finite `R`-module of finite projective
dimension. Then
```
  pd_R(M) + depth_R(M) = depth(R).
```

The hypothesis "finite projective dimension" is encoded by an explicit
upper bound `n : ℕ` on the projective dimension (so the formula compares
finite numeric quantities cleanly without `WithBot ℕ∞`-arithmetic
subtleties).

The case `pd_R(M) = 0` (`M` finite free) goes via the finite-free-module +
`depth_pi_const_eq_depth_of_nonempty` route; the case `pd_R(M) = k + 1` is
`auslander_buchsbaum_formula_succ_pd`. 






 * Provenance: REFERENCE.
-/
theorem auslander_buchsbaum_formula
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [_root_.Module.Finite R M]
    [Nontrivial M]
    (n : ℕ)
    (_hpd : _root_.Module.projectiveDimension R M = (n : WithBot ℕ∞)) :
    (n : ℕ∞) + Module.depth (IsLocalRing.maximalIdeal R) M
      = Module.depth (IsLocalRing.maximalIdeal R) R := by
  -- We split on `n` to isolate the base case `pd_R(M) = 0` (where `M` is
  -- finite free over a Noetherian local ring) from the case `pd_R(M) = k + 1`
  -- (which inducts on `pd` along minimal surjections in
  -- `auslander_buchsbaum_formula_succ_pd`).
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · -- **Base case `n = 0`**: `pd_R(M) = 0` ⟹ `M` projective ⟹ (finite + local)
    -- `M` free ⟹ `depth(M) = depth(R)`. The formula
    -- `0 + depth(M) = depth(R)` collapses to `depth(M) = depth(R)`.
    subst hn0
    rw [Nat.cast_zero, zero_add]
    -- Step 1: unfold `_root_.Module.projectiveDimension` to the categorical
    -- form, then apply `projectiveDimension_eq_zero_iff`.
    have hpd' :
        CategoryTheory.projectiveDimension (ModuleCat.of R M) = (0 : WithBot ℕ∞) := by
      unfold _root_.Module.projectiveDimension at _hpd
      exact _hpd
    obtain ⟨hproj, _hNonZero⟩ :=
      (CategoryTheory.projectiveDimension_eq_zero_iff _).mp hpd'
    -- Step 2: `CategoryTheory.Projective (ModuleCat.of R M)` ⟹ `Module.Projective R M`.
    have hMproj : _root_.Module.Projective R M :=
      (IsProjective.iff_projective M).mpr hproj
    -- Step 3: `Module.Projective` ⟹ `Module.Flat`.
    haveI : _root_.Module.Flat R M := _root_.Module.Flat.of_projective
    -- Step 4: `Module.Flat` + `IsLocalRing` + `Module.Finite` ⟹ `Module.Free`.
    haveI : _root_.Module.Free R M := _root_.Module.free_of_flat_of_isLocalRing
    -- Step 5: with `M` finite free + `Nontrivial`, identify
    -- `depth(M) = depth(R)` via the `Module.finBasis` equivalence and
    -- `depth_eq_of_linearEquiv`, then `depth(Fin k → R) = depth(R)` for
    -- `k ≥ 1` via `depth_pi_const_eq_depth_of_nonempty`.
    have hk : 0 < _root_.Module.finrank R M :=
      (_root_.Module.finrank_pos_iff_of_free R M).mpr inferInstance
    set k : ℕ := _root_.Module.finrank R M with hk_def
    -- Build the equivalence `M ≃ₗ[R] (Fin k → R)` via the chosen basis.
    let e : M ≃ₗ[R] (Fin k → R) := (_root_.Module.finBasis R M).equivFun
    -- Transport `depth(M) = depth(Fin k → R)` along `e`.
    have hdepth_M_eq : Module.depth (IsLocalRing.maximalIdeal R) M
        = Module.depth (IsLocalRing.maximalIdeal R) (Fin k → R) :=
      Module.depth_eq_of_linearEquiv _ e
    rw [hdepth_M_eq]
    -- `depth(ι → M) = depth(M)` for nonempty finite `ι` (Pi-quotient
    -- decomposition + regular-sequence transport).
    haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact Module.depth_pi_const_eq_depth_of_nonempty _
  · -- **Case `n = k + 1`**: delegate to `auslander_buchsbaum_formula_succ_pd`.
    obtain ⟨k, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn_pos)
    exact auslander_buchsbaum_formula_succ_pd k _hpd

end RingTheory
