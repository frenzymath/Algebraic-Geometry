/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.WindowLedgerF3
import AlgebraicJacobian.RiemannRoch.BaseDivisor

/-!
# DDR-2 (mechanism) — the abstract window pinch (`informal/spec-dd-r.md` §1(ii))

The pure Riemann–Roch mechanism of the certified-degree pinch, π-free: against an
abstract embedding-level divisor `N` carrying the *transported* DD-0 window facts —
`H¹(𝒪(N)) = 0` (`hNwin`), `H¹(𝒪(N − D')) = 0` for all `deg D' ≤ 2g` (`hNnorm`, the
`N`-avatar of the ledger's `window_normalization`), and the budget `2g ≤ deg N`
(`hNdeg`, the `N`-avatar of `two_mul_genus_le_M_mul_windowδ`) — a divisor `D` whose
normalization window `H⁰(𝒪(N − D))` has corank exactly `g` in `H⁰(𝒪(N))` has
`deg D = g`, and is recovered pointwise as the base divisor of that window.

This is the form the fibrewise consumers (DDR-8) instantiate at a residue field
`K = κ(p)`, where the window divisor is the *base-field transport* of `M·F` at the
**base ledger constant** `M = windowM_choice π hπ g` — which need not agree with the
`K`-level ledger constant (`windowBound` is a fixed choice per field), so the window
facts enter as transported hypotheses, discharged by ledger names at the base field and
moved across the extension by the DD-4 transport seam.

* `AlgebraicGeometry.h0_window_sub_single_lt` — the strict drop at a point (abstract-`N`
  transcription of P-fib's `h0_normalization_sub_single_lt`).
* `AlgebraicGeometry.baseDivisorAt_window_normalization` — recovery of an effective
  degree-`g` divisor from its window (abstract-`N` transcription of P-fib's
  `baseDivisorAt_normalization`; the DDR-8 hook).
* `AlgebraicGeometry.deg_eq_genus_of_window_corank` — **the pinch**: corank `g` forces
  `deg D = g`.  First the DD-0 section bound (`h0_divisorSheaf_le_max_of_h0_one`) caps
  `deg D ≤ 2g` (`h⁰(𝒪(N − D)) = deg N + 1 − 2g ≥ 1`, F1's move), then the exact
  normalization window reads the degree off the corank.  No carve, no Mayer–Vietoris,
  no adaptation independence, no `hdeg`.
* `AlgebraicGeometry.deg_eq_genus_of_normalization_corank` — the ledger form: at the
  pack's own DD-0 constants the three `N`-hypotheses ARE the ledger names
  `window_embedding` / `window_normalization` / `two_mul_genus_le_M_mul_windowδ`.

No numeric window bound appears (DAT-D discipline rule 1).  The family-level
deliverables (`deg_divFamDivisor_of_carve`, `baseDivisor_eq_divFamDivisor_of_carve`)
are in `RiemannRoch/CarveDegree.lean`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule

namespace AlgebraicGeometry

open Scheme

section WindowPinch

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

/-- **The strict drop at a point, abstract window form**: for an effective `D'` of degree
`g` under an embedding level `N` with exact normalization windows (`hNnorm`) and budget
`2g ≤ deg N`, adding any closed point strictly drops `h⁰(𝒪(N − D'))`: when `deg x ≤ g`
both normalization windows are exact and the drop is `deg x ≥ 1`; when `deg x > g` the
raw DD-0 section bound undercuts the window value.  The abstract-`N` transcription of
P-fib's `h0_normalization_sub_single_lt` (consumed fibrewise by DDR-8, where `N` is the
base-field transport of the ledger window `M·F`). -/
lemma h0_window_sub_single_lt (n : ℕ) {gamma : ℕ}
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ))
    (N : Y.CurveDivisor)
    (hNnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ 2 * (n : ℤ) →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (n : ℤ) ≤ CurveDivisor.deg K N)
    (D' : Y.CurveDivisor) (hdeg : CurveDivisor.deg K D' = (n : ℤ))
    {x : Y} (hx : x ≠ genericPoint Y) (hgamma : gamma ≤ n := by omega) :
    Sheaf.h0 (Y.divisorSheaf K (N - D' - CurveDivisor.single hx 1))
      < Sheaf.h0 (Y.divisorSheaf K (N - D')) := by
  have hdx : 0 < Y.residueDeg K x := Scheme.residueDeg_pos hx
  have hdxz : (1 : ℤ) ≤ (Y.residueDeg K x : ℤ) := by exact_mod_cast hdx
  have hdegsingle : CurveDivisor.deg K (CurveDivisor.single hx 1)
      = 1 * (Y.residueDeg K x : ℤ) := CurveDivisor.deg_single K ⟨x, hx⟩ 1
  have hnn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hn2 : CurveDivisor.deg K D' ≤ 2 * (n : ℤ) := by omega
  have hbig : (Sheaf.h0 (Y.divisorSheaf K (N - D')) : ℤ)
      = CurveDivisor.deg K N - CurveDivisor.deg K D'
        + Sheaf.chi (Y.moduleKSheaf K) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hNnorm D' hn2),
      Scheme.CurveDivisor.deg_sub' K]
  rw [hχ, hdeg] at hbig
  have hsplit : N - D' - CurveDivisor.single hx 1
      = N - (D' + CurveDivisor.single hx 1) := by
    abel
  have hdegD'x : CurveDivisor.deg K (D' + CurveDivisor.single hx 1)
      = (n : ℤ) + (Y.residueDeg K x : ℤ) := by
    rw [CurveDivisor.deg_add, hdeg, hdegsingle]
    ring
  by_cases hd : (Y.residueDeg K x : ℤ) ≤ (n : ℤ)
  · -- small residue degree: both windows are exact
    have hn2' : CurveDivisor.deg K (D' + CurveDivisor.single hx 1) ≤ 2 * (n : ℤ) := by
      omega
    have hsmall : (Sheaf.h0 (Y.divisorSheaf K
          (N - (D' + CurveDivisor.single hx 1))) : ℤ)
        = CurveDivisor.deg K N
            - CurveDivisor.deg K (D' + CurveDivisor.single hx 1)
          + Sheaf.chi (Y.moduleKSheaf K) := by
      rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hNnorm _ hn2'),
        Scheme.CurveDivisor.deg_sub' K]
    rw [hχ, hdegD'x] at hsmall
    rw [hsplit]
    omega
  · -- large residue degree: the section bound undercuts the window
    have hsec := h0_divisorSheaf_le_max_of_h0_one K hO
      (N - D' - CurveDivisor.single hx 1)
    have hdegsub : CurveDivisor.deg K (N - D' - CurveDivisor.single hx 1)
        = CurveDivisor.deg K N - (n : ℤ) - (Y.residueDeg K x : ℤ) := by
      rw [Scheme.CurveDivisor.deg_sub' K, Scheme.CurveDivisor.deg_sub' K, hdeg,
        hdegsingle]
      ring
    rw [hdegsub] at hsec
    rcases le_max_iff.mp hsec with h0le | hvle
    · omega
    · omega

/-- **Recovery of the divisor from its window, abstract window form** (the DDR-8 hook):
for an effective `D'` of degree `g` under an embedding level `N` with exact
normalization windows and budget `2g ≤ deg N`, the base multiplicity of
`H⁰(𝒪(N − D'))` relative to `N` at every closed point is exactly `D'ₓ` — `≥` because
every section obeys the pole bound, `≤` because the strict drop provides a section not
vanishing one order deeper.  The abstract-`N` transcription of P-fib's
`baseDivisorAt_normalization`. -/
lemma baseDivisorAt_window_normalization (n : ℕ) {gamma : ℕ}
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ))
    (N : Y.CurveDivisor)
    (hNnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ 2 * (n : ℤ) →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (n : ℤ) ≤ CurveDivisor.deg K N)
    (D' : Y.CurveDivisor) (hD'0 : 0 ≤ D')
    (hdeg : CurveDivisor.deg K D' = (n : ℤ)) {x : Y} (hx : x ≠ genericPoint Y)
    (hgamma : gamma ≤ n := by omega) :
    (Scheme.baseDivisorAt K (divisorSections K (N - D') ⊤) N ⟨x, hx⟩ : ℤ)
      = coeffAt hx D' := by
  set T : Submodule K Y.functionField := divisorSections K (N - D') ⊤ with hT
  have hTA : T ≤ divisorSections K N ⊤ := by
    rw [hT]
    refine divisorSections_mono K ?_ ⊤
    refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy => ?_)
    have h0y := CurveDivisor.le_iff_coeffAt.mp hD'0 y hy
    rw [CurveDivisor.coeffAt_zero] at h0y
    rw [CurveDivisor.coeffAt_sub]
    omega
  have hnn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hn2 : CurveDivisor.deg K D' ≤ 2 * (n : ℤ) := by omega
  have hrank : (Sheaf.h0 (Y.divisorSheaf K (N - D')) : ℤ)
      = CurveDivisor.deg K N - CurveDivisor.deg K D'
        + Sheaf.chi (Y.moduleKSheaf K) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hNnorm D' hn2),
      Scheme.CurveDivisor.deg_sub' K]
  rw [hχ, hdeg] at hrank
  have hfr : Module.finrank K ↥T = Sheaf.h0 (Y.divisorSheaf K (N - D')) := by
    rw [hT]
    exact finrank_divisorSections_top K _
  have hTne : ∃ f ∈ T, f ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
    have := hfr
    rw [hbot, finrank_bot] at this
    omega
  refine le_antisymm ?_ ?_
  · -- `≤`: the strict drop provides an exact section
    have hlt : Sheaf.h0 (Y.divisorSheaf K (N - D' - CurveDivisor.single hx 1))
        < Sheaf.h0 (Y.divisorSheaf K (N - D')) :=
      h0_window_sub_single_lt n hO hχ N hNnorm hNdeg D' hdeg hx
    have hle : divisorSections K (N - D' - CurveDivisor.single hx 1) ⊤ ≤ T := by
      rw [hT]
      refine divisorSections_mono K ?_ ⊤
      refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy => ?_)
      by_cases hyx : y = x
      · subst hyx
        rw [CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_sub,
          CurveDivisor.coeffAt_single_self]
        omega
      · rw [CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_sub,
          CurveDivisor.coeffAt_single_of_ne hx hy hyx]
        omega
    have hne : divisorSections K (N - D' - CurveDivisor.single hx 1) ⊤ ≠ T := by
      intro heq
      have hfr2 : Module.finrank K
          ↥(divisorSections K (N - D' - CurveDivisor.single hx 1) ⊤)
          = Sheaf.h0 (Y.divisorSheaf K (N - D' - CurveDivisor.single hx 1)) :=
        finrank_divisorSections_top K _
      rw [heq, hfr] at hfr2
      omega
    obtain ⟨f, hfT, hfnot⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
    have hf0 : f ≠ 0 := by
      intro h0
      exact hfnot (h0 ▸ Submodule.zero_mem _)
    -- `f` obeys the `D'`-bound everywhere and violates the deeper bound at `x`
    have hmem := (mem_divisorSections_top_iff K hf0).mp (hT ▸ hfT)
    have hviol : ¬ (0 ≤ (N - D' - CurveDivisor.single hx 1)
        + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf0)) := by
      intro hok
      exact hfnot ((mem_divisorSections_top_iff K hf0).mpr hok)
    -- the violation must be at `x`, forcing exactness there
    have hexact : coeffAt hx (N
        + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf0))
        ≤ coeffAt hx D' := by
      by_contra hgt
      apply hviol
      refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy => ?_)
      have hy0 := CurveDivisor.le_iff_coeffAt.mp hmem y hy
      rw [CurveDivisor.coeffAt_zero] at hy0 ⊢
      rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub] at hy0
      rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_sub]
      by_cases hyx : y = x
      · subst hyx
        rw [CurveDivisor.coeffAt_single_self]
        rw [CurveDivisor.coeffAt_add] at hgt
        omega
      · rw [CurveDivisor.coeffAt_single_of_ne hx hy hyx]
        omega
    refine le_trans (Scheme.baseDivisorAt_le_coeffAt K hTA (hT ▸ hfT) hf0 hx) ?_
    rwa [CurveDivisor.coeffAt_add] at hexact ⊢
  · -- `≥`: every section obeys the pole bound at `x`
    obtain ⟨f, hfT, hf0, hach⟩ := Scheme.exists_coeffAt_eq_baseDivisorAt K hTA hTne hx
    have hmem := (mem_divisorSections_top_iff K hf0).mp (hT ▸ hfT)
    have hy0 := CurveDivisor.le_iff_coeffAt.mp hmem x hx
    rw [CurveDivisor.coeffAt_zero, CurveDivisor.coeffAt_add,
      CurveDivisor.coeffAt_sub] at hy0
    rw [← hach, CurveDivisor.coeffAt_add]
    omega

/-- **The residual base multiplicity vanishes in the normalized window.**  The
base-divisor recovery relative to `N` identifies `bd(H⁰(𝒪(N - D)))` with `D`; the
generic normalization lemma then says that the same section space has no residual
base point relative to `N - D`. -/
lemma baseDivisorAt_window_residual_eq_zero (n : ℕ) {gamma : ℕ}
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ))
    (N : Y.CurveDivisor)
    (hNnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ 2 * (n : ℤ) →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (n : ℤ) ≤ CurveDivisor.deg K N)
    (D : Y.CurveDivisor) (hD0 : 0 ≤ D)
    (hdeg : CurveDivisor.deg K D = (n : ℤ)) {x : Y} (hx : x ≠ genericPoint Y)
    (hgamma : gamma ≤ n := by omega) :
    (Scheme.baseDivisorAt K (divisorSections K (N - D) ⊤) (N - D) ⟨x, hx⟩ : ℤ) = 0 := by
  let T : Submodule K Y.functionField := divisorSections K (N - D) ⊤
  have hne : ∃ f ∈ T, f ≠ 0 := by
    have hnn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    have hn2 : CurveDivisor.deg K D ≤ 2 * (n : ℤ) := by omega
    have hrank : (Sheaf.h0 (Y.divisorSheaf K (N - D)) : ℤ)
        = CurveDivisor.deg K N - CurveDivisor.deg K D
          + Sheaf.chi (Y.moduleKSheaf K) := by
      rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hNnorm D hn2),
        Scheme.CurveDivisor.deg_sub' K]
    rw [hχ, hdeg] at hrank
    have hfr : Module.finrank K (T : Type u) = Sheaf.h0 (Y.divisorSheaf K (N - D)) := by
      rw [show T = divisorSections K (N - D) ⊤ from rfl]
      exact finrank_divisorSections_top K _
    refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
    rw [hbot, finrank_bot] at hfr
    omega
  have hTA : T ≤ divisorSections K N ⊤ := by
    rw [show T = divisorSections K (N - D) ⊤ from rfl]
    refine divisorSections_mono K ?_ ⊤
    refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy ↦ ?_)
    have h0y := CurveDivisor.le_iff_coeffAt.mp hD0 y hy
    rw [CurveDivisor.coeffAt_zero] at h0y
    rw [CurveDivisor.coeffAt_sub]
    omega
  have hbase : Scheme.baseDivisor K T N hne = D := by
    refine CurveDivisor.ext_coeffAt (fun y hy => ?_)
    rw [Scheme.coeffAt_baseDivisor K hne hy]
    simpa [T] using (baseDivisorAt_window_normalization n hO hχ N hNnorm hNdeg D hD0 hdeg hy)
  have hres := Scheme.baseDivisorAt_sub_baseDivisor_eq_zero K hTA hne hx
  rw [hbase] at hres
  exact_mod_cast hres

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] in
/-- **The certified-degree pinch, abstract window form** (spec-dd-r §1(ii)): a divisor
`D` whose normalization window `H⁰(𝒪(N − D))` has corank exactly `g` inside an exact
embedding window `H⁰(𝒪(N))` of budget `2g ≤ deg N` has `deg D = g`.  First the DD-0
section bound caps `deg D ≤ 2g` (`h⁰(𝒪(N − D)) = deg N + 1 − 2g ≥ 1`, F1's move), then
the exact normalization window reads the degree off the corank.  No carve, no
Mayer–Vietoris, no adaptation independence. -/
theorem deg_eq_genus_of_window_corank (n : ℕ) {gamma : ℕ}
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ))
    (N : Y.CurveDivisor)
    (hNwin : Subsingleton (Sheaf.HModule (Y.divisorSheaf K N) 1))
    (hNnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ 2 * (n : ℤ) →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (n : ℤ) ≤ CurveDivisor.deg K N)
    (D : Y.CurveDivisor)
    (hcorank : Module.finrank K ↥(divisorSections K (N - D) ⊤) + n
      = Sheaf.h0 (Y.divisorSheaf K N)) (hgamma : gamma ≤ n := by omega) :
    CurveDivisor.deg K D = (n : ℤ) := by
  have hrN : (Sheaf.h0 (Y.divisorSheaf K N) : ℤ)
      = CurveDivisor.deg K N + Sheaf.chi (Y.moduleKSheaf K) :=
    h0_eq_deg_add_chi_of_subsingleton_hModule_one _ hNwin
  rw [hχ] at hrN
  have hfr : Module.finrank K ↥(divisorSections K (N - D) ⊤)
      = Sheaf.h0 (Y.divisorSheaf K (N - D)) := finrank_divisorSections_top K _
  rw [hfr] at hcorank
  have hdegND : CurveDivisor.deg K (N - D)
      = CurveDivisor.deg K N - CurveDivisor.deg K D :=
    Scheme.CurveDivisor.deg_sub' K N D
  -- F1: the section bound caps `deg D ≤ 2g`
  have hsec := h0_divisorSheaf_le_max_of_h0_one K hO (N - D)
  rw [hdegND] at hsec
  have hD2n : CurveDivisor.deg K D ≤ 2 * (n : ℤ) := by
    rcases le_max_iff.mp hsec with h0le | hvle
    · omega
    · omega
  -- the exact normalization window reads off the degree
  have hnorm : (Sheaf.h0 (Y.divisorSheaf K (N - D)) : ℤ)
      = CurveDivisor.deg K N - CurveDivisor.deg K D
        + Sheaf.chi (Y.moduleKSheaf K) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hNnorm D hD2n), hdegND]
  rw [hχ] at hnorm
  omega

/-! ## §2 The ledger form -/

variable (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
  (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))

/-- **The certified-degree pinch, ledger form**: at the pack's own DD-0 window
`N = M·F`, the three transported hypotheses of `deg_eq_genus_of_window_corank` are the
ledger names `window_embedding`, `window_normalization`, and
`two_mul_genus_le_M_mul_windowδ`. -/
theorem deg_eq_genus_of_normalization_corank (g : ℕ)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (D : Y.CurveDivisor)
    (hcorank : Module.finrank K
        ↥(divisorSections K (windowM_choice π hπ g • fiberWeilDivisor π - D) ⊤) + g
      = Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • fiberWeilDivisor π))) :
    CurveDivisor.deg K D = (g : ℤ) := by
  refine deg_eq_genus_of_window_corank g hO hχ _ (window_embedding π hπ g)
    (fun D' hD' => window_normalization π hπ g D' hD') ?_ D hcorank
  rw [Scheme.CurveDivisor.deg_nsmul' K, deg_fiberWeilDivisor_windowδ]
  exact two_mul_genus_le_M_mul_windowδ π hπ g hO hχ

end WindowPinch

end AlgebraicGeometry
