/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.BpfSpan

/-!
# DD-F — P-fib, the persistence heart of the Div^g carve

**The fibrewise heart of the DAT-D campaign** (`informal/dat-d-worksheet.md` §3.2;
`informal/dd-f-probe-verdict.md` §2 "P-fib in three lines"): on the curve bundle `Y`
over any field `K` with the DD-0 window ledger, given subspaces
`K_M ⊆ H⁰(𝒪(MF))`, `K' ⊆ H⁰(𝒪((M+s)F))` of codimension exactly `g` satisfying the
carve `(♦)` — `H⁰(𝒪(sF)) · K_M ⊆ K'` — there is a **unique** effective divisor `D` of
degree `g` with

  `K_M = H⁰(𝒪(MF − D))`  and  `K' = H⁰(𝒪((M+s)F − D))`
  (`existsUnique_effective_divisor_of_carve`).

## Route

* **F1 (normalization)**: `D := bd(K_M)` relative to `MF`; the DD-0 section bound caps
  `deg D ≤ 2g`, then the exact normalization window sharpens to `deg D ≤ g`
  (`inside the main proof`); `K_M ⊆ H⁰(𝒪(MF − D))` with no residual base point.
* **F3-core**: the bpf-span lemma (`mulSpan_eq_divisorSections_of_basepointFree`) makes
  the products span the full shifted window, which `(♦)` traps inside `K'`; the corank
  budget forces `deg D = g` and both containments to be equalities (the probe's `(♦)` +
  corank-`g` pinch).
* **Uniqueness**: `D` is recovered from `K_M` as its base divisor — at every closed
  point the window `H⁰(𝒪(MF − D))` drops strictly when the point is added
  (`h0_normalization_sub_single_lt`: the normalization window when `deg x ≤ g`, the raw
  section bound when `deg x > g`), so `bd(H⁰(𝒪(MF − D̃))) = D̃` for every effective `D̃`
  of degree `g` (`baseDivisorAt_normalization`).

This is the exact statement of worksheet §3.2 (⟹ direction; ⟸ is DD-4's §2.3), on the
DD-1c field-dictionary vocabulary: divisors are `CurveDivisor`, window sections are
`divisorSections _ _ ⊤ ⊆ K(Y)`, the carve is elementwise multiplication.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule

namespace AlgebraicGeometry

open Scheme

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
  (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
  (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))

/-! ## The strict drop at a point -/

/-- **The strict drop**: for an effective `D'` of degree `g`, adding any closed point to
the normalization window strictly drops `h⁰`: when `deg x ≤ g` the normalization windows
at depth `≤ 2g` are exact and the drop is `deg x ≥ 1`; when `deg x > g` the raw DD-0
section bound already undercuts the window value. The per-point recovery of `D'` from
`H⁰(𝒪(MF − D'))`. -/
lemma h0_normalization_sub_single_lt
    (g : ℕ) (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (D' : Y.CurveDivisor)
    (hdeg : CurveDivisor.deg K D' = (g : ℤ)) {x : Y} (hx : x ≠ genericPoint Y) :
    Sheaf.h0 (Y.divisorSheaf K
        (windowM_choice π hπ g • fiberWeilDivisor π - D' - CurveDivisor.single hx 1))
      < Sheaf.h0 (Y.divisorSheaf K
        (windowM_choice π hπ g • fiberWeilDivisor π - D')) := by
  have hdegF : CurveDivisor.deg K (fiberWeilDivisor π) = windowδ π :=
    deg_fiberWeilDivisor_windowδ π
  have hMd := two_mul_genus_le_M_mul_windowδ π hπ g hO hχ
  have hdx : 0 < Y.residueDeg K x := Scheme.residueDeg_pos hx
  have hdxz : (1 : ℤ) ≤ (Y.residueDeg K x : ℤ) := by exact_mod_cast hdx
  have hdegsingle : CurveDivisor.deg K (CurveDivisor.single hx 1)
      = 1 * (Y.residueDeg K x : ℤ) := CurveDivisor.deg_single K ⟨x, hx⟩ 1
  have hg2 : CurveDivisor.deg K D' ≤ 2 * (g : ℤ) := by omega
  have hbig := rank_normalization π hπ g D' hg2
  rw [hχ, hdeg] at hbig
  -- the subtracted-point divisor rewritten as one normalization
  have hsplit : windowM_choice π hπ g • fiberWeilDivisor π - D' - CurveDivisor.single hx 1
      = windowM_choice π hπ g • fiberWeilDivisor π - (D' + CurveDivisor.single hx 1) := by
    abel
  have hdegD'x : CurveDivisor.deg K (D' + CurveDivisor.single hx 1)
      = (g : ℤ) + (Y.residueDeg K x : ℤ) := by
    rw [CurveDivisor.deg_add, hdeg, hdegsingle]
    ring
  by_cases hd : (Y.residueDeg K x : ℤ) ≤ (g : ℤ)
  · -- small residue degree: both windows are exact
    have hg2' : CurveDivisor.deg K (D' + CurveDivisor.single hx 1) ≤ 2 * (g : ℤ) := by
      omega
    have hsmall := rank_normalization π hπ g (D' + CurveDivisor.single hx 1) hg2'
    rw [hχ, hdegD'x] at hsmall
    rw [hsplit]
    omega
  · -- large residue degree: the section bound undercuts the window
    have hsec := h0_divisorSheaf_le_max_of_h0_one K hO
      (windowM_choice π hπ g • fiberWeilDivisor π - D' - CurveDivisor.single hx 1)
    have hdegsub : CurveDivisor.deg K
        (windowM_choice π hπ g • fiberWeilDivisor π - D' - CurveDivisor.single hx 1)
        = (windowM_choice π hπ g : ℤ) * windowδ π - (g : ℤ)
          - (Y.residueDeg K x : ℤ) := by
      rw [Scheme.CurveDivisor.deg_sub' K, Scheme.CurveDivisor.deg_sub' K,
        Scheme.CurveDivisor.deg_nsmul' K, hdegF, hdeg, hdegsingle]
      ring
    rw [hdegsub] at hsec
    rcases le_max_iff.mp hsec with h0le | hvle
    · omega
    · omega

/-! ## The base-divisor recovery -/

/-- **Recovery of the divisor from its window** (the uniqueness mechanism): for an
effective `D̃` of degree `g`, the base multiplicity of `H⁰(𝒪(MF − D̃))` relative to `MF`
at every closed point is exactly `D̃ₓ` — `≥` because every section obeys the pole bound,
`≤` because the strict drop provides a section not vanishing one order deeper. -/
lemma baseDivisorAt_normalization
    (g : ℕ) (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (D' : Y.CurveDivisor) (hD'0 : 0 ≤ D')
    (hdeg : CurveDivisor.deg K D' = (g : ℤ)) {x : Y} (hx : x ≠ genericPoint Y) :
    (Scheme.baseDivisorAt K
        (divisorSections K (windowM_choice π hπ g • fiberWeilDivisor π - D') ⊤)
        (windowM_choice π hπ g • fiberWeilDivisor π) ⟨x, hx⟩ : ℤ)
      = coeffAt hx D' := by
  set Fd : Y.CurveDivisor := fiberWeilDivisor π with hFd
  set T : Submodule K Y.functionField :=
    divisorSections K (windowM_choice π hπ g • Fd - D') ⊤ with hT
  have hTA : T ≤ divisorSections K (windowM_choice π hπ g • Fd) ⊤ := by
    rw [hT]
    refine divisorSections_mono K ?_ ⊤
    refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy => ?_)
    have h0y := CurveDivisor.le_iff_coeffAt.mp hD'0 y hy
    rw [CurveDivisor.coeffAt_zero] at h0y
    rw [CurveDivisor.coeffAt_sub]
    omega
  -- the window is nonzero
  have hg2 : CurveDivisor.deg K D' ≤ 2 * (g : ℤ) := by
    have : (0 : ℤ) ≤ g := Int.natCast_nonneg g
    omega
  have hrank : (Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • Fd - D')) : ℤ)
      = (windowM_choice π hπ g : ℤ) * windowδ π - CurveDivisor.deg K D'
        + Sheaf.chi (Y.moduleKSheaf K) :=
    rank_normalization π hπ g D' hg2
  rw [hχ, hdeg] at hrank
  have hMd := two_mul_genus_le_M_mul_windowδ π hπ g hO hχ
  have hfr : Module.finrank K ↥T = Sheaf.h0 (Y.divisorSheaf K
      (windowM_choice π hπ g • Fd - D')) := by
    rw [hT]
    exact finrank_divisorSections_top K _
  have hTne : ∃ f ∈ T, f ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
    have := hfr
    rw [hbot, finrank_bot] at this
    omega
  refine le_antisymm ?_ ?_
  · -- `≤`: the strict drop provides an exact section
    have hlt : Sheaf.h0 (Y.divisorSheaf K
        (windowM_choice π hπ g • Fd - D' - CurveDivisor.single hx 1))
        < Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • Fd - D')) :=
      h0_normalization_sub_single_lt π hπ g hO hχ D' hdeg hx
    have hle : divisorSections K
        (windowM_choice π hπ g • Fd - D' - CurveDivisor.single hx 1) ⊤ ≤ T := by
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
    have hne : divisorSections K
        (windowM_choice π hπ g • Fd - D' - CurveDivisor.single hx 1) ⊤ ≠ T := by
      intro heq
      have hfr2 : Module.finrank K ↥(divisorSections K
          (windowM_choice π hπ g • Fd - D' - CurveDivisor.single hx 1) ⊤)
          = Sheaf.h0 (Y.divisorSheaf K
            (windowM_choice π hπ g • Fd - D' - CurveDivisor.single hx 1)) :=
        finrank_divisorSections_top K _
      rw [heq, hfr] at hfr2
      omega
    obtain ⟨f, hfT, hfnot⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
    have hf0 : f ≠ 0 := by
      intro h0
      exact hfnot (h0 ▸ Submodule.zero_mem _)
    -- `f` obeys the `D'`-bound everywhere and violates the deeper bound at `x`
    have hmem := (mem_divisorSections_top_iff K hf0).mp (hT ▸ hfT)
    have hviol : ¬ (0 ≤ (windowM_choice π hπ g • Fd - D' - CurveDivisor.single hx 1)
        + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf0)) := by
      intro hok
      exact hfnot ((mem_divisorSections_top_iff K hf0).mpr hok)
    -- the violation must be at `x`, forcing exactness there
    have hexact : coeffAt hx (windowM_choice π hπ g • Fd
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

/-! ## P-fib -/

/-- **P-fib** (★★★, worksheet §3.2 — the persistence heart of the Div^g carve): for
subspaces `K_M ⊆ H⁰(𝒪(MF))` and `K' ⊆ H⁰(𝒪((M+s)F))` of codimension exactly `g`
satisfying the carve `(♦)` — every product of a multiplier section with an element of
`K_M` lies in `K'` — there is a **unique** effective divisor `D` of degree `g` with
`K_M = H⁰(𝒪(MF − D))` and `K' = H⁰(𝒪((M+s)F − D))`. -/
theorem existsUnique_effective_divisor_of_carve
    (g : ℕ) (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (KM : Submodule K Y.functionField)
    (hKM : KM ≤ divisorSections K (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)
    (hKMrank : Module.finrank K ↥KM + g
      = Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • fiberWeilDivisor π)))
    (K' : Submodule K Y.functionField)
    (hK' : K' ≤ divisorSections K
      ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)
    (hK'rank : Module.finrank K ↥K' + g
      = Sheaf.h0 (Y.divisorSheaf K
          ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π)))
    (hcarve : ∀ h ∈ divisorSections K (windowS_choice π hπ g • fiberWeilDivisor π) ⊤,
      ∀ f ∈ KM, h * f ∈ K') :
    ∃! D : Y.CurveDivisor, 0 ≤ D ∧ CurveDivisor.deg K D = (g : ℤ) ∧
      KM = divisorSections K (windowM_choice π hπ g • fiberWeilDivisor π - D) ⊤ ∧
      K' = divisorSections K
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π - D) ⊤ := by
  classical
  set Fd : Y.CurveDivisor := fiberWeilDivisor π with hFd
  haveI hK'fin : Module.Finite K ↥K' := Submodule.finiteDimensional_of_le hK'
  have hdegF : CurveDivisor.deg K Fd = windowδ π := deg_fiberWeilDivisor_windowδ π
  have hδ1 := one_le_windowδ π
  have hMd := two_mul_genus_le_M_mul_windowδ π hπ g hO hχ
  -- ranks of the two embedding windows
  have hrM : (Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • Fd)) : ℤ)
      = (windowM_choice π hπ g : ℤ) * windowδ π + 1 - (g : ℤ) := by
    rw [hFd]
    exact rank_embedding_of_genus π hπ g hχ
  have hrMs : (Sheaf.h0 (Y.divisorSheaf K
        ((windowM_choice π hπ g + windowS_choice π hπ g) • Fd)) : ℤ)
      = ((windowM_choice π hπ g : ℤ) + (windowS_choice π hπ g : ℤ)) * windowδ π
        + 1 - (g : ℤ) := by
    rw [hFd]
    exact rank_embedding_shift_of_genus π hπ g hχ
  -- F1: `K_M` is nonzero, its base divisor is the divisor
  have hKMne : ∃ f ∈ KM, f ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
    rw [hbot, finrank_bot] at hKMrank
    omega
  set D : Y.CurveDivisor := Scheme.baseDivisor K KM (windowM_choice π hπ g • Fd) hKMne
    with hDdef
  have hD0 : 0 ≤ D := Scheme.baseDivisor_nonneg K hKMne
  have hDdeg0 : 0 ≤ CurveDivisor.deg K D := Scheme.CurveDivisor.deg_nonneg K hD0
  have hKMsub : KM ≤ divisorSections K (windowM_choice π hπ g • Fd - D) ⊤ := by
    rw [hDdef]
    exact Scheme.le_divisorSections_sub_baseDivisor K hKM hKMne
  -- the degree of the normalization level
  have hdegND : CurveDivisor.deg K (windowM_choice π hπ g • Fd - D)
      = (windowM_choice π hπ g : ℤ) * windowδ π - CurveDivisor.deg K D := by
    rw [Scheme.CurveDivisor.deg_sub' K, Scheme.CurveDivisor.deg_nsmul' K, hdegF]
  -- F1 degree bound: first `≤ 2g` by the section bound, then `≤ g` by the exact window
  have hfrKM : Module.finrank K ↥KM
      ≤ Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • Fd - D)) := by
    rw [← finrank_divisorSections_top K _]
    exact Submodule.finrank_mono hKMsub
  have hKMpos : 0 < Module.finrank K ↥KM := by omega
  have hposND : 0 < Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • Fd - D)) := by
    omega
  have hsec := h0_le_deg_add_one_of_pos K hO (windowM_choice π hπ g • Fd - D) hposND
  rw [hdegND] at hsec
  have hD2g : CurveDivisor.deg K D ≤ 2 * (g : ℤ) := by omega
  have hrND : (Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • Fd - D)) : ℤ)
      = (windowM_choice π hπ g : ℤ) * windowδ π - CurveDivisor.deg K D
        + Sheaf.chi (Y.moduleKSheaf K) :=
    rank_normalization π hπ g D hD2g
  rw [hχ] at hrND
  have hDg : CurveDivisor.deg K D ≤ (g : ℤ) := by omega
  -- the codimension of `K_M` inside its normalization window
  set c : ℕ := Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • Fd - D))
    - Module.finrank K ↥KM with hcdef
  have hcrank : Module.finrank K ↥KM + c
      = Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • Fd - D)) := by
    omega
  have hcg : c ≤ g := by omega
  -- the bpf achievers
  have hbpf : ∀ (x : Y) (hx : x ≠ genericPoint Y),
      ∃ (f : Y.functionField) (_ : f ∈ KM) (hf : f ≠ 0),
        coeffAt hx ((windowM_choice π hπ g • Fd - D)
          + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) = 0 := by
    intro x hx
    rw [hDdef]
    exact Scheme.exists_achiever_baseDivisor_sub K hKM hKMne hx
  -- F3-core: the span is the full shifted window
  have hspan : Scheme.mulSpan K (divisorSections K (windowS_choice π hπ g • Fd) ⊤) KM
      = divisorSections K
          ((windowM_choice π hπ g + windowS_choice π hπ g) • Fd - D) ⊤ :=
    mulSpan_eq_divisorSections_of_basepointFree π hπ g hO hχ D hD0 hDg
      KM hKMsub c hcg hcrank hbpf
  -- `(♦)` traps the span inside `K'`
  have hspanle : divisorSections K
      ((windowM_choice π hπ g + windowS_choice π hπ g) • Fd - D) ⊤ ≤ K' := by
    rw [← hspan]
    exact Scheme.mulSpan_le K hcarve
  -- corank pinch: `deg D = g`
  have hdegMsD : CurveDivisor.deg K
      ((windowM_choice π hπ g + windowS_choice π hπ g) • Fd - D)
      = ((windowM_choice π hπ g : ℤ) + (windowS_choice π hπ g : ℤ)) * windowδ π
        - CurveDivisor.deg K D := by
    rw [Scheme.CurveDivisor.deg_sub' K, Scheme.CurveDivisor.deg_nsmul' K, hdegF]
    push_cast
    ring
  have hrMsD : (Sheaf.h0 (Y.divisorSheaf K
        ((windowM_choice π hπ g + windowS_choice π hπ g) • Fd - D)) : ℤ)
      = ((windowM_choice π hπ g : ℤ) + (windowS_choice π hπ g : ℤ)) * windowδ π
        - CurveDivisor.deg K D + Sheaf.chi (Y.moduleKSheaf K) :=
    rank_normalization_shift π hπ g D hD2g
  rw [hχ] at hrMsD
  have hfrK' : Sheaf.h0 (Y.divisorSheaf K
      ((windowM_choice π hπ g + windowS_choice π hπ g) • Fd - D))
      ≤ Module.finrank K ↥K' := by
    rw [← finrank_divisorSections_top K _]
    exact Submodule.finrank_mono hspanle
  have hDeqg : CurveDivisor.deg K D = (g : ℤ) := by omega
  -- the two equalities
  have hKMeq : KM = divisorSections K (windowM_choice π hπ g • Fd - D) ⊤ := by
    refine Submodule.eq_of_le_of_finrank_le hKMsub ?_
    rw [finrank_divisorSections_top K _]
    omega
  have hK'eq : K' = divisorSections K
      ((windowM_choice π hπ g + windowS_choice π hπ g) • Fd - D) ⊤ := by
    refine (Submodule.eq_of_le_of_finrank_le hspanle ?_).symm
    rw [finrank_divisorSections_top K _]
    omega
  refine ⟨D, ⟨hD0, hDeqg, hKMeq, hK'eq⟩, ?_⟩
  -- uniqueness: the divisor is the base divisor of `K_M`
  rintro D' ⟨hD'0, hD'deg, hKM', _⟩
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  have hrec : (Scheme.baseDivisorAt K
      (divisorSections K (windowM_choice π hπ g • Fd - D') ⊤)
      (windowM_choice π hπ g • Fd) ⟨x, hx⟩ : ℤ) = coeffAt hx D' :=
    baseDivisorAt_normalization π hπ g hO hχ D' hD'0 hD'deg hx
  have hcoeffD : coeffAt hx D
      = (Scheme.baseDivisorAt K KM (windowM_choice π hπ g • Fd) ⟨x, hx⟩ : ℤ) := by
    rw [hDdef]
    exact Scheme.coeffAt_baseDivisor K hKMne hx
  rw [hKM'] at hcoeffD
  rw [hcoeffD]
  exact hrec.symm

end AlgebraicGeometry
