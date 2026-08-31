/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.BpfSpanCore
import AlgebraicJacobian.RiemannRoch.WindowLedgerF3

/-!
# DD-F — the bpf-span lemma (F3-core)

**The keystone of the P-fib route** (`informal/dd-f-probe-verdict.md` §2–3, the probe's
main finding; `informal/dat-d-worksheet.md` §3.3 F3): on the curve bundle `Y` with the
DD-0 window ledger, let `D ≥ 0` with `deg D ≤ g` and let `T ⊆ H⁰(𝒪(MF − D))` be a
subspace of codimension `c ≤ g` with **no base point** relative to `MF − D`. Then

  `span(H⁰(𝒪(sF)) · T) = H⁰(𝒪((M+s)F − D))`  — the FULL shifted window
  (`mulSpan_eq_divisorSections_of_basepointFree`).

## Route (the probe's §3, in the sum-intersection formalization)

Fix a functional `Λ` killing the span (the separating shell reduces to this):

* **(3a)** the annihilator kernel `N_Λ = {h ∈ H⁰(𝒪(sF)) : Λ(h·H⁰(𝒪(MF − D))) = 0}` has
  codimension `≤ c` (`finrank_le_finrank_annKernel_add`), hence is nonzero
  (`2g ≤ s·δ`, the ledger budget);
* **(3b)** its base locus `E = bd(N_Λ)` has `deg E ≤ g + c ≤ 2g` (the DD-0 section
  bound against the exact multiplier rank);
* **(3c)** the **descent engine** run on achievers of `E` shows `Λ` kills
  `H⁰(𝒪(MF − D + sF − E))`;
* **(3e)** at each point `x` of `E`, the **tower engine** with a bpf achiever
  `fx ∈ T` (exact order at `x`) lifts the kill up the multiplicity of `x`; the final
  iterated sum-intersection over the points of `E` reassembles the full window, so
  `Λ = 0` on it. ∎

The `≤ 2g`-codimension bound is spent exactly and only in (3b); the FULL multiplier
window is spent exactly in the tower jumps (worksheet §3.6(a) pencil counterexample).
Every window is discharged through the DD-0 ledger names and the `WindowLedgerF3`
addenda; no numeric bound appears outside them.
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

/-- **The bpf-span lemma** (★★, F3-core — the probe's main finding, closing worksheet
§3.3 F3+F4 in one statement): for an effective `D` of degree `≤ g` and a subspace
`T ⊆ H⁰(𝒪(MF − D))` of codimension `c ≤ g` with no base point relative to `MF − D`,
the products by the full multiplier window span the full shifted window:
`span(H⁰(𝒪(sF)) · T) = H⁰(𝒪((M+s)F − D))`. -/
theorem mulSpan_eq_divisorSections_of_basepointFree
    (g : ℕ) (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (D : Y.CurveDivisor) (hD0 : 0 ≤ D)
    (hDg : CurveDivisor.deg K D ≤ (g : ℤ))
    (T : Submodule K Y.functionField)
    (hTN : T ≤ divisorSections K
      (windowM_choice π hπ g • fiberWeilDivisor π - D) ⊤)
    (c : ℕ) (hcg : c ≤ g)
    (hc : Module.finrank K ↥T + c
      = Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • fiberWeilDivisor π - D)))
    (hbpf : ∀ (x : Y) (hx : x ≠ genericPoint Y),
      ∃ (f : Y.functionField) (_ : f ∈ T) (hf : f ≠ 0),
        coeffAt hx ((windowM_choice π hπ g • fiberWeilDivisor π - D)
          + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) = 0) :
    Scheme.mulSpan K
        (divisorSections K (windowS_choice π hπ g • fiberWeilDivisor π) ⊤) T
      = divisorSections K
          ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π - D)
          ⊤ := by
  classical
  set Fd : Y.CurveDivisor := fiberWeilDivisor π with hFd
  set N : Y.CurveDivisor := windowM_choice π hπ g • Fd - D with hN
  set A : Y.CurveDivisor := windowS_choice π hπ g • Fd with hA
  -- degree bookkeeping
  have hdegF : CurveDivisor.deg K Fd = windowδ π := deg_fiberWeilDivisor_windowδ π
  have hdegA : CurveDivisor.deg K A
      = (windowS_choice π hπ g : ℤ) * windowδ π := by
    rw [hA, Scheme.CurveDivisor.deg_nsmul' K, hdegF]
  have hdegN : CurveDivisor.deg K N
      = (windowM_choice π hπ g : ℤ) * windowδ π - CurveDivisor.deg K D := by
    rw [hN, Scheme.CurveDivisor.deg_sub' K, Scheme.CurveDivisor.deg_nsmul' K, hdegF]
  -- ledger budgets
  have hδ1 := one_le_windowδ π
  have hb2s := two_mul_genus_le_S_mul_windowδ π hπ g hO hχ
  have hbMnorm := windowBound_le_M_norm π hπ g
  have hbds := windowBound_add_two_mul_genus_le_M_sub_S_mul π hπ g
  have hbtw := windowBound_add_windowδ_le_S_mul_sub π hπ g
  have hD0deg : 0 ≤ CurveDivisor.deg K D := Scheme.CurveDivisor.deg_nonneg K hD0
  have hAdeg0 : 0 ≤ CurveDivisor.deg K A := by
    rw [hdegA]
    exact mul_nonneg (Int.natCast_nonneg _) (windowδ_nonneg π)
  -- rank of the multiplier window
  have hrs : (Sheaf.h0 (Y.divisorSheaf K A) : ℤ)
      = (windowS_choice π hπ g : ℤ) * windowδ π + 1 - (g : ℤ) := by
    rw [hA, hFd]
    exact rank_embedding_mult_of_genus π hπ g hχ
  -- the target window is `N + A`
  have hdivEq : (windowM_choice π hπ g + windowS_choice π hπ g) • Fd - D = N + A := by
    rw [hN, hA, add_nsmul]
    abel
  rw [hdivEq]
  -- the easy inclusion: products satisfy the pole bound
  have hSle : Scheme.mulSpan K (divisorSections K A ⊤) T
      ≤ divisorSections K (N + A) ⊤ := by
    refine Scheme.mulSpan_le K (fun a ha f hf => ?_)
    have hmul := mul_mem_divisorSections_top K ha (hTN hf)
    have hAN : A + N = N + A := add_comm A N
    rwa [hAN] at hmul
  refine le_antisymm hSle (Submodule.le_of_forall_dual_ker ?_)
  intro Λ hSΛ
  -- the annihilator kernel of `Λ`
  set NL : Submodule K Y.functionField :=
    Scheme.annKernel K (divisorSections K A ⊤) (divisorSections K N ⊤) Λ with hNLdef
  have hNLleA : NL ≤ divisorSections K A ⊤ := Scheme.annKernel_le K _ _ Λ
  -- (3a) codimension bound
  have hkill : ∀ h ∈ divisorSections K A ⊤, ∀ f ∈ T, Λ (h * f) = 0 := by
    intro h hh f hf
    exact LinearMap.mem_ker.mp (hSΛ (Scheme.mul_mem_mulSpan K hh hf))
  have hcodim : Module.finrank K ↥(divisorSections K A ⊤)
      ≤ Module.finrank K ↥NL + c := by
    refine finrank_le_finrank_annKernel_add K hTN ?_ hkill
    rw [finrank_divisorSections_top K N]
    exact hc
  -- (3a′) `N_Λ` is nonzero
  have hfrA : Module.finrank K ↥(divisorSections K A ⊤) = Sheaf.h0 (Y.divisorSheaf K A) :=
    finrank_divisorSections_top K A
  have hNLpos : 0 < Module.finrank K ↥NL := by
    have h1 : (Sheaf.h0 (Y.divisorSheaf K A) : ℤ) ≤ (Module.finrank K ↥NL : ℤ) + c := by
      exact_mod_cast hfrA ▸ hcodim
    omega
  have hNLne : ∃ f ∈ NL, f ≠ 0 := by
    have : NL ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hNLpos
      omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  -- (3b) the base locus of `N_Λ` and its degree bound
  set E : Y.CurveDivisor := Scheme.baseDivisor K NL A hNLne with hEdef
  have hE0 : 0 ≤ E := Scheme.baseDivisor_nonneg K hNLne
  have hEdeg : CurveDivisor.deg K E ≤ (g : ℤ) + c := by
    have hsub : NL ≤ divisorSections K (A - E) ⊤ :=
      Scheme.le_divisorSections_sub_baseDivisor K hNLleA hNLne
    have hmono : Module.finrank K ↥NL
        ≤ Module.finrank K ↥(divisorSections K (A - E) ⊤) :=
      Submodule.finrank_mono hsub
    have hbr := finrank_divisorSections_top K (A - E)
    have hpos : 0 < Sheaf.h0 (Y.divisorSheaf K (A - E)) := by
      omega
    have hsec := h0_le_deg_add_one_of_pos K hO (A - E) hpos
    have hdegAE : CurveDivisor.deg K (A - E)
        = (windowS_choice π hπ g : ℤ) * windowδ π - CurveDivisor.deg K E := by
      rw [Scheme.CurveDivisor.deg_sub' K, hdegA]
    rw [hdegAE] at hsec
    omega
  have hEdeg2g : CurveDivisor.deg K E ≤ 2 * (g : ℤ) := by omega
  -- (3c) the descent: `Λ` kills `H⁰(𝒪(N + A − E))`
  have hkillsAh : ∀ (h : Y.functionField) (_ : h ∈ NL) (hne : h ≠ 0),
      divisorSections K
        ((N + A) - (A + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 h hne))) ⊤
        ≤ LinearMap.ker Λ := by
    intro h hh hne
    have hdiveq : (N + A)
        - (A + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 h hne))
        = N - Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 h hne) := by
      abel
    rw [hdiveq, ← map_mulLinear_divisorSections_top K hne N]
    rintro _ ⟨f, hf, rfl⟩
    rw [LinearMap.mem_ker, Scheme.mulLinear_apply]
    exact (Scheme.mem_annKernel K).mp hh |>.2 f hf
  have hwin_descent : ∀ G : Y.CurveDivisor, 0 ≤ G →
      CurveDivisor.deg K G ≤ 2 * CurveDivisor.deg K A →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K ((N + A) - G)) 1) := by
    intro G hG0 hGdeg
    refine windowBound_spec π hπ _ ?_
    rw [Scheme.CurveDivisor.deg_sub' K, CurveDivisor.deg_add, hdegN, hdegA]
    rw [hdegA] at hGdeg
    omega
  have hkillsE : divisorSections K ((N + A) - E) ⊤ ≤ LinearMap.ker Λ := by
    rw [hEdef]
    exact Scheme.descent_baseDivisor_le K (N + A) A hAdeg0 NL hNLne hNLleA
      hwin_descent (LinearMap.ker Λ) hkillsAh
  -- (3e) the tower at each point of `E`
  have htower : ∀ (x : Y) (hx : x ≠ genericPoint Y),
      divisorSections K ((N + A) - E + CurveDivisor.single hx (coeffAt hx E)) ⊤
        ≤ LinearMap.ker Λ := by
    intro x hx
    obtain ⟨fx, hfxT, hfx, hfxord⟩ := hbpf x hx
    have hfxmem : 0 ≤ N + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 fx hfx) :=
      (mem_divisorSections_top_iff K hfx).mp (hTN hfxT)
    have he0 : 0 ≤ coeffAt hx E := by
      have := CurveDivisor.le_iff_coeffAt.mp hE0 x hx
      rwa [CurveDivisor.coeffAt_zero] at this
    set n : ℕ := (coeffAt hx E).toNat with hn
    have hncast : (n : ℤ) = coeffAt hx E := Int.toNat_of_nonneg he0
    have hnle : (n : ℤ) ≤ coeffAt hx E := le_of_eq hncast
    have hdx0 : (0 : ℤ) ≤ (Y.residueDeg K x : ℤ) := Int.natCast_nonneg _
    have hdegsingle : ∀ j : ℤ, CurveDivisor.deg K (CurveDivisor.single hx j)
        = j * (Y.residueDeg K x : ℤ) := fun j =>
      CurveDivisor.deg_single K ⟨x, hx⟩ j
    have hwinB : ∀ j : ℕ, j ≤ n → Subsingleton (Sheaf.HModule
        (Y.divisorSheaf K (N + A - E + CurveDivisor.single hx (j : ℤ))) 1) := by
      intro j _
      refine windowBound_spec π hπ _ ?_
      have hjd : (0 : ℤ) ≤ (j : ℤ) * (Y.residueDeg K x : ℤ) :=
        mul_nonneg (Int.natCast_nonneg _) hdx0
      rw [CurveDivisor.deg_add, Scheme.CurveDivisor.deg_sub' K, CurveDivisor.deg_add,
        hdegN, hdegA, hdegsingle]
      omega
    have hwinA : ∀ j : ℕ, j ≤ n → Subsingleton (Sheaf.HModule
        (Y.divisorSheaf K ((A - E + CurveDivisor.single hx (j : ℤ))
          - Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 fx hfx))) 1) := by
      intro j _
      refine windowBound_spec π hπ _ ?_
      have hjd : (0 : ℤ) ≤ (j : ℤ) * (Y.residueDeg K x : ℤ) :=
        mul_nonneg (Int.natCast_nonneg _) hdx0
      rw [Scheme.CurveDivisor.deg_sub' K, deg_divOf K, CurveDivisor.deg_add,
        Scheme.CurveDivisor.deg_sub' K, hdegA, hdegsingle]
      omega
    have happ := Scheme.multiplier_tower_le K N A E hE0 hx hfx hfxmem hfxord n hnle
      hwinB hwinA
    have hsingle : CurveDivisor.single hx ((n : ℕ) : ℤ)
        = CurveDivisor.single hx (coeffAt hx E) := by
      rw [hncast]
    rw [hsingle] at happ
    have hNAE : N + A - E = (N + A) - E := rfl
    refine le_trans happ (sup_le ?_ ?_)
    · exact hkillsE
    · refine le_trans (Scheme.map_mulLinear_le_mulSpan K hfxT) ?_
      exact hSΛ
  -- final reassembly over the points of `E`
  by_cases hE : E = 0
  · rw [hE, sub_zero] at hkillsE
    exact hkillsE
  · have hSne : (toFinsupp E).support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      exact hE
    set Efam : {x : Y // x ≠ genericPoint Y} → Y.CurveDivisor :=
      fun p => E - CurveDivisor.single p.2 (coeffAt p.2 E) with hEfam
    have hfam0 : ∀ p ∈ (toFinsupp E).support, 0 ≤ Efam p := by
      intro p _
      refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy => ?_)
      rw [CurveDivisor.coeffAt_zero, hEfam]
      have hEy : 0 ≤ coeffAt hy E := by
        have := CurveDivisor.le_iff_coeffAt.mp hE0 y hy
        rwa [CurveDivisor.coeffAt_zero] at this
      by_cases hyp : y = p.1
      · have hyp' : (⟨y, hy⟩ : {x : Y // x ≠ genericPoint Y}) = p := Subtype.ext hyp
        subst hyp'
        rw [CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_single_self]
        omega
      · rw [CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_single_of_ne p.2 hy hyp]
        omega
    have hfamB : ∀ p ∈ (toFinsupp E).support, Efam p ≤ E := by
      intro p _
      refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy => ?_)
      rw [hEfam]
      have hEy : 0 ≤ coeffAt hy E := by
        have := CurveDivisor.le_iff_coeffAt.mp hE0 y hy
        rwa [CurveDivisor.coeffAt_zero] at this
      by_cases hyp : y = p.1
      · have hyp' : (⟨y, hy⟩ : {x : Y // x ≠ genericPoint Y}) = p := Subtype.ext hyp
        subst hyp'
        rw [CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_single_self]
        omega
      · rw [CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_single_of_ne p.2 hy hyp]
        omega
    have hwin_final : ∀ G : Y.CurveDivisor, 0 ≤ G → G ≤ E →
        Subsingleton (Sheaf.HModule (Y.divisorSheaf K ((N + A) - G)) 1) := by
      intro G hG0 hGE
      refine windowBound_spec π hπ _ ?_
      have hGdeg : CurveDivisor.deg K G ≤ CurveDivisor.deg K E :=
        Scheme.CurveDivisor.deg_mono K hGE
      rw [Scheme.CurveDivisor.deg_sub' K, CurveDivisor.deg_add, hdegN, hdegA]
      omega
    have hiter := finsetSup_divisorSections_sub K (toFinsupp E).support hSne
      (N + A) E Efam hfam0 hfamB hwin_final
    have hinf0 : (toFinsupp E).support.inf' hSne Efam = 0 := by
      refine le_antisymm ?_ (Finset.le_inf' hSne Efam (fun p hp => hfam0 p hp))
      refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy => ?_)
      rw [CurveDivisor.coeffAt_zero,
        Scheme.CurveDivisor.coeffAt_finsetInf' (toFinsupp E).support hSne Efam hy]
      by_cases hmem : (⟨y, hy⟩ : {x : Y // x ≠ genericPoint Y}) ∈ (toFinsupp E).support
      · refine le_trans (Finset.inf'_le _ hmem) ?_
        rw [hEfam, CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_single_self]
        omega
      · obtain ⟨p₀, hp₀⟩ := hSne
        refine le_trans (Finset.inf'_le _ hp₀) ?_
        have hyE : coeffAt hy E = 0 := Finsupp.notMem_support_iff.mp hmem
        have hyne : y ≠ p₀.1 := by
          intro hcontr
          exact hmem (by rwa [show (⟨y, hy⟩ : {x : Y // x ≠ genericPoint Y}) = p₀
            from Subtype.ext hcontr])
        rw [hEfam, CurveDivisor.coeffAt_sub,
          CurveDivisor.coeffAt_single_of_ne p₀.2 hy hyne, hyE]
        omega
    have hfinal : divisorSections K
        ((N + A) - (toFinsupp E).support.inf' hSne Efam) ⊤ ≤ LinearMap.ker Λ := by
      rw [← hiter]
      refine Finset.sup_le (fun p hp => ?_)
      have hdivp : (N + A) - Efam p
          = (N + A) - E + CurveDivisor.single p.2 (coeffAt p.2 E) := by
        rw [hEfam]
        refine CurveDivisor.ext_coeffAt (fun y hy => ?_)
        simp only [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub]
        ring
      rw [hdivp]
      exact htower p.1 p.2
    rwa [hinf0, sub_zero] at hfinal

end AlgebraicGeometry
