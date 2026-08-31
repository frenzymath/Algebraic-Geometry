/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.BpfSpanCore
import AlgebraicJacobian.RiemannRoch.CarveDegreePinch

/-!
# P-fib-N — the pack-parametrized persistence heart (`informal/w4-g4-worksheet.md` §1.4)

The required new brick of W4-G4 §0 verdict 1: P-fib
(`RiemannRoch/PFib.lean`, `existsUnique_effective_divisor_of_carve`) is pinned to the
fibre field's OWN ledger constants `windowM_choice π hπ g`, and per the I-0204 binding
finding the ledger constants do NOT transport across `k → κ(p)`
(`RiemannRoch/WindowFieldTransport.lean`).  This file restates the whole P-fib chain
π-free, against ABSTRACT embedding/multiplier divisors `N` (∼ the transported `M·F`)
and `S` (∼ the transported `s·F`), shifted window spelled `N + S` (∼ `(M+s)·F`).

## The pack interface (the §1.4 audit result)

The §1.4-mandated audit of the bpf-span window threading found the five-fact list
sketched there (`hNwin`/`hSwin`/`hNdeg`/`hNnorm`/`hNsnorm`) **insufficient** — the descent
stage of the F3-core (`Scheme.descent_baseDivisor_le`) visits levels `N + S − D − G`
with `deg G ≤ 2·deg S`, far below the `deg ≤ 2g` normalization families, and the tower
stage visits multiplier levels `S − E + j·x − div fₓ` at depth `deg E ≤ 2g` below `S`.
The honest transported interface is the DAT-0a avatar itself: a **vanishing threshold**
`β` with `hvan : ∀ W, β ≤ deg W → H¹(𝒪(W)) = 0` (the `windowBound_spec` shape — at a
residue field it is produced by the π-free peeling `subsingleton_hModule_one_of_witness`
from a transported witness, or from a transported normalization family via
`subsingleton_hModule_one_of_normalization` below), plus the three budget avatars

* `hSdeg : 2g ≤ deg S`   (avatar of `two_mul_genus_le_S_mul_windowδ`),
* `hβS : β + 2g ≤ deg S`  (tower budget, `windowBound_add_windowδ_le_S_mul_sub`),
* `hβN : β + 2g + deg S ≤ deg N`  (descent budget, verbatim
  `windowBound_add_two_mul_genus_le_M_sub_S_mul`),

and `hNdeg : 2g ≤ deg N` (avatar of `two_mul_genus_le_M_mul_windowδ`).  The worksheet's
`hNwin`/`hSwin`/`hNnorm`/`hNsnorm` are one-line consequences of `hvan` + budgets,
derived where needed inside the proofs; the drop/recovery layer is consumed from the
landed DDR-2 pack forms (`baseDivisorAt_window_normalization`, `CarveDegreePinch.lean`).

* `AlgebraicGeometry.subsingleton_hModule_one_of_normalization` — a normalization family
  at depth `t` below `N₀` IS a vanishing threshold at `β = deg N₀ − t`; turns the landed
  fibre fact `subsingleton_h1_windowN_sub` into `hvan`.
* `AlgebraicGeometry.mulSpan_eq_divisorSections_of_basepointFree_pack` — the F3-core
  bpf-span lemma against the pack (abstract-`N,S` transcription of
  `mulSpan_eq_divisorSections_of_basepointFree`, `RiemannRoch/BpfSpan.lean`).
* `AlgebraicGeometry.existsUnique_effective_divisor_of_carve_pack` — **P-fib-N**: the
  pack form of the persistence heart (worksheet §1.4 statement pin, audited bundle).

The ledger consistency instantiation (the pack hypotheses discharged by the DD-0 names
at the pack's own field, re-deriving P-fib) is `RiemannRoch/PFibPackLedger.lean`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule

namespace AlgebraicGeometry

open Scheme

section PFibPack

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)] in
/-- **A normalization family is a vanishing threshold**: if `H¹(𝒪(N₀ − D')) = 0` for
every divisor `D'` of degree `≤ t`, then every divisor `W` of degree `≥ deg N₀ − t` has
vanishing `H¹` — write `W = N₀ − (N₀ − W)` and feed `N₀ − W` to the family.  This turns
the landed fibre fact `subsingleton_h1_windowN_sub` (`WindowFieldTransport.lean`) into
the `hvan` threshold of the P-fib-N pack at `β = deg N − 2g`. -/
theorem subsingleton_hModule_one_of_normalization
    (t : ℤ) (N₀ : Y.CurveDivisor)
    (hnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ t →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N₀ - D')) 1))
    (W : Y.CurveDivisor)
    (hW : CurveDivisor.deg K N₀ - t ≤ CurveDivisor.deg K W) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K W) 1) := by
  have hdeg : CurveDivisor.deg K (N₀ - W) ≤ t := by
    rw [Scheme.CurveDivisor.deg_sub' K]
    omega
  have h := hnorm (N₀ - W) hdeg
  rwa [sub_sub_cancel] at h

/-- **The bpf-span lemma, pack form** (F3-core against the transported window pack; the
abstract-`N,S` transcription of `mulSpan_eq_divisorSections_of_basepointFree`,
`RiemannRoch/BpfSpan.lean`): for an effective `D` of degree `≤ g` and a subspace
`T ⊆ H⁰(𝒪(N − D))` of codimension `c ≤ g` with no base point relative to `N − D`, the
products by the full multiplier window span the full shifted window:
`span(H⁰(𝒪(S)) · T) = H⁰(𝒪(N + S − D))`.  The ledger names of the original are replaced
by the pack: `windowBound_spec ↦ hvan` (threshold `β`),
`two_mul_genus_le_S_mul_windowδ ↦ hSdeg`, the tower budget `↦ hβS`, the descent budget
`↦ hβN`; the descent/tower engines (`BpfSpanCore.lean`) are window-generic and consumed
as-is. -/
theorem mulSpan_eq_divisorSections_of_basepointFree_pack
    (n : ℕ) {gamma : ℕ}
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ))
    (N S : Y.CurveDivisor) (β : ℤ)
    (hvan : ∀ W : Y.CurveDivisor, β ≤ CurveDivisor.deg K W →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K W) 1))
    (hSdeg : 2 * (n : ℤ) ≤ CurveDivisor.deg K S)
    (hβS : β + 2 * (n : ℤ) ≤ CurveDivisor.deg K S)
    (hβN : β + 2 * (n : ℤ) + CurveDivisor.deg K S ≤ CurveDivisor.deg K N)
    (D : Y.CurveDivisor) (hD0 : 0 ≤ D)
    (hDg : CurveDivisor.deg K D ≤ (n : ℤ))
    (T : Submodule K Y.functionField)
    (hTN : T ≤ divisorSections K (N - D) ⊤)
    (c : ℕ) (hcn : c ≤ n)
    (hc : Module.finrank K ↥T + c = Sheaf.h0 (Y.divisorSheaf K (N - D)))
    (hbpf : ∀ (x : Y) (hx : x ≠ genericPoint Y),
      ∃ (f : Y.functionField) (_ : f ∈ T) (hf : f ≠ 0),
        coeffAt hx ((N - D)
          + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) = 0)
    (hgamma : gamma ≤ n := by omega) :
    Scheme.mulSpan K (divisorSections K S ⊤) T
      = divisorSections K (N + S - D) ⊤ := by
  classical
  set ND : Y.CurveDivisor := N - D with hND
  -- degree bookkeeping
  have hD0deg : 0 ≤ CurveDivisor.deg K D := Scheme.CurveDivisor.deg_nonneg K hD0
  have hdegND : CurveDivisor.deg K ND
      = CurveDivisor.deg K N - CurveDivisor.deg K D := by
    rw [hND, Scheme.CurveDivisor.deg_sub' K]
  have hSdeg0 : 0 ≤ CurveDivisor.deg K S := by omega
  -- the multiplier window is exact: `h⁰(𝒪(S)) = deg S + 1 − g`
  have hrs : (Sheaf.h0 (Y.divisorSheaf K S) : ℤ)
      = CurveDivisor.deg K S + 1 - (gamma : ℤ) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hvan S (by omega)), hχ]
    ring
  -- the target window is `ND + S`
  have hdivEq : N + S - D = ND + S := by
    rw [hND]
    abel
  rw [hdivEq]
  -- the easy inclusion: products satisfy the pole bound
  have hSle : Scheme.mulSpan K (divisorSections K S ⊤) T
      ≤ divisorSections K (ND + S) ⊤ := by
    refine Scheme.mulSpan_le K (fun a ha f hf => ?_)
    have hmul := mul_mem_divisorSections_top K ha (hTN hf)
    rwa [add_comm S ND] at hmul
  refine le_antisymm hSle (Submodule.le_of_forall_dual_ker ?_)
  intro Λ hSΛ
  -- the annihilator kernel of `Λ`
  set NL : Submodule K Y.functionField :=
    Scheme.annKernel K (divisorSections K S ⊤) (divisorSections K ND ⊤) Λ with hNLdef
  have hNLleS : NL ≤ divisorSections K S ⊤ := Scheme.annKernel_le K _ _ Λ
  -- (3a) codimension bound
  have hkill : ∀ h ∈ divisorSections K S ⊤, ∀ f ∈ T, Λ (h * f) = 0 := by
    intro h hh f hf
    exact LinearMap.mem_ker.mp (hSΛ (Scheme.mul_mem_mulSpan K hh hf))
  have hcodim : Module.finrank K ↥(divisorSections K S ⊤)
      ≤ Module.finrank K ↥NL + c := by
    refine finrank_le_finrank_annKernel_add K hTN ?_ hkill
    rw [finrank_divisorSections_top K ND]
    exact hc
  -- (3a′) `N_Λ` is nonzero
  have hfrS : Module.finrank K ↥(divisorSections K S ⊤)
      = Sheaf.h0 (Y.divisorSheaf K S) := finrank_divisorSections_top K S
  have hNLpos : 0 < Module.finrank K ↥NL := by
    have h1 : (Sheaf.h0 (Y.divisorSheaf K S) : ℤ)
        ≤ (Module.finrank K ↥NL : ℤ) + c := by
      exact_mod_cast hfrS ▸ hcodim
    omega
  have hNLne : ∃ f ∈ NL, f ≠ 0 := by
    have : NL ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hNLpos
      omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  -- (3b) the base locus of `N_Λ` and its degree bound
  set E : Y.CurveDivisor := Scheme.baseDivisor K NL S hNLne with hEdef
  have hE0 : 0 ≤ E := Scheme.baseDivisor_nonneg K hNLne
  have hEdeg : CurveDivisor.deg K E ≤ (gamma : ℤ) + c := by
    have hsub : NL ≤ divisorSections K (S - E) ⊤ :=
      Scheme.le_divisorSections_sub_baseDivisor K hNLleS hNLne
    have hmono : Module.finrank K ↥NL
        ≤ Module.finrank K ↥(divisorSections K (S - E) ⊤) :=
      Submodule.finrank_mono hsub
    have hbr := finrank_divisorSections_top K (S - E)
    have hpos : 0 < Sheaf.h0 (Y.divisorSheaf K (S - E)) := by
      omega
    have hsec := h0_le_deg_add_one_of_pos K hO (S - E) hpos
    have hdegSE : CurveDivisor.deg K (S - E)
        = CurveDivisor.deg K S - CurveDivisor.deg K E :=
      Scheme.CurveDivisor.deg_sub' K S E
    rw [hdegSE] at hsec
    omega
  -- (3c) the descent: `Λ` kills `H⁰(𝒪(ND + S − E))`
  have hkillsSh : ∀ (h : Y.functionField) (_ : h ∈ NL) (hne : h ≠ 0),
      divisorSections K
        ((ND + S) - (S + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 h hne))) ⊤
        ≤ LinearMap.ker Λ := by
    intro h hh hne
    have hdiveq : (ND + S)
        - (S + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 h hne))
        = ND - Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 h hne) := by
      abel
    rw [hdiveq, ← map_mulLinear_divisorSections_top K hne ND]
    rintro _ ⟨f, hf, rfl⟩
    rw [LinearMap.mem_ker, Scheme.mulLinear_apply]
    exact (Scheme.mem_annKernel K).mp hh |>.2 f hf
  have hwin_descent : ∀ G : Y.CurveDivisor, 0 ≤ G →
      CurveDivisor.deg K G ≤ 2 * CurveDivisor.deg K S →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K ((ND + S) - G)) 1) := by
    intro G hG0 hGdeg
    refine hvan _ ?_
    rw [Scheme.CurveDivisor.deg_sub' K, CurveDivisor.deg_add, hdegND]
    omega
  have hkillsE : divisorSections K ((ND + S) - E) ⊤ ≤ LinearMap.ker Λ := by
    rw [hEdef]
    exact Scheme.descent_baseDivisor_le K (ND + S) S hSdeg0 NL hNLne hNLleS
      hwin_descent (LinearMap.ker Λ) hkillsSh
  -- (3e) the tower at each point of `E`
  have htower : ∀ (x : Y) (hx : x ≠ genericPoint Y),
      divisorSections K ((ND + S) - E + CurveDivisor.single hx (coeffAt hx E)) ⊤
        ≤ LinearMap.ker Λ := by
    intro x hx
    obtain ⟨fx, hfxT, hfx, hfxord⟩ := hbpf x hx
    have hfxmem : 0 ≤ ND
        + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 fx hfx) :=
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
        (Y.divisorSheaf K (ND + S - E + CurveDivisor.single hx (j : ℤ))) 1) := by
      intro j _
      refine hvan _ ?_
      have hjd : (0 : ℤ) ≤ (j : ℤ) * (Y.residueDeg K x : ℤ) :=
        mul_nonneg (Int.natCast_nonneg _) hdx0
      rw [CurveDivisor.deg_add, Scheme.CurveDivisor.deg_sub' K, CurveDivisor.deg_add,
        hdegND, hdegsingle]
      omega
    have hwinS : ∀ j : ℕ, j ≤ n → Subsingleton (Sheaf.HModule
        (Y.divisorSheaf K ((S - E + CurveDivisor.single hx (j : ℤ))
          - Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 fx hfx))) 1) := by
      intro j _
      refine hvan _ ?_
      have hjd : (0 : ℤ) ≤ (j : ℤ) * (Y.residueDeg K x : ℤ) :=
        mul_nonneg (Int.natCast_nonneg _) hdx0
      rw [Scheme.CurveDivisor.deg_sub' K, deg_divOf K, CurveDivisor.deg_add,
        Scheme.CurveDivisor.deg_sub' K, hdegsingle]
      omega
    have happ := Scheme.multiplier_tower_le K ND S E hE0 hx hfx hfxmem hfxord n hnle
      hwinB hwinS
    have hsingle : CurveDivisor.single hx ((n : ℕ) : ℤ)
        = CurveDivisor.single hx (coeffAt hx E) := by
      rw [hncast]
    rw [hsingle] at happ
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
        Subsingleton (Sheaf.HModule (Y.divisorSheaf K ((ND + S) - G)) 1) := by
      intro G hG0 hGE
      have hGdeg : CurveDivisor.deg K G ≤ CurveDivisor.deg K E :=
        Scheme.CurveDivisor.deg_mono K hGE
      refine hvan _ ?_
      rw [Scheme.CurveDivisor.deg_sub' K, CurveDivisor.deg_add, hdegND]
      omega
    have hiter := finsetSup_divisorSections_sub K (toFinsupp E).support hSne
      (ND + S) E Efam hfam0 hfamB hwin_final
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
        ((ND + S) - (toFinsupp E).support.inf' hSne Efam) ⊤ ≤ LinearMap.ker Λ := by
      rw [← hiter]
      refine Finset.sup_le (fun p hp => ?_)
      have hdivp : (ND + S) - Efam p
          = (ND + S) - E + CurveDivisor.single p.2 (coeffAt p.2 E) := by
        rw [hEfam]
        refine CurveDivisor.ext_coeffAt (fun y hy => ?_)
        simp only [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub]
        ring
      rw [hdivp]
      exact htower p.1 p.2
    rwa [hinf0, sub_zero] at hfinal

/-- **P-fib-N** (★★★, worksheet §1.4 — the pack-parametrized persistence heart): on the
abstract curve `Y` over any field `K`, against the transported window pack — a vanishing
threshold `β` (`hvan`, the DAT-0a avatar) and the degree budgets `hNdeg`/`hSdeg`/`hβS`/
`hβN` — subspaces `K_M ⊆ H⁰(𝒪(N))` and `K' ⊆ H⁰(𝒪(N + S))` of codimension exactly `g`
satisfying the carve `(♦)` — every product of a multiplier section with an element of
`K_M` lies in `K'` — determine a **unique** effective divisor `D` of degree `g` with
`K_M = H⁰(𝒪(N − D))` and `K' = H⁰(𝒪(N + S − D))`.  The abstract-pack transcription of
P-fib (`existsUnique_effective_divisor_of_carve`, `RiemannRoch/PFib.lean`), consumed
fibrewise at `N`/`S` the base-field transports of `M·F`/`s·F` (DDR-8/W4-G4); the
uniqueness leg is the landed DDR-2 recovery `baseDivisorAt_window_normalization`. -/
theorem existsUnique_effective_divisor_of_carve_pack
    (n : ℕ) {gamma : ℕ}
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ))
    (N S : Y.CurveDivisor) (β : ℤ)
    (hvan : ∀ W : Y.CurveDivisor, β ≤ CurveDivisor.deg K W →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K W) 1))
    (hNdeg : 2 * (n : ℤ) ≤ CurveDivisor.deg K N)
    (hSdeg : 2 * (n : ℤ) ≤ CurveDivisor.deg K S)
    (hβS : β + 2 * (n : ℤ) ≤ CurveDivisor.deg K S)
    (hβN : β + 2 * (n : ℤ) + CurveDivisor.deg K S ≤ CurveDivisor.deg K N)
    (KM : Submodule K Y.functionField)
    (hKM : KM ≤ divisorSections K N ⊤)
    (hKMrank : Module.finrank K ↥KM + n = Sheaf.h0 (Y.divisorSheaf K N))
    (K' : Submodule K Y.functionField)
    (hK' : K' ≤ divisorSections K (N + S) ⊤)
    (hK'rank : Module.finrank K ↥K' + n = Sheaf.h0 (Y.divisorSheaf K (N + S)))
    (hcarve : ∀ h ∈ divisorSections K S ⊤, ∀ f ∈ KM, h * f ∈ K')
    (hgamma : gamma ≤ n := by omega) :
    ∃! D : Y.CurveDivisor, 0 ≤ D ∧ CurveDivisor.deg K D = (n : ℤ) ∧
      KM = divisorSections K (N - D) ⊤ ∧
      K' = divisorSections K (N + S - D) ⊤ := by
  classical
  haveI hK'fin : Module.Finite K ↥K' := Submodule.finiteDimensional_of_le hK'
  have hSdeg0 : 0 ≤ CurveDivisor.deg K S := by omega
  -- ranks of the two embedding windows
  have hrM : (Sheaf.h0 (Y.divisorSheaf K N) : ℤ)
      = CurveDivisor.deg K N + 1 - (gamma : ℤ) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hvan N (by omega)), hχ]
    ring
  have hrMs : (Sheaf.h0 (Y.divisorSheaf K (N + S)) : ℤ)
      = CurveDivisor.deg K N + CurveDivisor.deg K S + 1 - (gamma : ℤ) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
        (hvan (N + S) (by rw [CurveDivisor.deg_add]; omega)),
      CurveDivisor.deg_add, hχ]
    ring
  -- the transported normalization family at `N` (worksheet `hNnorm`, derived)
  have hNnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ 2 * (n : ℤ) →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N - D')) 1) := by
    intro D' hD'
    refine hvan _ ?_
    rw [Scheme.CurveDivisor.deg_sub' K]
    omega
  -- F1: `K_M` is nonzero, its base divisor is the divisor
  have hKMne : ∃ f ∈ KM, f ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
    rw [hbot, finrank_bot] at hKMrank
    omega
  set D : Y.CurveDivisor := Scheme.baseDivisor K KM N hKMne with hDdef
  have hD0 : 0 ≤ D := Scheme.baseDivisor_nonneg K hKMne
  have hDdeg0 : 0 ≤ CurveDivisor.deg K D := Scheme.CurveDivisor.deg_nonneg K hD0
  have hKMsub : KM ≤ divisorSections K (N - D) ⊤ := by
    rw [hDdef]
    exact Scheme.le_divisorSections_sub_baseDivisor K hKM hKMne
  have hdegND : CurveDivisor.deg K (N - D)
      = CurveDivisor.deg K N - CurveDivisor.deg K D :=
    Scheme.CurveDivisor.deg_sub' K N D
  -- F1 degree bound: first `≤ 2g` by the section bound, then `≤ g` by the exact window
  have hfrKM : Module.finrank K ↥KM ≤ Sheaf.h0 (Y.divisorSheaf K (N - D)) := by
    rw [← finrank_divisorSections_top K _]
    exact Submodule.finrank_mono hKMsub
  have hKMpos : 0 < Module.finrank K ↥KM := by omega
  have hposND : 0 < Sheaf.h0 (Y.divisorSheaf K (N - D)) := by omega
  have hsec := h0_le_deg_add_one_of_pos K hO (N - D) hposND
  rw [hdegND] at hsec
  have hD2n : CurveDivisor.deg K D ≤ 2 * (n : ℤ) := by omega
  have hrND : (Sheaf.h0 (Y.divisorSheaf K (N - D)) : ℤ)
      = CurveDivisor.deg K N - CurveDivisor.deg K D + 1 - (gamma : ℤ) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hNnorm D hD2n), hdegND, hχ]
    ring
  have hDn : CurveDivisor.deg K D ≤ (n : ℤ) := by omega
  -- the codimension of `K_M` inside its normalization window
  set c : ℕ := Sheaf.h0 (Y.divisorSheaf K (N - D)) - Module.finrank K ↥KM with hcdef
  have hcrank : Module.finrank K ↥KM + c
      = Sheaf.h0 (Y.divisorSheaf K (N - D)) := by
    omega
  have hcn : c ≤ n := by omega
  -- the bpf achievers
  have hbpf : ∀ (x : Y) (hx : x ≠ genericPoint Y),
      ∃ (f : Y.functionField) (_ : f ∈ KM) (hf : f ≠ 0),
        coeffAt hx ((N - D)
          + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) = 0 := by
    intro x hx
    rw [hDdef]
    exact Scheme.exists_achiever_baseDivisor_sub K hKM hKMne hx
  -- F3-core: the span is the full shifted window
  have hspan : Scheme.mulSpan K (divisorSections K S ⊤) KM
      = divisorSections K (N + S - D) ⊤ :=
    mulSpan_eq_divisorSections_of_basepointFree_pack n hO hχ N S β hvan hSdeg hβS hβN
      D hD0 hDn KM hKMsub c hcn hcrank hbpf
  -- `(♦)` traps the span inside `K'`
  have hspanle : divisorSections K (N + S - D) ⊤ ≤ K' := by
    rw [← hspan]
    exact Scheme.mulSpan_le K hcarve
  -- corank pinch: `deg D = g`
  have hdegMsD : CurveDivisor.deg K (N + S - D)
      = CurveDivisor.deg K N + CurveDivisor.deg K S - CurveDivisor.deg K D := by
    rw [Scheme.CurveDivisor.deg_sub' K, CurveDivisor.deg_add]
  have hrMsD : (Sheaf.h0 (Y.divisorSheaf K (N + S - D)) : ℤ)
      = CurveDivisor.deg K N + CurveDivisor.deg K S - CurveDivisor.deg K D
        + 1 - (gamma : ℤ) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
        (hvan (N + S - D) (by rw [hdegMsD]; omega)), hdegMsD, hχ]
    ring
  have hfrK' : Sheaf.h0 (Y.divisorSheaf K (N + S - D)) ≤ Module.finrank K ↥K' := by
    rw [← finrank_divisorSections_top K _]
    exact Submodule.finrank_mono hspanle
  have hDeqn : CurveDivisor.deg K D = (n : ℤ) := by omega
  -- the two equalities
  have hKMeq : KM = divisorSections K (N - D) ⊤ := by
    refine Submodule.eq_of_le_of_finrank_le hKMsub ?_
    rw [finrank_divisorSections_top K _]
    omega
  have hK'eq : K' = divisorSections K (N + S - D) ⊤ := by
    refine (Submodule.eq_of_le_of_finrank_le hspanle ?_).symm
    rw [finrank_divisorSections_top K _]
    omega
  refine ⟨D, ⟨hD0, hDeqn, hKMeq, hK'eq⟩, ?_⟩
  -- uniqueness: the divisor is recovered as the base divisor of `K_M` (DDR-2 hook)
  rintro D' ⟨hD'0, hD'deg, hKM', _⟩
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  have hrec : (Scheme.baseDivisorAt K (divisorSections K (N - D') ⊤) N ⟨x, hx⟩ : ℤ)
      = coeffAt hx D' :=
    baseDivisorAt_window_normalization n hO hχ N hNnorm hNdeg D' hD'0 hD'deg hx
  have hcoeffD : coeffAt hx D
      = (Scheme.baseDivisorAt K KM N ⟨x, hx⟩ : ℤ) := by
    rw [hDdef]
    exact Scheme.coeffAt_baseDivisor K hKMne hx
  rw [hKM'] at hcoeffD
  rw [hcoeffD]
  exact hrec.symm

end PFibPack

end AlgebraicGeometry
