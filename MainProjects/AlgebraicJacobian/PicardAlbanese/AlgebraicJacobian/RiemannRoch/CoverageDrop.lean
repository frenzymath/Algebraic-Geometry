/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.BaseDivisor
import AlgebraicJacobian.RiemannRoch.FLVClass

/-!
# DAT-B B-1 — the oracle-parametrized greedy `h⁰`-drop to `h⁰ = 1`

The coverage-side normalization of the DAT-B worksheet (`informal/w4-datb-worksheet.md`
§1.4, COV-2): on the curve bundle `Y` over a field `K` (the fibre field of the coverage
argument), given an **admissible point oracle** `P` — a set of closed `K`-rational points
(`residueDeg = 1`) meeting every nonempty open — and a divisor `W` of degree `g + e` with
`H¹(𝒪(W)) = 0`, there is an effective divisor `Σ` of degree `e` supported in `P` with

  `h⁰(𝒪(W − Σ)) = 1`  and  `H¹(𝒪(W − Σ)) = 0`
  (`exists_effective_sub_h0_eq_one`, the keystone).

The pointwise coverage theorem (B-5, worksheet §1.2 step 5) consumes this with
`P :=` the base-changed `C(K_s)`-points supplied by the density oracle of B-2
(`Curve/SepPointsDense.lean`); the oracle parametrization decouples the density
discharge from the pure Riemann–Roch drop.

## Route (worksheet §1.4, per step for the current `W'` with `h¹ = 0`, `deg = g + e'`)

* **The bad locus is small** (`exists_admissible_nonbase_point`): `H⁰(𝒪(W'))` is nonzero
  (rank anchor `h0_eq_deg_add_chi_of_subsingleton_hModule_one`), its base divisor
  (`Scheme.baseDivisor`, the DD-F kit) has finite support consisting of closed points, so
  the non-base locus contains a nonempty open (complement of a finite closed set in the
  irreducible curve — it contains the generic point) and the oracle supplies an admissible
  point there; the base-divisor achiever (`exists_coeffAt_eq_baseDivisorAt`) turns
  "outside the support" into an exact-order section.
* **Exact drop at a rational non-base point** (`h0_sub_single_of_rational_nonbase`):
  `h⁰(𝒪(W' − x)) ≤ h⁰(𝒪(W')) − 1` — sections of `W' − x` are sections of `W'`, a *proper*
  submodule since the non-base section violates the deeper pole bound at `x`
  (`Submodule.finrank_lt_finrank_of_lt` through the `h⁰` bridge
  `finrank_divisorSections_top`) — while the χ-ledger (`chi_divisorSheaf`) with
  `residueDeg x = 1` and `h¹(𝒪(W')) = 0` gives `χ(𝒪(W' − x)) = h⁰(𝒪(W')) − 1`; equality
  forces BOTH `h⁰(𝒪(W' − x)) = h⁰(𝒪(W')) − 1` AND `h¹(𝒪(W' − x)) = 0` — the induction
  invariant.
* **Terminate at `e' = 0`**: `h⁰ = 1` by the rank anchor at `deg = g`, `χ(𝒪) = 1 − g`.

The strict-drop precedents `h0_normalization_sub_single_lt` (`PFib.lean`) and
`h0_window_sub_single_lt` (`CarveDegreePinch.lean`) are window-specific mirrors of the
drop step (worksheet risk 3 mitigation); their `deg_single`/`coeffAt` bookkeeping is
imitated, not consumed.  Pure field level — no scheme beyond the fibre curve appears
(the DD-F discipline).  The genus enters only through `hχ : χ(𝒪_Y) = 1 − g`; the
worksheet's standing `h⁰(𝒪_Y) = 1` is not needed by this brick and is not threaded.
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

/-! ## The bad locus is small: an admissible non-base point -/

omit [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)] in
/-- **An admissible non-base point** (worksheet §1.4 bullet 1): if `H⁰(𝒪(W))` is nonzero
and `P` is dense (meets every nonempty open) and consists of closed points, then some
`x ∈ P` is *not* a base point of the system: some nonzero section `f ∈ H⁰(𝒪(W))` has
exact order at `x`, `(W + div f)ₓ = 0`.  The base locus is contained in the support of
the base divisor `bd(H⁰(𝒪(W)))` — a finite set of closed points, whose complement is a
nonempty open (it contains the generic point); the base-divisor achiever
(`Scheme.exists_coeffAt_eq_baseDivisorAt`) realizes the vanishing base multiplicity
outside the support. -/
theorem exists_admissible_nonbase_point (P : Set Y)
    (hdense : ∀ U : Y.Opens, (U : Set Y).Nonempty → (P ∩ U).Nonempty)
    (hPcl : ∀ x ∈ P, x ≠ genericPoint Y)
    (W : Y.CurveDivisor) (hpos : 0 < Sheaf.h0 (Y.divisorSheaf K W)) :
    ∃ (x : Y) (hx : x ≠ genericPoint Y) (_ : x ∈ P) (f : Y.functionField)
      (_ : f ∈ divisorSections K W ⊤) (hf : f ≠ 0),
      coeffAt hx (W + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf))
        = 0 := by
  classical
  set T : Submodule K Y.functionField := divisorSections K W ⊤ with hT
  have hTne : ∃ f ∈ T, f ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
    have hfr : Module.finrank K ↥T = Sheaf.h0 (Y.divisorSheaf K W) :=
      finrank_divisorSections_top K W
    rw [hbot, finrank_bot] at hfr
    omega
  set B : Y.CurveDivisor := Scheme.baseDivisor K T W hTne with hB
  -- the support of the base divisor is a finite set of closed points
  have hclosed : IsClosed (⋃ p ∈ (toFinsupp B).support, ({p.1} : Set Y)) :=
    isClosed_biUnion_finset (fun p _ =>
      isClosed_singleton_of_ne_genericPoint (Y ↘ Spec (CommRingCat.of K)) p.2)
  set U : Y.Opens :=
    ⟨(⋃ p ∈ (toFinsupp B).support, ({p.1} : Set Y))ᶜ, hclosed.isOpen_compl⟩ with hU
  have hUne : (U : Set Y).Nonempty := by
    refine ⟨genericPoint Y, fun hmem => ?_⟩
    obtain ⟨p, _, hp⟩ := Set.mem_iUnion₂.mp hmem
    exact p.2 (Set.mem_singleton_iff.mp hp).symm
  obtain ⟨x, hxP, hxU⟩ := hdense U hUne
  have hx : x ≠ genericPoint Y := hPcl x hxP
  -- outside the support the base multiplicity vanishes
  have hxc : x ∉ ⋃ p ∈ (toFinsupp B).support, ({p.1} : Set Y) := hxU
  have hxB : coeffAt hx B = 0 := by
    by_contra hne
    exact hxc (Set.mem_iUnion₂.mpr
      ⟨⟨x, hx⟩, Finsupp.mem_support_iff.mpr hne, rfl⟩)
  have hBat : (Scheme.baseDivisorAt K T W ⟨x, hx⟩ : ℤ) = 0 := by
    rw [← Scheme.coeffAt_baseDivisor K hTne hx]
    exact hxB
  -- the achiever realizes the vanishing base multiplicity
  obtain ⟨f, hfT, hf, hach⟩ :=
    Scheme.exists_coeffAt_eq_baseDivisorAt K (le_refl T) hTne hx
  exact ⟨x, hx, hxP, f, hfT, hf, hach.trans hBat⟩

/-! ## The exact drop at a rational non-base point -/

/-- **The exact drop** (worksheet §1.4 bullet 2): at a closed `K`-rational point `x`
(`residueDeg x = 1`) that is not a base point of `H⁰(𝒪(W))` — witnessed by a nonzero
section `f` of exact order at `x` — and under `H¹(𝒪(W)) = 0`,

  `h⁰(𝒪(W − x)) + 1 = h⁰(𝒪(W))`  and  `H¹(𝒪(W − x)) = 0`.

`≤`: sections of `W − x` are sections of `W` vanishing one order deeper at `x`, a proper
subspace since `f` violates the deeper bound — one linear condition as `residueDeg x = 1`.
`≥`: the χ-ledger gives `χ(𝒪(W − x)) = χ(𝒪(W)) − 1 = h⁰(𝒪(W)) − 1` and `h¹ ≥ 0`.
Equality forces both conclusions — the induction invariant of the greedy drop. -/
theorem h0_sub_single_of_rational_nonbase (W : Y.CurveDivisor)
    (h1W : Subsingleton (Sheaf.HModule (Y.divisorSheaf K W) 1))
    {x : Y} (hx : x ≠ genericPoint Y) (hdx : Y.residueDeg K x = 1)
    {f : Y.functionField} (hfW : f ∈ divisorSections K W ⊤) (hf : f ≠ 0)
    (hnb : coeffAt hx (W + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf))
      = 0) :
    Sheaf.h0 (Y.divisorSheaf K (W - CurveDivisor.single hx 1)) + 1
        = Sheaf.h0 (Y.divisorSheaf K W) ∧
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (W - CurveDivisor.single hx 1)) 1) := by
  -- sections of `W − x` sit inside sections of `W` …
  have hle : divisorSections K (W - CurveDivisor.single hx 1) ⊤
      ≤ divisorSections K W ⊤ := by
    refine divisorSections_mono K ?_ ⊤
    refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy => ?_)
    rw [CurveDivisor.coeffAt_sub]
    by_cases hyx : y = x
    · subst hyx
      rw [CurveDivisor.coeffAt_single_self]
      omega
    · rw [CurveDivisor.coeffAt_single_of_ne hx hy hyx]
      omega
  -- … properly: the exact-order section violates the deeper bound at `x`
  have hfnot : f ∉ divisorSections K (W - CurveDivisor.single hx 1) ⊤ := by
    intro hmem
    have h0le := (mem_divisorSections_top_iff K hf).mp hmem
    have hcoeff := CurveDivisor.le_iff_coeffAt.mp h0le x hx
    rw [CurveDivisor.coeffAt_zero, CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub,
      CurveDivisor.coeffAt_single_self] at hcoeff
    rw [CurveDivisor.coeffAt_add] at hnb
    omega
  have hne : divisorSections K (W - CurveDivisor.single hx 1) ⊤
      ≠ divisorSections K W ⊤ := by
    intro heq
    rw [← heq] at hfW
    exact hfnot hfW
  have hdrop : Sheaf.h0 (Y.divisorSheaf K (W - CurveDivisor.single hx 1))
      < Sheaf.h0 (Y.divisorSheaf K W) := by
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
    rwa [finrank_divisorSections_top K _, finrank_divisorSections_top K _] at hlt
  -- the χ-ledger on both levels
  have hchiW := chi_divisorSheaf K W
  have hchiWx := chi_divisorSheaf K (W - CurveDivisor.single hx 1)
  have hdegsub : CurveDivisor.deg K (W - CurveDivisor.single hx 1)
      = CurveDivisor.deg K W - 1 := by
    rw [Scheme.CurveDivisor.deg_sub' K, Scheme.CurveDivisor.deg_single' K hx 1, hdx,
      Nat.cast_one, mul_one]
  rw [hdegsub] at hchiWx
  have hh0W : Sheaf.chi (Y.divisorSheaf K W) = (Sheaf.h0 (Y.divisorSheaf K W) : ℤ) :=
    Sheaf.chi_eq_h0 h1W
  have hchidef : Sheaf.chi (Y.divisorSheaf K (W - CurveDivisor.single hx 1))
      = (Sheaf.h0 (Y.divisorSheaf K (W - CurveDivisor.single hx 1)) : ℤ)
        - (Sheaf.h1 (Y.divisorSheaf K (W - CurveDivisor.single hx 1)) : ℤ) := rfl
  have hh1 : Sheaf.h1 (Y.divisorSheaf K (W - CurveDivisor.single hx 1)) = 0 := by omega
  refine ⟨by omega, ?_⟩
  haveI := moduleFinite_hModule_divisorSheaf_one K (W - CurveDivisor.single hx 1)
  exact Module.finrank_zero_iff.mp hh1

/-! ## The keystone: the greedy drop to `h⁰ = 1` -/

/-- **COV-2, the oracle-parametrized greedy `h⁰`-drop** (★ B-1 keystone, worksheet §1.4):
on the curve bundle `Y` over the field `K` with `χ(𝒪_Y) = 1 − g`, let `P` be an
admissible point oracle — closed points, `K`-rational (`residueDeg = 1`), dense (meeting
every nonempty open).  Then every divisor `W` of degree `g + e` with `H¹(𝒪(W)) = 0`
admits an effective divisor `Σ` of degree `e` supported in `P` with

  `h⁰(𝒪(W − Σ)) = 1`  and  `H¹(𝒪(W − Σ)) = 0`.

Induction on `e`: at each step the rank anchor gives `h⁰ = e' + 1 ≥ 1`, the oracle
supplies a rational non-base point (`exists_admissible_nonbase_point`), and the exact
drop (`h0_sub_single_of_rational_nonbase`) preserves the invariant `h¹ = 0` while
lowering the degree budget by one.  The pointwise coverage theorem (B-5) instantiates
`P` with the base-changed `C(K_s)`-points of B-2. -/
theorem exists_effective_sub_h0_eq_one (g : ℕ)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (P : Set Y)
    (hdense : ∀ U : Y.Opens, (U : Set Y).Nonempty → (P ∩ U).Nonempty)
    (hPcl : ∀ x ∈ P, x ≠ genericPoint Y)
    (hPdeg : ∀ x ∈ P, Y.residueDeg K x = 1)
    (W : Y.CurveDivisor) (e : ℕ)
    (hdeg : CurveDivisor.deg K W = (g : ℤ) + e)
    (h1 : Subsingleton (Sheaf.HModule (Y.divisorSheaf K W) 1)) :
    ∃ S : Y.CurveDivisor, 0 ≤ S ∧ CurveDivisor.deg K S = (e : ℤ) ∧
      (∀ (x : Y) (hx : x ≠ genericPoint Y), coeffAt hx S ≠ 0 → x ∈ P) ∧
      Sheaf.h0 (Y.divisorSheaf K (W - S)) = 1 ∧
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (W - S)) 1) := by
  suffices H : ∀ (e : ℕ) (W : Y.CurveDivisor),
      CurveDivisor.deg K W = (g : ℤ) + e →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K W) 1) →
      ∃ S : Y.CurveDivisor, 0 ≤ S ∧ CurveDivisor.deg K S = (e : ℤ) ∧
        (∀ (x : Y) (hx : x ≠ genericPoint Y), coeffAt hx S ≠ 0 → x ∈ P) ∧
        Sheaf.h0 (Y.divisorSheaf K (W - S)) = 1 ∧
        Subsingleton (Sheaf.HModule (Y.divisorSheaf K (W - S)) 1) from
    H e W hdeg h1
  intro e
  induction e with
  | zero =>
    intro W hdeg h1
    have hanchor := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := K) W h1
    rw [hχ, hdeg] at hanchor
    refine ⟨0, le_refl 0, by rw [CurveDivisor.deg_zero, Nat.cast_zero], ?_, ?_, ?_⟩
    · intro x hx hne
      exact (hne (CurveDivisor.coeffAt_zero hx)).elim
    · rw [sub_zero]
      push_cast at hanchor
      omega
    · rw [sub_zero]
      exact h1
  | succ e ih =>
    intro W hdeg h1
    -- `h⁰(𝒪(W)) = e + 2 > 0` by the rank anchor
    have hanchor := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := K) W h1
    rw [hχ, hdeg] at hanchor
    have hpos : 0 < Sheaf.h0 (Y.divisorSheaf K W) := by
      push_cast at hanchor
      omega
    -- an admissible non-base point and the exact drop there
    obtain ⟨x, hx, hxP, f, hfW, hf, hnb⟩ :=
      exists_admissible_nonbase_point P hdense hPcl W hpos
    obtain ⟨hdrop, h1'⟩ :=
      h0_sub_single_of_rational_nonbase W h1 hx (hPdeg x hxP) hfW hf hnb
    have hdeg' : CurveDivisor.deg K (W - CurveDivisor.single hx 1) = (g : ℤ) + e := by
      rw [Scheme.CurveDivisor.deg_sub' K, Scheme.CurveDivisor.deg_single' K hx 1,
        hPdeg x hxP, Nat.cast_one, mul_one, hdeg]
      push_cast
      ring
    obtain ⟨S', hS'0, hS'deg, hS'P, hS'h0, hS'h1⟩ :=
      ih (W - CurveDivisor.single hx 1) hdeg' h1'
    have hsplit : W - (S' + CurveDivisor.single hx 1)
        = W - CurveDivisor.single hx 1 - S' := by
      abel
    refine ⟨S' + CurveDivisor.single hx 1, ?_, ?_, ?_, ?_, ?_⟩
    · -- effectivity
      refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy => ?_)
      have h0S' := CurveDivisor.le_iff_coeffAt.mp hS'0 y hy
      rw [CurveDivisor.coeffAt_zero] at h0S'
      rw [CurveDivisor.coeffAt_zero, CurveDivisor.coeffAt_add]
      by_cases hyx : y = x
      · subst hyx
        rw [CurveDivisor.coeffAt_single_self]
        omega
      · rw [CurveDivisor.coeffAt_single_of_ne hx hy hyx]
        omega
    · -- degree
      rw [CurveDivisor.deg_add, hS'deg, Scheme.CurveDivisor.deg_single' K hx 1,
        hPdeg x hxP, Nat.cast_one, mul_one]
      push_cast
      ring
    · -- support in `P`
      intro y hy hne
      rw [CurveDivisor.coeffAt_add] at hne
      by_cases hyx : y = x
      · subst hyx
        exact hxP
      · rw [CurveDivisor.coeffAt_single_of_ne hx hy hyx, add_zero] at hne
        exact hS'P y hy hne
    · rw [hsplit]
      exact hS'h0
    · rw [hsplit]
      exact hS'h1

end AlgebraicGeometry
