/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.FLVClass

/-!
# DD-0 — the section bound `h⁰(𝒪(A)) ≤ max 0 (deg A + 1)`

The section-bound half of the DAT-D brick DD-0 (`informal/dat-d-worksheet.md` §5 DD-0,
consumed by the P-fib normalization step F1 of §3.3): on the curve bundle `X` (integral,
smooth of relative dimension one, quasi-compact over a field `K`, with finite `H⁰`/`H¹`
of `𝒪_X`), the global-section count of any divisor sheaf is bounded by its degree,

`h⁰(𝒪(A)) ≤ max 0 (deg A + h⁰(𝒪_X))`,

hence `≤ max 0 (deg A + 1)` when `h⁰(𝒪_X) = 1` (the geometrically-integral curve value,
`ChiCurve.h0_moduleKSheaf`; kept as an explicit hypothesis here so the ledger layer stays
on the abstract bundle).

## Route (worksheet §5 DD-0: "peeling on the landed slice SES; base case via
effective-witness degree ≥ 0")

* **`h¹` never drops under effective twists** (`h1_add_single_le` →
  `h1_add_effective_le`): the dévissage SES `0 → 𝒪(D − x) → 𝒪(D) → sky → 0` has
  skyscraper cokernel with no `H¹`, so the slice machinery
  (`Sheaf.HModule.surjective_map_f`, `ChiSlice.lean`) gives a surjection
  `H¹(𝒪(D − x)) ↠ H¹(𝒪(D))`; peel point by point exactly as `peel_effective`
  (`FLVClass.lean`). In particular `h¹(𝒪(E)) ≤ h¹(𝒪_X)` for `E ≥ 0`
  (`h1_le_of_effective`).
* **The effective witness** (`exists_effective_of_h0_pos`): a nonzero global section of
  `𝒪(A)` is a rational function `g` with `A + div g ≥ 0`, an *effective* divisor of the
  same class — the extraction of `exists_effective_of_picClass` run from `0 < h⁰`
  directly (no Riemann inequality needed). This is the base case: `0 < h⁰ ⟹ deg A ≥ 0`.
* **Assembly** (`h0_le_deg_add_h0_of_pos`, keystone `h0_divisorSheaf_le_max`): if
  `h⁰(𝒪(A)) > 0`, replace `A` by the effective witness `E` (class-invariance of `h⁰` and
  `deg`, `ClassCohomology`/`Degree`), then the χ-ledger `chi_divisorSheaf` reads
  `h⁰(𝒪(E)) = χ(𝒪_X) + deg E + h¹(𝒪(E)) ≤ deg A + h⁰(𝒪_X)`.

The `h¹`-monotonicity lemmas are exported (not private): F1's window comparisons reuse
them, and they are the natural `H¹`-side companion of `peel_effective`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-! ## `h¹` never drops under effective twists -/

/-- **The `h¹` dévissage step**: enlarging the divisor by a closed point can only shrink
`h¹`: `h¹(𝒪(D)) ≤ h¹(𝒪(D − x))`. The dévissage SES `0 → 𝒪(D − x) → 𝒪(D) → sky → 0` has
skyscraper cokernel with vanishing `H¹`, so the slice surjection
`Sheaf.HModule.surjective_map_f` maps `H¹(𝒪(D − x))` onto `H¹(𝒪(D))`. -/
theorem h1_le_h1_sub_single {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor) :
    Sheaf.h1 (X.divisorSheaf K D)
      ≤ Sheaf.h1 (X.divisorSheaf K (D - CurveDivisor.single hx 1)) := by
  haveI : Subsingleton (Sheaf.HModule (devissageSES K hx D).X₃ 1) :=
    skyModule_subsingleton_hModule_one x (jumpModule K hx D)
  haveI : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₁ 1) :=
    moduleFinite_hModule_divisorSheaf_one K (devissageDivisor hx D)
  have hsurj : Function.Surjective (Sheaf.HModule.map (devissageSES K hx D).f 1) :=
    Sheaf.HModule.surjective_map_f (devissageSES_shortExact K hx D) 1
  have hle : Sheaf.h1 (devissageSES K hx D).X₂ ≤ Sheaf.h1 (devissageSES K hx D).X₁ :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  have hX₁ : Sheaf.h1 (devissageSES K hx D).X₁
      = Sheaf.h1 (X.divisorSheaf K (D - CurveDivisor.single hx 1)) := by
    have h : Sheaf.h1 (devissageSES K hx D).X₁
        = Sheaf.h1 (X.divisorSheaf K (devissageDivisor hx D)) := rfl
    rw [h, devissageDivisor_eq_sub hx D]
  have hX₂ : Sheaf.h1 (devissageSES K hx D).X₂ = Sheaf.h1 (X.divisorSheaf K D) := rfl
  rw [← hX₂, ← hX₁]
  exact hle

/-- **Peeling one point on `h¹`**: `h¹(𝒪(B + x)) ≤ h¹(𝒪(B))` — the additive form of the
dévissage step. -/
theorem h1_add_single_le {x : X} (hx : x ≠ genericPoint X) (B : X.CurveDivisor) :
    Sheaf.h1 (X.divisorSheaf K (B + CurveDivisor.single hx 1))
      ≤ Sheaf.h1 (X.divisorSheaf K B) := by
  have h := h1_le_h1_sub_single K hx (B + CurveDivisor.single hx 1)
  have heq : B + CurveDivisor.single hx 1 - CurveDivisor.single hx 1 = B := by abel
  rwa [heq] at h

/-- **Peeling a multiple of a point on `h¹`**: `h¹(𝒪(A + n·x)) ≤ h¹(𝒪(A))` — iterating
`h1_add_single_le`. -/
theorem h1_add_nsmul_single_le {x : X} (hx : x ≠ genericPoint X) (A : X.CurveDivisor)
    (n : ℕ) :
    Sheaf.h1 (X.divisorSheaf K (A + n • CurveDivisor.single hx 1))
      ≤ Sheaf.h1 (X.divisorSheaf K A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := h1_add_single_le K hx (A + n • CurveDivisor.single hx 1)
    have heq : A + n • CurveDivisor.single hx 1 + CurveDivisor.single hx 1
        = A + (n + 1) • CurveDivisor.single hx 1 := by
      rw [succ_nsmul]; abel
    rw [heq] at hstep
    exact le_trans hstep ih

/-- **Effective peeling on `h¹`**: `h¹(𝒪(A + E)) ≤ h¹(𝒪(A))` for any effective `E` —
peel the finitely many points of `E` one multiplicity-block at a time, by induction on
the size of the support (the `peel_effective` skeleton, `FLVClass.lean`). -/
theorem h1_add_effective_le (A E : X.CurveDivisor) (hE : 0 ≤ E) :
    Sheaf.h1 (X.divisorSheaf K (A + E)) ≤ Sheaf.h1 (X.divisorSheaf K A) := by
  suffices H : ∀ (n : ℕ) (E : X.CurveDivisor), 0 ≤ E →
      (toFinsupp E).support.card = n →
      Sheaf.h1 (X.divisorSheaf K (A + E)) ≤ Sheaf.h1 (X.divisorSheaf K A) from
    H _ E hE rfl
  intro n
  induction n with
  | zero =>
    intro E hE hc
    have hE0 : E = 0 :=
      Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp hc)
    rw [hE0, add_zero]
  | succ n ih =>
    intro E hE hc
    classical
    have hne : (toFinsupp E).support.Nonempty := by
      rw [← Finset.card_pos, hc]; exact Nat.succ_pos n
    obtain ⟨p, hp⟩ := hne
    set b : ℤ := toFinsupp E p with hb
    have hb_nonneg : 0 ≤ b := Finsupp.le_def.mp hE p
    have hbpos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm (Finsupp.mem_support_iff.mp hp))
    set E' : X.CurveDivisor := Finsupp.erase p (toFinsupp E) with hE'
    have hdecomp : CurveDivisor.single p.2 b + E' = E := by
      rw [hE', hb]
      exact Finsupp.single_add_erase p (toFinsupp E)
    have hE'nonneg : 0 ≤ E' := by
      rw [hE']
      refine Finsupp.le_def.mpr (fun q => ?_)
      by_cases hq : q = p
      · subst hq; rw [Finsupp.erase_same]; rfl
      · rw [Finsupp.erase_ne hq]; exact Finsupp.le_def.mp hE q
    have hcard : (toFinsupp E').support.card = n := by
      have hEF : toFinsupp E' = Finsupp.erase p (toFinsupp E) := rfl
      rw [hEF, Finsupp.support_erase, Finset.card_erase_of_mem hp, hc, Nat.succ_sub_one]
    have hsingle : CurveDivisor.single p.2 b = b.toNat • CurveDivisor.single p.2 1 := by
      rw [CurveDivisor.nsmul_single_one, Int.toNat_of_nonneg hb_nonneg]
    have hsplit : A + E = (A + E') + b.toNat • CurveDivisor.single p.2 1 := by
      rw [← hdecomp, ← hsingle]; abel
    rw [hsplit]
    exact le_trans (h1_add_nsmul_single_le K p.2 (A + E') b.toNat) (ih E' hE'nonneg hcard)

/-- **`h¹` of an effective divisor sheaf is at most `h¹(𝒪_X)`**: peel all of `E` off the
zero divisor and identify `𝒪(0) ≅ 𝒪_X` (`divisorSheafZeroIso`). -/
theorem h1_le_of_effective (E : X.CurveDivisor) (hE : 0 ≤ E) :
    Sheaf.h1 (X.divisorSheaf K E) ≤ Sheaf.h1 (X.moduleKSheaf K) := by
  have h := h1_add_effective_le K 0 E hE
  rw [zero_add, Sheaf.h1_congr (divisorSheafZeroIso K)] at h
  exact h

/-! ## The effective witness of a divisor with a section -/

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **An effective witness of any class with a nonzero section.** If `h⁰(𝒪(A)) > 0` then
the class of `A` is realized by an **effective** divisor: a nonzero global section of
`𝒪(A)` is `g ∈ K(X)ˣ` with `A + div g ≥ 0`, and that shift is effective of the same
class. This is `exists_effective_of_picClass` (`FLVClass.lean`) with the Riemann-
inequality entry point replaced by the direct hypothesis `0 < h⁰`; in particular it
forces `deg A ≥ 0` — the base case of the section bound. -/
theorem exists_effective_of_h0_pos (A : X.CurveDivisor)
    (hA : 0 < Sheaf.h0 (X.divisorSheaf K A)) :
    ∃ E : X.CurveDivisor, 0 ≤ E ∧ CurveDivisor.picClass K E = CurveDivisor.picClass K A := by
  haveI : Nontrivial (Sheaf.HModule (X.divisorSheaf K A) 0) :=
    Module.nontrivial_of_finrank_pos hA
  -- a nonzero global section `g ∈ 𝒪(A)(⊤) ⊆ K(X)`.
  obtain ⟨t, ht⟩ := exists_ne (0 : Sheaf.HModule (X.divisorSheaf K A) 0)
  set s := (Sheaf.HModule.linearEquiv₀ (Opens.grothendieckTopology (X : TopCat))
    (isTerminalTop : IsTerminal (⊤ : X.Opens)) (X.divisorSheaf K A)) t with hs
  have hsne : s ≠ 0 := by
    rw [hs]; exact (LinearEquiv.map_ne_zero_iff _).mpr ht
  set g : X.functionField := divisorVal K s with hg
  have hgmem : g ∈ divisorSections K A ⊤ := divisorVal_mem K s
  have hgne : g ≠ 0 := by
    intro h
    exact hsne (divisorSection_ext K
      (show divisorVal K s = divisorVal K (0 : _) from by rw [← hg, h]; rfl))
  -- the unit `u` and the effective shift.
  set u : X.functionFieldˣ := Units.mk0 g hgne with hu
  have huval : (u : X.functionField) = g := rfl
  refine ⟨A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u, ?_, ?_⟩
  · -- effectivity: `coeffAt (A + div u) ≥ 0` from the pole bound
    refine Finsupp.le_def.mpr (fun p => ?_)
    change (0 : ℤ) ≤ coeffAt p.2 (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u)
    have htop : ((⊤ : X.Opens) : Set X).Nonempty := ⟨genericPoint X, trivial⟩
    have hb := (mem_divisorSections_of_nonempty K htop).mp hgmem p.1 p.2 trivial
    rw [← huval, Scheme.ord_val_eq K u p.2, divisorBound_le_iff p.2,
      CurveDivisor.coeffAt_neg] at hb
    rw [CurveDivisor.coeffAt_add]
    omega
  · -- same class
    rw [CurveDivisor.picClass_add, CurveDivisor.picClass_divOf, mul_one]

/-! ## The section bound -/

/-- **The section bound, positive case**: if `𝒪(A)` has a nonzero section then
`h⁰(𝒪(A)) ≤ deg A + h⁰(𝒪_X)`. Replace `A` by its effective witness (class-invariance of
`h⁰` and `deg`), read `h⁰ = χ(𝒪_X) + deg + h¹` off the χ-ledger, and bound `h¹` by
`h¹(𝒪_X)` (effective peeling). -/
theorem h0_le_deg_add_h0_of_pos (A : X.CurveDivisor)
    (hA : 0 < Sheaf.h0 (X.divisorSheaf K A)) :
    (Sheaf.h0 (X.divisorSheaf K A) : ℤ)
      ≤ CurveDivisor.deg K A + (Sheaf.h0 (X.moduleKSheaf K) : ℤ) := by
  obtain ⟨E, hE, hEc⟩ := exists_effective_of_h0_pos K A hA
  have h0eq : Sheaf.h0 (X.divisorSheaf K A) = Sheaf.h0 (X.divisorSheaf K E) :=
    (h0_divisorSheaf_eq_of_picClass_eq K hEc).symm
  have hdeg : CurveDivisor.deg K E = CurveDivisor.deg K A :=
    deg_eq_deg_of_picClass_eq K hEc
  have hchiE := chi_divisorSheaf K E
  have hh1 : Sheaf.h1 (X.divisorSheaf K E) ≤ Sheaf.h1 (X.moduleKSheaf K) :=
    h1_le_of_effective K E hE
  have hchiE' : Sheaf.chi (X.divisorSheaf K E)
      = (Sheaf.h0 (X.divisorSheaf K E) : ℤ) - Sheaf.h1 (X.divisorSheaf K E) := rfl
  have hchiO : Sheaf.chi (X.moduleKSheaf K)
      = (Sheaf.h0 (X.moduleKSheaf K) : ℤ) - Sheaf.h1 (X.moduleKSheaf K) := rfl
  omega

/-- **DD-0 section bound, ledger form** (★): for every Weil divisor `A` on the curve
bundle, `h⁰(𝒪(A)) ≤ max 0 (deg A + h⁰(𝒪_X))`. The `max` absorbs the divisors with no
sections (where `deg A` may be arbitrarily negative). -/
theorem h0_divisorSheaf_le_max (A : X.CurveDivisor) :
    (Sheaf.h0 (X.divisorSheaf K A) : ℤ)
      ≤ max 0 (CurveDivisor.deg K A + (Sheaf.h0 (X.moduleKSheaf K) : ℤ)) := by
  by_cases h : Sheaf.h0 (X.divisorSheaf K A) = 0
  · rw [h]
    exact le_max_of_le_left (by norm_num)
  · exact le_max_of_le_right
      (h0_le_deg_add_h0_of_pos K A (Nat.pos_of_ne_zero h))

/-- **DD-0 section bound, the worksheet spelling** (★): when `h⁰(𝒪_X) = 1` (the
geometrically-integral curve value, discharged by `h0_moduleKSheaf` at the curve layer),
`h⁰(𝒪(A)) ≤ max 0 (deg A + 1)` for every Weil divisor `A`. This is the bound the P-fib
normalization F1 consumes (`informal/dat-d-worksheet.md` §3.3, §5 DD-0). -/
theorem h0_divisorSheaf_le_max_of_h0_one (hO : Sheaf.h0 (X.moduleKSheaf K) = 1)
    (A : X.CurveDivisor) :
    (Sheaf.h0 (X.divisorSheaf K A) : ℤ) ≤ max 0 (CurveDivisor.deg K A + 1) := by
  have h := h0_divisorSheaf_le_max K A
  rw [hO] at h
  exact_mod_cast h

/-- **DD-0 section bound, linear form**: with `h⁰(𝒪_X) = 1` and a nonzero section,
`h⁰(𝒪(A)) ≤ deg A + 1` — the form used pointwise in F1's base-divisor bound
`deg bd(K_M) ≤ 2g`. -/
theorem h0_le_deg_add_one_of_pos (hO : Sheaf.h0 (X.moduleKSheaf K) = 1)
    (A : X.CurveDivisor) (hA : 0 < Sheaf.h0 (X.divisorSheaf K A)) :
    (Sheaf.h0 (X.divisorSheaf K A) : ℤ) ≤ CurveDivisor.deg K A + 1 := by
  have h := h0_le_deg_add_h0_of_pos K A hA
  rw [hO] at h
  exact_mod_cast h

end AlgebraicGeometry
