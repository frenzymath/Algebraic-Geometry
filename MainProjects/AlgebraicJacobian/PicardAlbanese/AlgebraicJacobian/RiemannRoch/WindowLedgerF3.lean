/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.WindowLedger
import AlgebraicJacobian.RiemannRoch.SectionBound

/-!
# DD-F brick 6 — window-ledger addenda for the bpf-span route (F3)

The DD-F-owned extension of the DD-0 window ledger (`informal/dd-f-probe-verdict.md`
inventory brick 6; ownership per the verdict's "either a DD-F-owned `WindowLedgerF3.lean`
extension or a sanctioned append"). Every lemma is pure arithmetic over the DD-0 ledger
names (`windowBound_spec`, `windowS_spec`, `windowM_spec`, `windowδ`) — no downstream file
states a numeric window (DAT-D discipline rule 1); the P-fib files consume THESE names
plus `windowBound_spec`.

## The genus disjunction

The ledger never asserts `windowBound ≥ 0`; when `windowBound ≤ 0` the vanishing
`windowBound_spec` already fires at the zero divisor, forcing `h¹(𝒪_Y) = 0` and hence
`g = 0` under the consumer-supplied normalizations `h⁰(𝒪_Y) = 1`, `χ(𝒪_Y) = 1 − g`
(`genus_eq_zero_of_windowBound_nonpos`). This disjunction converts the ledger's
`b`-relative inequalities into the absolute bounds the bpf-span dimension counts need:

* `two_mul_genus_le_S_mul_windowδ` : `2g ≤ s·δ` — the annihilator kernel `N_L` is nonzero
  (probe step 3a/3b);
* `two_mul_genus_le_M_mul_windowδ` : `2g ≤ M·δ` — `K_M ≠ ⊥` in F1;
* `three_mul_genus_le_M_mul_windowδ` : `3g ≤ M·δ` — the bpf subspace is nonzero at every
  codimension `c ≤ g`.

## The window budgets

* `windowBound_add_two_mul_genus_le_M_sub_S_mul` : `b + 2g ≤ (M − s)·δ` — the deepest
  level of the descent stage (probe 3c): sups `G ⊔ A_x ≤ A₁ + A_x` of two `s`-window
  shifts cost at most `2s·δ`, and the budget `(g+2)(s+1) ≥ s` of `windowM_spec` absorbs
  one of them;
* `windowBound_add_windowδ_le_S_mul_sub` : `b + δ ≤ s·δ − 2g` — the tower levels
  `s·F − E + j·x` with `deg E ≤ 2g` (probe 3e), a rearrangement of `windowS_spec`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section LedgerF3

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
  (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
  (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))

/-- **The genus disjunction, degenerate branch**: if the uniform bound satisfies
`windowBound ≤ 0`, then `windowBound_spec` fires at the zero divisor, so `h¹(𝒪_Y) = 0`
and the normalizations `h⁰(𝒪_Y) = 1`, `χ(𝒪_Y) = 1 − g` force `g = 0`. -/
theorem genus_eq_zero_of_windowBound_nonpos (g : ℕ)
    (hb : windowBound π hπ ≤ 0)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ)) : g = 0 := by
  have hsub : Subsingleton (Sheaf.HModule (Y.divisorSheaf K (0 : Y.CurveDivisor)) 1) := by
    refine windowBound_spec π hπ 0 ?_
    rw [CurveDivisor.deg_zero]
    exact hb
  have h10 : Sheaf.h1 (Y.divisorSheaf K (0 : Y.CurveDivisor)) = 0 :=
    Sheaf.h1_eq_zero hsub
  have hcongr : Sheaf.h1 (Y.divisorSheaf K (0 : Y.CurveDivisor))
      = Sheaf.h1 (Y.moduleKSheaf K) :=
    Sheaf.h1_congr (divisorSheafZeroIso K)
  have hchi : Sheaf.chi (Y.moduleKSheaf K)
      = (Sheaf.h0 (Y.moduleKSheaf K) : ℤ) - (Sheaf.h1 (Y.moduleKSheaf K) : ℤ) := rfl
  omega

/-- **`2g ≤ s·δ`** — the absolute multiplier budget. Feeds the nontriviality of the
annihilator kernel `N_L` (probe 3a/3b): `r_s = s·δ + 1 − g > c` for every `c ≤ g`. -/
theorem two_mul_genus_le_S_mul_windowδ (g : ℕ)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ)) :
    2 * (g : ℤ) ≤ (windowS_choice π hπ g : ℤ) * windowδ π := by
  by_cases hb : windowBound π hπ ≤ 0
  · have hg0 : g = 0 := genus_eq_zero_of_windowBound_nonpos π hπ g hb hO hχ
    subst hg0
    simpa using mul_nonneg (Int.natCast_nonneg (windowS_choice π hπ 0)) (windowδ_nonneg π)
  · have hb1 : 0 < windowBound π hπ := not_le.mp hb
    have hspec := windowS_spec π hπ g
    have hδ := one_le_windowδ π
    nlinarith [hspec, hδ, hb1]

/-- **`2g ≤ M·δ`** — the absolute embedding budget. Feeds `K_M ≠ ⊥` in F1
(`dim K_M = M·δ + 1 − 2g ≥ 1`). -/
theorem two_mul_genus_le_M_mul_windowδ (g : ℕ)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ)) :
    2 * (g : ℤ) ≤ (windowM_choice π hπ g : ℤ) * windowδ π := by
  by_cases hb : windowBound π hπ ≤ 0
  · have hg0 : g = 0 := genus_eq_zero_of_windowBound_nonpos π hπ g hb hO hχ
    subst hg0
    simpa using mul_nonneg (Int.natCast_nonneg (windowM_choice π hπ 0)) (windowδ_nonneg π)
  · have hb1 : 0 < windowBound π hπ := not_le.mp hb
    have hnorm := windowBound_le_M_norm π hπ g
    omega

/-- **`3g ≤ M·δ`** — the strengthened embedding budget. Feeds the nontriviality of the
bpf subspace in the bpf-span lemma: `dim T = h⁰(𝒪(MF − D)) − c ≥ M·δ − ℓ + 1 − 2g ≥ 1`
for `ℓ ≤ g`, `c ≤ g`. -/
theorem three_mul_genus_le_M_mul_windowδ (g : ℕ)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ)) :
    3 * (g : ℤ) ≤ (windowM_choice π hπ g : ℤ) * windowδ π := by
  by_cases hb : windowBound π hπ ≤ 0
  · have hg0 : g = 0 := genus_eq_zero_of_windowBound_nonpos π hπ g hb hO hχ
    subst hg0
    simpa using mul_nonneg (Int.natCast_nonneg (windowM_choice π hπ 0)) (windowδ_nonneg π)
  · have hb1 : 0 < windowBound π hπ := not_le.mp hb
    have hspec := windowM_spec π hπ g
    have hδ := one_le_windowδ π
    have hs : (0 : ℤ) ≤ (windowS_choice π hπ g : ℤ) := Int.natCast_nonneg _
    have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
    -- `(s + 1)·δ ≥ 1`, hence `(g + 2)(s + 1)δ ≥ g + 2`, so `M·δ ≥ b + 2g + g + 2 ≥ 3g + 3`
    have hone : (1 : ℤ) ≤ ((windowS_choice π hπ g : ℤ) + 1) * windowδ π := by
      nlinarith [hs, hδ]
    have hcube : ((g : ℤ) + 2)
        ≤ ((g : ℤ) + 2) * (((windowS_choice π hπ g : ℤ) + 1) * windowδ π) :=
      le_mul_of_one_le_right (by positivity) hone
    rw [← mul_assoc] at hcube
    linarith [hspec, hcube, hb1, hg]

/-- **The descent budget** `b + 2g ≤ (M − s)·δ`, spelled `b + 2g + s·δ ≤ M·δ`: the deepest
window of the bpf-span descent stage (probe 3c) — a level `N + sF − (G ⊔ A_x)` with
`G, A_x ≤ div h + sF` costs at most `2s·δ` below `(M+s)·δ − deg D`, and `windowM_spec`'s
budget `(g+2)(s+1) ≥ s` pays for it. -/
theorem windowBound_add_two_mul_genus_le_M_sub_S_mul (g : ℕ) :
    windowBound π hπ + 2 * (g : ℤ) + (windowS_choice π hπ g : ℤ) * windowδ π
      ≤ (windowM_choice π hπ g : ℤ) * windowδ π := by
  have hspec := windowM_spec π hπ g
  have hδ := windowδ_nonneg π
  have hs : (0 : ℤ) ≤ (windowS_choice π hπ g : ℤ) := Int.natCast_nonneg _
  have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
  -- `(g + 2)(s + 1) ≥ s`, so `(g + 2)(s + 1)δ ≥ s·δ`
  have hcoeff : (windowS_choice π hπ g : ℤ)
      ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) := by
    nlinarith [hs, hg]
  have hmul : (windowS_choice π hπ g : ℤ) * windowδ π
      ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π :=
    mul_le_mul_of_nonneg_right hcoeff hδ
  omega

/-- **The tower budget** `b + δ ≤ s·δ − 2g`: the levels `sF − E + j·x` with
`deg E ≤ 2g` of the bpf-span tower stage (probe 3e) stay in-window — a rearrangement of
`windowS_spec`. -/
theorem windowBound_add_windowδ_le_S_mul_sub (g : ℕ) :
    windowBound π hπ + windowδ π
      ≤ (windowS_choice π hπ g : ℤ) * windowδ π - 2 * (g : ℤ) := by
  have hspec := windowS_spec π hπ g
  have hδ := windowδ_nonneg π
  nlinarith [hspec, hδ]

/-! ## The decoupled budget

The universal divisor family is budgeted by its degree `n`, while the Riemann--Roch
normalization carries an independent curve parameter `gamma`.  The coverage path uses
`gamma ≤ n`; keeping this relation explicit here lets the diagonal API above remain
source-compatible and gives the widened tower the exact arithmetic it needs.
-/

theorem two_mul_genus_le_S_mul_windowδ_at (gamma n : ℕ) (hgamma : gamma ≤ n)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ)) :
    2 * (gamma : ℤ) ≤ (windowS_choice π hπ n : ℤ) * windowδ π := by
  by_cases hb : windowBound π hπ ≤ 0
  · have hgamma0 := genus_eq_zero_of_windowBound_nonpos π hπ gamma hb hO hχ
    subst hgamma0
    simpa using mul_nonneg (Int.natCast_nonneg (windowS_choice π hπ n)) (windowδ_nonneg π)
  · have hb1 : 0 < windowBound π hπ := not_le.mp hb
    have hspec := windowS_spec π hπ n
    have hδ := one_le_windowδ π
    have hcast : (gamma : ℤ) ≤ (n : ℤ) := by exact_mod_cast hgamma
    nlinarith [hspec, hδ, hb1]

theorem two_mul_genus_le_M_mul_windowδ_at (gamma n : ℕ) (hgamma : gamma ≤ n)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ)) :
    2 * (gamma : ℤ) ≤ (windowM_choice π hπ n : ℤ) * windowδ π := by
  by_cases hb : windowBound π hπ ≤ 0
  · have hgamma0 := genus_eq_zero_of_windowBound_nonpos π hπ gamma hb hO hχ
    subst hgamma0
    simpa using mul_nonneg (Int.natCast_nonneg (windowM_choice π hπ n)) (windowδ_nonneg π)
  · have hb1 : 0 < windowBound π hπ := not_le.mp hb
    have hnorm := windowBound_le_M_norm π hπ n
    have hcast : (gamma : ℤ) ≤ (n : ℤ) := by exact_mod_cast hgamma
    omega

theorem three_mul_genus_le_M_mul_windowδ_at (gamma n : ℕ) (hgamma : gamma ≤ n)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ)) :
    3 * (gamma : ℤ) ≤ (windowM_choice π hπ n : ℤ) * windowδ π := by
  by_cases hb : windowBound π hπ ≤ 0
  · have hgamma0 := genus_eq_zero_of_windowBound_nonpos π hπ gamma hb hO hχ
    subst hgamma0
    simpa using mul_nonneg (Int.natCast_nonneg (windowM_choice π hπ n)) (windowδ_nonneg π)
  · have hb1 : 0 < windowBound π hπ := not_le.mp hb
    have hspec := windowM_spec π hπ n
    have hδ := one_le_windowδ π
    have hs : (0 : ℤ) ≤ (windowS_choice π hπ n : ℤ) := Int.natCast_nonneg _
    have hgamma' : (0 : ℤ) ≤ (gamma : ℤ) := Int.natCast_nonneg _
    have hcast : (gamma : ℤ) ≤ (n : ℤ) := by exact_mod_cast hgamma
    have hone : (1 : ℤ) ≤ ((windowS_choice π hπ n : ℤ) + 1) * windowδ π := by
      nlinarith [hs, hδ]
    have hcube : ((n : ℤ) + 2)
        ≤ ((n : ℤ) + 2) * (((windowS_choice π hπ n : ℤ) + 1) * windowδ π) :=
      le_mul_of_one_le_right (by positivity) hone
    rw [← mul_assoc] at hcube
    linarith [hspec, hcube, hb1, hgamma']

/-! The degree-keyed forms used by the decoupled P-fib spine.  They do not mention an
Euler-characteristic parameter: after the positive normalization of `windowBound`, the
ledger itself supplies the full `2*n`/`3*n` slack needed by a degree-`n` family. -/

theorem two_mul_degree_le_S_mul_windowδ (n : ℕ) :
    2 * (n : ℤ) ≤ (windowS_choice π hπ n : ℤ) * windowδ π := by
  have hspec := windowS_spec π hπ n
  have hδ := one_le_windowδ π
  have hb := windowBound_pos π hπ
  nlinarith

theorem two_mul_degree_le_M_mul_windowδ (n : ℕ) :
    2 * (n : ℤ) ≤ (windowM_choice π hπ n : ℤ) * windowδ π := by
  have hnorm := windowBound_le_M_norm π hπ n
  have hb := windowBound_pos π hπ
  omega

theorem three_mul_degree_le_M_mul_windowδ (n : ℕ) :
    3 * (n : ℤ) ≤ (windowM_choice π hπ n : ℤ) * windowδ π := by
  have hspec := windowM_spec π hπ n
  have hb := windowBound_pos π hπ
  have hδ := one_le_windowδ π
  have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg _
  have hs : (0 : ℤ) ≤ (windowS_choice π hπ n : ℤ) := Int.natCast_nonneg _
  have hone : (1 : ℤ) ≤ ((windowS_choice π hπ n : ℤ) + 1) * windowδ π := by
    nlinarith
  have hcube : ((n : ℤ) + 2)
      ≤ ((n : ℤ) + 2) * (((windowS_choice π hπ n : ℤ) + 1) * windowδ π) :=
    le_mul_of_one_le_right (by positivity) hone
  rw [← mul_assoc] at hcube
  nlinarith

end LedgerF3

end AlgebraicGeometry
