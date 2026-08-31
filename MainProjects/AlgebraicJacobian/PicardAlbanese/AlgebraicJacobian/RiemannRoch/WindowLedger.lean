/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.UniformVanishing
import AlgebraicJacobian.RiemannRoch.ThetaDegree

/-!
# DD-0 — the window ledger of the Div^g-lite campaign

The single home for the fixed twist exponents of the DAT-D campaign
(`informal/dat-d-worksheet.md` §2.1, §5 DD-0). Every downstream file (DD-F/DD-4/DD-C …)
imports its window facts **by name from here**; a numeric degree bound appearing
downstream is a spec violation (DAT-D discipline rule 1).

For the abstract curve bundle `Y` (integral, smooth of relative dimension one, lft and
quasi-compact over a field `K`, with finite `H⁰`/`H¹` of `𝒪_Y`) carrying a **finite
dominant** morphism `π : Y ⟶ ℙ¹`, the ledger fixes three integers/naturals and one lemma
per window used by the P-fib route (§3.3).

## The named constants

* `windowBound π hπ : ℤ` — the DAT-0a uniform vanishing bound `b`, a **fixed choice**
  (`Classical.choose` of `exists_bound_subsingleton_hModule_one_of_isFinite_toP1`, which
  is existential). This file is the **only** consumer of DAT-0a directly (risk 7): if
  DAT-0a's packaging shifts, only `windowBound`/`windowBound_spec` change.
* `windowδ π : ℤ` — the twist degree `δ = classDeg (Θ) = deg F ≥ 1` (DAT-0b).
* `windowS_choice π hπ g : ℕ` — the multiplier step `s`, least with `(s − 1)·δ ≥ b + 3g`
  (strengthened from `2g` for the P-fib-N tower budget, I-0234; the historical `2g` fact
  survives as `windowS_spec`).
* `windowM_choice π hπ g : ℕ` — the embedding exponent `M`, least with
  `M·δ ≥ b + 2g + (g + 2)·(s + 1)·δ`.

Here `g : ℕ` is the genus supplied by the consumer (the ledger arithmetic never assumes
`g = χ`-anything; the rank exports take `χ(𝒪_Y) = 1 − g` as a hypothesis, discharged by
the consumer's curve).

## The windows (each an `H¹ = 0`, i.e. `Subsingleton (HModule (𝒪(…)) 1)`, via DAT-0a)

Writing `F := fiberWeilDivisor π` (`deg F = δ`, `F ≥ 0`) and `P` any divisor with
`deg P = δ` (the pole fibre of §1.1), for `deg D ≤ 2g` and `0 ≤ j ≤ g + 1`:

* embedding windows `window_embedding{,_shift,_mult}`: `𝒪(A·F)` for `A ∈ {M, M+s, s}`;
* normalization windows `window_normalization{,_shift}`: `𝒪(A·F − D)`;
* lane windows `window_lane{,_shift}`: `𝒪(A·F − D − j·P)`;
* the multiplier lane window `window_mult_lane`: `𝒪(s·F − D − P)` — F3's
  `A_P`-surjectivity budget `(s − 1)·δ ≥ b + 2g` spent.

All are proved from `windowBound_spec` (DAT-0a) applied to the degree of the divisor,
whose lower bound `≥ b` is the arithmetic of `windowM_spec`/`windowS_spec`.

## The rank values (rank anchor, `FLVClass.lean`)

`rank_embedding{,_shift,_mult}` give `h⁰(𝒪(A·F)) = A·δ + χ(𝒪_Y)`, and the `…_of_genus`
variants rewrite `χ(𝒪_Y) = 1 − g` to `r_A = A·δ + 1 − g` (§2.1). The lane dimensions of
F2's graded pieces are `rank_normalization{,_shift}` and `rank_lane{,_shift}`:
`h⁰ = A·δ − deg D − j·δ + χ(𝒪_Y)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

/-! ## Degree arithmetic helpers -/

section DegHelpers

variable {K : Type u} [CommRing K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- Degree of a natural multiple: `deg (n • D) = n · deg D`. -/
private lemma deg_nsmul (n : ℕ) (D : X.CurveDivisor) :
    CurveDivisor.deg K (n • D) = n * CurveDivisor.deg K D := by
  induction n with
  | zero => rw [zero_nsmul, CurveDivisor.deg_zero, Nat.cast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, CurveDivisor.deg_add, ih]; push_cast; ring

/-- Degree of a difference: `deg (A − B) = deg A − deg B`. -/
private lemma deg_sub (A B : X.CurveDivisor) :
    CurveDivisor.deg K (A - B) = CurveDivisor.deg K A - CurveDivisor.deg K B := by
  rw [sub_eq_add_neg, CurveDivisor.deg_add, CurveDivisor.deg_neg, sub_eq_add_neg]

end DegHelpers

section Ledger

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
  (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
  (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))

/-! ## The uniform vanishing bound `b` (DAT-0a, fixed choice) -/

/-- **The positive DAT-0a bound `b`, fixed.**  We normalize the chosen bound to at least
`1`.  This is still a valid vanishing threshold: a divisor above `max 1 b₀` is above the
raw DAT-0a witness `b₀`, while the positive normalization keeps the high-window tower
available on genus-zero curves at positive divisor degree. -/
noncomputable def windowBound : ℤ :=
  max 1 (exists_bound_subsingleton_hModule_one_of_isFinite_toP1 π hπ).choose

/-- **The defining property of `b`**: every Weil divisor of degree `≥ b` has vanishing
`H¹`. This is the only window fact all the specific windows below route through. -/
theorem windowBound_spec (D : Y.CurveDivisor)
    (hD : windowBound π hπ ≤ CurveDivisor.deg K D) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K D) 1) := by
  have hraw : (exists_bound_subsingleton_hModule_one_of_isFinite_toP1 π hπ).choose
      ≤ windowBound π hπ := by
    rw [windowBound]
    exact le_max_right _ _
  exact (exists_bound_subsingleton_hModule_one_of_isFinite_toP1 π hπ).choose_spec D
    (hraw.trans hD)

/-- The normalized ledger bound is strictly positive. -/
theorem windowBound_pos : 0 < windowBound π hπ := by
  simp [windowBound]

/-! ## The twist degree `δ` (DAT-0b) -/

/-- **The twist degree `δ = classDeg Θ = deg F ≥ 1`.** -/
noncomputable def windowδ : ℤ := classDeg K (fiberTwist π 1)

/-- `1 ≤ δ` (DAT-0b, `one_le_classDeg_fiberTwist_one`). -/
theorem one_le_windowδ : 1 ≤ windowδ π := one_le_classDeg_fiberTwist_one π

/-- `0 ≤ δ`. -/
theorem windowδ_nonneg : 0 ≤ windowδ π := le_trans zero_le_one (one_le_windowδ π)

omit [IsFinite π] in
/-- The fiber Weil divisor has degree `δ`: `deg F = δ` (DAT-0b,
`classDeg_fiberTwist_one`). -/
theorem deg_fiberWeilDivisor_windowδ :
    CurveDivisor.deg K (fiberWeilDivisor π) = windowδ π :=
  (classDeg_fiberTwist_one π).symm

/-! ## The multiplier step `s` and the embedding exponent `M` -/

private theorem windowS_exists (g : ℕ) :
    ∃ s : ℕ, windowBound π hπ + 3 * (g : ℤ) ≤ ((s : ℤ) - 1) * windowδ π := by
  set T : ℤ := windowBound π hπ + 3 * (g : ℤ) with hT
  refine ⟨T.toNat + 1, ?_⟩
  have hδ : 1 ≤ windowδ π := one_le_windowδ π
  have h1 : ((T.toNat : ℤ)) ≤ (T.toNat : ℤ) * windowδ π :=
    le_mul_of_one_le_right (Int.natCast_nonneg _) hδ
  have h2 : T ≤ (T.toNat : ℤ) := Int.self_le_toNat T
  have h3 : (((T.toNat + 1 : ℕ) : ℤ) - 1) = (T.toNat : ℤ) := by push_cast; ring
  rw [h3]; linarith

/-- **The multiplier step `s`** — least `s` with `(s − 1)·δ ≥ b + 3g` (worksheet §2.1,
budget strengthened `2g → 3g` for the P-fib-N tower discharge at residue fields,
I-0234). Used by F3 (graded surjectivity of `H_s` onto the `P`-level algebra). -/
noncomputable def windowS_choice (g : ℕ) : ℕ := Nat.find (windowS_exists π hπ g)

/-- **The strengthened defining inequality of `s`**: `(s − 1)·δ ≥ b + 3g` — the
P-fib-N tower budget `hβS` at `κ(p)` (I-0234). -/
theorem windowS_spec_three (g : ℕ) :
    windowBound π hπ + 3 * (g : ℤ) ≤ ((windowS_choice π hπ g : ℤ) - 1) * windowδ π :=
  Nat.find_spec (windowS_exists π hπ g)

/-- **The original defining inequality of `s`**: `(s − 1)·δ ≥ b + 2g` — kept in its
historical shape so every pre-I-0234 consumer is byte-compatible; strictly weaker than
`windowS_spec_three`. F3's `A_P`-surjectivity window. -/
theorem windowS_spec (g : ℕ) :
    windowBound π hπ + 2 * (g : ℤ) ≤ ((windowS_choice π hπ g : ℤ) - 1) * windowδ π := by
  have h := windowS_spec_three π hπ g
  have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
  linarith

private theorem windowM_exists (g : ℕ) :
    ∃ M : ℕ, windowBound π hπ + 2 * (g : ℤ)
        + ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π
      ≤ (M : ℤ) * windowδ π := by
  set U : ℤ := windowBound π hπ + 2 * (g : ℤ)
      + ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π with hU
  refine ⟨U.toNat, ?_⟩
  have hδ : 1 ≤ windowδ π := one_le_windowδ π
  have h1 : ((U.toNat : ℤ)) ≤ (U.toNat : ℤ) * windowδ π :=
    le_mul_of_one_le_right (Int.natCast_nonneg _) hδ
  have h2 : U ≤ (U.toNat : ℤ) := Int.self_le_toNat U
  linarith

/-- **The embedding exponent `M`** — least `M` with `M·δ ≥ b + 2g + (g + 2)·(s + 1)·δ`
(worksheet §2.1). Chosen so every embedding/normalization/lane window down to depth
`g + 1` in `P`-steps stays `≥ b`. -/
noncomputable def windowM_choice (g : ℕ) : ℕ := Nat.find (windowM_exists π hπ g)

/-- **The defining inequality of `M`**: `M·δ ≥ b + 2g + (g + 2)·(s + 1)·δ`. -/
theorem windowM_spec (g : ℕ) :
    windowBound π hπ + 2 * (g : ℤ)
        + ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π
      ≤ (windowM_choice π hπ g : ℤ) * windowδ π :=
  Nat.find_spec (windowM_exists π hπ g)

/-! ## Derived degree lower bounds -/

/-- **The embedding bound**: `b ≤ M·δ`. -/
theorem windowBound_le_M_mul (g : ℕ) :
    windowBound π hπ ≤ (windowM_choice π hπ g : ℤ) * windowδ π := by
  have hspec := windowM_spec π hπ g
  have hnn : 0 ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) (windowδ_nonneg π)
  linarith

/-- **The embedding bound at `s`**: `b ≤ s·δ`. -/
theorem windowBound_le_S_mul (g : ℕ) :
    windowBound π hπ ≤ (windowS_choice π hπ g : ℤ) * windowδ π := by
  have hspec := windowS_spec π hπ g
  have hδ : 0 ≤ windowδ π := windowδ_nonneg π
  have hg : (0 : ℤ) ≤ 2 * (g : ℤ) := by positivity
  -- `(s − 1)·δ ≥ b + 2g ≥ b`, and `s·δ = (s−1)·δ + δ ≥ (s−1)·δ`
  nlinarith [hspec, hδ, hg]

/-- **The normalization bound**: `b ≤ M·δ − 2g`. -/
theorem windowBound_le_M_norm (g : ℕ) :
    windowBound π hπ ≤ (windowM_choice π hπ g : ℤ) * windowδ π - 2 * (g : ℤ) := by
  have hspec := windowM_spec π hπ g
  have hnn : 0 ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) (windowδ_nonneg π)
  linarith

/-- **The lane bound**: `b ≤ M·δ − 2g − (g + 1)·δ`. Every `M`-lane window at depth
`≤ g + 1` in `P`-steps and effective slack `deg D ≤ 2g` sits above it. -/
theorem windowBound_le_M_lane (g : ℕ) :
    windowBound π hπ
      ≤ (windowM_choice π hπ g : ℤ) * windowδ π - 2 * (g : ℤ)
          - ((g : ℤ) + 1) * windowδ π := by
  have hspec := windowM_spec π hπ g
  have hδ : 0 ≤ windowδ π := windowδ_nonneg π
  have hs : (0 : ℤ) ≤ (windowS_choice π hπ g : ℤ) := Int.natCast_nonneg _
  have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
  -- `(g + 2)·(s + 1) − (g + 1) ≥ 1 ≥ 0`, so `(g+2)(s+1)δ ≥ (g+1)δ`
  have hcoeff : ((g : ℤ) + 1) ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) := by
    nlinarith [hs, hg]
  have hmul : ((g : ℤ) + 1) * windowδ π
      ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π :=
    mul_le_mul_of_nonneg_right hcoeff hδ
  linarith

/-- The shift slack: `0 ≤ s·δ` — the `M ↦ M + s` window shifts only raise degrees. -/
theorem windowS_mul_windowδ_nonneg (g : ℕ) :
    0 ≤ (windowS_choice π hπ g : ℤ) * windowδ π :=
  mul_nonneg (Int.natCast_nonneg _) (windowδ_nonneg π)

/-! ## The windows: `H¹ = 0` at every twist the P-fib route visits (§3.3)

Every lemma is `windowBound_spec` (DAT-0a) plus ledger arithmetic; no consumer restates
a degree bound. -/

/-- **The embedding window**: `H¹(𝒪(M·F)) = 0`. The window carrying the first
Grassmannian factor `H_M`. -/
theorem window_embedding (g : ℕ) :
    Subsingleton (Sheaf.HModule
      (Y.divisorSheaf K (windowM_choice π hπ g • fiberWeilDivisor π)) 1) := by
  refine windowBound_spec π hπ _ ?_
  rw [deg_nsmul, deg_fiberWeilDivisor_windowδ]
  exact windowBound_le_M_mul π hπ g

/-- **The shifted embedding window**: `H¹(𝒪((M+s)·F)) = 0`. The window carrying the
second Grassmannian factor `H_{M+s}`. -/
theorem window_embedding_shift (g : ℕ) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K
      ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π)) 1) := by
  refine windowBound_spec π hπ _ ?_
  rw [deg_nsmul, deg_fiberWeilDivisor_windowδ]
  have hM := windowBound_le_M_mul π hπ g
  have hs := windowS_mul_windowδ_nonneg π hπ g
  push_cast
  linarith

/-- **The multiplier window**: `H¹(𝒪(s·F)) = 0`. The window carrying the multiplier
space `H_s` of the carve `(♦)`. -/
theorem window_embedding_mult (g : ℕ) :
    Subsingleton (Sheaf.HModule
      (Y.divisorSheaf K (windowS_choice π hπ g • fiberWeilDivisor π)) 1) := by
  refine windowBound_spec π hπ _ ?_
  rw [deg_nsmul, deg_fiberWeilDivisor_windowδ]
  exact windowBound_le_S_mul π hπ g

/-- **The normalization window**: `H¹(𝒪(M·F − D)) = 0` for every divisor of degree
`≤ 2g` (in particular the F1 base divisor, whose degree the section bound caps at `2g`).
-/
theorem window_normalization (g : ℕ) (D : Y.CurveDivisor)
    (hD : CurveDivisor.deg K D ≤ 2 * (g : ℤ)) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K
      (windowM_choice π hπ g • fiberWeilDivisor π - D)) 1) := by
  refine windowBound_spec π hπ _ ?_
  rw [deg_sub, deg_nsmul, deg_fiberWeilDivisor_windowδ]
  have hM := windowBound_le_M_norm π hπ g
  linarith

/-- **The shifted normalization window**: `H¹(𝒪((M+s)·F − D)) = 0` for `deg D ≤ 2g`. -/
theorem window_normalization_shift (g : ℕ) (D : Y.CurveDivisor)
    (hD : CurveDivisor.deg K D ≤ 2 * (g : ℤ)) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K
      ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π - D)) 1) := by
  refine windowBound_spec π hπ _ ?_
  rw [deg_sub, deg_nsmul, deg_fiberWeilDivisor_windowδ]
  have hM := windowBound_le_M_norm π hπ g
  have hs := windowS_mul_windowδ_nonneg π hπ g
  push_cast
  linarith

/-- **The lane window**: `H¹(𝒪(M·F − D − j·P)) = 0` for `deg D ≤ 2g`, lane depth
`j ≤ g + 1`, and any `P` of degree `δ` (the pole fibre). The `V_j` lanes of the P-fib
route (§3.3 F2). -/
theorem window_lane (g : ℕ) (D : Y.CurveDivisor)
    (hD : CurveDivisor.deg K D ≤ 2 * (g : ℤ)) (j : ℕ) (hj : j ≤ g + 1)
    (P : Y.CurveDivisor) (hP : CurveDivisor.deg K P = windowδ π) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K
      (windowM_choice π hπ g • fiberWeilDivisor π - D - j • P)) 1) := by
  refine windowBound_spec π hπ _ ?_
  rw [deg_sub, deg_sub, deg_nsmul, deg_nsmul, deg_fiberWeilDivisor_windowδ, hP]
  have hlane := windowBound_le_M_lane π hπ g
  have hδ := windowδ_nonneg π
  have hjle : (j : ℤ) ≤ (g : ℤ) + 1 := by exact_mod_cast hj
  have hjδ : (j : ℤ) * windowδ π ≤ ((g : ℤ) + 1) * windowδ π :=
    mul_le_mul_of_nonneg_right hjle hδ
  linarith

/-- **The shifted lane window**: `H¹(𝒪((M+s)·F − D − j·P)) = 0` for `deg D ≤ 2g`,
`j ≤ g + 1`, `deg P = δ`. The `W_j` lanes of the P-fib route (§3.3 F2). -/
theorem window_lane_shift (g : ℕ) (D : Y.CurveDivisor)
    (hD : CurveDivisor.deg K D ≤ 2 * (g : ℤ)) (j : ℕ) (hj : j ≤ g + 1)
    (P : Y.CurveDivisor) (hP : CurveDivisor.deg K P = windowδ π) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K
      ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π - D - j • P))
      1) := by
  refine windowBound_spec π hπ _ ?_
  rw [deg_sub, deg_sub, deg_nsmul, deg_nsmul, deg_fiberWeilDivisor_windowδ, hP]
  have hlane := windowBound_le_M_lane π hπ g
  have hδ := windowδ_nonneg π
  have hs := windowS_mul_windowδ_nonneg π hπ g
  have hjle : (j : ℤ) ≤ (g : ℤ) + 1 := by exact_mod_cast hj
  have hjδ : (j : ℤ) * windowδ π ≤ ((g : ℤ) + 1) * windowδ π :=
    mul_le_mul_of_nonneg_right hjle hδ
  push_cast
  linarith

/-- **The multiplier lane window**: `H¹(𝒪(s·F − D − P)) = 0` for `deg D ≤ 2g` and
`deg P = δ`. This is what the `(s − 1)·δ ≥ b + 2g` budget of `windowS_spec` buys: the
restriction `H⁰(𝒪(s·F)) ↠ Γ(𝒪_P)` of F3's `A_P`-surjectivity is onto because this `H¹`
vanishes (take `D = 0`; the `deg D ≤ 2g` slack is free). -/
theorem window_mult_lane (g : ℕ) (D : Y.CurveDivisor)
    (hD : CurveDivisor.deg K D ≤ 2 * (g : ℤ))
    (P : Y.CurveDivisor) (hP : CurveDivisor.deg K P = windowδ π) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K
      (windowS_choice π hπ g • fiberWeilDivisor π - D - P)) 1) := by
  refine windowBound_spec π hπ _ ?_
  rw [deg_sub, deg_sub, deg_nsmul, deg_fiberWeilDivisor_windowδ, hP]
  have hspec := windowS_spec π hπ g
  linarith

/-! ## The rank values (rank anchor: `h0_eq_deg_add_chi_of_subsingleton_hModule_one`) -/

/-- **The rank of the embedding window**: `h⁰(𝒪(M·F)) = M·δ + χ(𝒪_Y)`. -/
theorem rank_embedding (g : ℕ) :
    (Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • fiberWeilDivisor π)) : ℤ)
      = (windowM_choice π hπ g : ℤ) * windowδ π + Sheaf.chi (Y.moduleKSheaf K) := by
  rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (window_embedding π hπ g),
    deg_nsmul, deg_fiberWeilDivisor_windowδ]

/-- **The rank of the shifted embedding window**: `h⁰(𝒪((M+s)·F)) = (M+s)·δ + χ(𝒪_Y)`. -/
theorem rank_embedding_shift (g : ℕ) :
    (Sheaf.h0 (Y.divisorSheaf K
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π)) : ℤ)
      = ((windowM_choice π hπ g : ℤ) + (windowS_choice π hπ g : ℤ)) * windowδ π
        + Sheaf.chi (Y.moduleKSheaf K) := by
  rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (window_embedding_shift π hπ g),
    deg_nsmul, deg_fiberWeilDivisor_windowδ]
  push_cast
  ring

/-- **The rank of the multiplier window**: `h⁰(𝒪(s·F)) = s·δ + χ(𝒪_Y)`. -/
theorem rank_embedding_mult (g : ℕ) :
    (Sheaf.h0 (Y.divisorSheaf K (windowS_choice π hπ g • fiberWeilDivisor π)) : ℤ)
      = (windowS_choice π hπ g : ℤ) * windowδ π + Sheaf.chi (Y.moduleKSheaf K) := by
  rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (window_embedding_mult π hπ g),
    deg_nsmul, deg_fiberWeilDivisor_windowδ]

/-- **`r_M = M·δ + 1 − g`** (§2.1): the genus form of the embedding rank, under the
consumer-supplied `χ(𝒪_Y) = 1 − g`. -/
theorem rank_embedding_of_genus (g : ℕ)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ)) :
    (Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • fiberWeilDivisor π)) : ℤ)
      = (windowM_choice π hπ g : ℤ) * windowδ π + 1 - (g : ℤ) := by
  rw [rank_embedding π hπ g, hχ]; ring

/-- **`r_{M+s} = (M+s)·δ + 1 − g`** (§2.1): the genus form of the shifted embedding
rank. -/
theorem rank_embedding_shift_of_genus (g : ℕ)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ)) :
    (Sheaf.h0 (Y.divisorSheaf K
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π)) : ℤ)
      = ((windowM_choice π hπ g : ℤ) + (windowS_choice π hπ g : ℤ)) * windowδ π
        + 1 - (g : ℤ) := by
  rw [rank_embedding_shift π hπ g, hχ]; ring

/-- **`r_s = s·δ + 1 − g`** (§2.1): the genus form of the multiplier rank. -/
theorem rank_embedding_mult_of_genus (g : ℕ)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ)) :
    (Sheaf.h0 (Y.divisorSheaf K (windowS_choice π hπ g • fiberWeilDivisor π)) : ℤ)
      = (windowS_choice π hπ g : ℤ) * windowδ π + 1 - (g : ℤ) := by
  rw [rank_embedding_mult π hπ g, hχ]; ring

/-- **The rank of the normalization window**: `h⁰(𝒪(M·F − D)) = M·δ − deg D + χ(𝒪_Y)`
for `deg D ≤ 2g`. -/
theorem rank_normalization (g : ℕ) (D : Y.CurveDivisor)
    (hD : CurveDivisor.deg K D ≤ 2 * (g : ℤ)) :
    (Sheaf.h0 (Y.divisorSheaf K
        (windowM_choice π hπ g • fiberWeilDivisor π - D)) : ℤ)
      = (windowM_choice π hπ g : ℤ) * windowδ π - CurveDivisor.deg K D
        + Sheaf.chi (Y.moduleKSheaf K) := by
  rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
      (window_normalization π hπ g D hD),
    deg_sub, deg_nsmul, deg_fiberWeilDivisor_windowδ]

/-- **The rank of the shifted normalization window**:
`h⁰(𝒪((M+s)·F − D)) = (M+s)·δ − deg D + χ(𝒪_Y)` for `deg D ≤ 2g`. -/
theorem rank_normalization_shift (g : ℕ) (D : Y.CurveDivisor)
    (hD : CurveDivisor.deg K D ≤ 2 * (g : ℤ)) :
    (Sheaf.h0 (Y.divisorSheaf K
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π - D)) : ℤ)
      = ((windowM_choice π hπ g : ℤ) + (windowS_choice π hπ g : ℤ)) * windowδ π
        - CurveDivisor.deg K D + Sheaf.chi (Y.moduleKSheaf K) := by
  rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
      (window_normalization_shift π hπ g D hD),
    deg_sub, deg_nsmul, deg_fiberWeilDivisor_windowδ]
  push_cast
  ring

/-- **The rank of the lane window**: `dim V_j = M·δ − deg D − j·δ + χ(𝒪_Y)` for
`deg D ≤ 2g`, `j ≤ g + 1`, `deg P = δ` — the exact lane dimensions of F2. -/
theorem rank_lane (g : ℕ) (D : Y.CurveDivisor)
    (hD : CurveDivisor.deg K D ≤ 2 * (g : ℤ)) (j : ℕ) (hj : j ≤ g + 1)
    (P : Y.CurveDivisor) (hP : CurveDivisor.deg K P = windowδ π) :
    (Sheaf.h0 (Y.divisorSheaf K
        (windowM_choice π hπ g • fiberWeilDivisor π - D - j • P)) : ℤ)
      = (windowM_choice π hπ g : ℤ) * windowδ π - CurveDivisor.deg K D
        - (j : ℤ) * windowδ π + Sheaf.chi (Y.moduleKSheaf K) := by
  rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
      (window_lane π hπ g D hD j hj P hP),
    deg_sub, deg_sub, deg_nsmul, deg_nsmul, deg_fiberWeilDivisor_windowδ, hP]

/-- **The rank of the shifted lane window**:
`dim W_j = (M+s)·δ − deg D − j·δ + χ(𝒪_Y)` for `deg D ≤ 2g`, `j ≤ g + 1`, `deg P = δ`.
-/
theorem rank_lane_shift (g : ℕ) (D : Y.CurveDivisor)
    (hD : CurveDivisor.deg K D ≤ 2 * (g : ℤ)) (j : ℕ) (hj : j ≤ g + 1)
    (P : Y.CurveDivisor) (hP : CurveDivisor.deg K P = windowδ π) :
    (Sheaf.h0 (Y.divisorSheaf K
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π - D
          - j • P)) : ℤ)
      = ((windowM_choice π hπ g : ℤ) + (windowS_choice π hπ g : ℤ)) * windowδ π
        - CurveDivisor.deg K D - (j : ℤ) * windowδ π
        + Sheaf.chi (Y.moduleKSheaf K) := by
  rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
      (window_lane_shift π hπ g D hD j hj P hP),
    deg_sub, deg_sub, deg_nsmul, deg_nsmul, deg_fiberWeilDivisor_windowδ, hP]
  push_cast
  ring

/-- **The rank of the multiplier lane window**:
`h⁰(𝒪(s·F − D − P)) = s·δ − deg D − δ + χ(𝒪_Y)` for `deg D ≤ 2g`, `deg P = δ` — the
codimension count behind F3's `A_P`-surjectivity (`dim A_P = δ`). -/
theorem rank_mult_lane (g : ℕ) (D : Y.CurveDivisor)
    (hD : CurveDivisor.deg K D ≤ 2 * (g : ℤ))
    (P : Y.CurveDivisor) (hP : CurveDivisor.deg K P = windowδ π) :
    (Sheaf.h0 (Y.divisorSheaf K
        (windowS_choice π hπ g • fiberWeilDivisor π - D - P)) : ℤ)
      = (windowS_choice π hπ g : ℤ) * windowδ π - CurveDivisor.deg K D - windowδ π
        + Sheaf.chi (Y.moduleKSheaf K) := by
  rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
      (window_mult_lane π hπ g D hD P hP),
    deg_sub, deg_sub, deg_nsmul, deg_fiberWeilDivisor_windowδ, hP]

end Ledger

end AlgebraicGeometry
