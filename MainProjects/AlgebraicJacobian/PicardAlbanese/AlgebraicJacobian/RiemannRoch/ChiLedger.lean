/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.ChiFiniteness
import AlgebraicJacobian.RiemannRoch.MulEquiv

/-!
# The χ-ledger: `chi_step`, `chi_divisorSheaf`, and Riemann–Roch-lite

The Euler-characteristic ledger for divisor sheaves on the curve bundle `X` (integral,
smooth of relative dimension one and quasi-compact over a field `K`, with finite `H⁰` and
`H¹` of the structure sheaf — the two instance hypotheses through which properness enters):

* `AlgebraicGeometry.chi_skyModule`: `χ(sky_x M) = dim_K M` — the skyscraper contribution.
* `AlgebraicGeometry.chi_step` (★ ledger keystone): the one-point dévissage step
  `χ(𝒪(D)) = χ(𝒪(D − x)) + [κ(x) : K]`, from the additivity of `χ` along the dévissage
  short exact sequence `0 → 𝒪(D − x) → 𝒪(D) → sky_x J → 0` and `dim_K J = residueDeg x`.
* `AlgebraicGeometry.chi_divisorSheaf` (★ ledger keystone): the closed ledger
  `χ(𝒪(D)) = χ(𝒪_X) + deg D`, by dévissage induction from `𝒪(0) ≅ 𝒪_X`.
* `AlgebraicGeometry.deg_divOf`: principal divisors have degree zero — transport `χ`
  along the multiplication isomorphism `𝒪(0) ≅ 𝒪(0 − div g)` and cancel in the ledger.
* `AlgebraicGeometry.riemann_inequality` (G9): `deg D + χ(𝒪_X) ≤ h⁰(𝒪(D))`.
* `AlgebraicGeometry.h0_nsmul_point_unbounded` (G9): `h⁰(𝒪(n·x))` is unbounded in `n`,
  for any closed point `x` — no rational point is needed, only `residueDeg x ≥ 1`.

All statements are phrased against the one-point divisor `CurveDivisor.single hx 1`
(definitionally the dévissage twist: `devissageDivisor_eq_sub`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

/-! ## The skyscraper contribution -/

section Skyscraper

variable {K : Type u} [CommRing K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

/-- `h⁰` of a skyscraper sheaf is the dimension of its value module. -/
theorem h0_skyModule (x : X) (M : ModuleCat.{u} K) :
    Sheaf.h0 (skyModule x M) = Module.finrank K M :=
  (skyModuleGammaEquiv x M).finrank_eq

/-- **The Euler characteristic of a skyscraper** is the dimension of its value module:
`h¹` vanishes and `h⁰` is computed by `skyModuleGammaEquiv`. -/
theorem chi_skyModule [Nontrivial K] (x : X) (M : ModuleCat.{u} K) :
    Sheaf.chi (skyModule x M) = Module.finrank K M := by
  rw [Sheaf.chi_eq_h0 (skyModule_subsingleton_hModule_one x M), h0_skyModule]

end Skyscraper

/-! ## The ledger -/

section Ledger

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- **The dévissage step of the χ-ledger** (★): subtracting a closed point `x` from the
divisor drops the Euler characteristic by the residue degree `[κ(x) : K]`:
`χ(𝒪(D)) = χ(𝒪(D − x)) + residueDeg x`. The divisor `D − CurveDivisor.single hx 1` is
definitionally the dévissage twist `devissageDivisor hx D` of the landed short exact
sequence (`devissageDivisor_eq_sub`). -/
theorem chi_step {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor) :
    Sheaf.chi (X.divisorSheaf K D) =
      Sheaf.chi (X.divisorSheaf K (D - CurveDivisor.single hx 1)) + X.residueDeg K x := by
  have hS := devissageSES_shortExact K hx D
  -- the five finiteness inputs and the `H¹(sky) = 0` input, in the `devissageSES` spelling
  haveI h₁0 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₁ 0) :=
    moduleFinite_hModule_divisorSheaf_zero K (devissageDivisor hx D)
  haveI h₁1 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₁ 1) :=
    moduleFinite_hModule_divisorSheaf_one K (devissageDivisor hx D)
  haveI h₂0 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₂ 0) :=
    moduleFinite_hModule_divisorSheaf_zero K D
  haveI h₂1 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₂ 1) :=
    moduleFinite_hModule_divisorSheaf_one K D
  haveI h₃0 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₃ 0) :=
    haveI := moduleFinite_jumpModule K hx D
    moduleFinite_hModule_skyModule_zero x (jumpModule K hx D)
  haveI h₃1 : Subsingleton (Sheaf.HModule (devissageSES K hx D).X₃ 1) :=
    skyModule_subsingleton_hModule_one x (jumpModule K hx D)
  have hadd := Sheaf.chi_eq_add_of_shortExact hS
  -- identify the three χ's with their divisor-sheaf/skyscraper spellings (definitional)
  have hX₂ : Sheaf.chi (devissageSES K hx D).X₂ = Sheaf.chi (X.divisorSheaf K D) := rfl
  have hX₁ : Sheaf.chi (devissageSES K hx D).X₁ =
      Sheaf.chi (X.divisorSheaf K (D - CurveDivisor.single hx 1)) := rfl
  have hX₃ : Sheaf.chi (devissageSES K hx D).X₃ = (X.residueDeg K x : ℤ) := by
    have h := chi_skyModule x (jumpModule K hx D)
    rw [finrank_jumpModule K hx D] at h
    exact h
  rw [hX₂, hX₁, hX₃] at hadd
  exact hadd

/-- **The χ-ledger, closed** (★): for every Weil divisor `D` on the curve bundle,
`χ(𝒪(D)) = χ(𝒪_X) + deg D`. Base case `𝒪(0) ≅ 𝒪_X`, step `chi_step`, glue
`CurveDivisor.induction_devissage`. -/
theorem chi_divisorSheaf (D : X.CurveDivisor) :
    Sheaf.chi (X.divisorSheaf K D) =
      Sheaf.chi (X.moduleKSheaf K) + CurveDivisor.deg K D := by
  refine Scheme.CurveDivisor.induction_devissage
    (P := fun D => Sheaf.chi (X.divisorSheaf K D) =
      Sheaf.chi (X.moduleKSheaf K) + CurveDivisor.deg K D)
    ?_ (fun {x} hx D => ?_) D
  · rw [Sheaf.chi_congr (divisorSheafZeroIso K), CurveDivisor.deg_zero, add_zero]
  · rw [devissageDivisor_eq_sub hx D]
    have hstep := chi_step K hx D
    have hdeg := deg_devissageDivisor K hx D
    rw [devissageDivisor_eq_sub hx D] at hdeg
    constructor <;> intro h <;> omega

/-- **Principal divisors have degree zero**: `deg (div g) = 0` for a unit `g` of the
function field. Multiplication by `g` identifies `𝒪(0)` with `𝒪(0 − div g)`
(`mulEquivDivisorSheaf`), so the two sides of the χ-ledger force the degrees to agree. -/
theorem deg_divOf (g : X.functionFieldˣ) :
    CurveDivisor.deg K (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) = 0 := by
  have hcongr := Sheaf.chi_congr (mulEquivDivisorSheaf K g (0 : X.CurveDivisor))
  rw [chi_divisorSheaf K (0 : X.CurveDivisor),
    chi_divisorSheaf K ((0 : X.CurveDivisor) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g),
    CurveDivisor.deg_zero, zero_sub, CurveDivisor.deg_neg] at hcongr
  omega

/-- **The Riemann inequality** (G9, general conditional form): for every Weil divisor `D`,
`deg D + χ(𝒪_X) ≤ h⁰(𝒪(D))` — from the χ-ledger and `h¹ ≥ 0`. The curve-level
`deg D + 1 − genus` form is derived in `ChiCurve`. -/
theorem riemann_inequality (D : X.CurveDivisor) :
    CurveDivisor.deg K D + Sheaf.chi (X.moduleKSheaf K) ≤
      (Sheaf.h0 (X.divisorSheaf K D) : ℤ) := by
  have h := chi_divisorSheaf K D
  have hchi : Sheaf.chi (X.divisorSheaf K D) ≤ (Sheaf.h0 (X.divisorSheaf K D) : ℤ) := by
    rw [Sheaf.chi]
    omega
  omega

/-- **Unbounded growth of `h⁰` along multiples of a point** (G9): for every closed point
`x` and every bound `N` there is `n` with `N ≤ h⁰(𝒪(n · x))`. No rational point is
needed: `residueDeg x ≥ 1` suffices. -/
theorem h0_nsmul_point_unbounded {x : X} (hx : x ≠ genericPoint X) (N : ℕ) :
    ∃ n : ℕ, N ≤ Sheaf.h0 (X.divisorSheaf K (n • CurveDivisor.single hx 1)) := by
  have key : ∀ n : ℕ, (n : ℤ) - Sheaf.h1 (X.moduleKSheaf K) ≤
      (Sheaf.h0 (X.divisorSheaf K (n • CurveDivisor.single hx 1)) : ℤ) := by
    intro n
    have hchi := chi_divisorSheaf K (n • CurveDivisor.single hx 1)
    rw [Scheme.CurveDivisor.nsmul_single_one hx n,
      Scheme.CurveDivisor.deg_single' K hx (n : ℤ)] at hchi
    have hchile : Sheaf.chi (X.divisorSheaf K (n • CurveDivisor.single hx 1)) ≤
        (Sheaf.h0 (X.divisorSheaf K (n • CurveDivisor.single hx 1)) : ℤ) := by
      rw [Sheaf.chi]
      omega
    have hres : (1 : ℤ) ≤ (X.residueDeg K x : ℤ) := by
      exact_mod_cast Scheme.residueDeg_pos hx
    have hmul : (n : ℤ) * 1 ≤ (n : ℤ) * (X.residueDeg K x : ℤ) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    have hchiO : Sheaf.chi (X.moduleKSheaf K) =
        (Sheaf.h0 (X.moduleKSheaf K) : ℤ) - Sheaf.h1 (X.moduleKSheaf K) := rfl
    -- `hchi` rewrote the divisor to `single hx n`; transport back is definitional
    have hchi' : Sheaf.chi (X.divisorSheaf K (n • CurveDivisor.single hx 1)) =
        Sheaf.chi (X.moduleKSheaf K) + (n : ℤ) * (X.residueDeg K x : ℤ) := by
      rw [Scheme.CurveDivisor.nsmul_single_one hx n]
      exact hchi
    omega
  refine ⟨N + Sheaf.h1 (X.moduleKSheaf K), ?_⟩
  have h := key (N + Sheaf.h1 (X.moduleKSheaf K))
  omega

end Ledger

end AlgebraicGeometry
