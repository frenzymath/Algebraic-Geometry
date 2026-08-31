/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.PFibPack
import AlgebraicJacobian.RiemannRoch.WindowFieldTransport
import AlgebraicJacobian.Picard.DivisorFamilyFieldDictionary

/-!
# G-4 — the fibre P-fib-N firing at the transported windows (worksheet §1.5, I-0233/I-0234)

The fibre layer of the universal seed (`Picard/DivSchemeSeedUniv.lean`): at any field
extension `K/k` (used at `K = κ(q)` for primes `q` of the pair chart rings), the P-fib-N
pack keystone `existsUnique_effective_divisor_of_carve_pack`
(`RiemannRoch/PFibPack.lean`) is fired with the transported windows `N := windowN`
(the `M·F`-transport, `RiemannRoch/WindowFieldTransport.lean`) and `S := windowS`
(the `s·F`-transport, defined here) — every pack slot discharged from the landed
`N`-pack and the DD-0 ledger.

**The I-0234 arithmetic seam, resolved.**  The pack's vanishing threshold `hvan` at `K`
is produced by peeling (`subsingleton_hModule_one_of_witness`) from a transported
`a`-exponent witness window; the minimal such exponent is

* `windowA_choice` — the least `a` with `b ≤ a·δ` (`windowA_spec`), so that
  `a·δ < b + δ` whenever `a ≠ 0` (`windowA_mul_lt`), giving the threshold
  `β = a·δ + g`;
* `windowA_add_three_mul_genus_le_S_mul` — **the tower budget** `a·δ + 3g ≤ s·δ`, from
  the strengthened ledger inequality `windowS_spec_three` (`b + 3g ≤ (s−1)·δ`, the
  I-0234 `2g → 3g` strengthening);
* `windowA_add_three_mul_genus_add_S_le_M_mul` — **the descent budget**
  `a·δ + 3g + s·δ ≤ M·δ`, absorbed by `windowM_spec`'s `(g+2)(s+1)·δ` slack.

Both budgets are stated under `0 < windowBound` — in the degenerate branch
`windowBound ≤ 0` the genus is zero (`genus_eq_zero_of_windowBound_nonpos`) and the
keystone is proved directly (`D = 0` is forced by `eq_zero_of_deg_le_zero`), which is
what closes the corner where the ledger's `s`-minimality is not publicly available.

* `AlgebraicGeometry.windowS` — the transported multiplier window `S` on the fibre
  curve, with `deg_windowS` (`= s·δ`), `subsingleton_h1_windowS`, and the size
  transport `h0_windowS` (`h⁰_K(𝒪(S)) = h⁰_k(𝒪(s·F))`, the `Φ_s`-surjectivity count);
* `AlgebraicGeometry.subsingleton_h1_of_windowA_le_deg` — **`hvan` at `K`**: every
  divisor of degree `≥ a·δ + g` has vanishing `H¹` (witness peeling at the transported
  `a`-window);
* `AlgebraicGeometry.existsUnique_effective_divisor_of_carve_windowN` — **the
  keystone**: subspaces `K_M ⊆ H⁰(𝒪(N))`, `K' ⊆ H⁰(𝒪(N + S))` of corank exactly `g`
  satisfying the elementwise carve determine a unique effective divisor `D` of degree
  `g` with `K_M = H⁰(𝒪(N − D))` and `K' = H⁰(𝒪(N + S − D))` — P-fib-N at the
  transported windows, every pack hypothesis discharged.

The consumer (the seed construction) feeds `K_M`/`K'` as the Φ-images of the universal
fibre kernel pair (`divUniversal_carve_residueField` + the G-3 dictionary `divFamPhi`)
— that bridge is the remaining G-4 layer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule
attribute [local instance 10000] AlgebraicGeometry.relCurve.instOver

namespace AlgebraicGeometry

open Scheme

/-! ## The minimal witness exponent `a` and the I-0234 budgets (ledger arithmetic) -/

section WindowA

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
  (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
  (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))

private theorem windowA_exists : ∃ a : ℕ, windowBound π hπ ≤ (a : ℤ) * windowδ π := by
  refine ⟨(windowBound π hπ).toNat, ?_⟩
  have hδ : 1 ≤ windowδ π := one_le_windowδ π
  have h1 : (((windowBound π hπ).toNat : ℤ)) ≤ ((windowBound π hπ).toNat : ℤ) * windowδ π :=
    le_mul_of_one_le_right (Int.natCast_nonneg _) hδ
  have h2 : windowBound π hπ ≤ ((windowBound π hπ).toNat : ℤ) :=
    Int.self_le_toNat _
  linarith

/-- **The minimal witness exponent `a`** — the least `a` with `b ≤ a·δ` (the smallest
ledger window whose transported avatar carries an `H¹`-vanishing witness at every field
extension).  The peeled threshold at a field is `β = a·δ + g`. -/
noncomputable def windowA_choice : ℕ := Nat.find (windowA_exists π hπ)

/-- The defining inequality of `a`: `b ≤ a·δ`. -/
theorem windowA_spec : windowBound π hπ ≤ (windowA_choice π hπ : ℤ) * windowδ π :=
  Nat.find_spec (windowA_exists π hπ)

/-- **Minimality of `a`**: whenever `a ≠ 0`, `a·δ < b + δ` (one exponent down already
fails the bound). -/
theorem windowA_mul_lt (ha : windowA_choice π hπ ≠ 0) :
    (windowA_choice π hπ : ℤ) * windowδ π < windowBound π hπ + windowδ π := by
  have h1 : windowA_choice π hπ - 1 < windowA_choice π hπ :=
    Nat.sub_lt (Nat.pos_of_ne_zero ha) one_pos
  have hmin : ¬ (windowBound π hπ
      ≤ ((windowA_choice π hπ - 1 : ℕ) : ℤ) * windowδ π) :=
    Nat.find_min (windowA_exists π hπ) h1
  have hcast : ((windowA_choice π hπ - 1 : ℕ) : ℤ) = (windowA_choice π hπ : ℤ) - 1 := by
    have := Nat.one_le_iff_ne_zero.mpr ha
    omega
  rw [hcast] at hmin
  push Not at hmin
  have hexp : ((windowA_choice π hπ : ℤ) - 1) * windowδ π
      = (windowA_choice π hπ : ℤ) * windowδ π - windowδ π := by ring
  linarith

/-- The exponent `a` is nonzero whenever the ledger bound is positive. -/
theorem windowA_ne_zero (hb : 0 < windowBound π hπ) : windowA_choice π hπ ≠ 0 := by
  intro h0
  have hspec := windowA_spec π hπ
  rw [h0] at hspec
  simp only [Nat.cast_zero, zero_mul] at hspec
  omega

/-- **The `H¹` window at the exponent `a`**: `H¹(𝒪(a·F)) = 0` — `windowBound_spec` at
degree `a·δ ≥ b`. -/
theorem window_embedding_windowA :
    Subsingleton (Sheaf.HModule
      (Y.divisorSheaf K (windowA_choice π hπ • fiberWeilDivisor π)) 1) := by
  refine windowBound_spec π hπ _ ?_
  rw [Scheme.CurveDivisor.deg_nsmul' K, deg_fiberWeilDivisor_windowδ]
  exact windowA_spec π hπ

/-- **The tower budget** (the I-0234 seam, resolved by `windowS_spec_three`):
`a·δ + 3g ≤ s·δ` whenever the ledger bound is positive. -/
theorem windowA_add_three_mul_genus_le_S_mul (hb : 0 < windowBound π hπ) (g : ℕ) :
    (windowA_choice π hπ : ℤ) * windowδ π + 3 * (g : ℤ)
      ≤ (windowS_choice π hπ g : ℤ) * windowδ π := by
  have hlt := windowA_mul_lt π hπ (windowA_ne_zero π hπ hb)
  have h3 := windowS_spec_three π hπ g
  have hexp : ((windowS_choice π hπ g : ℤ) - 1) * windowδ π
      = (windowS_choice π hπ g : ℤ) * windowδ π - windowδ π := by ring
  linarith

/-- **The descent budget**: `a·δ + 3g + s·δ ≤ M·δ` whenever the ledger bound is
positive — `windowM_spec`'s `(g+2)(s+1)·δ` slack absorbs the witness threshold. -/
theorem windowA_add_three_mul_genus_add_S_le_M_mul (hb : 0 < windowBound π hπ) (g : ℕ) :
    (windowA_choice π hπ : ℤ) * windowδ π + 3 * (g : ℤ)
        + (windowS_choice π hπ g : ℤ) * windowδ π
      ≤ (windowM_choice π hπ g : ℤ) * windowδ π := by
  have hlt := windowA_mul_lt π hπ (windowA_ne_zero π hπ hb)
  have hM := windowM_spec π hπ g
  have hδ := one_le_windowδ π
  have hs : (0 : ℤ) ≤ (windowS_choice π hπ g : ℤ) := Int.natCast_nonneg _
  have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
  have h1 : (1 : ℤ) ≤ ((windowS_choice π hπ g : ℤ) + 1) * windowδ π := by nlinarith
  have h2 : ((g : ℤ) + 1) * 1
      ≤ ((g : ℤ) + 1) * (((windowS_choice π hπ g : ℤ) + 1) * windowδ π) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith [hlt, hM, h2, hδ, hs, hg]

end WindowA

/-! ## The transported multiplier window `S` and the `hvan` threshold at `K` -/

section Transport

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable (K : Type u) [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
variable [IsIntegral C.left]

noncomputable local instance instOverCleftSUF : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]
variable [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]

set_option linter.unusedSectionVars false in
/-- **The `H¹` input at the witness exponent `a`**, transported onto the relative theta
pair — the `a`-companion of `relThetaPairH1_windowM`/`relThetaPairH1_windowS`. -/
theorem relThetaPairH1_windowA :
    Subsingleton
      (relTwistPair C k π (relThetaCocycle C k π (windowA_choice π hπ))).H1 :=
  subsingleton_relThetaPairH1 C π _
    ((subsingleton_hModule_thetaTwistSheaf_one_iff k π _).mpr
      (window_embedding_windowA π hπ))

/-- **The transported multiplier window `S`** on the fibre curve: the transported
window divisor at the `k`-ledger multiplier exponent `s = windowS_choice π hπ g` — the
`S` of the P-fib-N pack, the companion of `windowN`. -/
noncomputable def windowS (g : ℕ) : (relCurve C K).CurveDivisor :=
  windowTransportDivisor C K π (windowS_choice π hπ g)

/-- The degree of `S` is the `k`-ledger multiplier degree `s·δ`. -/
theorem deg_windowS (g : ℕ) :
    CurveDivisor.deg K (windowS C K hπ g)
      = (windowS_choice π hπ g : ℤ) * windowδ π :=
  deg_windowTransportDivisor C K π _

set_option linter.unusedSectionVars false in
/-- **`hSwin`**: `H¹(𝒪(S)) = 0` — the transported multiplier window
(`window_embedding_mult` at `k`, pushed across the collapse and the base change). -/
theorem subsingleton_h1_windowS (g : ℕ) :
    Subsingleton (Sheaf.HModule
      ((relCurve C K).divisorSheaf K (windowS C K hπ g)) 1) :=
  subsingleton_h1_windowTransportDivisor C K π _ (relThetaPairH1_windowS C hπ g)

/-- **The multiplier window size transport** `h⁰_K(𝒪(S)) = h⁰_k(𝒪(s·F))` — the
`Φ_s`-surjectivity dimension count of the seed's carve bridge (mirror of
`h0_windowN`). -/
theorem h0_windowS (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ)) :
    Sheaf.h0 ((relCurve C K).divisorSheaf K (windowS C K hπ g))
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowS_choice π hπ g • fiberWeilDivisor π)) := by
  have hK : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowS C K hπ g)) : ℤ)
      = CurveDivisor.deg K (windowS C K hπ g)
        + Sheaf.chi ((relCurve C K).moduleKSheaf K) :=
    h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (subsingleton_h1_windowS C K hπ g)
  have hk : (Sheaf.h0 (C.left.divisorSheaf k
        (windowS_choice π hπ g • fiberWeilDivisor π)) : ℤ)
      = (windowS_choice π hπ g : ℤ) * windowδ π + 1 - (g : ℤ) :=
    rank_embedding_mult_of_genus π hπ g hχ
  have hcast : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowS C K hπ g)) : ℤ)
      = (Sheaf.h0 (C.left.divisorSheaf k
          (windowS_choice π hπ g • fiberWeilDivisor π)) : ℤ) := by
    rw [hK, deg_windowS, hχK, hk]
    ring
  exact_mod_cast hcast

/-- **The decoupled multiplier-window size transport**: the `S`-window is keyed by
the divisor degree `g`, while its Euler-characteristic normalization is keyed by the
independent curve parameter `gamma`. -/
theorem h0_windowS_at (g : ℕ) {gamma : ℕ}
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (gamma : ℤ)) :
    Sheaf.h0 ((relCurve C K).divisorSheaf K (windowS C K hπ g))
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowS_choice π hπ g • fiberWeilDivisor π)) := by
  have hK : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowS C K hπ g)) : ℤ)
      = CurveDivisor.deg K (windowS C K hπ g)
        + Sheaf.chi ((relCurve C K).moduleKSheaf K) :=
    h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (subsingleton_h1_windowS C K hπ g)
  have hk := rank_embedding_mult π hπ g
  rw [hχ] at hk
  have hcast : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowS C K hπ g)) : ℤ)
      = (Sheaf.h0 (C.left.divisorSheaf k
          (windowS_choice π hπ g • fiberWeilDivisor π)) : ℤ) := by
    rw [hK, deg_windowS, hχK, hk]
  exact_mod_cast hcast

set_option linter.unusedSectionVars false in
/-- The transported witness at the exponent `a`: `H¹` of the transported `a`-window
vanishes. -/
theorem subsingleton_h1_windowA_transport :
    Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K
      (windowTransportDivisor C K π (windowA_choice π hπ))) 1) :=
  subsingleton_h1_windowTransportDivisor C K π _ (relThetaPairH1_windowA C hπ)

/-- **`hvan` at `K`** (the P-fib-N vanishing threshold, worksheet §1.5): every divisor
of degree `≥ a·δ + g` on the fibre curve has vanishing `H¹` — witness peeling
(`subsingleton_hModule_one_of_witness`) at the transported `a`-window. -/
theorem subsingleton_h1_of_windowA_le_deg (g : ℕ)
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ))
    (W : (relCurve C K).CurveDivisor)
    (hW : (windowA_choice π hπ : ℤ) * windowδ π + (g : ℤ) ≤ CurveDivisor.deg K W) :
    Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K W) 1) := by
  refine subsingleton_hModule_one_of_witness K
    (windowTransportDivisor C K π (windowA_choice π hπ)) W
    (subsingleton_h1_windowA_transport C K hπ) ?_
  rw [deg_windowTransportDivisor, hχK]
  linarith

end Transport

/-! ## The keystone: P-fib-N fired at the transported windows -/

section Keystone

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable (K : Type u) [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
variable [IsIntegral C.left]

noncomputable local instance instOverCleftSUFK : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]
variable [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]

/-- **The fibre P-fib-N keystone at the transported windows** (worksheet §1.5, the
G-4 fibre heart): on the fibre curve over any field extension `K/k`, subspaces
`K_M ⊆ H⁰(𝒪(N))` and `K' ⊆ H⁰(𝒪(N + S))` of corank exactly `g` at the transported
windows `N = windowN` (the `M·F`-transport) and `S = windowS` (the `s·F`-transport),
satisfying the elementwise carve `(♦)`, determine a **unique** effective divisor `D`
of degree `g` with `K_M = H⁰(𝒪(N − D))` and `K' = H⁰(𝒪(N + S − D))`.

Every pack slot of `existsUnique_effective_divisor_of_carve_pack` is discharged:
`hvan` by witness peeling at the minimal exponent `a` (threshold `β = a·δ + g`),
`hNdeg` by `two_mul_genus_le_deg_windowN`, `hSdeg` by `two_mul_genus_le_S_mul_windowδ`,
the budgets by `windowA_add_three_mul_genus_le_S_mul` (I-0234's `windowS_spec_three`)
and `windowA_add_three_mul_genus_add_S_le_M_mul`.  In the degenerate ledger branch
`windowBound ≤ 0` the genus is zero and `D = 0` is forced directly. -/
theorem existsUnique_effective_divisor_of_carve_windowN (g : ℕ)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hOK : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ))
    (KM : Submodule K (relCurve C K).functionField)
    (hKM : KM ≤ divisorSections K (windowN C K hπ g) ⊤)
    (hKMrank : Module.finrank K ↥KM + g
      = Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g)))
    (K' : Submodule K (relCurve C K).functionField)
    (hK' : K' ≤ divisorSections K (windowN C K hπ g + windowS C K hπ g) ⊤)
    (hK'rank : Module.finrank K ↥K' + g
      = Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowN C K hπ g + windowS C K hπ g)))
    (hcarve : ∀ h ∈ divisorSections K (windowS C K hπ g) ⊤, ∀ f ∈ KM, h * f ∈ K') :
    ∃! D : (relCurve C K).CurveDivisor, 0 ≤ D ∧ CurveDivisor.deg K D = (g : ℤ) ∧
      KM = divisorSections K (windowN C K hπ g - D) ⊤ ∧
      K' = divisorSections K (windowN C K hπ g + windowS C K hπ g - D) ⊤ := by
  by_cases hb : windowBound π hπ ≤ 0
  · -- degenerate ledger branch: `g = 0`, the divisor is forced to be `0`
    have hg0 : g = 0 := genus_eq_zero_of_windowBound_nonpos π hπ g hb hO hχ
    subst hg0
    have hKMeq : KM = divisorSections K (windowN C K hπ 0) ⊤ := by
      refine Submodule.eq_of_le_of_finrank_le hKM ?_
      rw [finrank_divisorSections_top K _]
      omega
    have hK'eq : K' = divisorSections K (windowN C K hπ 0 + windowS C K hπ 0) ⊤ := by
      refine Submodule.eq_of_le_of_finrank_le hK' ?_
      rw [finrank_divisorSections_top K _]
      omega
    refine ⟨0, ⟨le_rfl, by rw [CurveDivisor.deg_zero, Nat.cast_zero], ?_, ?_⟩, ?_⟩
    · rw [sub_zero]; exact hKMeq
    · rw [sub_zero]; exact hK'eq
    · rintro D' ⟨hD'0, hD'deg, -, -⟩
      refine Scheme.CurveDivisor.eq_zero_of_deg_le_zero K hD'0 ?_
      rw [hD'deg, Nat.cast_zero]
  · -- main branch: `0 < b`, the pack fires at threshold `β = a·δ + g`
    push Not at hb
    refine existsUnique_effective_divisor_of_carve_pack g hOK hχK
      (windowN C K hπ g) (windowS C K hπ g)
      ((windowA_choice π hπ : ℤ) * windowδ π + (g : ℤ))
      (fun W hW => subsingleton_h1_of_windowA_le_deg C K hπ g hχK W hW)
      (two_mul_genus_le_deg_windowN C K hπ g hO hχ)
      (by rw [deg_windowS]
          exact two_mul_genus_le_S_mul_windowδ π hπ g hO hχ)
      (by rw [deg_windowS]
          have := windowA_add_three_mul_genus_le_S_mul π hπ hb g
          linarith)
      (by rw [deg_windowS, deg_windowN]
          have := windowA_add_three_mul_genus_add_S_le_M_mul π hπ hb g
          linarith)
      KM hKM hKMrank K' hK' hK'rank hcarve

/-- **The decoupled fibre P-fib keystone.**  The transported windows and Grassmannian
coranks are keyed by the divisor-family degree `g`; the structure-sheaf Euler
characteristic is normalized by an independent `gamma ≤ g`. -/
theorem existsUnique_effective_divisor_of_carve_windowN_at (g : ℕ) {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hOK : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (gamma : ℤ))
    (KM : Submodule K (relCurve C K).functionField)
    (hKM : KM ≤ divisorSections K (windowN C K hπ g) ⊤)
    (hKMrank : Module.finrank K ↥KM + g
      = Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g)))
    (K' : Submodule K (relCurve C K).functionField)
    (hK' : K' ≤ divisorSections K (windowN C K hπ g + windowS C K hπ g) ⊤)
    (hK'rank : Module.finrank K ↥K' + g
      = Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowN C K hπ g + windowS C K hπ g)))
    (hcarve : ∀ h ∈ divisorSections K (windowS C K hπ g) ⊤, ∀ f ∈ KM, h * f ∈ K') :
    ∃! D : (relCurve C K).CurveDivisor, 0 ≤ D ∧ CurveDivisor.deg K D = (g : ℤ) ∧
      KM = divisorSections K (windowN C K hπ g - D) ⊤ ∧
      K' = divisorSections K (windowN C K hπ g + windowS C K hπ g - D) ⊤ := by
  have hb := windowBound_pos π hπ
  have hgamma' : (gamma : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgamma
  refine existsUnique_effective_divisor_of_carve_pack (gamma := gamma) g hOK hχK
    (windowN C K hπ g) (windowS C K hπ g)
    ((windowA_choice π hπ : ℤ) * windowδ π + (gamma : ℤ))
    (fun W hW => subsingleton_h1_of_windowA_le_deg C K hπ gamma hχK W hW)
    (two_mul_degree_le_deg_windowN C K hπ g)
    (by rw [deg_windowS]
        exact two_mul_degree_le_S_mul_windowδ π hπ g)
    (by
      rw [deg_windowS]
      have hbudget := windowA_add_three_mul_genus_le_S_mul π hπ hb g
      linarith)
    (by
      rw [deg_windowS, deg_windowN]
      have hbudget := windowA_add_three_mul_genus_add_S_le_M_mul π hπ hb g
      linarith)
    KM hKM hKMrank K' hK' hK'rank hcarve (hgamma := hgamma)

end Keystone
/-! ## The Φ-side interface (G-3 dictionary addenda for the seed bridge) -/

section PhiInterface

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftSUFP : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable (a : ℕ)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **The full-window image dictionary**: `Φ` carries the whole free window `K ⊗[k] H_a`
exactly onto `H⁰(𝒪(N(a)))` at the transported window divisor — the `d`-free companion
of `map_divFamPhi_divisorWindow`, giving both the pole-bound side (`hKM`/`hK'`) and the
multiplier surjectivity (`hcarve`'s `h`-side) of the seed's P-fib-N inputs. -/
theorem map_divFamPhi_top
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    Submodule.map (divFamPhi C K π a hH1) ⊤
      = Scheme.divisorSections K (windowTransportDivisor C K π a) ⊤ := by
  have h1 : Submodule.map (relThetaWindowEquiv C K π a hH1).toLinearMap
      (⊤ : Submodule K (K ⊗[k]
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))) = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact (relThetaWindowEquiv C K π a hH1).surjective
  have h2 : Submodule.map (thetaFieldRead C K π a) ⊤
      = Scheme.divisorSections K (thetaFieldDivisor C K π a) ⊤ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨s, -, rfl⟩
      exact thetaFieldRead_mem C K π a s
    · intro f hf
      obtain ⟨s, hs⟩ := exists_thetaFieldRead_eq C K π a hf
      exact ⟨s, trivial, hs⟩
  have hmk : Units.mk0
      ((thetaFieldShiftUnit C K π a : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField)
      (Units.ne_zero (thetaFieldShiftUnit C K π a)) = thetaFieldShiftUnit C K π a :=
    Units.ext rfl
  simp only [divFamPhi]
  rw [Submodule.map_comp, Submodule.map_comp, h1, h2,
    map_mulLinear_divisorSections_top K
      (Units.ne_zero (thetaFieldShiftUnit C K π a)) _]
  congr 1
  rw [hmk, ← divOf_thetaFieldShiftUnit C K π a]
  abel

/-- Every `Φ`-value satisfies the transported pole bound — the `hKM`/`hK'` inclusion
side of the seed's P-fib-N inputs. -/
theorem divFamPhi_apply_mem
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (x : K ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :
    divFamPhi C K π a hH1 x
      ∈ Scheme.divisorSections K (windowTransportDivisor C K π a) ⊤ :=
  map_divFamPhi_top C K π a hH1 ▸ Submodule.mem_map_of_mem trivial

/-- **`Φ`-surjectivity onto the transported window sections** — the multiplier-side
realization of the seed's `hcarve` (every `h ∈ H⁰(𝒪(S))` is a `Φ`-value). -/
theorem exists_divFamPhi_eq
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    {f : (relCurve C K).functionField}
    (hf : f ∈ Scheme.divisorSections K (windowTransportDivisor C K π a) ⊤) :
    ∃ x, divFamPhi C K π a hH1 x = f := by
  rw [← map_divFamPhi_top C K π a hH1] at hf
  obtain ⟨x, -, hx⟩ := hf
  exact ⟨x, hx⟩

omit [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **`Φ` preserves dimensions**: the image of a submodule under the injective
dictionary has the same `K`-dimension — the `hKMrank`/`hK'rank` transport of the seed's
P-fib-N inputs (composed with the fibre corank law
`finrank_ker_baseChangeMkQ_add_of_field`). -/
theorem finrank_map_divFamPhi
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (N : Submodule K (K ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))) :
    Module.finrank K ↥(Submodule.map (divFamPhi C K π a hH1) N)
      = Module.finrank K ↥N :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (divFamPhi_injective C K π a hH1) N)).symm

end PhiInterface

end AlgebraicGeometry
