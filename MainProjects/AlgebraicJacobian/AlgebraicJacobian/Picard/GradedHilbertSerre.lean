/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Graded Hilbert–Serre rationality layer

This file houses the `IsRatHilb` toolkit and the `GradedModule` ambient
subquotient induction that establish the rationality of graded Hilbert series
(Stacks 00K1).

A function `f : ℕ → ℚ` satisfies `IsRatHilb f d` when it eventually agrees with
the coefficient sequence of a rational power series `p · (1 - X)⁻ᵈ` with
`p : ℚ[X]`. The class is closed under differences, shifts and — the substantial
step — antidifferentiation, which raises `d` by one. The graded input is fed in
through an induction on the number of polynomial variables: multiplication by a
degree-raising endomorphism `x` on a graded module `M` has homogeneous kernel and
cokernel, both again finite over one fewer variable, and the degreewise
rank–nullity identity turns the first difference of the Hilbert function of `M`
into the Hilbert function of that kernel/cokernel pair.

## Main results

* `IsRatHilb.antidiff` — the antidifference step: if the first difference of `H`
  is eventually the coefficient sequence of `q · (1 - X)⁻ᵉ`, then `H` is
  eventually the coefficient sequence of `p · (1 - X)^{-(e+1)}`.
* `GradedModule.subquotient_hilbertSeries_rational` — the ambient subquotient
  induction: for a subquotient datum of length `r`, the degreewise rank
  difference satisfies `IsRatHilb _ r`.
* `gradedModule_hilbertSeries_rational` — the keystone: for a graded
  `κ`-module finite over `MvPolynomial (Fin r) κ` with finite-dimensional
  components, the Hilbert function is eventually a coefficient sequence of
  `p · (1 - X)⁻ʳ`.

## References

* [Stacks, Tag 00K1](https://stacks.math.columbia.edu/tag/00K1)

Blueprint: `blueprint/src/chapters/Picard_GradedHilbertSerre.tex`.
-/

set_option autoImplicit false

/-! ## Project-local Mathlib supplement — graded Hilbert–Serre rationality -/

namespace AlgebraicGeometry

open PowerSeries Polynomial in
lemma coeff_invOneSubPow_one_mul (F : ℚ⟦X⟧) (n : ℕ) :
    ((PowerSeries.invOneSubPow ℚ 1).val * F).coeff n
      = ∑ k ∈ Finset.range (n + 1), F.coeff k := by
  have h1 : (PowerSeries.invOneSubPow ℚ 1).val = PowerSeries.mk (fun _ => (1 : ℚ)) := by
    have := PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose (S := ℚ) (d := 0)
    simpa using this
  rw [h1, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk, one_mul]
  rw [← Finset.sum_range_reflect (fun k => F.coeff k) (n + 1)]
  apply Finset.sum_congr rfl
  intro x _
  congr 1

open PowerSeries Polynomial in
/-- **Antidifference step for rational Hilbert series.** If the first difference
`H (n+1) - H n` is, for `n ≫ 0`, the `n`-th coefficient of the rational series
`q · (1-X)^{-e}`, then `H` itself is, for `n ≫ 0`, the `n`-th coefficient of
`p · (1-X)^{-(e+1)}` for an explicit polynomial `p`. This is the power-series
heart of the inductive step in graded Hilbert–Serre (Stacks 00K1). Project-local:
Mathlib supplies only the converse extraction `Polynomial.existsUnique_hilbertPoly`. -/
lemma rationalHilbert_antidiff
    (H δ : ℕ → ℚ) (q : Polynomial ℚ) (e N : ℕ)
    (hδ : ∀ n, N < n → δ n = ((q : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ e).val).coeff n)
    (hH : ∀ n, N < n → H (n + 1) - H n = δ (n + 1)) :
    ∃ (p : Polynomial ℚ), ∀ n, N < n →
      H n = ((p : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ (e + 1)).val).coeff n := by
  set F : ℚ⟦X⟧ := (q : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ e).val with hF
  -- Partial-sum identity: the order-`(e+1)` series accumulates the order-`e` coefficients.
  have hsum : ∀ m, ((q : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ (e + 1)).val).coeff m
      = ∑ k ∈ Finset.range (m + 1), F.coeff k := by
    intro m
    have hmul : (q : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ (e + 1)).val
        = (PowerSeries.invOneSubPow ℚ 1).val * F := by
      rw [hF, show (e + 1) = 1 + e from by omega, PowerSeries.invOneSubPow_add, Units.val_mul]
      ring
    rw [hmul, coeff_invOneSubPow_one_mul]
  -- Telescoping `H` from its first differences, expressed via `F`.
  have hstep : ∀ n, N < n → H (n + 1) - H n = F.coeff (n + 1) := by
    intro n hn
    rw [hH n hn, hδ (n + 1) (by omega)]
  have htel : ∀ j, H (N + 1 + j)
      = H (N + 1) + ∑ i ∈ Finset.range j, F.coeff (N + 2 + i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Finset.sum_range_succ, show N + 2 + j = N + 1 + (j + 1) from by omega]
        have hs := hstep (N + 1 + j) (by omega)
        rw [show (N + 1 + j) + 1 = N + 1 + (j + 1) from by omega] at hs
        linarith [hs, ih]
  -- Constant-absorption: a constant function is the order-`(e+1)` coefficient of `C·(1-X)^e`.
  have hCconst : ∀ (c : ℚ),
      c • (PowerSeries.invOneSubPow ℚ 1).val
        = ((Polynomial.C c * (1 - Polynomial.X) ^ e : Polynomial ℚ) : ℚ⟦X⟧)
            * (PowerSeries.invOneSubPow ℚ (e + 1)).val := by
    intro c
    have hkey : (1 - PowerSeries.X : ℚ⟦X⟧) ^ e * (PowerSeries.invOneSubPow ℚ (e + 1)).val
        = (PowerSeries.invOneSubPow ℚ 1).val := by
      rw [Nat.add_comm e 1]
      exact PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ 1 e
    rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_X, mul_assoc, hkey, PowerSeries.smul_eq_C_mul]
  have hcoeff1 : ∀ m, (PowerSeries.invOneSubPow ℚ 1).val.coeff m = 1 := by
    intro m
    have h1 : (PowerSeries.invOneSubPow ℚ 1).val = PowerSeries.mk (fun _ => (1 : ℚ)) := by
      have := PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose (S := ℚ) (d := 0)
      simpa using this
    rw [h1, PowerSeries.coeff_mk]
  -- Assemble the polynomial numerator.
  set B : ℚ := ∑ k ∈ Finset.range (N + 2), F.coeff k with hB
  set C0 : ℚ := H (N + 1) - B with hC0
  refine ⟨Polynomial.C C0 * (1 - Polynomial.X) ^ e + q, ?_⟩
  intro n hn
  -- Rewrite `H n` via the telescoping identity at `j = n - (N+1)`.
  obtain ⟨j, rfl⟩ : ∃ j, n = N + 1 + j := ⟨n - (N + 1), by omega⟩
  rw [htel j]
  -- The tail sum is an `Ico`-window of `F`.
  have htail : ∑ i ∈ Finset.range j, F.coeff (N + 2 + i)
      = ∑ k ∈ Finset.Ico (N + 2) (N + 2 + j), F.coeff k := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  rw [htail]
  -- Split `range (n+1) = range (N+2) ∪ Ico (N+2) (n+1)` in the partial-sum identity.
  have hsplit : ∑ k ∈ Finset.range (N + 1 + j + 1), F.coeff k
      = B + ∑ k ∈ Finset.Ico (N + 2) (N + 2 + j), F.coeff k := by
    rw [hB, Finset.range_eq_Ico, Finset.range_eq_Ico,
      show N + 1 + j + 1 = N + 2 + j from by omega,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (N + 2)) (by omega : N + 2 ≤ N + 2 + j)]
  -- Now compute the target coefficient and match.
  rw [show ((Polynomial.C C0 * (1 - Polynomial.X) ^ e + q : Polynomial ℚ) : ℚ⟦X⟧)
        = ((Polynomial.C C0 * (1 - Polynomial.X) ^ e : Polynomial ℚ) : ℚ⟦X⟧) + (q : ℚ⟦X⟧)
      from by push_cast; ring,
    add_mul, map_add, ← hCconst C0]
  rw [show (C0 • (PowerSeries.invOneSubPow ℚ 1).val).coeff (N + 1 + j)
        = C0 * (PowerSeries.invOneSubPow ℚ 1).val.coeff (N + 1 + j)
      from by rw [map_smul]; rfl, hcoeff1, mul_one,
    hsum (N + 1 + j), hsplit, hC0]
  ring

open PowerSeries Polynomial in
/-- Internal predicate for graded Hilbert–Serre: `f : ℕ → ℚ` is, for `n ≫ 0`, the
`n`-th coefficient of the rational power series `p · (1-X)^{-d}` for some numerator
polynomial `p`. The closure lemmas below (`bump`, `sub`, `shiftRight`, `antidiff`,
`ofEventuallyZero`) are the inductive toolkit for the rationality proof. -/
def IsRatHilb (f : ℕ → ℚ) (d : ℕ) : Prop :=
  ∃ (p : Polynomial ℚ) (N : ℕ), ∀ n, N < n →
    f n = ((p : ℚ⟦X⟧) * (PowerSeries.invOneSubPow ℚ d).val).coeff n

/-- An eventually-zero Hilbert function is rational of order `0` (numerator `0`). -/
lemma IsRatHilb.ofEventuallyZero {f : ℕ → ℚ} (N : ℕ) (hf : ∀ n, N < n → f n = 0) :
    IsRatHilb f 0 := by
  refine ⟨0, N, fun n hn => ?_⟩
  rw [hf n hn]
  simp

open PowerSeries Polynomial in
/-- The order of a rational Hilbert function may be raised by one (multiply the
numerator by `(1-X)`); this lets two series be brought to a common denominator. -/
lemma IsRatHilb.bump {f : ℕ → ℚ} {d : ℕ} (h : IsRatHilb f d) :
    IsRatHilb f (d + 1) := by
  obtain ⟨p, N, hp⟩ := h
  refine ⟨p * (1 - Polynomial.X), N, fun n hn => ?_⟩
  rw [hp n hn]
  congr 1
  have hkey : (1 - PowerSeries.X : ℚ⟦X⟧) ^ 1 * (PowerSeries.invOneSubPow ℚ (d + 1)).val
      = (PowerSeries.invOneSubPow ℚ d).val :=
    PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ d 1
  rw [pow_one] at hkey
  rw [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X,
    mul_assoc, hkey]

open PowerSeries Polynomial in
/-- Rational Hilbert functions of the same order are closed under pointwise difference. -/
lemma IsRatHilb.sub {f g : ℕ → ℚ} {d : ℕ} (hf : IsRatHilb f d) (hg : IsRatHilb g d) :
    IsRatHilb (fun n => f n - g n) d := by
  obtain ⟨p, Np, hp⟩ := hf
  obtain ⟨q, Nq, hq⟩ := hg
  refine ⟨p - q, max Np Nq, fun n hn => ?_⟩
  simp only
  rw [hp n (lt_of_le_of_lt (le_max_left _ _) hn), hq n (lt_of_le_of_lt (le_max_right _ _) hn),
    Polynomial.coe_sub, sub_mul, map_sub]

open PowerSeries Polynomial in
/-- Right-shift closure: if `f` is rational of order `d`, so is `n ↦ f (n-1)`
(multiply the numerator by `X`). -/
lemma IsRatHilb.shiftRight {f : ℕ → ℚ} {d : ℕ} (h : IsRatHilb f d) :
    IsRatHilb (fun n => f (n - 1)) d := by
  obtain ⟨p, N, hp⟩ := h
  refine ⟨Polynomial.X * p, N + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [hp m (by omega), Polynomial.coe_mul, Polynomial.coe_X, mul_assoc,
    PowerSeries.coeff_succ_X_mul]

/-- The antidifference step, packaged for the predicate: if `g` is rational of order
`e` and `H (n+1) - H n = g (n+1)` eventually, then `H` is rational of order `e+1`. -/
lemma IsRatHilb.antidiff {H g : ℕ → ℚ} {e N : ℕ} (hg : IsRatHilb g e)
    (hH : ∀ n, N < n → H (n + 1) - H n = g (n + 1)) : IsRatHilb H (e + 1) := by
  obtain ⟨q, Ng, hq⟩ := hg
  obtain ⟨p, hp⟩ := rationalHilbert_antidiff H g q e (max N Ng)
    (fun n hn => hq n (lt_of_le_of_lt (le_max_right _ _) hn))
    (fun n hn => hH n (lt_of_le_of_lt (le_max_left _ _) hn))
  exact ⟨p, max N Ng, hp⟩

/-- **Inductive-step engine for graded Hilbert–Serre (Stacks 00K1).** The entire
power-series side of the inductive step: if the Hilbert function `hM` of `M` has
first difference matching the alternating sum `hC (n+1) - hK n` of the Hilbert
functions of the cokernel `C = M/xM` and kernel `K = ker(x : M → M(1))` — the
content of the degreewise short exact sequence `0 → K_n → M_n → M_{n+1} → C_{n+1} → 0`
— and both `hC, hK` are rational of order `d`, then `hM` is rational of order `d+1`.
The only remaining (graded-algebra) obligation in the rationality proof is to produce
`hK, hC` with this difference identity and apply the induction hypothesis. -/
lemma IsRatHilb.ofDiffEq {hM hC hK : ℕ → ℚ} {d N : ℕ}
    (hC' : IsRatHilb hC d) (hK' : IsRatHilb hK d)
    (hdiff : ∀ n, N < n → hM (n + 1) - hM n = hC (n + 1) - hK n) :
    IsRatHilb hM (d + 1) := by
  have hg : IsRatHilb (fun n => hC n - hK (n - 1)) d := hC'.sub hK'.shiftRight
  refine IsRatHilb.antidiff (g := fun n => hC n - hK (n - 1)) (N := N) hg ?_
  intro n hn
  simp only [Nat.add_sub_cancel]
  exact hdiff n hn

/-! ## Project-local Mathlib supplement — graded-module API for Stacks 00K1

This namespace builds the graded-module side of the Stacks 00K1 inductive step
(graded Hilbert–Serre rationality). It wraps the existing Mathlib homogeneous-submodule
scaffold (`Submodule.IsHomogeneous`, `DirectSum.Decomposition`, `GradedRing`,
`QuotSMulTop`) with the induced gradings on the derived objects (homogeneous submodule,
quotient module, quotient ring) that Mathlib does not supply, together with the
degreewise rank–nullity difference identity. Blueprint: `subsec:gradedModuleApi`
(G1–G5, D5). -/

namespace GradedModule

section G1

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]
variable (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- **G1(a) — independence of the graded pieces of a homogeneous submodule.** The graded
pieces `ℳ i ⊓ p` of any submodule `p` are independent, since they refine the independent
grading family `ℳ` of the ambient module. Project-local: half of the induced internal
direct sum decomposition of a homogeneous submodule. -/
theorem homogeneousSubmodule_inf_iSupIndep (p : Submodule R M) :
    iSupIndep fun i => ℳ i ⊓ p :=
  ((DirectSum.Decomposition.isInternal ℳ).submodule_iSupIndep).mono fun _ => inf_le_left

/-- **G1(b) — a homogeneous submodule is the supremum of its graded pieces.** For an
internally graded module `M = ⨁ ℳ i` and a homogeneous submodule `p`
(`Submodule.IsHomogeneous`), `p = ⨆ i, (ℳ i ⊓ p)`. Combined with
`homogeneousSubmodule_inf_iSupIndep` this exhibits the induced internal direct sum grading
`p = ⨁ i, (ℳ i ⊓ p)` that Mathlib's `HomogeneousSubmodule` scaffold does not supply; it
gives the graded kernel `K = ker(x : M → M(1))` its grading
`K_n = ker(x : M_n → M_{n+1})`.

Stated in the ambient `M` (independence + supremum) rather than as
`DirectSum.IsInternal` on the subtype `↥p`: the latter triggers a runaway `isDefEq`
reduction of `DirectSum.coeLinearMap` over a subtype module. Project-local: the homogeneity
input is `Submodule.IsHomogeneous.mem_iff`. -/
theorem homogeneousSubmodule_iSup_inf_eq (p : Submodule R M) (hp : p.IsHomogeneous ℳ) :
    ⨆ i, (ℳ i ⊓ p) = p := by
  letI : ∀ (i : ι) (x : ℳ i), Decidable (x ≠ 0) := fun _ _ => Classical.dec _
  apply le_antisymm
  · exact iSup_le fun i => inf_le_right
  · intro x hx
    rw [← DirectSum.sum_support_decompose ℳ x]
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
    exact Submodule.mem_inf.mpr
      ⟨SetLike.coe_mem (DirectSum.decompose ℳ x i),
        (Submodule.IsHomogeneous.mem_iff ℳ hp).mp hx i⟩

end G1

/-- **D5 — degreewise rank–nullity difference.** For a `κ`-linear map `φ : V → W`
between finite-dimensional `κ`-vector spaces,
`dim W − dim V = dim (W ⧸ range φ) − dim (ker φ)` (integer-valued). Applied
degreewise with `φ = (x : M_n → M_{n+1})` this is the `hdiff` hypothesis consumed by
`AlgebraicGeometry.IsRatHilb.ofDiffEq`. Pure linear algebra — no graded structure used.
Project-local: Mathlib has the two halves (`LinearMap.finrank_range_add_finrank_ker`,
`Submodule.finrank_quotient_add_finrank`) but not this packaged difference. -/
theorem degreewise_finrank_diff {κ V W : Type*} [Field κ]
    [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    [AddCommGroup W] [Module κ W] [FiniteDimensional κ W]
    (φ : V →ₗ[κ] W) :
    (Module.finrank κ W : ℤ) - Module.finrank κ V
      = (Module.finrank κ (W ⧸ LinearMap.range φ) : ℤ)
        - Module.finrank κ (LinearMap.ker φ) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range φ)
  omega

/-! ### Ambient subquotient induction for Stacks 00K1

The Route-2 graded-module side of the inductive step. Everything is phrased over a
**fixed** ambient graded `κ`-module `M = ⨁ ℳ n`: a subquotient is a pair of homogeneous
submodules `N' ≤ N ⊆ M`, and its Hilbert function is the ambient dimension difference
`n ↦ dim_κ(N ⊓ ℳ n) − dim_κ(N' ⊓ ℳ n)`. The kernel and cokernel of a degree-one
endomorphism are again ambient subquotient pairs, so no `DirectSum.Decomposition` on a
quotient/subtype carrier is ever formed (cf.
`memory/graded-quotient-module-isdefeq-pathology.md`). -/

section Subquotient

variable {κ M : Type*} [Field κ] [AddCommGroup M] [Module κ M]
variable (ℳ : ℕ → Submodule κ M) [DirectSum.Decomposition ℳ]

/-- A `κ`-linear endomorphism `x` of `M` **raises degree by one** with respect to the
grading `ℳ` when `x (ℳ n) ⊆ ℳ (n+1)` for every `n`. This is the abstract, graded-ring-free
form of "multiplication by a degree-one element" used in the Stacks 00K1 induction.
Project-local. -/
def RaisesDegree (x : M →ₗ[κ] M) : Prop := ∀ n, (ℳ n).map x ≤ ℳ (n + 1)

omit [DirectSum.Decomposition ℳ] in
/-- Membership form of `RaisesDegree`. -/
lemma RaisesDegree.mem {x : M →ₗ[κ] M} (hx : RaisesDegree ℳ x) {n : ℕ} {m : M}
    (hm : m ∈ ℳ n) : x m ∈ ℳ (n + 1) :=
  hx n (Submodule.mem_map_of_mem hm)

/-- The **ambient subquotient Hilbert function** of a pair of homogeneous submodules
`N' ≤ N ⊆ M`: `n ↦ dim_κ(N ⊓ ℳ n) − dim_κ(N' ⊓ ℳ n)` (computed in `ℤ`, cast to `ℚ`).
This is the data the Stacks 00K1 induction tracks; it depends only on the ambient
intersections `N ⊓ ℳ n`, `N' ⊓ ℳ n` of submodules of the fixed `M`. Project-local. -/
noncomputable def subquotientHilb (N N' : Submodule κ M) (n : ℕ) : ℚ :=
  (((Module.finrank κ ↥(N ⊓ ℳ n) : ℤ) - (Module.finrank κ ↥(N' ⊓ ℳ n) : ℤ) : ℤ) : ℚ)

/-- A degree-raising endomorphism shifts the homogeneous decomposition: the degree-`(i+1)`
component of `x m` is `x` applied to the degree-`i` component of `m`. This is the ambient
commutation fact that makes preimages and images of homogeneous submodules under `x`
homogeneous. Project-local. -/
lemma decompose_raisesDegree {x : M →ₗ[κ] M} (hx : RaisesDegree ℳ x) (m : M) (i : ℕ) :
    (DirectSum.decompose ℳ (x m) (i + 1) : M) = x (DirectSum.decompose ℳ m i) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ m, map_sum, DirectSum.decompose_sum]
  simp only [DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
  rw [Finset.sum_eq_single i]
  · exact DirectSum.decompose_of_mem_same ℳ
      (hx i (Submodule.mem_map_of_mem (SetLike.coe_mem _)))
  · intro j _ hji
    rw [DirectSum.decompose_of_mem_ne ℳ
      (hx j (Submodule.mem_map_of_mem (SetLike.coe_mem _))) (by omega : j + 1 ≠ i + 1)]
  · intro hi
    simp [DFinsupp.notMem_support_iff.mp hi]

/-- The preimage of a homogeneous submodule under a degree-raising endomorphism is
homogeneous. Project-local. -/
lemma comap_isHomogeneous {x : M →ₗ[κ] M} (hx : RaisesDegree ℳ x)
    {N' : Submodule κ M} (hN' : N'.IsHomogeneous ℳ) :
    (N'.comap x).IsHomogeneous ℳ := by
  intro i z hz
  rw [Submodule.mem_comap, ← decompose_raisesDegree ℳ hx z i]
  exact (Submodule.IsHomogeneous.mem_iff ℳ hN').mp (Submodule.mem_comap.mp hz) (i + 1)

/-- A degree-raising endomorphism kills the degree-zero component: `x m` has no degree-`0`
part. Project-local. -/
lemma decompose_raisesDegree_zero {x : M →ₗ[κ] M} (hx : RaisesDegree ℳ x) (m : M) :
    (DirectSum.decompose ℳ (x m) 0 : M) = 0 := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ m, map_sum, DirectSum.decompose_sum]
  simp only [DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [DirectSum.decompose_of_mem_ne ℳ
    (hx j (Submodule.mem_map_of_mem (SetLike.coe_mem _))) (by omega : j + 1 ≠ 0)]

/-- The image of a homogeneous submodule under a degree-raising endomorphism is
homogeneous. Project-local. -/
lemma map_isHomogeneous {x : M →ₗ[κ] M} (hx : RaisesDegree ℳ x)
    {N : Submodule κ M} (hN : N.IsHomogeneous ℳ) :
    (N.map x).IsHomogeneous ℳ := by
  intro i z hz
  obtain ⟨m, hm, rfl⟩ := hz
  cases i with
  | zero => rw [decompose_raisesDegree_zero ℳ hx m]; exact Submodule.zero_mem _
  | succ i =>
      rw [decompose_raisesDegree ℳ hx m i]
      exact Submodule.mem_map_of_mem ((Submodule.IsHomogeneous.mem_iff ℳ hN).mp hm i)

/-- **Ambient image identity.** For a homogeneous submodule `N` and a degree-raising
endomorphism `x`, the degree-`(n+1)` part of `x · N` is `x · (N ⊓ ℳ n)`. Project-local. -/
lemma map_inf_degree_eq {x : M →ₗ[κ] M} (hx : RaisesDegree ℳ x)
    {N : Submodule κ M} (hN : N.IsHomogeneous ℳ) (n : ℕ) :
    N.map x ⊓ ℳ (n + 1) = (N ⊓ ℳ n).map x := by
  apply le_antisymm
  · rintro y ⟨hy1, hy2⟩
    obtain ⟨m, hm, rfl⟩ := hy1
    refine Submodule.mem_map.mpr ⟨DirectSum.decompose ℳ m n, ?_, ?_⟩
    · exact Submodule.mem_inf.mpr
        ⟨(Submodule.IsHomogeneous.mem_iff ℳ hN).mp hm n, SetLike.coe_mem _⟩
    · rw [← decompose_raisesDegree ℳ hx m n]
      exact DirectSum.decompose_of_mem_same ℳ hy2
  · refine le_inf (Submodule.map_mono inf_le_left) ?_
    rw [Submodule.map_le_iff_le_comap]
    exact fun m hm => hx.mem ℳ (Submodule.mem_inf.mp hm).2

/-- **Ambient distributive law.** Intersecting a sum of two homogeneous submodules with a
graded piece distributes: `(P + Q) ⊓ ℳ k = (P ⊓ ℳ k) + (Q ⊓ ℳ k)`. Project-local. -/
lemma sup_inf_degree_eq {P Q : Submodule κ M}
    (hP : P.IsHomogeneous ℳ) (hQ : Q.IsHomogeneous ℳ) (k : ℕ) :
    (P ⊔ Q) ⊓ ℳ k = (P ⊓ ℳ k) ⊔ (Q ⊓ ℳ k) := by
  apply le_antisymm
  · rintro z ⟨hzPQ, hzk⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hzPQ
    have hpk : (DirectSum.decompose ℳ p k : M) ∈ P ⊓ ℳ k :=
      Submodule.mem_inf.mpr ⟨(Submodule.IsHomogeneous.mem_iff ℳ hP).mp hp k, SetLike.coe_mem _⟩
    have hqk : (DirectSum.decompose ℳ q k : M) ∈ Q ⊓ ℳ k :=
      Submodule.mem_inf.mpr ⟨(Submodule.IsHomogeneous.mem_iff ℳ hQ).mp hq k, SetLike.coe_mem _⟩
    have hsum : (DirectSum.decompose ℳ p k : M) + (DirectSum.decompose ℳ q k : M) = p + q := by
      have h := DirectSum.decompose_of_mem_same ℳ hzk
      rw [DirectSum.decompose_add, DirectSum.add_apply] at h
      simpa using h
    exact hsum ▸ Submodule.add_mem_sup hpk hqk
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)

/-- The intersection of two homogeneous submodules is homogeneous. Project-local: Mathlib
provides no lattice-closure lemmas for `Submodule.IsHomogeneous`. -/
lemma inf_isHomogeneous {p q : Submodule κ M} (hp : p.IsHomogeneous ℳ)
    (hq : q.IsHomogeneous ℳ) : (p ⊓ q).IsHomogeneous ℳ := by
  intro i z hz
  exact Submodule.mem_inf.mpr
    ⟨(Submodule.IsHomogeneous.mem_iff ℳ hp).mp (Submodule.mem_inf.mp hz).1 i,
      (Submodule.IsHomogeneous.mem_iff ℳ hq).mp (Submodule.mem_inf.mp hz).2 i⟩

/-- The sum (supremum) of two homogeneous submodules is homogeneous. Project-local. -/
lemma sup_isHomogeneous {p q : Submodule κ M} (hp : p.IsHomogeneous ℳ)
    (hq : q.IsHomogeneous ℳ) : (p ⊔ q).IsHomogeneous ℳ := by
  intro i z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
  have hcoe : (DirectSum.decompose ℳ (a + b) i : M)
      = ↑(DirectSum.decompose ℳ a i) + ↑(DirectSum.decompose ℳ b i) := by
    rw [DirectSum.decompose_add, DirectSum.add_apply]; rfl
  rw [hcoe]
  exact Submodule.add_mem_sup ((Submodule.IsHomogeneous.mem_iff ℳ hp).mp ha i)
    ((Submodule.IsHomogeneous.mem_iff ℳ hq).mp hb i)

/-! #### Kernel/cokernel subquotient building blocks

For a degree-raising endomorphism `x` and a homogeneous pair `N' ≤ N`, the kernel
subquotient is the pair `(N ⊓ x⁻¹N', N')` and the cokernel subquotient is the pair
`(N, N' + x·N)`. The lemmas here record that both new pairs are homogeneous, nest correctly,
are annihilated by `x`, and are preserved by any endomorphism `t` commuting with `x` that
preserves the original pair — the ambient (carrier-free) content of
`lem:graded_subquotient_ker_coker`. -/

/-- The kernel subquotient's lower module `N ⊓ x⁻¹N'` is homogeneous. Project-local. -/
lemma ker_isHomogeneous {x : M →ₗ[κ] M} (hx : RaisesDegree ℳ x)
    {N N' : Submodule κ M} (hN : N.IsHomogeneous ℳ) (hN' : N'.IsHomogeneous ℳ) :
    (N ⊓ N'.comap x).IsHomogeneous ℳ :=
  inf_isHomogeneous ℳ hN (comap_isHomogeneous ℳ hx hN')

/-- The cokernel subquotient's upper module `N' ⊔ x·N` is homogeneous. Project-local. -/
lemma coker_isHomogeneous {x : M →ₗ[κ] M} (hx : RaisesDegree ℳ x)
    {N N' : Submodule κ M} (hN : N.IsHomogeneous ℳ) (hN' : N'.IsHomogeneous ℳ) :
    (N' ⊔ N.map x).IsHomogeneous ℳ :=
  sup_isHomogeneous ℳ hN' (map_isHomogeneous ℳ hx hN)

omit [DirectSum.Decomposition ℳ] in
/-- The kernel subquotient nests: `N' ≤ N ⊓ x⁻¹N'`, using `N' ≤ N` and that `x` preserves
`N'`. Project-local. -/
lemma ker_le {x : M →ₗ[κ] M} {N N' : Submodule κ M} (hle : N' ≤ N)
    (hpresN' : N'.map x ≤ N') : N' ≤ N ⊓ N'.comap x :=
  le_inf hle (Submodule.map_le_iff_le_comap.mp hpresN')

omit [DirectSum.Decomposition ℳ] in
/-- The cokernel subquotient nests: `N' ⊔ x·N ≤ N`, using `N' ≤ N` and that `x` preserves
`N`. Project-local. -/
lemma coker_le {x : M →ₗ[κ] M} {N N' : Submodule κ M} (hle : N' ≤ N)
    (hpresN : N.map x ≤ N) : N' ⊔ N.map x ≤ N :=
  sup_le hle hpresN

omit [DirectSum.Decomposition ℳ] in
/-- `x` annihilates the kernel subquotient: `x·(N ⊓ x⁻¹N') ≤ N'`. Project-local. -/
lemma ker_annihilate {x : M →ₗ[κ] M} {N N' : Submodule κ M} :
    (N ⊓ N'.comap x).map x ≤ N' :=
  Submodule.map_le_iff_le_comap.mpr inf_le_right

omit [DirectSum.Decomposition ℳ] in
/-- `x` annihilates the cokernel subquotient: `x·N ≤ N' ⊔ x·N`. Project-local. -/
lemma coker_annihilate {x : M →ₗ[κ] M} {N N' : Submodule κ M} :
    N.map x ≤ N' ⊔ N.map x :=
  le_sup_right

omit [DirectSum.Decomposition ℳ] in
/-- An endomorphism `t` commuting with `x` and preserving `N'` preserves the preimage
`x⁻¹N'`. Project-local. -/
lemma comap_map_le_of_commute {x t : M →ₗ[κ] M} (hcomm : Commute x t)
    {N' : Submodule κ M} (ht' : N'.map t ≤ N') :
    (N'.comap x).map t ≤ N'.comap x := by
  rw [Submodule.map_le_iff_le_comap]
  intro m hm
  rw [Submodule.mem_comap] at hm
  rw [Submodule.mem_comap, Submodule.mem_comap]
  have key : x (t m) = t (x m) := LinearMap.congr_fun hcomm.eq m
  rw [key]
  exact ht' (Submodule.mem_map_of_mem hm)

omit [DirectSum.Decomposition ℳ] in
/-- An endomorphism `t` commuting with `x` and preserving `N` preserves the image `x·N`.
Project-local. -/
lemma map_map_le_of_commute {x t : M →ₗ[κ] M} (hcomm : Commute x t)
    {N : Submodule κ M} (htN : N.map t ≤ N) :
    (N.map x).map t ≤ N.map x := by
  rw [Submodule.map_le_iff_le_comap]
  rintro y ⟨m, hm, rfl⟩
  rw [Submodule.mem_comap]
  have key : t (x m) = x (t m) := (LinearMap.congr_fun hcomm.eq m).symm
  rw [key]
  exact Submodule.mem_map_of_mem (htN (Submodule.mem_map_of_mem hm))

/-- The dimension of the preimage of `S` under the inclusion of a submodule `p` equals the
dimension of the ambient intersection `p ⊓ S`. Project-local helper for the degreewise
difference identity. -/
lemma finrank_comap_subtype (p S : Submodule κ M) :
    Module.finrank κ ↥(Submodule.comap p.subtype S) = Module.finrank κ ↥(p ⊓ S) := by
  rw [← Submodule.map_comap_subtype p S]
  exact (Submodule.equivMapOfInjective p.subtype p.injective_subtype _).finrank_eq

variable [∀ n, FiniteDimensional κ ↥(ℳ n)]

/-- **D6 — subquotient degreewise difference.** For a degree-raising endomorphism `x` and
homogeneous submodules `N`, `N'`, the first difference of the ambient subquotient Hilbert
function of `(N, N')` equals the alternating sum of the Hilbert functions of the cokernel
subquotient `C = (N, N' ⊔ x·N)` and kernel subquotient `K = (N ⊓ x⁻¹N', N')`:
`hilb(n+1) − hilb(n) = hilb_C(n+1) − hilb_K(n)`. This is the `hdiff` hypothesis consumed by
`IsRatHilb.ofDiffEq` in the Stacks 00K1 induction. Project-local. -/
lemma subquotient_degreewise_diff {x : M →ₗ[κ] M} (hx : RaisesDegree ℳ x)
    {N N' : Submodule κ M} (hN : N.IsHomogeneous ℳ) (hN' : N'.IsHomogeneous ℳ) (n : ℕ) :
    subquotientHilb ℳ N N' (n + 1) - subquotientHilb ℳ N N' n
      = subquotientHilb ℳ N (N' ⊔ N.map x) (n + 1)
        - subquotientHilb ℳ (N ⊓ N'.comap x) N' n := by
  classical
  haveI : FiniteDimensional κ ↥(N ⊓ ℳ n) := Submodule.finiteDimensional_of_le inf_le_right
  haveI : FiniteDimensional κ ↥(N' ⊓ ℳ (n + 1)) := Submodule.finiteDimensional_of_le inf_le_right
  set T : Submodule κ M := (N ⊓ ℳ n).map x with hTdef
  have hT : N.map x ⊓ ℳ (n + 1) = T := map_inf_degree_eq ℳ hx hN n
  have hTle : T ≤ ℳ (n + 1) := hT ▸ inf_le_right
  haveI : FiniteDimensional κ ↥T := Submodule.finiteDimensional_of_le hTle
  -- the two linear maps into `M ⧸ N'`
  set φ : ↥(N ⊓ ℳ n) →ₗ[κ] (M ⧸ N') := (N'.mkQ).comp (x.comp (N ⊓ ℳ n).subtype) with hφ
  set g : ↥T →ₗ[κ] (M ⧸ N') := (N'.mkQ).comp T.subtype with hg
  have hrange : LinearMap.range φ = LinearMap.range g := by
    rw [hφ, hg, LinearMap.range_comp, LinearMap.range_comp, LinearMap.range_comp,
      Submodule.range_subtype, Submodule.range_subtype, hTdef]
  have hkerφ : Module.finrank κ ↥(LinearMap.ker φ)
      = Module.finrank κ ↥((N ⊓ N'.comap x) ⊓ ℳ n) := by
    have hk : LinearMap.ker φ = Submodule.comap (N ⊓ ℳ n).subtype (N'.comap x) := by
      rw [hφ, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_comp]
    have heq : (N ⊓ ℳ n) ⊓ N'.comap x = (N ⊓ N'.comap x) ⊓ ℳ n := inf_right_comm _ _ _
    rw [hk, finrank_comap_subtype, heq]
  have hkerg : Module.finrank κ ↥(LinearMap.ker g) = Module.finrank κ ↥(T ⊓ N') := by
    rw [hg, LinearMap.ker_comp, Submodule.ker_mkQ, finrank_comap_subtype]
  -- inclusion–exclusion linking the cokernel block to `b` and `T`
  have hC : (N' ⊔ N.map x) ⊓ ℳ (n + 1) = (N' ⊓ ℳ (n + 1)) ⊔ T := by
    rw [sup_inf_degree_eq ℳ hN' (map_isHomogeneous ℳ hx hN), hT]
  have hinf : (N' ⊓ ℳ (n + 1)) ⊓ T = T ⊓ N' := by
    rw [inf_right_comm, inf_of_le_left (le_trans inf_le_right hTle), inf_comm]
  have hIE := Submodule.finrank_sup_add_finrank_inf_eq (N' ⊓ ℳ (n + 1)) T
  rw [← hC, hinf] at hIE
  -- the two rank–nullity identities
  have RN := LinearMap.finrank_range_add_finrank_ker φ
  have RG := LinearMap.finrank_range_add_finrank_ker g
  rw [hkerφ] at RN
  rw [hkerg, ← hrange] at RG
  -- the integer dimension identity
  have key : Module.finrank κ ↥((N' ⊔ N.map x) ⊓ ℳ (n + 1))
              + Module.finrank κ ↥((N ⊓ N'.comap x) ⊓ ℳ n)
           = Module.finrank κ ↥(N ⊓ ℳ n)
              + Module.finrank κ ↥(N' ⊓ ℳ (n + 1)) := by
    omega
  -- assemble
  simp only [subquotientHilb]
  push_cast
  have keyQ : (Module.finrank κ ↥((N' ⊔ N.map x) ⊓ ℳ (n + 1)) : ℚ)
              + Module.finrank κ ↥((N ⊓ N'.comap x) ⊓ ℳ n)
           = Module.finrank κ ↥(N ⊓ ℳ n) + Module.finrank κ ↥(N' ⊓ ℳ (n + 1)) := by
    exact_mod_cast key
  linarith [keyQ]

end Subquotient

/-! ### Polynomial-module structure from commuting endomorphisms

A finite family `t : Fin r → End κ M` of pairwise-commuting `κ`-linear endomorphisms makes `M`
a module over the **free** polynomial ring `MvPolynomial (Fin r) κ`, with `X i` acting as
`t i`. The free polynomial ring — not the subalgebra `Algebra.adjoin κ (range t)` — is used so
that the inductive transfer (`subquotient_finite_transfer`) has the ring surjection
`MvPolynomial (Fin (r+1)) κ ↠ MvPolynomial (Fin r) κ` available; relations among the `t i`
inside `End κ M` would obstruct the analogous surjection of subalgebras. -/

section PolyModule

variable {κ M : Type*} [Field κ] [AddCommGroup M] [Module κ M]

/-- The ring homomorphism `MvPolynomial (Fin r) κ →+* End κ M` evaluating a polynomial at a
pairwise-commuting family `t` of endomorphisms, factored through the commutative subalgebra
`Algebra.adjoin κ (range t) ⊆ End κ M` (commutative by `Algebra.isMulCommutative_adjoin`).
Project-local: the engine for the `MvPolynomial`-module structure on `M`. -/
noncomputable def polyEndHom {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) :
    MvPolynomial (Fin r) κ →+* Module.End κ M :=
  letI : IsMulCommutative (Algebra.adjoin κ (Set.range t)) :=
    Algebra.isMulCommutative_adjoin κ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact (hcomm i j).eq)
  letI : CommRing (Algebra.adjoin κ (Set.range t)) := IsMulCommutative.instCommRing
  ((Algebra.adjoin κ (Set.range t)).val.toRingHom).comp
    (MvPolynomial.aeval
      (fun i => (⟨t i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ :
        Algebra.adjoin κ (Set.range t)))).toRingHom

/-- The evaluation ring hom sends the variable `X i` to the endomorphism `t i`. -/
@[simp] lemma polyEndHom_X {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) (i : Fin r) :
    polyEndHom t hcomm (MvPolynomial.X i) = t i := by
  letI : IsMulCommutative (Algebra.adjoin κ (Set.range t)) :=
    Algebra.isMulCommutative_adjoin κ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact (hcomm i j).eq)
  letI : CommRing (Algebra.adjoin κ (Set.range t)) := IsMulCommutative.instCommRing
  simp [polyEndHom]

/-- The evaluation ring hom sends a constant `C c` to the scalar endomorphism `c • 1`. -/
@[simp] lemma polyEndHom_C {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) (c : κ) :
    polyEndHom t hcomm (MvPolynomial.C c) = c • (1 : Module.End κ M) := by
  letI : IsMulCommutative (Algebra.adjoin κ (Set.range t)) :=
    Algebra.isMulCommutative_adjoin κ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact (hcomm i j).eq)
  letI : CommRing (Algebra.adjoin κ (Set.range t)) := IsMulCommutative.instCommRing
  simp only [polyEndHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPolynomial.aeval_C]
  rw [Algebra.algebraMap_eq_smul_one]
  simp

/-- The `MvPolynomial (Fin r) κ`-module structure on `M` in which `X i` acts as `t i`,
obtained by restricting scalars along `polyEndHom`. Project-local: the module over the free
polynomial ring required by the ambient subquotient induction. -/
@[implicit_reducible]
noncomputable def polyModule {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) : Module (MvPolynomial (Fin r) κ) M :=
  Module.compHom M (polyEndHom t hcomm)

/-- In the polynomial-module structure, `X i` acts as the endomorphism `t i`. -/
lemma polyModule_X_smul {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) (i : Fin r) (m : M) :
    letI := polyModule t hcomm
    (MvPolynomial.X i : MvPolynomial (Fin r) κ) • m = t i m := by
  change polyEndHom t hcomm (MvPolynomial.X i) • m = t i m
  rw [polyEndHom_X, Module.End.smul_def]

/-- In the polynomial-module structure, a constant `C c` acts by the scalar `c`. -/
lemma polyModule_C_smul {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) (c : κ) (m : M) :
    letI := polyModule t hcomm
    (MvPolynomial.C c : MvPolynomial (Fin r) κ) • m = c • m := by
  change polyEndHom t hcomm (MvPolynomial.C c) • m = c • m
  rw [polyEndHom_C, Module.End.smul_def]
  simp

/-- The polynomial-module structure is compatible with the `κ`-action (scalar tower):
the algebra map `κ → MvPolynomial (Fin r) κ` followed by the polynomial action recovers the
original `κ`-action on `M`. -/
lemma polyModule_isScalarTower {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) :
    letI := polyModule t hcomm
    IsScalarTower κ (MvPolynomial (Fin r) κ) M := by
  letI := polyModule t hcomm
  refine IsScalarTower.of_algebraMap_smul fun c m => ?_
  change polyEndHom t hcomm (algebraMap κ (MvPolynomial (Fin r) κ) c) • m = c • m
  rw [MvPolynomial.algebraMap_eq, polyEndHom_C, Module.End.smul_def]
  simp

/-- A `κ`-submodule `N` that is stable under each commuting endomorphism `t i` is a
`MvPolynomial (Fin r) κ`-submodule of `M` (same carrier), for the polynomial-module structure
`polyModule`. Project-local: lifts an ambient `t`-stable submodule to the polynomial ring,
keeping every carrier an ambient submodule of `M` (no derived carrier). -/
noncomputable def polySubmodule {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) (N : Submodule κ M)
    (hN : ∀ i, N.map (t i) ≤ N) :
    letI := polyModule t hcomm
    Submodule (MvPolynomial (Fin r) κ) M :=
  letI := polyModule t hcomm
  { carrier := N
    add_mem' := fun ha hb => N.add_mem ha hb
    zero_mem' := N.zero_mem
    smul_mem' := by
      have key : ∀ (p : MvPolynomial (Fin r) κ), ∀ m ∈ N, p • m ∈ N := by
        intro p
        induction p using MvPolynomial.induction_on with
        | C a => intro m hm; rw [polyModule_C_smul]; exact N.smul_mem a hm
        | add p q hp hq => intro m hm; rw [add_smul]; exact N.add_mem (hp m hm) (hq m hm)
        | mul_X p i hp =>
            intro m hm
            rw [mul_smul, polyModule_X_smul]
            exact hp _ (hN i (Submodule.mem_map_of_mem hm))
      intro p m hm
      exact key p m hm }

/-- The carrier of `polySubmodule` is the original `κ`-submodule. -/
@[simp] lemma polySubmodule_coe {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) (N : Submodule κ M)
    (hN : ∀ i, N.map (t i) ≤ N) :
    letI := polyModule t hcomm
    ((polySubmodule t hcomm N hN : Submodule (MvPolynomial (Fin r) κ) M) : Set M) = N :=
  rfl

end PolyModule

/-! ### The last-variable surjection of polynomial rings

The finiteness transfer of the ambient subquotient induction factors the action of
`MvPolynomial (Fin (r+1)) κ` on a subquotient annihilated by the last endomorphism through the
free polynomial ring on one fewer variable, `MvPolynomial (Fin r) κ`, via the surjection
`X (Fin.last r) ↦ 0`, `X (Fin.castSucc i) ↦ X i`. -/

section LastVar

variable {κ : Type*} [Field κ]

/-- The `κ`-algebra surjection `MvPolynomial (Fin (r+1)) κ ↠ MvPolynomial (Fin r) κ` sending the
last variable `X (Fin.last r)` to `0` and `X (Fin.castSucc i)` to `X i`. Project-local: the ring
surjection along which the finiteness transfer factors
(`lem:fg_restrictScalars_of_surjective_mathlib`). -/
noncomputable def lastVarAlgHom (r : ℕ) (κ : Type*) [Field κ] :
    MvPolynomial (Fin (r + 1)) κ →ₐ[κ] MvPolynomial (Fin r) κ :=
  MvPolynomial.aeval (Fin.lastCases 0 (fun i => MvPolynomial.X i))

@[simp] lemma lastVarAlgHom_X_castSucc (r : ℕ) (i : Fin r) :
    lastVarAlgHom r κ (MvPolynomial.X (Fin.castSucc i)) = MvPolynomial.X i := by
  simp [lastVarAlgHom]

@[simp] lemma lastVarAlgHom_X_last (r : ℕ) :
    lastVarAlgHom r κ (MvPolynomial.X (Fin.last r)) = 0 := by
  simp [lastVarAlgHom]

@[simp] lemma lastVarAlgHom_C (r : ℕ) (c : κ) :
    lastVarAlgHom r κ (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [lastVarAlgHom]

/-- `lastVarAlgHom` is a left inverse of `rename Fin.castSucc`, hence surjective. -/
lemma lastVarAlgHom_rename_castSucc (r : ℕ) (q : MvPolynomial (Fin r) κ) :
    lastVarAlgHom r κ (MvPolynomial.rename Fin.castSucc q) = q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma lastVarAlgHom_surjective (r : ℕ) : Function.Surjective (lastVarAlgHom r κ) :=
  fun q => ⟨MvPolynomial.rename Fin.castSucc q, lastVarAlgHom_rename_castSucc r q⟩

instance lastVarAlgHom_ringHomSurjective (r : ℕ) :
    RingHomSurjective (lastVarAlgHom r κ).toRingHom :=
  ⟨lastVarAlgHom_surjective r⟩

end LastVar

/-! ### Finiteness transfer down one variable

The keystone of the ambient subquotient induction: if a subquotient is finite over the free
polynomial ring `MvPolynomial (Fin (r+1)) κ` and the last endomorphism annihilates it, then it is
finite over `MvPolynomial (Fin r) κ`. The action factors through the `lastVarAlgHom` surjection. -/

section Transfer

variable {κ M : Type*} [Field κ] [AddCommGroup M] [Module κ M]

/-- A `t`-stable submodule `P'` is closed under the action of any polynomial via `polyEndHom`. -/
lemma polyEndHom_mem_of_stable {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) {P' : Submodule κ M}
    (hP' : ∀ i, P'.map (t i) ≤ P') (p : MvPolynomial (Fin r) κ) :
    ∀ m ∈ P', (polyEndHom t hcomm p) m ∈ P' := by
  induction p using MvPolynomial.induction_on with
  | C a => intro m hm; rw [polyEndHom_C]; simpa using P'.smul_mem a hm
  | add p q hp hq =>
      intro m hm; rw [map_add, LinearMap.add_apply]; exact P'.add_mem (hp m hm) (hq m hm)
  | mul_X p i hp =>
      intro m hm; rw [map_mul, polyEndHom_X, Module.End.mul_apply]
      exact hp _ (hP' i (Submodule.mem_map_of_mem hm))

/-- **Mod-`P'` semilinearity heart.** For `m ∈ P`, evaluating a polynomial `s` via the full
endomorphism family `t` agrees, modulo `P'`, with first projecting away the last variable
(`lastVarAlgHom`) and evaluating via `t ∘ Fin.castSucc` — provided the last endomorphism
`x = t (Fin.last r)` carries `P` into `P'` and `P, P'` are stable under every `t i`. This is the
algebraic content of the finiteness transfer (`lem:graded_subquotient_finite_transfer`). -/
lemma polyEndHom_lastVar_sub_mem {r : ℕ} (t : Fin (r + 1) → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) {P P' : Submodule κ M}
    (hP : ∀ i, P.map (t i) ≤ P) (hP' : ∀ i, P'.map (t i) ≤ P')
    (hannih : P.map (t (Fin.last r)) ≤ P')
    (s : MvPolynomial (Fin (r + 1)) κ) :
    ∀ m ∈ P, (polyEndHom t hcomm s) m
      - (polyEndHom (fun i => t (Fin.castSucc i)) (fun _ _ => hcomm _ _)
          (lastVarAlgHom r κ s)) m ∈ P' := by
  induction s using MvPolynomial.induction_on with
  | C a =>
      intro m _
      rw [lastVarAlgHom_C, polyEndHom_C, polyEndHom_C, sub_self]
      exact P'.zero_mem
  | add p q hp hq =>
      intro m hm
      rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
      have := P'.add_mem (hp m hm) (hq m hm)
      convert this using 1
      abel
  | mul_X p j hp =>
      intro m hm
      rw [map_mul, polyEndHom_X, Module.End.mul_apply]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
      · -- `j = castSucc i`: reduce to the IH at `t (castSucc i) m ∈ P`
        rw [map_mul, lastVarAlgHom_X_castSucc, map_mul, polyEndHom_X, Module.End.mul_apply]
        exact hp _ (hP _ (Submodule.mem_map_of_mem hm))
      · -- `j = last`: the right term vanishes; the left lands in `P'` by annihilation
        rw [map_mul, lastVarAlgHom_X_last, mul_zero, map_zero, LinearMap.zero_apply, sub_zero]
        exact polyEndHom_mem_of_stable t hcomm hP' p _
          (hannih (Submodule.mem_map_of_mem hm))

/-- **Finiteness transfer down one variable (core).** If the subquotient `P/P'` (carriers
ambient submodules of `M`, stable under every `t i`) is finite over `MvPolynomial (Fin (r+1)) κ`
and the last endomorphism `t (Fin.last r)` carries `P` into `P'`, then `P/P'` is finite over
`MvPolynomial (Fin r) κ` for the action of `t ∘ Fin.castSucc`. The action factors through the
`lastVarAlgHom` surjection; finiteness transfers by `Module.Finite.of_surjective`. -/
lemma subquotient_finite_transfer {r : ℕ} (t : Fin (r + 1) → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) {P P' : Submodule κ M}
    (hP : ∀ i, P.map (t i) ≤ P) (hP' : ∀ i, P'.map (t i) ≤ P')
    (hannih : P.map (t (Fin.last r)) ≤ P')
    (hpar : letI := polyModule t hcomm
      Module.Finite (MvPolynomial (Fin (r + 1)) κ)
        (↥(polySubmodule t hcomm P hP) ⧸
          (polySubmodule t hcomm P' hP').comap (polySubmodule t hcomm P hP).subtype)) :
    letI := polyModule (fun i => t (Fin.castSucc i)) (fun _ _ => hcomm _ _)
    Module.Finite (MvPolynomial (Fin r) κ)
      (↥(polySubmodule (fun i => t (Fin.castSucc i)) (fun _ _ => hcomm _ _) P
            (fun _ => hP _)) ⧸
        (polySubmodule (fun i => t (Fin.castSucc i)) (fun _ _ => hcomm _ _) P'
            (fun _ => hP' _)).comap
          (polySubmodule (fun i => t (Fin.castSucc i)) (fun _ _ => hcomm _ _) P
            (fun _ => hP _)).subtype) := by
  classical
  letI iS := polyModule t hcomm
  letI iS' := polyModule (fun i => t (Fin.castSucc i)) (fun i j => hcomm _ _)
  haveI := hpar
  set σ : MvPolynomial (Fin (r + 1)) κ →+* MvPolynomial (Fin r) κ :=
    (lastVarAlgHom r κ).toRingHom with hσ
  -- the σ-semilinear map out of the numerator `↥Pbig` into the target quotient `Q^S'`
  set g : ↥(polySubmodule t hcomm P hP) →ₛₗ[σ]
      (↥(polySubmodule (fun i => t (Fin.castSucc i)) (fun i j => hcomm _ _) P (fun i => hP _)) ⧸
        (polySubmodule (fun i => t (Fin.castSucc i)) (fun i j => hcomm _ _) P'
            (fun i => hP' _)).comap
          (polySubmodule (fun i => t (Fin.castSucc i)) (fun i j => hcomm _ _) P
            (fun i => hP _)).subtype) :=
    { toFun := fun y => Submodule.Quotient.mk ⟨(y : M), y.2⟩
      map_add' := fun a b => by rw [← Submodule.Quotient.mk_add]; rfl
      map_smul' := by
        intro s y
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
        change (polyEndHom t hcomm s) (y : M)
          - (polyEndHom (fun i => t (Fin.castSucc i)) (fun i j => hcomm _ _) (σ s)) (y : M) ∈ P'
        exact polyEndHom_lastVar_sub_mem t hcomm hP hP' hannih s (y : M) y.2 }
    with hg
  have hgsurj : Function.Surjective g := by
    intro z
    refine Submodule.Quotient.induction_on _ z (fun y => ?_)
    exact ⟨⟨(y : M), y.2⟩, rfl⟩
  refine Module.Finite.of_surjective
    (Submodule.liftQ ((polySubmodule t hcomm P' hP').comap (polySubmodule t hcomm P hP).subtype)
      g ?_) ?_
  · -- the denominator `K` is killed by `g`
    intro y hy
    rw [LinearMap.mem_ker, hg]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact (Submodule.mem_comap).mp hy
  · -- `liftQ` of a surjection is surjective
    intro z
    obtain ⟨y, hy⟩ := hgsurj z
    exact ⟨Submodule.Quotient.mk y, by rw [Submodule.liftQ_apply]; exact hy⟩

/-- Enlarging the denominator keeps `S`-finiteness: `N/P₂` is a quotient of `N/P₁` when
`P₁ ≤ P₂`, so finiteness of the latter transfers along the surjection. -/
lemma polyQuot_finite_of_le_denominator {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) {N P₁ P₂ : Submodule κ M}
    (hN : ∀ i, N.map (t i) ≤ N) (hP₁ : ∀ i, P₁.map (t i) ≤ P₁) (hP₂ : ∀ i, P₂.map (t i) ≤ P₂)
    (h12 : P₁ ≤ P₂)
    (hfin : letI := polyModule t hcomm
      Module.Finite (MvPolynomial (Fin r) κ)
        (↥(polySubmodule t hcomm N hN) ⧸
          (polySubmodule t hcomm P₁ hP₁).comap (polySubmodule t hcomm N hN).subtype)) :
    letI := polyModule t hcomm
    Module.Finite (MvPolynomial (Fin r) κ)
      (↥(polySubmodule t hcomm N hN) ⧸
        (polySubmodule t hcomm P₂ hP₂).comap (polySubmodule t hcomm N hN).subtype) := by
  letI := polyModule t hcomm
  haveI := hfin
  refine Module.Finite.of_surjective
    (Submodule.liftQ ((polySubmodule t hcomm P₁ hP₁).comap (polySubmodule t hcomm N hN).subtype)
      ((polySubmodule t hcomm P₂ hP₂).comap (polySubmodule t hcomm N hN).subtype).mkQ ?_) ?_
  · rw [Submodule.ker_mkQ]
    exact Submodule.comap_mono (fun x hx => h12 hx)
  · intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- Shrinking the numerator keeps `S`-finiteness: `N₁/P'` embeds as an `S`-submodule of `N₂/P'`
when `N₁ ≤ N₂`, and a submodule of a Noetherian (finite over a Noetherian ring) module is
finite. -/
lemma polyQuot_finite_of_le_numerator {r : ℕ} (t : Fin r → Module.End κ M)
    (hcomm : ∀ i j, Commute (t i) (t j)) {N₁ N₂ P' : Submodule κ M}
    (hN₁ : ∀ i, N₁.map (t i) ≤ N₁) (hN₂ : ∀ i, N₂.map (t i) ≤ N₂) (hP' : ∀ i, P'.map (t i) ≤ P')
    (h12 : N₁ ≤ N₂)
    (hfin : letI := polyModule t hcomm
      Module.Finite (MvPolynomial (Fin r) κ)
        (↥(polySubmodule t hcomm N₂ hN₂) ⧸
          (polySubmodule t hcomm P' hP').comap (polySubmodule t hcomm N₂ hN₂).subtype)) :
    letI := polyModule t hcomm
    Module.Finite (MvPolynomial (Fin r) κ)
      (↥(polySubmodule t hcomm N₁ hN₁) ⧸
        (polySubmodule t hcomm P' hP').comap (polySubmodule t hcomm N₁ hN₁).subtype) := by
  letI := polyModule t hcomm
  haveI : IsNoetherianRing (MvPolynomial (Fin r) κ) := MvPolynomial.isNoetherianRing_fin
  haveI := hfin
  haveI : _root_.IsNoetherian (MvPolynomial (Fin r) κ)
      (↥(polySubmodule t hcomm N₂ hN₂) ⧸
        (polySubmodule t hcomm P' hP').comap (polySubmodule t hcomm N₂ hN₂).subtype) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  -- the inclusion of numerators descends to an injective `S`-linear map of quotients
  set incl : ↥(polySubmodule t hcomm N₁ hN₁) →ₗ[MvPolynomial (Fin r) κ]
      ↥(polySubmodule t hcomm N₂ hN₂) :=
    Submodule.inclusion (fun x hx => h12 hx) with hincl
  refine Module.Finite.of_injective
    (Submodule.mapQ ((polySubmodule t hcomm P' hP').comap (polySubmodule t hcomm N₁ hN₁).subtype)
      ((polySubmodule t hcomm P' hP').comap (polySubmodule t hcomm N₂ hN₂).subtype) incl ?_) ?_
  · intro y hy
    rw [Submodule.mem_comap] at hy ⊢
    exact hy
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | _ y =>
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap] at hz
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hz

end Transfer

/-! ### The ambient subquotient datum

Bundles a homogeneous pair `N' ≤ N` of a fixed graded `κ`-module `M = ⨁ ℳ n` with `r`
pairwise-commuting degree-raising endomorphisms preserving the pair, plus the finiteness of
the represented subquotient `N/N'` over the free polynomial ring `MvPolynomial (Fin r) κ` (via
`polySubmodule`, so the underlying carriers stay ambient submodules of `M`). This is the
length-`r` carrier of the Stacks 00K1 ambient induction (`def:graded_subquotientHilb`). -/

section Datum

variable {κ M : Type*} [Field κ] [AddCommGroup M] [Module κ M]
variable (ℳ : ℕ → Submodule κ M) [DirectSum.Decomposition ℳ]

/-- A length-`r` **ambient subquotient datum** over the fixed graded module `M = ⨁ ℳ n`.
Project-local: the carrier of the Stacks 00K1 ambient induction (`def:graded_subquotientHilb`).
The finiteness field `hfin` records that the represented subquotient `N/N'` is a finite module
over the free polynomial ring `MvPolynomial (Fin r) κ` acting through the `t i`; the carriers
involved are the ambient `t`-stable submodules `polySubmodule … N`, `polySubmodule … N'`. -/
structure SubquotientDatum (r : ℕ) where
  /-- The upper homogeneous submodule. -/
  N : Submodule κ M
  /-- The lower homogeneous submodule. -/
  N' : Submodule κ M
  /-- `N'` is contained in `N`. -/
  hle : N' ≤ N
  /-- `N` is homogeneous. -/
  hN : N.IsHomogeneous ℳ
  /-- `N'` is homogeneous. -/
  hN' : N'.IsHomogeneous ℳ
  /-- The `r` degree-raising endomorphisms. -/
  t : Fin r → Module.End κ M
  /-- They pairwise commute. -/
  hcomm : ∀ i j, Commute (t i) (t j)
  /-- Each raises degree by one. -/
  hraise : ∀ i, RaisesDegree ℳ (t i)
  /-- Each preserves `N`. -/
  hpresN : ∀ i, N.map (t i) ≤ N
  /-- Each preserves `N'`. -/
  hpresN' : ∀ i, N'.map (t i) ≤ N'
  /-- The represented subquotient `N/N'` is finite over `MvPolynomial (Fin r) κ`. -/
  hfin : letI := polyModule t hcomm
    Module.Finite (MvPolynomial (Fin r) κ)
      (↥(polySubmodule t hcomm N hpresN) ⧸
        (polySubmodule t hcomm N' hpresN').comap (polySubmodule t hcomm N hpresN).subtype)

/-- The ambient Hilbert function `n ↦ dim_κ(N ⊓ ℳ n) − dim_κ(N' ⊓ ℳ n)` of a subquotient
datum (`def:graded_subquotientHilb`). -/
noncomputable def SubquotientDatum.hilb {r : ℕ} (D : SubquotientDatum ℳ r) : ℕ → ℚ :=
  subquotientHilb ℳ D.N D.N'

/-- The kernel pair's lower module `N ⊓ x⁻¹N'` is stable under every endomorphism of the family
(needed for the finiteness transfer over the full polynomial ring). -/
lemma ker_stable_full {r : ℕ} (D : SubquotientDatum ℳ (r + 1)) (i : Fin (r + 1)) :
    (D.N ⊓ (D.N').comap (D.t (Fin.last r))).map (D.t i)
      ≤ D.N ⊓ (D.N').comap (D.t (Fin.last r)) :=
  le_trans (le_inf (Submodule.map_mono inf_le_left) (Submodule.map_mono inf_le_right))
    (inf_le_inf (D.hpresN i) (comap_map_le_of_commute (D.hcomm (Fin.last r) i) (D.hpresN' i)))

/-- The cokernel pair's upper module `N' ⊔ x·N` is stable under every endomorphism of the family. -/
lemma coker_stable_full {r : ℕ} (D : SubquotientDatum ℳ (r + 1)) (i : Fin (r + 1)) :
    (D.N' ⊔ D.N.map (D.t (Fin.last r))).map (D.t i)
      ≤ D.N' ⊔ D.N.map (D.t (Fin.last r)) := by
  rw [Submodule.map_sup]
  exact sup_le_sup (D.hpresN' i)
    (map_map_le_of_commute (D.hcomm (Fin.last r) i) (D.hpresN i))

/-- **Kernel constructor.** From a length-`(r+1)` subquotient datum, the kernel subquotient
`(N ⊓ x⁻¹N', N')` of multiplication by `x = t (last)`, as a length-`r` datum on `t ∘ castSucc`.
All non-finiteness fields are the ambient kernel/cokernel calculus; the finiteness field is the
keystone transfer `subquotient_finite_transfer` (`lem:graded_subquotient_finite_transfer`). -/
noncomputable def SubquotientDatum.ker {r : ℕ} (D : SubquotientDatum ℳ (r + 1)) :
    SubquotientDatum ℳ r where
  N := D.N ⊓ (D.N').comap (D.t (Fin.last r))
  N' := D.N'
  hle := ker_le D.hle (D.hpresN' (Fin.last r))
  hN := ker_isHomogeneous ℳ (D.hraise (Fin.last r)) D.hN D.hN'
  hN' := D.hN'
  t := fun i => D.t (Fin.castSucc i)
  hcomm := fun _ _ => D.hcomm _ _
  hraise := fun _ => D.hraise _
  hpresN := fun i => ker_stable_full ℳ D (Fin.castSucc i)
  hpresN' := fun _ => D.hpresN' _
  hfin :=
    subquotient_finite_transfer D.t D.hcomm (ker_stable_full ℳ D) D.hpresN'
      ker_annihilate
      (polyQuot_finite_of_le_numerator D.t D.hcomm (ker_stable_full ℳ D) D.hpresN D.hpresN'
        inf_le_left D.hfin)

/-- **Cokernel constructor.** From a length-`(r+1)` subquotient datum, the cokernel subquotient
`(N, N' ⊔ x·N)` of multiplication by `x = t (last)`, as a length-`r` datum on `t ∘ castSucc`. -/
noncomputable def SubquotientDatum.coker {r : ℕ} (D : SubquotientDatum ℳ (r + 1)) :
    SubquotientDatum ℳ r where
  N := D.N
  N' := D.N' ⊔ D.N.map (D.t (Fin.last r))
  hle := coker_le D.hle (D.hpresN (Fin.last r))
  hN := D.hN
  hN' := coker_isHomogeneous ℳ (D.hraise (Fin.last r)) D.hN D.hN'
  t := fun i => D.t (Fin.castSucc i)
  hcomm := fun _ _ => D.hcomm _ _
  hraise := fun _ => D.hraise _
  hpresN := fun _ => D.hpresN _
  hpresN' := fun i => coker_stable_full ℳ D (Fin.castSucc i)
  hfin :=
    subquotient_finite_transfer D.t D.hcomm D.hpresN (coker_stable_full ℳ D)
      coker_annihilate
      (polyQuot_finite_of_le_denominator D.t D.hcomm D.hpresN D.hpresN' (coker_stable_full ℳ D)
        le_sup_left D.hfin)

/-- Base-case finiteness: a module finite over `MvPolynomial σ κ` for an *empty* index `σ` —
in particular `σ = Fin 0`, the length-zero subquotient datum — is finite-dimensional over `κ`,
since `MvPolynomial σ κ ≃ₐ[κ] κ`. Project-local: the base case of the Stacks 00K1 induction.
Stated outside the `Datum` section as it needs no grading. -/
lemma finiteDimensional_of_mvPolynomial_isEmpty_finite
    {κ : Type*} [Field κ] {σ : Type*} [IsEmpty σ]
    {Q : Type*} [AddCommGroup Q] [Module κ Q]
    [Module (MvPolynomial σ κ) Q] [IsScalarTower κ (MvPolynomial σ κ) Q]
    [Module.Finite (MvPolynomial σ κ) Q] : FiniteDimensional κ Q := by
  haveI : Module.Finite κ (MvPolynomial σ κ) :=
    Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv κ σ).symm.toLinearEquiv
  exact Module.Finite.trans (MvPolynomial σ κ) Q

section Induction

variable [∀ n, FiniteDimensional κ ↥(ℳ n)]

/-- **Independence of images modulo the kernel.** If a family `g i` of submodules of `A` is
"independent modulo `ker π`" — every `a ∈ g i` that also lies in `ker π ⊔ ⨆ j ≠ i, g j` already
lies in `ker π` — then the images `π '' (g i)` form an `iSupIndep` family. The image family
inherits the degree-`i` separation of the `g i` once the kernel is quotiented out. Project-local:
the abstract lattice core of the base-case independence
(`lem:graded_subquotient_base_eventuallyZero`, Step 1), kept ring-agnostic so it can be applied to
the `κ`-linear quotient map `↥N ↠ N/N'`. -/
lemma iSupIndep_map_of_mem_ker_sup {F A Q : Type*} [Field F] [AddCommGroup A]
    [Module F A] [AddCommGroup Q] [Module F Q] (π : A →ₗ[F] Q) {ι : Type*} (g : ι → Submodule F A)
    (h : ∀ i, ∀ a ∈ g i, a ∈ LinearMap.ker π ⊔ ⨆ j, ⨆ (_ : j ≠ i), g j → a ∈ LinearMap.ker π) :
    iSupIndep (fun i => Submodule.map π (g i)) := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro q hq1 hq2
  obtain ⟨a, ha, rfl⟩ := hq1
  rw [show (⨆ j, ⨆ (_ : j ≠ i), Submodule.map π (g j))
      = Submodule.map π (⨆ j, ⨆ (_ : j ≠ i), g j) by simp_rw [Submodule.map_iSup]] at hq2
  obtain ⟨b, hb, hbq⟩ := hq2
  have ha' : a ∈ LinearMap.ker π ⊔ ⨆ j, ⨆ (_ : j ≠ i), g j := by
    have hab : a = (a - b) + b := by abel
    rw [hab]
    refine Submodule.add_mem_sup ?_ hb
    rw [LinearMap.mem_ker, map_sub, hbq, sub_self]
  exact (LinearMap.mem_ker).mp (h i a ha ha')

omit [∀ n, FiniteDimensional κ ↥(ℳ n)] in
/-- **Base case of the ambient subquotient induction.** A length-`0` subquotient datum has an
eventually-zero ambient Hilbert function: the subquotient `N/N'` is finite over
`MvPolynomial (Fin 0) κ ≃ κ`, hence finite-dimensional over `κ`, so its degreewise pieces — an
independent family inside the finite-dimensional quotient — vanish for large degree. -/
lemma subquotient_base_eventuallyZero (D : SubquotientDatum ℳ 0) :
    ∃ K, ∀ n, K < n → subquotientHilb ℳ D.N D.N' n = 0 := by
  classical
  letI := polyModule D.t D.hcomm
  haveI hts : IsScalarTower κ (MvPolynomial (Fin 0) κ) M := polyModule_isScalarTower D.t D.hcomm
  haveI := D.hfin
  -- the subquotient `Q = N/N'` is finite-dimensional over `κ`
  haveI hfd : FiniteDimensional κ (↥(polySubmodule D.t D.hcomm D.N D.hpresN) ⧸
      (polySubmodule D.t D.hcomm D.N' D.hpresN').comap
        (polySubmodule D.t D.hcomm D.N D.hpresN).subtype) :=
    finiteDimensional_of_mvPolynomial_isEmpty_finite (σ := Fin 0)
  set W : Submodule (MvPolynomial (Fin 0) κ) ↥(polySubmodule D.t D.hcomm D.N D.hpresN) :=
    (polySubmodule D.t D.hcomm D.N' D.hpresN').comap
      (polySubmodule D.t D.hcomm D.N D.hpresN).subtype with hW
  set Q := ↥(polySubmodule D.t D.hcomm D.N D.hpresN) ⧸ W with hQ
  -- the degreewise image map `ψ n : N ⊓ ℳ n →ₗ[κ] Q`, `m ↦ [m]`
  set ψ : ∀ n, ↥(D.N ⊓ ℳ n) →ₗ[κ] Q := fun n =>
    { toFun := fun m => Submodule.Quotient.mk ⟨(m : M), (Submodule.mem_inf.mp m.2).1⟩
      map_add' := fun a b => by rw [← Submodule.Quotient.mk_add]; rfl
      map_smul' := fun c a => by
        simp only [RingHom.id_apply, SetLike.val_smul]
        rw [← Submodule.Quotient.mk_smul]
        rfl } with hψ
  -- the ranges form an independent family in the finite-dimensional `Q`
  have hindep : iSupIndep (fun n => LinearMap.range (ψ n)) := by
    -- ROUTE (b): direct membership analysis, reading off the degree-`i` homogeneous component in
    -- the ambient `M` (never building an outgoing `κ`-linear map out of `Q`).
    -- *Core ambient fact.* A homogeneous element of degree `i` lying in `N' ⊔ ⨆_{j≠i} ℳ j` is in
    -- `N'`: its degree-`i` component is itself, equals the degree-`i` component of its `N'`-part
    -- (the `⨆_{j≠i} ℳ j`-part contributes `0` in degree `i`), and `N'` is homogeneous.
    have core : ∀ (i : ℕ) (x : M), x ∈ ℳ i →
        x ∈ D.N' ⊔ (⨆ j, ⨆ (_ : j ≠ i), ℳ j) → x ∈ D.N' := by
      intro i x hxi hxmem
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxmem
      set proj : M →ₗ[κ] M :=
        (ℳ i).subtype ∘ₗ (DirectSum.component κ ℕ (fun n => ℳ n) i) ∘ₗ
          (DirectSum.decomposeLinearEquiv ℳ).toLinearMap with hproj
      have hpe : ∀ m : M, proj m = ↑((DirectSum.decompose ℳ m) i) := fun m => rfl
      have hx_eq : proj x = x := by rw [hpe]; exact DirectSum.decompose_of_mem_same ℳ hxi
      have hu_pn : proj u ∈ D.N' := by
        rw [hpe]; exact (Submodule.IsHomogeneous.mem_iff ℳ D.hN').mp hu i
      have hv_zero : proj v = 0 := by
        have hker : (⨆ j, ⨆ (_ : j ≠ i), ℳ j) ≤ LinearMap.ker proj := by
          apply iSup_le; intro j; apply iSup_le; intro hji w hw
          rw [LinearMap.mem_ker, hpe]
          exact DirectSum.decompose_of_mem_ne ℳ hw hji
        exact (LinearMap.mem_ker).mp (hker hv)
      have hsum : proj x = proj u + proj v := by rw [← map_add, huv]
      rw [hx_eq, hv_zero, add_zero] at hsum
      rw [hsum]; exact hu_pn
    -- The `κ`-linear quotient map `Φ : ↥N ↠ Q = N/N'` (the un-restricted form of `ψ`).
    set Φ : ↥(D.N) →ₗ[κ] Q :=
      { toFun := fun c => Submodule.Quotient.mk ⟨(c : M), c.2⟩
        map_add' := fun a b => by rw [← Submodule.Quotient.mk_add]; rfl
        map_smul' := fun c a => by
          simp only [RingHom.id_apply, SetLike.val_smul]
          rw [← Submodule.Quotient.mk_smul]; rfl } with hΦ
    -- The lifted source pieces `g n ⊆ ↥N` corresponding to `N ⊓ ℳ n`.
    set g : ℕ → Submodule κ ↥(D.N) :=
      fun n => Submodule.comap D.N.subtype (D.N ⊓ ℳ n) with hg
    -- `range (ψ n) = map Φ (g n)`: `ψ n` is `Φ` precomposed with the inclusion of `N ⊓ ℳ n`.
    have hrange : ∀ n, (ψ n).range = Submodule.map Φ (g n) := by
      intro n
      have hcomp : ψ n = Φ ∘ₗ Submodule.inclusion (inf_le_left : D.N ⊓ ℳ n ≤ D.N) := by
        ext m; rfl
      rw [hcomp, LinearMap.range_comp, Submodule.range_inclusion]
    rw [show (fun n => (ψ n).range) = (fun n => Submodule.map Φ (g n)) from funext hrange]
    -- Apply the abstract independence-modulo-kernel lemma; discharge its hypothesis via `core`.
    apply iSupIndep_map_of_mem_ker_sup Φ g
    intro i a ha hmem
    have hai : (a : M) ∈ ℳ i := (Submodule.mem_inf.mp ((Submodule.mem_comap).mp ha)).2
    -- Push the `↥N`-level membership down to `M` along the subtype.
    have hpush : (a : M) ∈ D.N' ⊔ (⨆ j, ⨆ (_ : j ≠ i), ℳ j) := by
      have hle : Submodule.map D.N.subtype (LinearMap.ker Φ ⊔ ⨆ j, ⨆ (_ : j ≠ i), g j)
          ≤ D.N' ⊔ (⨆ j, ⨆ (_ : j ≠ i), ℳ j) := by
        rw [Submodule.map_sup]
        refine sup_le_sup ?_ ?_
        · rintro y ⟨c, hc, rfl⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker, hΦ] at hc
          simp only [LinearMap.coe_mk, AddHom.coe_mk] at hc
          rw [Submodule.Quotient.mk_eq_zero, hW, Submodule.mem_comap] at hc
          exact hc
        · rw [Submodule.map_iSup]
          refine iSup_mono fun j => ?_
          rw [Submodule.map_iSup]
          refine iSup_mono fun hji => ?_
          calc Submodule.map D.N.subtype (g j) ≤ D.N ⊓ ℳ j := Submodule.map_comap_le _ _
            _ ≤ ℳ j := inf_le_right
      exact hle ⟨a, hmem, rfl⟩
    have hmemN' : (a : M) ∈ D.N' := core i a hai hpush
    rw [LinearMap.mem_ker, hΦ]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Submodule.Quotient.mk_eq_zero, hW, Submodule.mem_comap]
    exact hmemN'
  haveI : _root_.IsNoetherian κ Q := isNoetherian_of_isNoetherianRing_of_finite κ Q
  have hfinset := Submodule.finite_ne_bot_of_iSupIndep hindep
  obtain ⟨K, hK⟩ := hfinset.bddAbove
  refine ⟨K, fun n hn => ?_⟩
  -- beyond `K`, `range (ψ n) = ⊥`, forcing `N ⊓ ℳ n ≤ N'`, hence the Hilbert value is `0`
  have hbot : LinearMap.range (ψ n) = ⊥ := by
    by_contra h
    exact absurd (hK h) (not_le.mpr hn)
  have hsub : D.N ⊓ ℳ n ≤ D.N' := by
    intro m hm
    have h0 : ψ n ⟨m, hm⟩ = 0 := by
      have hmem : ψ n ⟨m, hm⟩ ∈ LinearMap.range (ψ n) := LinearMap.mem_range_self _ _
      rw [hbot, Submodule.mem_bot] at hmem; exact hmem
    have h1 : (⟨m, (Submodule.mem_inf.mp hm).1⟩ :
        ↥(polySubmodule D.t D.hcomm D.N D.hpresN)) ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero]; exact h0
    rw [hW, Submodule.mem_comap] at h1
    exact h1
  have heq : D.N ⊓ ℳ n = D.N' ⊓ ℳ n :=
    le_antisymm (le_inf hsub inf_le_right) (inf_le_inf D.hle le_rfl)
  have hfr : Module.finrank κ ↥(D.N ⊓ ℳ n) = Module.finrank κ ↥(D.N' ⊓ ℳ n) := by rw [heq]
  simp only [subquotientHilb, hfr, sub_self, Int.cast_zero]

/-- **The ambient subquotient induction (Stacks 00K1).** The ambient Hilbert function of a
length-`r` subquotient datum is a rational Hilbert function of order `r`
(`lem:graded_subquotient_isRatHilb`). Induction on `r`: the base case is the eventually-zero
function; the step feeds the kernel/cokernel data (`SubquotientDatum.ker`, `.coker`) and the
degreewise difference identity into `IsRatHilb.ofDiffEq`. -/
lemma subquotient_hilbertSeries_rational :
    ∀ {r : ℕ} (D : SubquotientDatum ℳ r), IsRatHilb (SubquotientDatum.hilb ℳ D) r := by
  intro r
  induction r with
  | zero =>
      intro D
      obtain ⟨K, hK⟩ := subquotient_base_eventuallyZero ℳ D
      exact IsRatHilb.ofEventuallyZero K hK
  | succ r ih =>
      intro D
      have hx : RaisesDegree ℳ (D.t (Fin.last r)) := D.hraise _
      refine IsRatHilb.ofDiffEq (N := 0) (ih (SubquotientDatum.coker ℳ D))
        (ih (SubquotientDatum.ker ℳ D)) ?_
      intro n _
      change subquotientHilb ℳ D.N D.N' (n + 1) - subquotientHilb ℳ D.N D.N' n
        = subquotientHilb ℳ D.N (D.N' ⊔ D.N.map (D.t (Fin.last r))) (n + 1)
          - subquotientHilb ℳ (D.N ⊓ (D.N').comap (D.t (Fin.last r))) D.N' n
      exact subquotient_degreewise_diff ℳ hx D.hN D.hN' n

end Induction

end Datum

end GradedModule

/-- **Graded Hilbert–Serre: rationality of the Hilbert series** (`lem:gradedHilbertSerre_rational`).
For a graded `κ`-module `M = ⨁ ℳ n` with finite-dimensional components, equipped with `r`
pairwise-commuting degree-one endomorphisms (the degree-one generators of the action) for which `M`
is finite over the free polynomial ring `MvPolynomial (Fin r) κ`, the Hilbert function
`n ↦ dim_κ ℳ n` is a rational Hilbert function of order `r`: there are `p ∈ ℚ[X]` and `N` with
`dim_κ ℳ n = [Xⁿ](p · (1 - X)⁻ʳ)` for all `n > N`. This is the substantive (non-Mathlib) half of
graded Hilbert–Serre; it is obtained from the ambient subquotient induction
(`GradedModule.subquotient_hilbertSeries_rational`) applied to the top datum `(⊤, ⊥)`. -/
lemma gradedModule_hilbertSeries_rational {κ M : Type*} [Field κ] [AddCommGroup M] [Module κ M]
    (ℳ : ℕ → Submodule κ M) [DirectSum.Decomposition ℳ] [∀ n, FiniteDimensional κ ↥(ℳ n)]
    {r : ℕ} (t : Fin r → Module.End κ M) (hcomm : ∀ i j, Commute (t i) (t j))
    (hraise : ∀ i, GradedModule.RaisesDegree ℳ (t i))
    (hfin : letI := GradedModule.polyModule t hcomm
      Module.Finite (MvPolynomial (Fin r) κ) M) :
    IsRatHilb (fun n => (Module.finrank κ ↥(ℳ n) : ℚ)) r := by
  letI := GradedModule.polyModule t hcomm
  haveI := hfin
  -- the top datum `(⊤, ⊥)`: its finiteness is exactly `M` finite over the polynomial ring
  have hfintop : Module.Finite (MvPolynomial (Fin r) κ)
      (↥(GradedModule.polySubmodule t hcomm ⊤ (fun _ => le_top)) ⧸
        (GradedModule.polySubmodule t hcomm ⊥ (fun _ => by rw [Submodule.map_bot])).comap
          (GradedModule.polySubmodule t hcomm ⊤ (fun _ => le_top)).subtype) := by
    refine Module.Finite.of_surjective
      ({ toFun := fun m => Submodule.Quotient.mk ⟨m, Submodule.mem_top⟩
         map_add' := fun a b => by rw [← Submodule.Quotient.mk_add]; rfl
         map_smul' := fun c a => by rw [← Submodule.Quotient.mk_smul]; rfl } :
        M →ₗ[MvPolynomial (Fin r) κ] _) ?_
    intro z
    refine Submodule.Quotient.induction_on _ z (fun y => ⟨(y : M), rfl⟩)
  set D : GradedModule.SubquotientDatum ℳ r :=
    { N := ⊤
      N' := ⊥
      hle := bot_le
      hN := by intro i x _; exact Submodule.mem_top
      hN' := by intro i x hx; rw [Submodule.mem_bot] at hx; subst hx; simp
      t := t
      hcomm := hcomm
      hraise := hraise
      hpresN := fun _ => le_top
      hpresN' := fun _ => by rw [Submodule.map_bot]
      hfin := hfintop } with hD
  have hrat := GradedModule.subquotient_hilbertSeries_rational ℳ D
  have heq : GradedModule.SubquotientDatum.hilb ℳ D
      = fun n => (Module.finrank κ ↥(ℳ n) : ℚ) := by
    funext n
    change (((Module.finrank κ ↥((⊤ : Submodule κ M) ⊓ ℳ n) : ℤ)
        - (Module.finrank κ ↥((⊥ : Submodule κ M) ⊓ ℳ n) : ℤ) : ℤ) : ℚ)
      = (Module.finrank κ ↥(ℳ n) : ℚ)
    rw [top_inf_eq, bot_inf_eq, finrank_bot]
    simp
  rwa [heq] at hrat

end AlgebraicGeometry
