/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# The two-lattice finiteness lemma over Laurent polynomials

Let `k` be a commutative ring and `N` a module over the Laurent polynomial ring `k[T;T⁻¹]`.
Suppose `Q₀ Q₁ : Submodule k N` satisfy:

* `Q₀` is stable under multiplication by `T` and contains a finite set spanning `N`
  over `k[T;T⁻¹]`;
* `Q₁` is stable under multiplication by `T⁻¹`, and every element of `N` lands in `Q₁`
  after multiplication by a sufficiently negative power of `T`.

Then the quotient `N ⧸ (Q₀ ⊔ Q₁)` is a finite `k`-module
(`LaurentPolynomial.moduleFinite_quotient_sup_of_span_eq_top`).

The proof is the classical monomial ladder: pick a uniform `M` with `T ^ (-M) • xᵢ ∈ Q₁` for
the finitely many generators `xᵢ`; then `T ^ j • xᵢ` lies in `Q₀` for `j ≥ 0`, in `Q₁` for
`j ≤ -M`, and only the finite window `-M < j < 0` survives modulo `Q₀ + Q₁`.

This is the pure-algebra engine behind the finiteness of the coherent cohomology
`H¹(C, 𝒪_C)` of a curve `C` equipped with a finite morphism `π : C ⟶ ℙ¹`: apply it to
`N = Γ(π⁻¹D₊(x₀) ⊓ π⁻¹D₊(x₁))` with `Q₀, Q₁` the images of the sections over the two chart
preimages, so that `N ⧸ (Q₀ ⊔ Q₁)` computes `H¹` by Mayer–Vietoris.

## Main results

* `LaurentPolynomial.moduleFinite_quotient_sup_of_span_eq_top`: the keystone, with the
  first lattice hypothesis given by an explicit finite spanning set inside `Q₀`.
* `LaurentPolynomial.moduleFinite_quotient_sup_of_exists_smul_mem`: the symmetric
  localization form: both lattice hypotheses phrased as "surjectivity up to powers of `T`"
  (`∀ n, ∃ m, T ^ m • n ∈ Q₀` and `∀ n, ∃ m, T ^ (-m) • n ∈ Q₁`), given
  `Module.Finite k[T;T⁻¹] N`.
* `LaurentPolynomial.moduleFinite_quotient_sup_of_exists_pow_smul_mem`: the same, with the
  power hypotheses phrased via `T 1 ^ m` and `T (-1) ^ m`, the exact output shape of
  `IsLocalization.Away` surjectivity-up-to-powers statements.

## Implementation notes

The keystone requires only that the finite spanning set is *contained* in `Q₀` — not that it
generates `Q₀` over `k[T]`. This is deliberately weaker than the textbook statement and lets
the localization form dispense with any module-finiteness hypothesis on `Q₀` itself: a finite
`k[T;T⁻¹]`-generating set of `N` can be pushed into `Q₀` by clearing denominators.

No field hypothesis is needed anywhere: `k` is an arbitrary commutative ring.
-/

universe u v

open Submodule

namespace LaurentPolynomial

variable {k : Type u} [CommRing k] {N : Type v} [AddCommGroup N]
variable [Module k[T;T⁻¹] N] [Module k N] [IsScalarTower k k[T;T⁻¹] N]

/- A `k`-submodule stable under the action of a scalar `r` is stable under `r ^ m`. -/
omit [Module k[T;T⁻¹] N] [IsScalarTower k k[T;T⁻¹] N] in
private theorem pow_smul_mem {S : Type*} [Monoid S] [MulAction S N] {Q : Submodule k N}
    {r : S} (hr : ∀ x ∈ Q, r • x ∈ Q) {x : N} (hx : x ∈ Q) : ∀ m : ℕ, r ^ m • x ∈ Q
  | 0 => by simpa using hx
  | m + 1 => by
    rw [pow_succ', mul_smul]
    exact hr _ (pow_smul_mem hr hx m)

omit [IsScalarTower k k[T;T⁻¹] N] in
/-- A `k`-submodule of a `k[T;T⁻¹]`-module stable under the action of `T` is stable under
every nonnegative power of `T`. -/
theorem T_natCast_smul_mem {Q : Submodule k N} (hQ : ∀ x ∈ Q, (T 1 : k[T;T⁻¹]) • x ∈ Q)
    {x : N} (hx : x ∈ Q) (m : ℕ) : (T (m : ℤ) : k[T;T⁻¹]) • x ∈ Q := by
  have h : (T (m : ℤ) : k[T;T⁻¹]) = T 1 ^ m := by rw [T_pow, mul_one]
  rw [h]
  exact pow_smul_mem hQ hx m

omit [IsScalarTower k k[T;T⁻¹] N] in
/-- A `k`-submodule of a `k[T;T⁻¹]`-module stable under the action of `T⁻¹` is stable under
every negative power of `T`. -/
theorem T_neg_natCast_smul_mem {Q : Submodule k N} (hQ : ∀ x ∈ Q, (T (-1) : k[T;T⁻¹]) • x ∈ Q)
    {x : N} (hx : x ∈ Q) (m : ℕ) : (T (-(m : ℤ)) : k[T;T⁻¹]) • x ∈ Q := by
  have h : (T (-(m : ℤ)) : k[T;T⁻¹]) = T (-1) ^ m := by rw [T_pow, mul_neg_one]
  rw [h]
  exact pow_smul_mem hQ hx m

/-- **The two-lattice lemma**, spanning-set form. Let `N` be a module over the Laurent
polynomial ring `k[T;T⁻¹]` and let `Q₀ Q₁ : Submodule k N` be such that

* `Q₀` is stable under `T` and contains a finite set `s` spanning `N` over `k[T;T⁻¹]`;
* `Q₁` is stable under `T⁻¹` and every element of `N` lands in `Q₁` after multiplication
  by a sufficiently negative power of `T`.

Then `N ⧸ (Q₀ ⊔ Q₁)` is a finite `k`-module: it is spanned by the classes of the monomials
`T j • x` for `x ∈ s` and `-M < j < 0`, where `M` is a uniform bound with
`T (-M) • x ∈ Q₁` for all `x ∈ s`. -/
theorem moduleFinite_quotient_sup_of_span_eq_top {Q₀ Q₁ : Submodule k N} {s : Finset N}
    (hsQ₀ : ∀ x ∈ s, x ∈ Q₀)
    (hs : span k[T;T⁻¹] (s : Set N) = ⊤)
    (hQ₀ : ∀ x ∈ Q₀, (T 1 : k[T;T⁻¹]) • x ∈ Q₀)
    (hQ₁ : ∀ x ∈ Q₁, (T (-1) : k[T;T⁻¹]) • x ∈ Q₁)
    (hQ₁loc : ∀ n : N, ∃ m : ℕ, (T (-(m : ℤ)) : k[T;T⁻¹]) • n ∈ Q₁) :
    Module.Finite k (N ⧸ (Q₀ ⊔ Q₁)) := by
  classical
  -- Choose a uniform denominator bound `M` for the generators.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ x ∈ s, (T (-(M : ℤ)) : k[T;T⁻¹]) • x ∈ Q₁ := by
    choose μ hμ using hQ₁loc
    refine ⟨s.sup μ, fun x hx => ?_⟩
    have hle : μ x ≤ s.sup μ := Finset.le_sup hx
    have h1 : -((s.sup μ : ℕ) : ℤ) = -((s.sup μ - μ x : ℕ) : ℤ) + -(μ x : ℤ) := by omega
    rw [h1, T_add, mul_smul]
    exact T_neg_natCast_smul_mem hQ₁ (hμ x) _
  -- The finite window of monomials that survives modulo `Q₀ ⊔ Q₁`.
  set F : Finset N := (Finset.Ioo (-(M : ℤ)) 0 ×ˢ s).image fun p => (T p.1 : k[T;T⁻¹]) • p.2
    with hF
  -- The monomial ladder: every monomial multiple of a generator lies in
  -- `Q₀ ⊔ Q₁ ⊔ span k F`, by cases on the exponent.
  have window : ∀ x ∈ s, ∀ j : ℤ, (T j : k[T;T⁻¹]) • x ∈ Q₀ ⊔ Q₁ ⊔ span k (F : Set N) := by
    intro x hx j
    rcases le_or_gt 0 j with hj | hj
    · -- `j ≥ 0`: the monomial lies in `Q₀`.
      lift j to ℕ using hj
      exact mem_sup_left (mem_sup_left (T_natCast_smul_mem hQ₀ (hsQ₀ x hx) j))
    rcases le_or_gt j (-(M : ℤ)) with hjM | hjM
    · -- `j ≤ -M`: the monomial lies in `Q₁`.
      obtain ⟨d, rfl⟩ : ∃ d : ℕ, j = -(d : ℤ) + -(M : ℤ) := ⟨(-j - M).toNat, by omega⟩
      rw [T_add, mul_smul]
      exact mem_sup_left (mem_sup_right (T_neg_natCast_smul_mem hQ₁ (hM x hx) d))
    · -- `-M < j < 0`: the monomial lies in the finite window.
      refine mem_sup_right (subset_span ?_)
      rw [hF]
      exact Finset.mem_coe.mpr <| Finset.mem_image.mpr
        ⟨(j, x), Finset.mem_product.mpr ⟨Finset.mem_Ioo.mpr ⟨hjM, hj⟩, hx⟩, rfl⟩
  -- Upgrade from monomials to arbitrary Laurent polynomial coefficients.
  have hsmul : ∀ x ∈ s, ∀ f : k[T;T⁻¹], f • x ∈ Q₀ ⊔ Q₁ ⊔ span k (F : Set N) := by
    intro x hx f
    induction f using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      rw [add_smul]
      exact add_mem hp hq
    | C_mul_T n a =>
      rw [mul_smul, C_eq_algebraMap, algebraMap_smul]
      exact Submodule.smul_mem _ a (window x hx n)
  -- Hence the three-part sup is all of `N`.
  have hW : Q₀ ⊔ Q₁ ⊔ span k (F : Set N) = ⊤ := by
    rw [eq_top_iff]
    rintro n -
    have hn : n ∈ span k[T;T⁻¹] (s : Set N) := by rw [hs]; exact mem_top
    obtain ⟨f, -, rfl⟩ := mem_span_finset.mp hn
    exact sum_mem fun x hx => hsmul x hx (f x)
  -- So the image of the finite window spans the quotient.
  refine Module.finite_def.mpr ⟨F.image (Q₀ ⊔ Q₁).mkQ, ?_⟩
  rw [Finset.coe_image, span_image, map_mkQ_eq_top]
  exact hW

/-- **The two-lattice lemma**, localization form. Let `N` be a finite module over the Laurent
polynomial ring `k[T;T⁻¹]` and let `Q₀ Q₁ : Submodule k N` be such that

* `Q₀` is stable under `T` and every element of `N` lands in `Q₀` after multiplication by a
  sufficiently large power of `T`;
* `Q₁` is stable under `T⁻¹` and every element of `N` lands in `Q₁` after multiplication by a
  sufficiently negative power of `T`.

Then `N ⧸ (Q₀ ⊔ Q₁)` is a finite `k`-module.

The hypotheses on `Q₀` and `Q₁` are exactly the "surjectivity up to powers" statements
furnished by `IsLocalization.Away` when `N` is the sections of a scheme on an intersection of
two affine opens and `Q₀`, `Q₁` are the images of the restriction maps; see also
`moduleFinite_quotient_sup_of_exists_pow_smul_mem` for the variant phrased via `T 1 ^ m`. -/
theorem moduleFinite_quotient_sup_of_exists_smul_mem [Module.Finite k[T;T⁻¹] N]
    {Q₀ Q₁ : Submodule k N}
    (hQ₀ : ∀ x ∈ Q₀, (T 1 : k[T;T⁻¹]) • x ∈ Q₀)
    (hQ₁ : ∀ x ∈ Q₁, (T (-1) : k[T;T⁻¹]) • x ∈ Q₁)
    (hQ₀loc : ∀ n : N, ∃ m : ℕ, (T (m : ℤ) : k[T;T⁻¹]) • n ∈ Q₀)
    (hQ₁loc : ∀ n : N, ∃ m : ℕ, (T (-(m : ℤ)) : k[T;T⁻¹]) • n ∈ Q₁) :
    Module.Finite k (N ⧸ (Q₀ ⊔ Q₁)) := by
  classical
  -- Push a finite `k[T;T⁻¹]`-generating set of `N` into `Q₀` by clearing denominators.
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := k[T;T⁻¹]) (M := N)
  choose μ hμ using hQ₀loc
  refine moduleFinite_quotient_sup_of_span_eq_top
    (s := t.image fun n => (T (μ n : ℤ) : k[T;T⁻¹]) • n) ?_ ?_ hQ₀ hQ₁ hQ₁loc
  · intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hx
    exact hμ n
  · rw [eq_top_iff, ← ht]
    refine span_le.mpr fun n hn => ?_
    have hmem : (T (μ n : ℤ) : k[T;T⁻¹]) • n ∈
        span k[T;T⁻¹] ((t.image fun n => (T (μ n : ℤ) : k[T;T⁻¹]) • n : Finset N) : Set N) :=
      subset_span <| Finset.mem_coe.mpr <| Finset.mem_image_of_mem _ (Finset.mem_coe.mp hn)
    have hcancel : (T (-(μ n : ℤ)) : k[T;T⁻¹]) • ((T (μ n : ℤ) : k[T;T⁻¹]) • n) = n := by
      rw [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
    exact hcancel ▸ Submodule.smul_mem _ (T (-(μ n : ℤ))) hmem

/-- **The two-lattice lemma**, localization form with the "surjectivity up to powers"
hypotheses phrased via powers of `T 1` and `T (-1)` — the exact output shape of
`IsLocalization.Away`-style statements after transport to `k[T;T⁻¹]`.
See `moduleFinite_quotient_sup_of_exists_smul_mem`. -/
theorem moduleFinite_quotient_sup_of_exists_pow_smul_mem [Module.Finite k[T;T⁻¹] N]
    {Q₀ Q₁ : Submodule k N}
    (hQ₀ : ∀ x ∈ Q₀, (T 1 : k[T;T⁻¹]) • x ∈ Q₀)
    (hQ₁ : ∀ x ∈ Q₁, (T (-1) : k[T;T⁻¹]) • x ∈ Q₁)
    (hQ₀loc : ∀ n : N, ∃ m : ℕ, ((T 1 : k[T;T⁻¹]) ^ m) • n ∈ Q₀)
    (hQ₁loc : ∀ n : N, ∃ m : ℕ, ((T (-1) : k[T;T⁻¹]) ^ m) • n ∈ Q₁) :
    Module.Finite k (N ⧸ (Q₀ ⊔ Q₁)) := by
  refine moduleFinite_quotient_sup_of_exists_smul_mem hQ₀ hQ₁ (fun n => ?_) (fun n => ?_)
  · obtain ⟨m, hm⟩ := hQ₀loc n
    exact ⟨m, by rwa [T_pow, mul_one] at hm⟩
  · obtain ⟨m, hm⟩ := hQ₁loc n
    exact ⟨m, by rwa [T_pow, mul_neg_one] at hm⟩

end LaurentPolynomial
