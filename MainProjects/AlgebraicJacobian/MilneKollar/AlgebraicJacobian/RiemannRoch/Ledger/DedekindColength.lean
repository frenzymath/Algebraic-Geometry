/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Colength bricks: finrank additivity in exact sequences and Dedekind prime-power quotients

This file collects two self-contained pieces of pure linear / commutative algebra that feed the
Riemann–Roch and divisor lanes of the Algebraic Jacobian rebuild.  Nothing here mentions schemes
or sheaves; everything is stated for modules over a field `k` and for a Dedekind domain `B`.

## Deliverable 1 — finrank is additive along exact sequences

* `AlgebraicGeometry.finrank_add_of_exact` — for a short exact sequence
  `0 → A → B → C → 0` of finite-dimensional `k`-vector spaces,
  `finrank k B = finrank k A + finrank k C`.
* `AlgebraicGeometry.finrank_alt_sum_eq_zero_of_exact₅` — for a five-term exact sequence
  `0 → V₁ → V₂ → V₃ → V₄ → V₅ → 0`, the alternating sum of finranks vanishes in `ℤ`:
  `finrank V₁ - finrank V₂ + finrank V₃ - finrank V₄ + finrank V₅ = 0`.

The two-term statement is a thin wrapper around `Module.length_eq_add_of_exact` bridged to
`finrank` through `Module.length_eq_finrank`; the five-term statement is proved directly from
rank–nullity (`LinearMap.finrank_range_add_finrank_ker`) together with the identification of
kernels and ranges supplied by `Function.Exact`.

## Deliverable 2 — Dedekind prime-power colength

* `AlgebraicGeometry.finrank_quotSucc_jump` — the one-step filtration jump: for a principal ideal
  `I = (π) ≠ 0`, multiplication by `π ^ n` induces a `k`-linear isomorphism
  `(B ⧸ I) ≃ₗ[k] (I ^ n ⧸ I • ⊤)`, hence `finrank k (I ^ n ⧸ I • ⊤) = finrank k (B ⧸ I)`.
* `AlgebraicGeometry.finrank_quotient_span_pow` — the DVR/local colength formula
  `finrank k (B ⧸ I ^ e) = e • finrank k (B ⧸ I)` for a principal ideal `I ≠ 0`.
* `AlgebraicGeometry.finrank_quotient_eq_sum_factors_pow` — the multi-prime reduction: via the
  Chinese remainder theorem, `finrank k (B ⧸ I) = ∑_P finrank k (B ⧸ P ^ (mult of P in I))`,
  the sum ranging over the prime factors of a nonzero ideal `I` of the Dedekind domain `B`.
* `AlgebraicGeometry.finrank_quotient_span_eq_sum_ord` — the ord-weighted form
  `finrank k (B ⧸ (f)) = ∑_P (ord_P f) • finrank k (B ⧸ P)`, obtained from the previous two when
  the prime factors of `(f)` are principal (e.g. `B` a PID).

## References

* rank–nullity and length additivity: `Mathlib.RingTheory.Length`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`;
* principal prime-power quotients: `Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient`.
-/

set_option autoImplicit false

open Module (finrank length)

namespace AlgebraicGeometry

/-! ### Deliverable 1: finrank additivity in exact sequences -/

/-- **Additivity of `finrank` along a short exact sequence.**
For a short exact sequence of finite-dimensional `k`-vector spaces
`0 → A →f B →g C → 0` (`f` injective, `g` surjective, `Function.Exact f g`),
the dimension of the middle term is the sum of the outer dimensions:
`finrank k B = finrank k A + finrank k C`. -/
theorem finrank_add_of_exact
    {k A B C : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    [Module.Finite k A] [Module.Finite k B] [Module.Finite k C]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    finrank k B = finrank k A + finrank k C := by
  have hlen := Module.length_eq_add_of_exact f g hf hg hfg
  rw [Module.length_eq_finrank, Module.length_eq_finrank, Module.length_eq_finrank] at hlen
  exact_mod_cast hlen

/-- **Vanishing of the alternating sum of finranks along a five-term exact sequence.**
Given an exact sequence of finite-dimensional `k`-vector spaces
`0 → V₁ →f₁ V₂ →f₂ V₃ →f₃ V₄ →f₄ V₅ → 0`
(with `f₁` injective and `f₄` surjective), the alternating sum of dimensions vanishes in `ℤ`. -/
theorem finrank_alt_sum_eq_zero_of_exact₅
    {k V₁ V₂ V₃ V₄ V₅ : Type*} [Field k]
    [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    [AddCommGroup V₄] [Module k V₄] [AddCommGroup V₅] [Module k V₅]
    [Module.Finite k V₁] [Module.Finite k V₂] [Module.Finite k V₃] [Module.Finite k V₄]
    [Module.Finite k V₅]
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (h₁ : Function.Injective f₁) (e₁ : Function.Exact f₁ f₂) (e₂ : Function.Exact f₂ f₃)
    (e₃ : Function.Exact f₃ f₄) (h₄ : Function.Surjective f₄) :
    (finrank k V₁ : ℤ) - finrank k V₂ + finrank k V₃ - finrank k V₄ + finrank k V₅ = 0 := by
  -- Rank–nullity for each of the four maps.
  have rn₁ := LinearMap.finrank_range_add_finrank_ker f₁
  have rn₂ := LinearMap.finrank_range_add_finrank_ker f₂
  have rn₃ := LinearMap.finrank_range_add_finrank_ker f₃
  have rn₄ := LinearMap.finrank_range_add_finrank_ker f₄
  -- Left end: `f₁` injective ⇒ its kernel is trivial.
  have hk₁ : finrank k (LinearMap.ker f₁) = 0 := by
    rw [LinearMap.ker_eq_bot.2 h₁, finrank_bot]
  -- Exactness rewrites successive kernels as ranges.
  have ke₁ : finrank k (LinearMap.ker f₂) = finrank k (LinearMap.range f₁) := by
    rw [e₁.linearMap_ker_eq]
  have ke₂ : finrank k (LinearMap.ker f₃) = finrank k (LinearMap.range f₂) := by
    rw [e₂.linearMap_ker_eq]
  have ke₃ : finrank k (LinearMap.ker f₄) = finrank k (LinearMap.range f₃) := by
    rw [e₃.linearMap_ker_eq]
  -- Right end: `f₄` surjective ⇒ its range is everything.
  have hr₄ : finrank k (LinearMap.range f₄) = finrank k V₅ := by
    rw [LinearMap.range_eq_top.2 h₄, finrank_top]
  omega

/-! ### Deliverable 2: Dedekind prime-power colength -/

section PrimePower

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]

/-- **One-step filtration jump.**  For a nonzero principal ideal `I = (π)`, multiplication by
`π ^ n` induces a `B`-linear (hence `k`-linear) isomorphism `B ⧸ I ≃ I ^ n ⧸ I • ⊤`, so the two
quotients have the same `k`-dimension. -/
theorem finrank_quotSucc_jump {I : Ideal B} (h : I.IsPrincipal) (h' : I ≠ ⊥) (n : ℕ)
    [Module.Finite k (B ⧸ I)] :
    finrank k ((I ^ n : Ideal B) ⧸ (I • ⊤ : Submodule B (I ^ n : Ideal B))) = finrank k (B ⧸ I) :=
  ((Ideal.quotEquivPowQuotPowSucc h h' n).restrictScalars k).finrank_eq.symm

/-- The `k`-linear iso `B ⧸ I ≃ₗ[k] I ^ n ⧸ I ^ (n+1)`, realised as the image ideal
`(I ^ n).map (mk (I ^ (n+1)))` inside `B ⧸ I ^ (n+1)`. -/
noncomputable def quotEquivMapPow {I : Ideal B} (h : I.IsPrincipal) (h' : I ≠ ⊥) (n : ℕ) :
    (B ⧸ I) ≃ₗ[k] (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)) :=
  ((Ideal.quotEquivPowQuotPowSucc h h' n).trans
    (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I n)).restrictScalars k

/-- **Inductive step of the colength formula.**  For a nonzero principal ideal `I`,
`finrank k (B ⧸ I ^ (n+1)) = finrank k (B ⧸ I) + finrank k (B ⧸ I ^ n)`. -/
theorem finrank_quotient_pow_succ {I : Ideal B} (h : I.IsPrincipal) (h' : I ≠ ⊥) (n : ℕ)
    [Module.Finite k (B ⧸ I ^ (n + 1))] [Module.Finite k (B ⧸ I ^ n)] :
    finrank k (B ⧸ I ^ (n + 1)) = finrank k (B ⧸ I) + finrank k (B ⧸ I ^ n) := by
  have hle : I ^ (n + 1) ≤ I ^ n := Ideal.pow_le_pow_right n.le_succ
  -- The natural surjection `B ⧸ I ^ (n+1) → B ⧸ I ^ n`.
  set g : (B ⧸ I ^ (n + 1)) →ₗ[k] (B ⧸ I ^ n) :=
    (Ideal.Quotient.factorₐ k hle).toLinearMap with hg_def
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective hle
  -- Its kernel, as a `k`-submodule, is the image ideal `(I ^ n).map (mk (I ^ (n+1)))`.
  have hker : LinearMap.ker g =
      Submodule.restrictScalars k (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)) := by
    apply SetLike.ext
    intro x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, hg_def, AlgHom.toLinearMap_apply,
      Ideal.Quotient.factorₐ_apply, ← RingHom.mem_ker, Ideal.Quotient.factor_ker hle]
  -- The middle term splits as kernel plus image.
  have hsplit := finrank_add_of_exact (LinearMap.ker g).subtype g
    (Submodule.subtype_injective _) hg (LinearMap.exact_subtype_ker_map g)
  -- The kernel has the dimension of `B ⧸ I` via the filtration jump.
  have hkerdim : finrank k (LinearMap.ker g) = finrank k (B ⧸ I) := by
    rw [hker]
    exact ((quotEquivMapPow h h' n).finrank_eq.symm)
  rw [hsplit, hkerdim]

/-- Auxiliary induction for `finrank_quotient_span_pow`, threading finiteness explicitly. -/
private theorem finrank_quotient_span_pow_aux {I : Ideal B} (h : I.IsPrincipal) (h' : I ≠ ⊥) :
    ∀ e : ℕ, Module.Finite k (B ⧸ I ^ e) → finrank k (B ⧸ I ^ e) = e • finrank k (B ⧸ I) := by
  intro e
  induction e with
  | zero =>
    intro _
    rw [zero_smul, pow_zero, Ideal.one_eq_top]
    haveI : Subsingleton (B ⧸ (⊤ : Ideal B)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  | succ n ih =>
    intro hfin
    haveI := hfin
    haveI hfin_n : Module.Finite k (B ⧸ I ^ n) :=
      Module.Finite.of_surjective
        (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (I := I) n.le_succ)).toLinearMap
        (fun y => by
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
          exact ⟨Ideal.Quotient.mk _ x, rfl⟩)
    rw [finrank_quotient_pow_succ h h' n, ih hfin_n, succ_nsmul, add_comm]

/-- **Prime-power / DVR colength formula.**  For a nonzero principal ideal `I = (π)` in `B`
whose quotient `B ⧸ I ^ e` is finite over the base field `k`, the `k`-dimension of `B ⧸ I ^ e`
is `e` copies of the residue dimension: `finrank k (B ⧸ I ^ e) = e • finrank k (B ⧸ I)`. -/
theorem finrank_quotient_span_pow {I : Ideal B} (h : I.IsPrincipal) (h' : I ≠ ⊥) (e : ℕ)
    [Module.Finite k (B ⧸ I ^ e)] :
    finrank k (B ⧸ I ^ e) = e • finrank k (B ⧸ I) :=
  finrank_quotient_span_pow_aux h h' e inferInstance

end PrimePower

/-! ### Deliverable 2 (continued): the multi-prime colength sum -/

section MultiPrime

open UniqueFactorizationMonoid

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra k B]

/-- The Chinese remainder theorem for a Dedekind domain, upgraded to a `k`-algebra equivalence:
`B ⧸ I ≃ₐ[k] ∏_P B ⧸ P ^ (mult of P in I)`. -/
noncomputable def quotAlgEquivPiFactors {I : Ideal B} (hI : I ≠ ⊥) :
    (B ⧸ I) ≃ₐ[k]
      (∀ P : (factors I).toFinset,
        B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (factors I)) :=
  AlgEquiv.ofRingEquiv (f := IsDedekindDomain.quotientEquivPiFactors hI) fun x => by
    rw [IsScalarTower.algebraMap_apply k B (B ⧸ I), Ideal.Quotient.algebraMap_eq,
      IsDedekindDomain.quotientEquivPiFactors_mk]
    funext P
    rw [Pi.algebraMap_apply,
      IsScalarTower.algebraMap_apply k B
        (B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (factors I)),
      Ideal.Quotient.algebraMap_eq]

/-- **Multi-prime colength via the Chinese remainder theorem.**  For a nonzero ideal `I` of a
Dedekind domain `B`, finite over the base field `k`, the `k`-dimension of `B ⧸ I` is the sum,
over the prime factors `P` of `I`, of the `k`-dimensions of the prime-power quotients
`B ⧸ P ^ (mult of P in I)`. -/
theorem finrank_quotient_eq_sum_factors_pow {I : Ideal B} (hI : I ≠ ⊥)
    [∀ P : (factors I).toFinset,
        Module.Finite k (B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (factors I))] :
    finrank k (B ⧸ I) =
      ∑ P : (factors I).toFinset,
        finrank k (B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (factors I)) := by
  rw [(quotAlgEquivPiFactors hI).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

/-- **Dedekind colength formula (ord-weighted form).**  For `f ≠ 0` in a Dedekind domain `B`
whose height-one-prime factors are principal (e.g. `B` a PID) and whose prime-power residues are
finite over the base field `k`, the `k`-dimension of `B ⧸ (f)` is
`∑_P (ord_P f) • finrank k (B ⧸ P)`, the sum ranging over the prime factors of `(f)` with
`ord_P f` the multiplicity of `P` in the factorization. -/
theorem finrank_quotient_span_eq_sum_ord {f : B} (hf : f ≠ 0)
    (hprin : ∀ P : (factors (Ideal.span {f})).toFinset, (P : Ideal B).IsPrincipal)
    [∀ P : (factors (Ideal.span {f})).toFinset,
        Module.Finite k
          (B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (factors (Ideal.span {f})))] :
    finrank k (B ⧸ Ideal.span {f}) =
      ∑ P : (factors (Ideal.span {f})).toFinset,
        Multiset.count (P : Ideal B) (factors (Ideal.span {f})) •
          finrank k (B ⧸ (P : Ideal B)) := by
  have hI : Ideal.span {f} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [finrank_quotient_eq_sum_factors_pow hI]
  refine Finset.sum_congr rfl fun P _ => ?_
  have hPne : (P : Ideal B) ≠ ⊥ :=
    (prime_of_factor _ (Multiset.mem_toFinset.mp P.2)).ne_zero
  exact finrank_quotient_span_pow (hprin P) hPne _

end MultiPrime

end AlgebraicGeometry
