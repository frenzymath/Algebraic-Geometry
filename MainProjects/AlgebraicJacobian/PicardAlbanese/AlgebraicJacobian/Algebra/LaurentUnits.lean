/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# The units of a Laurent polynomial ring over a domain (mathlib supplement)

`R[T;T⁻¹]ˣ = Rˣ × ℤ` when `R` is a domain: every unit is `C c * T n` with `c` a unit of `R`,
and the exponent `n` is determined.  **Mathlib does not have this.**  The whole `IsUnit` API
of `Mathlib/Algebra/Polynomial/Laurent.lean` is the single lemma
`LaurentPolynomial.isUnit_T` (measured: `loogle` for `LaurentPolynomial, IsUnit` returns only
that, `(LaurentPolynomial ?R)ˣ` returns nothing, and `grep` of the mathlib file confirms one
`IsUnit` declaration).  The polynomial analogue `Polynomial.isUnit_iff` *is* in mathlib; the
Laurent case is missing because `T (-1)` is a unit, so there is no degree-zero argument.

## Why this is here

It is the multiplicative half of the `ℙ¹` chart data.  `Curve/P1Charts.lean` identifies the
overlap ring of the two standard charts with `LaurentPolynomial k` and provides the *additive*
Laurent span (`exists_res_add_res`), which is what computes `H¹(ℙ¹, 𝒪)`.  Computing
`Pic(ℙ¹)` instead needs the *unit group* of that same overlap ring modulo the images of the two
chart unit groups, and `Rˣ × ℤ` modulo `Rˣ` on each side is where the `ℤ` comes from.

## The proof, and the one place a hypothesis is used

Clear denominators (`LaurentPolynomial.exists_T_pow`): `f * T^a` and `f⁻¹ * T^b` are honest
polynomials whose product is `X ^ (a+b)`.  So the numerator divides a power of `X`, and
`X` is prime in `R[X]` **because `R` is a domain** — this is the only use of `IsDomain`.

**It is not removable, and that is a THEOREM here rather than a remark.**  An earlier version
of this header asserted the counterexample in prose, unverified (`I-1634`).  It is now
`isUnit_one_add_C_mul_T_of_sq_eq_zero` together with
`not_exists_eq_C_mul_T_one_add_C_mul_T`: whenever `e² = 0`, the element `1 + C e * T 1` is a
unit of `R[T;T⁻¹]` over **any** commutative ring, and whenever `e ≠ 0` it is not `C c * T n` for
any `c, n`.  Both hold with no domain hypothesis, and `k[ε]/ε²` supplies such an `e`, so the
classification genuinely fails there.  It cost fifteen lines; prose cost a reviewer more than
that to check.

## Main declarations

* `LaurentPolynomial.isUnit_iff_C_mul_T` — **the classification**, as an iff.
* `LaurentPolynomial.exists_eq_C_mul_T_of_isUnit` — its forward half, in the form consumers use.
* `LaurentPolynomial.isUnit_C_mul_T` — the converse half, over any commutative ring.
* `LaurentPolynomial.exp_unique` / `coeff_unique` — the exponent and coefficient are determined
  by the element (no domain hypothesis; the `omit` markers are the measurement).
* `LaurentPolynomial.unitsEquiv` — the unit group as `Rˣ × ℤ`, which is the form the Picard
  computation consumes.
* `LaurentPolynomial.isUnit_one_add_C_mul_T_of_sq_eq_zero` /
  `not_exists_eq_C_mul_T_one_add_C_mul_T` — **the domain hypothesis is necessary**, formalized
  rather than asserted.
-/

set_option autoImplicit false

universe u

open Polynomial

namespace LaurentPolynomial

variable {R : Type u} [CommRing R]

/-! ## The easy direction, over an arbitrary commutative ring -/

/-- A Laurent monomial with unit coefficient is a unit.  No domain hypothesis. -/
theorem isUnit_C_mul_T {c : R} (hc : IsUnit c) (n : ℤ) :
    IsUnit (LaurentPolynomial.C c * T n) :=
  (hc.map LaurentPolynomial.C).mul (isUnit_T n)

/-! ## The exponent is determined

Stated separately from the classification because it needs no domain hypothesis, and because
it is what makes `Pic(ℙ¹) ≅ ℤ` rather than merely a quotient of `ℤ`: without it the exponent
would be only a choice. -/

/-- **The exponent of a Laurent monomial is determined by the element**, as soon as its
coefficient is nonzero.  Evaluated at the index `n`, the two `Finsupp.single`s give `c` and
`0`. -/
theorem exp_unique {c d : R} (hc : c ≠ 0) {n m : ℤ}
    (h : (LaurentPolynomial.C c * T n : LaurentPolynomial R) = LaurentPolynomial.C d * T m) :
    n = m := by
  by_contra hne
  have h1 := congrArg (fun f : LaurentPolynomial R => f n) h
  simp only [← LaurentPolynomial.single_eq_C_mul_T] at h1
  rw [show (AddMonoidAlgebra.single n c : LaurentPolynomial R) = Finsupp.single n c from rfl,
      show (AddMonoidAlgebra.single m d : LaurentPolynomial R) = Finsupp.single m d from rfl,
      Finsupp.single_eq_same] at h1
  rw [Finsupp.single_apply, if_neg (fun hh : m = n => absurd hh.symm hne)] at h1
  exact hc h1

/-! ## The domain hypothesis is necessary

Not a remark: the two halves below are the counterexample, formalized.  Over a ring with a
nonzero square-zero element the classification fails, so `IsDomain` in the next section cannot
be dropped.  Neither statement needs a domain, which is the point. -/

/-- Over **any** commutative ring, `1 + C e * T 1` is a unit as soon as `e² = 0`: its inverse is
`1 - C e * T 1`, because the cross term carries `e²`. -/
theorem isUnit_one_add_C_mul_T_of_sq_eq_zero {e : R} (he : e * e = 0) :
    IsUnit (1 + LaurentPolynomial.C e * T 1 : LaurentPolynomial R) := by
  have hsq : (LaurentPolynomial.C e * T 1) * (LaurentPolynomial.C e * T (1 : ℤ))
      = LaurentPolynomial.C (e * e) * T (2 : ℤ) := by
    rw [map_mul, show (LaurentPolynomial.C e * T 1) * (LaurentPolynomial.C e * T (1 : ℤ))
      = (LaurentPolynomial.C e * LaurentPolynomial.C e) * (T 1 * T (1 : ℤ)) from by ring,
      ← T_add]
    norm_num
  refine ⟨⟨1 + LaurentPolynomial.C e * T 1, 1 - LaurentPolynomial.C e * T 1, ?_, ?_⟩, rfl⟩
  · rw [show (1 + LaurentPolynomial.C e * T 1) * (1 - LaurentPolynomial.C e * T (1 : ℤ))
      = 1 - (LaurentPolynomial.C e * T 1) * (LaurentPolynomial.C e * T (1 : ℤ)) from by ring,
      hsq, he, map_zero, zero_mul, sub_zero]
  · rw [show (1 - LaurentPolynomial.C e * T 1) * (1 + LaurentPolynomial.C e * T (1 : ℤ))
      = 1 - (LaurentPolynomial.C e * T 1) * (LaurentPolynomial.C e * T (1 : ℤ)) from by ring,
      hsq, he, map_zero, zero_mul, sub_zero]

/-- The coefficient of a Laurent monomial at an arbitrary index. -/
theorem C_mul_T_apply (c : R) (n m : ℤ) :
    (LaurentPolynomial.C c * T n : LaurentPolynomial R) m = if n = m then c else 0 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T,
    show (AddMonoidAlgebra.single n c : LaurentPolynomial R) = Finsupp.single n c from rfl,
    Finsupp.single_apply]

/-- **The other half of the counterexample**: with `e ≠ 0`, the unit `1 + C e * T 1` is not a
monomial `C c * T n`.  It has nonzero coefficients at both `0` and `1`, and a monomial has at
most one. -/
theorem not_exists_eq_C_mul_T_one_add_C_mul_T [Nontrivial R] {e : R} (he : e ≠ 0) :
    ¬ ∃ (c : R) (n : ℤ),
      (1 + LaurentPolynomial.C e * T 1 : LaurentPolynomial R) = LaurentPolynomial.C c * T n := by
  rintro ⟨c, n, h⟩
  have key : ∀ m : ℤ, (1 : LaurentPolynomial R) m + (if (1 : ℤ) = m then e else 0)
      = (if n = m then c else 0) := fun m => by
    simpa [C_mul_T_apply] using congrArg (fun f : LaurentPolynomial R => f m) h
  have hone : ∀ m : ℤ, (1 : LaurentPolynomial R) m = if (0 : ℤ) = m then (1 : R) else 0 :=
    fun m => by
      rw [show (1 : LaurentPolynomial R) = LaurentPolynomial.C (1 : R) * T (0 : ℤ) from by simp]
      exact C_mul_T_apply 1 0 m
  have h0 := key 0
  have h1 := key 1
  rw [hone] at h0 h1
  norm_num at h0 h1
  by_cases hn : n = 0
  · rw [if_pos hn] at h0
    rw [if_neg (by omega : ¬ n = 1)] at h1
    exact he h1
  · exact one_ne_zero ((if_neg hn) ▸ h0)

/-! ## The classification -/

variable [IsDomain R]

/-- **Every unit of `R[T;T⁻¹]` over a domain is `C c * T n` with `c` a unit.**

Clear denominators to get polynomials `p, q` with `p * q = X ^ (a + b)`; then `p ∣ X ^ (a+b)`
and `X` is prime, so `p` is a unit times `X ^ i`, and the polynomial unit is a constant by
`Polynomial.isUnit_iff`. -/
theorem exists_eq_C_mul_T_of_isUnit {f : LaurentPolynomial R} (hf : IsUnit f) :
    ∃ (c : R) (n : ℤ), IsUnit c ∧ f = LaurentPolynomial.C c * T n := by
  obtain ⟨g, hg⟩ := hf.exists_right_inv
  obtain ⟨a, p, hp⟩ := exists_T_pow f
  obtain ⟨b, q, hq⟩ := exists_T_pow g
  have key : Polynomial.toLaurent (p * q) = Polynomial.toLaurent (Polynomial.X ^ (a + b)) := by
    rw [map_mul, hp, hq]
    rw [show (f * T (a : ℤ)) * (g * T (b : ℤ)) = (f * g) * T ((a : ℤ) + b) by
      rw [T_add]; ring]
    rw [hg, one_mul]
    simp
  have hpq : p * q = Polynomial.X ^ (a + b) := toLaurent_injective key
  obtain ⟨i, _, u, hu⟩ := (dvd_prime_pow Polynomial.prime_X (a + b)).mp ⟨q, hpq.symm⟩
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp (Units.isUnit u⁻¹)
  have hpX : p = Polynomial.C c * Polynomial.X ^ i := by
    have hpu : p = Polynomial.X ^ i * (↑u⁻¹ : Polynomial R) := by rw [← hu, mul_assoc]; simp
    rw [hpu, hcu, mul_comm]
  refine ⟨c, (i : ℤ) - a, hc, ?_⟩
  have hf' : f = Polynomial.toLaurent p * T (-(a : ℤ)) := by
    rw [hp, mul_assoc, ← T_add]; simp
  rw [hf', hpX, map_mul, toLaurent_C, map_pow, toLaurent_X, mul_assoc, T_pow, ← T_add,
    show ((i : ℤ) * 1 + -(a : ℤ)) = (i : ℤ) - a by ring]

/-- **The unit classification of `R[T;T⁻¹]` over a domain**, as an iff. -/
theorem isUnit_iff_C_mul_T {f : LaurentPolynomial R} :
    IsUnit f ↔ ∃ (c : R) (n : ℤ), IsUnit c ∧ f = LaurentPolynomial.C c * T n := by
  refine ⟨exists_eq_C_mul_T_of_isUnit, ?_⟩
  rintro ⟨c, n, hc, rfl⟩
  exact isUnit_C_mul_T hc n

/-! ## The unit group as a product

The classification packaged as a group isomorphism `Rˣ × ℤ ≃* (R[T;T⁻¹])ˣ`.  This is the form
the Picard computation wants: the two chart unit groups of `ℙ¹` both land in the constants
(units of `k[t]` are constants by `Polynomial.isUnit_iff`), so the two-cover Čech `Ȟ¹` of units
is this group modulo `Rˣ` — the `ℤ` factor, and nothing else. -/

/-- `T n` as a unit. -/
noncomputable def tUnit (n : ℤ) : (LaurentPolynomial R)ˣ := (isUnit_T n).unit

omit [IsDomain R] in
@[simp]
theorem tUnit_coe (n : ℤ) : ((tUnit (R := R) n : (LaurentPolynomial R)ˣ)
    : LaurentPolynomial R) = T n := rfl

/-- The homomorphism `Rˣ × ℤ →* (R[T;T⁻¹])ˣ` sending `(c, n)` to `C c * T n`.  Over any
commutative ring; the domain hypothesis is only needed for surjectivity. -/
noncomputable def unitsHom :
    Rˣ × Multiplicative ℤ →* (LaurentPolynomial R)ˣ where
  toFun p := (Units.map (LaurentPolynomial.C : R →+* LaurentPolynomial R).toMonoidHom p.1)
      * tUnit (Multiplicative.toAdd p.2)
  map_one' := Units.ext (by
    change (LaurentPolynomial.C (1 : R)) * T (0 : ℤ) = 1
    rw [map_one, T_zero, one_mul])
  map_mul' a b := Units.ext (by
    change LaurentPolynomial.C ((a.1 * b.1 : Rˣ) : R) * T (Multiplicative.toAdd (a.2 * b.2))
      = (LaurentPolynomial.C (a.1 : R) * T (Multiplicative.toAdd a.2))
        * (LaurentPolynomial.C (b.1 : R) * T (Multiplicative.toAdd b.2))
    push_cast
    have hT : (T (Multiplicative.toAdd (a.2 * b.2)) : LaurentPolynomial R)
        = T (Multiplicative.toAdd a.2) * T (Multiplicative.toAdd b.2) := by
      rw [← T_add]; rfl
    rw [map_mul, hT]
    ring)

omit [IsDomain R] in
@[simp]
theorem unitsHom_coe (p : Rˣ × Multiplicative ℤ) :
    ((unitsHom p : (LaurentPolynomial R)ˣ) : LaurentPolynomial R)
      = LaurentPolynomial.C (p.1 : R) * T (Multiplicative.toAdd p.2) :=
  rfl

omit [IsDomain R] in
/-- The coefficient of a Laurent monomial is determined once the exponent is.  Companion to
`exp_unique`, and like it needs no domain hypothesis (the `omit` is the measurement). -/
theorem coeff_unique {c d : R} {n : ℤ}
    (h : (LaurentPolynomial.C c * T n : LaurentPolynomial R)
      = LaurentPolynomial.C d * T n) : c = d := by
  have h1 := congrArg (fun f : LaurentPolynomial R => f n) h
  simp only [← LaurentPolynomial.single_eq_C_mul_T] at h1
  rw [show (AddMonoidAlgebra.single n c : LaurentPolynomial R) = Finsupp.single n c from rfl,
      show (AddMonoidAlgebra.single n d : LaurentPolynomial R) = Finsupp.single n d from rfl,
      Finsupp.single_eq_same, Finsupp.single_eq_same] at h1
  exact h1

theorem unitsHom_surjective : Function.Surjective (unitsHom (R := R)) := by
  intro u
  obtain ⟨c, n, hc, hu⟩ := exists_eq_C_mul_T_of_isUnit u.isUnit
  refine ⟨(hc.unit, Multiplicative.ofAdd n), Units.ext ?_⟩
  rw [unitsHom_coe, hu]
  simp

theorem unitsHom_injective : Function.Injective (unitsHom (R := R)) := by
  intro p q hpq
  have h : LaurentPolynomial.C (p.1 : R) * T (Multiplicative.toAdd p.2)
      = LaurentPolynomial.C (q.1 : R) * T (Multiplicative.toAdd q.2) :=
    congrArg (fun v : (LaurentPolynomial R)ˣ => (v : LaurentPolynomial R)) hpq
  have hne : (p.1 : R) ≠ 0 := p.1.ne_zero
  have hexp : Multiplicative.toAdd p.2 = Multiplicative.toAdd q.2 := exp_unique hne h
  have hsnd : p.2 = q.2 := Multiplicative.toAdd.injective hexp
  have hsame : LaurentPolynomial.C (p.1 : R) * T (Multiplicative.toAdd p.2)
      = LaurentPolynomial.C (q.1 : R) * T (Multiplicative.toAdd p.2) := by
    rw [h, hexp]
  exact Prod.ext (Units.ext (coeff_unique hsame)) hsnd

/-- **`(R[T;T⁻¹])ˣ ≅ Rˣ × ℤ`** over a domain.  The `ℤ` is the exponent and the `Rˣ` is the
coefficient; `exp_unique` and `coeff_unique` are the two halves of injectivity, and the
classification is surjectivity. -/
noncomputable def unitsEquiv : Rˣ × Multiplicative ℤ ≃* (LaurentPolynomial R)ˣ :=
  MulEquiv.ofBijective unitsHom ⟨unitsHom_injective, unitsHom_surjective⟩

end LaurentPolynomial
