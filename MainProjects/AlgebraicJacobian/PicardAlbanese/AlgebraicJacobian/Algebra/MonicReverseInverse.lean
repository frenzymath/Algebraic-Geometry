/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Uniform polynomial reciprocals of units with integral inverses

Pure commutative algebra for the finite-scheme trivialization bricks (DD-4's theta
pairing, DD-2's certificate extraction — the shared "finite over the base ⟹ integral
coordinates" substrate):

* `Polynomial.Monic.mul_aeval_neg_divX_reverse` — **the reciprocal-witness identity**:
  if `s * w = 1` and `w` is annihilated by a monic `p ∈ R[X]`, then
  `s * q(s) = 1` for the *explicit universal* polynomial `q := -(p.reverse.divX)`.
  In other words the inverse of `s` lies in `R[s]`, with a witness polynomial that
  depends only on `p` — so a single `p` annihilating a coordinate in every member of a
  family of quotient algebras produces *one* global section inverting the coordinate
  simultaneously in all of them.
* `exists_monic_forall_aeval_eq_zero` — **the uniform monic annihilator**: finitely
  many integral elements, in possibly different `R`-algebras, are killed by a single
  monic polynomial (the product of individual integral equations).

The composite consumer shape (`AlgebraicJacobian.Picard.DivisorThetaPairing`): on a
colength scheme finite over the base, the chart-1 coordinate `t₁` is integral over `R`
in every chart-1 colength algebra; since `t₀ · t₁ = 1` on the chart overlaps, the
reciprocal witness turns the annihilator of `t₁` into a *global chart-0 section*
`H = q(t₀)` with `t₀ · H = 1` on every cross-overlap colength — the algebraic partition
of unity subordinate to the two coordinate loci.
-/

set_option autoImplicit false

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **The reciprocal-witness identity**: if `s * w = 1` and `w` is a root of a monic
polynomial `p` over `R`, then `s` is invertible inside the polynomial span `R[s]`, with
the explicit inverse `aeval s (-(p.reverse.divX))` — a witness polynomial depending only
on `p`, not on `s`, `w`, or the ambient algebra. -/
theorem Monic.mul_aeval_neg_divX_reverse {p : R[X]} (hp : p.Monic) {s w : S}
    (hsw : s * w = 1) (hw : Polynomial.aeval w p = 0) :
    s * Polynomial.aeval s (-p.reverse.divX) = 1 := by
  letI : Invertible w := ⟨s, hsw, by rw [mul_comm]; exact hsw⟩
  -- the reverse polynomial vanishes at `s = ⅟w`
  have h0 : Polynomial.aeval s p.reverse = 0 := by
    rw [Polynomial.aeval_def, ← invOf_eq_left_inv hsw]
    exact (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap R S) w p).mpr
      (by rw [← Polynomial.aeval_def]; exact hw)
  -- peel off the constant coefficient of the reverse, which is the leading coefficient
  have hdecomp := congrArg (Polynomial.aeval s) (Polynomial.X_mul_divX_add p.reverse)
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
    Polynomial.coeff_zero_reverse, hp.leadingCoeff, map_one, h0] at hdecomp
  rw [map_neg, mul_neg]
  exact neg_eq_of_add_eq_zero_right hdecomp

end Polynomial

/-- **The uniform monic annihilator**: finitely many integral elements, spread over an
arbitrary finite family of commutative `R`-algebras, are annihilated by a *single* monic
polynomial — the product of the individual integral equations. -/
theorem exists_monic_forall_aeval_eq_zero {R : Type*} [CommRing R] {ι : Type*}
    [Finite ι] {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    {x : ∀ i, B i} (hx : ∀ i, IsIntegral R (x i)) :
    ∃ p : Polynomial R, p.Monic ∧ ∀ i, Polynomial.aeval (x i) p = 0 := by
  letI := Fintype.ofFinite ι
  choose P hmon heval using hx
  refine ⟨∏ i : ι, P i,
    Polynomial.monic_prod_of_monic _ _ (fun i _ => hmon i), fun i => ?_⟩
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (by rw [Polynomial.aeval_def]; exact heval i)
