/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.LaurentNilpotentCoboundary

/-!
# NILPOTENCE OF LAURENT POLYNOMIALS IS COEFFICIENTWISE

The ℙ¹ two-chart Picard computation over an arbitrary (non-reduced) test ring runs into the
nilpotent part of the coefficient ring: over a domain a Laurent unit is `C c · Tⁿ`
(`Picard/LaurentTwoChartCoboundary.lean`), over a reduced ring the same
(`Algebra/LaurentCoboundaryReduced.lean`), and the gap between reduced and arbitrary is exactly
the units congruent to `1` modulo nilpotents.  `Algebra/LaurentReducedReduction.lean` reduces the
whole coboundary question to reduced rings; the reduction needs to know that the kernel of
`A[T;T⁻¹] → (A ⧸ nil A)[T;T⁻¹]` is the **nilpotent** Laurent polynomials, and that is a
coefficientwise statement.

This file is that coefficientwise dictionary, and nothing about Picard groups:

* `IsReduced (A[T;T⁻¹])` when `A` is reduced — proved by clearing denominators to `A[X]`, where
  reducedness is coefficientwise (`Polynomial.isNilpotent_iff`); there is no mathlib instance for
  the Laurent ring at this pin;
* a coefficient of a nilpotent Laurent polynomial is nilpotent — via base change to the reduced
  quotient `A ⧸ nil A`, where the image is `0`;
* conversely a Laurent polynomial with all coefficients nilpotent is nilpotent — it is a finite
  sum of nilpotent monomials;
* a coefficient of a product `x · y` lies in `I · J` when `x`'s coefficients lie in `I` and `y`'s
  in `J` — the Cauchy-product membership the halving step of the arbitrary-ring computation needs.

## Main declarations

* `AlgebraicGeometry.isReduced_laurent` — `A[T;T⁻¹]` is reduced when `A` is.
* `AlgebraicGeometry.coeff_isNilpotent_of_isNilpotent` — a coefficient of a nilpotent Laurent
  polynomial is nilpotent.
* `AlgebraicGeometry.isNilpotent_of_forall_coeff` — a Laurent polynomial with all coefficients
  nilpotent is nilpotent.
* `AlgebraicGeometry.isNilpotent_laurent_iff_forall_coeff` — the two together, as an `iff`.
* `AlgebraicGeometry.coeff_mul_mem_mul` — the Cauchy-product coefficient of `x · y` lies in
  `I · J`.
-/

set_option autoImplicit false

universe u

open CategoryTheory LaurentPolynomial

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A]

/-- **`A[T;T⁻¹]` is reduced when `A` is.**

Clear denominators: any Laurent polynomial `z` is `Polynomial.toLaurent p · T (-a)` for some `p`
and `a` (`exists_T_pow`), and multiplying a nilpotent by the unit `T a` keeps it nilpotent, so
`toLaurent p` is nilpotent; `toLaurent` is injective, `A[X]` is reduced coefficientwise, so
`p = 0` and hence `z = 0`.  Mathlib has no `IsReduced` instance for the Laurent ring at this pin,
so it is proved here. -/
theorem isReduced_laurent [_root_.IsReduced A] : _root_.IsReduced (LaurentPolynomial A) := by
  have hpoly : _root_.IsReduced (Polynomial A) := by
    refine ⟨fun p hp => ?_⟩
    rw [Polynomial.isNilpotent_iff] at hp
    ext i; simpa using (hp i).eq_zero
  refine ⟨fun z hz => ?_⟩
  obtain ⟨a, p, hp⟩ := LaurentPolynomial.exists_T_pow z
  have hpn : IsNilpotent (Polynomial.toLaurent p) := by
    rw [hp]; exact (Commute.all _ _).isNilpotent_mul_right hz
  have hp0 : p = 0 := by
    obtain ⟨n, hn⟩ := hpn
    have hpp : IsNilpotent p :=
      ⟨n, Polynomial.toLaurent_injective (by rw [map_pow, hn, map_zero])⟩
    exact hpp.eq_zero
  rw [hp0, map_zero] at hp
  exact (isUnit_T a).mul_left_eq_zero.mp hp.symm

/-- **A coefficient of a nilpotent Laurent polynomial is nilpotent.**

Base change to the reduced quotient `A ⧸ nil A`: the image of a nilpotent is nilpotent, and the
Laurent ring over a reduced ring is reduced (`isReduced_laurent`), so the image is `0`; reading
off coefficient `i` puts `z i` in the nilradical. -/
theorem coeff_isNilpotent_of_isNilpotent {z : LaurentPolynomial A} (hz : IsNilpotent z) (i : ℤ) :
    IsNilpotent (z i) := by
  haveI hrad : (nilradical A).IsRadical := Ideal.radical_isRadical 0
  haveI hred : _root_.IsReduced (A ⧸ nilradical A) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp hrad
  haveI : _root_.IsReduced (LaurentPolynomial (A ⧸ nilradical A)) := isReduced_laurent
  have h2 : (AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk (nilradical A))) z = 0 :=
    (hz.map _).eq_zero
  have h3 : Ideal.Quotient.mk (nilradical A) (z i) = 0 := by
    have hc := congrArg (fun w : LaurentPolynomial (A ⧸ nilradical A) => w i) h2
    rw [AddMonoidAlgebra.mapRingHom_apply] at hc
    rw [hc]; rfl
  rw [← mem_nilradical]
  exact (Ideal.Quotient.eq_zero_iff_mem).mp h3

/-- **A Laurent polynomial with all coefficients nilpotent is nilpotent.**

It is the finite sum `∑ᵢ C (z i) · T i` over its support, and each summand is nilpotent
(`C (z i)` is nilpotent, `T i` a unit). -/
theorem isNilpotent_of_forall_coeff {z : LaurentPolynomial A}
    (hz : ∀ i, IsNilpotent (z i)) : IsNilpotent z := by
  classical
  have hrep : z = ∑ i ∈ z.support, (LaurentPolynomial.C (z i) * LaurentPolynomial.T i) := by
    conv_lhs => rw [← Finsupp.sum_single z]
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [← LaurentPolynomial.single_eq_C_mul_T])
  rw [hrep]
  exact isNilpotent_sum fun i _ =>
    (Commute.all _ _).isNilpotent_mul_right
      ((hz i).map (LaurentPolynomial.C : A →+* LaurentPolynomial A))

/-- The two directions together: a Laurent polynomial is nilpotent iff every coefficient is. -/
theorem isNilpotent_laurent_iff_forall_coeff {z : LaurentPolynomial A} :
    IsNilpotent z ↔ ∀ i, IsNilpotent (z i) :=
  ⟨fun hz => coeff_isNilpotent_of_isNilpotent hz, isNilpotent_of_forall_coeff⟩

/-- **The Cauchy-product coefficient lies in the product ideal.**  If every coefficient of `x`
lies in `I` and every coefficient of `y` in `J`, then every coefficient of `x · y` lies in
`I · J`.  This is the membership the halving step of the arbitrary-ring ℙ¹ computation needs:
the cross term of two deformations along an ideal `I` lands in `I²`. -/
theorem coeff_mul_mem_mul {I J : Ideal A} {x y : LaurentPolynomial A}
    (hx : ∀ i, x i ∈ I) (hy : ∀ i, y i ∈ J) (m : ℤ) : (x * y) m ∈ I * J := by
  classical
  rw [AddMonoidAlgebra.mul_apply, Finsupp.sum]
  refine Ideal.sum_mem _ (fun a₁ _ => ?_)
  rw [Finsupp.sum]
  refine Ideal.sum_mem _ (fun a₂ _ => ?_)
  split
  · exact Ideal.mul_mem_mul (hx a₁) (hy a₂)
  · exact Ideal.zero_mem _

end AlgebraicGeometry
