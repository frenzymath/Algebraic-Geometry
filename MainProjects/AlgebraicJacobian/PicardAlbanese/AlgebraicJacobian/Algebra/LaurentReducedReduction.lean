/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.LaurentNilpotentCoboundary
import AlgebraicJacobian.Algebra.LaurentCoboundaryGeneral

/-!
# THE ℙ¹ COBOUNDARY QUESTION IS A QUESTION ABOUT REDUCED RINGS

`Algebra/LaurentNilpotentCoboundary.lean` proves that a Laurent unit congruent to `1` modulo a
nilpotent is a coboundary, over an arbitrary commutative ring.  On its own that is a statement
about a special class of units.  This file turns it into a **reduction of the test ring**:

> a Laurent unit whose image in `(A ⧸ nilradical A)[T;T⁻¹]` is a coboundary
> is itself a coboundary over `A`.

Since `A ⧸ nilradical A` is reduced, the ℙ¹ coboundary question at an *arbitrary* commutative
ring is equivalent to the same question at *reduced* rings.

**Honest scope (review I-1706).**  The arbitrary-ring coboundary question is *already* fully
answered upstream by `mem_laurentCoboundaryUnits_iff_general` (coboundary ⟺ `C c·(1+z)`, `c`
unit, `z` nilpotent).  So this file's reduction connects two results that are each already
complete characterisations; it adds **consumer-facing structure and reachability**, not new
mathematical ground.  `not_tUnit_mem_laurentCoboundaryUnits_general` below is therefore *also*
derivable directly from `iff_general`, without the reduced-quotient detour — it is stated here
because the "question about reduced rings" packaging is the shape a two-chart-cover consumer
reasons in.  With that caveat, what the reduction does is move the whole
obligation off the nilpotents, where it was blocked for a reason both that file and
`Algebra/LaurentUnits.lean` record (`1 + C e * T 1` is a unit at `e² = 0`), and onto a class
where the obstruction is of a different kind: over a reduced ring a Laurent unit *is* locally
`C c · Tⁿ`, and what fails is only that the exponent `n` need not be globally constant on
`Spec A`.

**This is a genuine weakening of the hypothesis, and the check is that the converse is not
free.** The forward direction below (a coboundary downstairs gives one upstairs) is the
substantive one.  The other direction is immediate — coboundaries push forward along any ring
map — so the two are *not* equivalent by symmetry, and the reduction is not a re-spelling of its
own hypothesis.  Stated as `mem_laurentCoboundaryUnits_iff_map_reduced`, with both halves
available separately.

## The two inputs, both proved here because neither is in mathlib at this pin

* `isUnit_of_isUnit_map` — **units are detected modulo a nilpotent kernel**.  If `φ` is
  surjective with `ker φ ≤ nilradical`, then `IsUnit (φ r) → IsUnit r`: lift the inverse, and
  `r * t - 1` lies in the kernel, hence is nilpotent, hence `r * t` is a unit.  Searched
  (`exact?` on both this and the unit-lifting form): absent.
* `isNilpotent_of_map_nilradical_eq_zero` — the kernel of `A[X] → (A ⧸ nil A)[X]` consists of
  nilpotent polynomials, via `Polynomial.isNilpotent_iff` (coefficientwise).  This is what makes
  the previous lemma applicable at the *chart* rings rather than only at `A`.

## Why the lift is by hand rather than by a `Pic`-functoriality lemma

The chart units downstairs are units of `(A ⧸ nil A)[X]`, and lifting them needs surjectivity of
`A[X] → (A ⧸ nil A)[X]` *plus* the unit-detection lemma above; a `Pic`-level statement would
give the class, not the presenting units, and the coboundary subgroup is defined by the presenting
units.  So the lift happens at the level of `Polynomial A`, which is also where the nilpotency of
the kernel is legible.

## Main declarations

* `AlgebraicGeometry.isUnit_of_isUnit_map` — units modulo a nilpotent kernel.
* `AlgebraicGeometry.isNilpotent_of_map_nilradical_eq_zero` — the polynomial kernel is nilpotent.
* `AlgebraicGeometry.mem_laurentCoboundaryUnits_of_map_reduced` — **the reduction**: a coboundary
  after killing the nilradical is a coboundary.
* `AlgebraicGeometry.mem_laurentCoboundaryUnits_iff_map_reduced` — bundled with the free
  converse, so the direction that carries content is visible.
* `AlgebraicGeometry.laurentCoboundaryUnits_map` — the free converse: a coboundary pushes forward
  along any coefficient base change.
* `AlgebraicGeometry.not_tUnit_mem_laurentCoboundaryUnits_general` — `t` is not a coboundary over
  *any* nontrivial ring, the arbitrary-ring generator of `Pic(ℙ¹_A) = ℤ`.
-/

set_option autoImplicit false

universe u

open Polynomial LaurentPolynomial

namespace AlgebraicGeometry

/-! ## Units modulo a nilpotent kernel -/

/-- **Units are detected modulo a nilpotent kernel**: for a surjective `φ` whose kernel consists
of nilpotents, `φ r` a unit forces `r` a unit.

Lift the inverse of `φ r` to some `t`; then `φ (r * t) = 1`, so `r * t - 1` is in the kernel and
hence nilpotent, so `r * t = 1 + (r * t - 1)` is a unit and `r` divides a unit.

Measured absent from mathlib at this pin, in both this form and the unit-lifting form
`∃ r : Rˣ, φ r = s`. -/
theorem isUnit_of_isUnit_map {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hs : Function.Surjective φ) (hker : RingHom.ker φ ≤ nilradical R) {r : R}
    (h : IsUnit (φ r)) : IsUnit r := by
  obtain ⟨t, ht⟩ := hs ((h.unit⁻¹ : Sˣ) : S)
  have h1 : φ (r * t) = 1 := by
    rw [map_mul, ht]
    calc φ r * ((h.unit⁻¹ : Sˣ) : S)
        = ((h.unit : Sˣ) : S) * ((h.unit⁻¹ : Sˣ) : S) := by rw [IsUnit.unit_spec]
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hnil : IsNilpotent (r * t - 1) := hker (by simp [RingHom.mem_ker, map_sub, h1])
  have hru : IsUnit (r * t) := by simpa using hnil.isUnit_one_add (R := R)
  exact isUnit_of_mul_isUnit_left hru

/-- The kernel of `A[X] → (A ⧸ nilradical A)[X]` consists of **nilpotent** polynomials: a
polynomial killed downstairs has every coefficient in the nilradical, and
`Polynomial.isNilpotent_iff` is exactly the coefficientwise criterion. -/
theorem isNilpotent_of_map_nilradical_eq_zero {A : Type u} [CommRing A] {p : Polynomial A}
    (h : Polynomial.mapRingHom (Ideal.Quotient.mk (nilradical A)) p = 0) :
    IsNilpotent p := by
  rw [Polynomial.isNilpotent_iff]
  intro i
  have hi : (Ideal.Quotient.mk (nilradical A)) (p.coeff i) = 0 := by
    have := congrArg (fun z => Polynomial.coeff z i) h
    simpa using this
  exact (Ideal.Quotient.eq_zero_iff_mem).mp hi

/-! ## The base-change map on Laurent rings, and that it commutes with both ℙ¹ charts -/

section BaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The Laurent ring is functorial in the coefficient ring: base change along `φ`.  Mathlib
spells this `AddMonoidAlgebra.mapRingHom` at `M := ℤ`; there is no `LaurentPolynomial.map`. -/
noncomputable abbrev laurentMap (φ : A →+* B) :
    LaurentPolynomial A →+* LaurentPolynomial B :=
  AddMonoidAlgebra.mapRingHom ℤ φ

/-- Base change on a Laurent monomial: `AddMonoidAlgebra.map_single` once the `C · T` spelling is
turned into `Finsupp.single` by `single_eq_C_mul_T`. -/
theorem laurentMap_C_mul_T (φ : A →+* B) (a : A) (n : ℤ) :
    laurentMap φ (LaurentPolynomial.C a * LaurentPolynomial.T n)
      = LaurentPolynomial.C (φ a) * LaurentPolynomial.T n := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T]
  exact AddMonoidAlgebra.map_single (φ : A →+ B) a n

/-- `T (-1) ^ n = T (-n)`, in the orientation the right chart produces.  `T_pow` is stated with
the exponent on the *left* of the product, so the arithmetic is done by hand. -/
private lemma T_neg_one_pow {R : Type u} [CommRing R] (n : ℕ) :
    (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial R) ^ n
      = LaurentPolynomial.T (-(n : ℤ)) := by
  have h := LaurentPolynomial.T_pow (R := R) (-1 : ℤ) n
  rw [show ((n : ℤ) * (-1)) = -(n : ℤ) from by ring] at h
  exact h

/-- **Base change commutes with the left ℙ¹ chart** `Polynomial.toLaurent`. -/
theorem laurentMap_toLaurent (φ : A →+* B) (p : Polynomial A) :
    laurentMap φ (Polynomial.toLaurent p)
      = Polynomial.toLaurent (Polynomial.mapRingHom φ p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow,
        laurentMap_C_mul_T]
      simp

/-- **Base change commutes with the right ℙ¹ chart** `rightChart`. -/
theorem laurentMap_rightChart (φ : A →+* B) (p : Polynomial A) :
    laurentMap φ (rightChart A p) = rightChart B (Polynomial.mapRingHom φ p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      have hl : rightChart A (Polynomial.C a * Polynomial.X ^ n)
          = LaurentPolynomial.C a * LaurentPolynomial.T (-(n : ℤ)) := by
        rw [map_mul, rightChart_C, map_pow, rightChart_X, T_neg_one_pow]
      have hr : rightChart B (Polynomial.C (φ a) * Polynomial.X ^ n)
          = LaurentPolynomial.C (φ a) * LaurentPolynomial.T (-(n : ℤ)) := by
        rw [map_mul, rightChart_C, map_pow, rightChart_X, T_neg_one_pow]
      rw [hl, laurentMap_C_mul_T]
      simp [hr]

/-- Base change sends a constant `C c` to `C (φ c)`; the `T 0` specialisation of
`laurentMap_C_mul_T`. -/
theorem laurentMap_C (φ : A →+* B) (c : A) :
    laurentMap φ (LaurentPolynomial.C c) = LaurentPolynomial.C (φ c) := by
  have h : laurentMap φ (LaurentPolynomial.C c * LaurentPolynomial.T 0)
      = LaurentPolynomial.C (φ c) * LaurentPolynomial.T 0 := laurentMap_C_mul_T φ c 0
  simpa using h

/-- Base change fixes the monomial `T n`; the `c = 1` specialisation of `laurentMap_C_mul_T`. -/
theorem laurentMap_T (φ : A →+* B) (n : ℤ) :
    laurentMap φ (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  have h := laurentMap_C_mul_T φ (1 : A) n
  simpa using h

/-- Base change fixes the unit `tUnit n`. -/
theorem laurentMap_tUnit (φ : A →+* B) (n : ℤ) :
    Units.map (laurentMap φ).toMonoidHom (LaurentPolynomial.tUnit n)
      = LaurentPolynomial.tUnit n := by
  apply Units.ext
  rw [Units.coe_map, LaurentPolynomial.tUnit_coe]
  change laurentMap φ (LaurentPolynomial.T n) = _
  rw [laurentMap_T, LaurentPolynomial.tUnit_coe]

end BaseChange

/-! ## The reduction of the test ring

The kernel of `laurentMap (mk (nilradical A))` consists of nilpotent Laurent polynomials, so a
Laurent unit whose image in the reduced quotient is a coboundary is itself `C c · (1 + z)` for a
unit `c` and a nilpotent `z` — a coboundary by the arbitrary-ring characterisation. -/

/-- A Laurent polynomial killed by base change along `mk (nilradical A)` has every coefficient in
the nilradical, i.e. nilpotent. -/
theorem coeff_isNilpotent_of_laurentMap_nilradical_eq_zero {A : Type u} [CommRing A]
    {z : LaurentPolynomial A}
    (h : laurentMap (Ideal.Quotient.mk (nilradical A)) z = 0) (i : ℤ) : IsNilpotent (z i) := by
  have h3 : Ideal.Quotient.mk (nilradical A) (z i) = 0 := by
    have hc := congrArg (fun w : LaurentPolynomial (A ⧸ nilradical A) => w i) h
    rw [show laurentMap (Ideal.Quotient.mk (nilradical A)) z
      = (AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk (nilradical A))) z from rfl,
      AddMonoidAlgebra.mapRingHom_apply] at hc
    rw [hc]; rfl
  rw [← mem_nilradical]
  exact (Ideal.Quotient.eq_zero_iff_mem).mp h3

/-- **A coboundary pushes forward along any coefficient base change.**  The free direction of the
reduction: `laurentMap_toLaurent`/`laurentMap_rightChart` carry the two chart presentations of a
coboundary to the chart presentations downstairs, so the image is a coboundary too. -/
theorem laurentCoboundaryUnits_map {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (u : (LaurentPolynomial A)ˣ) (hu : u ∈ laurentCoboundaryUnits A) :
    Units.map (laurentMap φ).toMonoidHom u ∈ laurentCoboundaryUnits B := by
  obtain ⟨v₁, v₂, hv⟩ := TruncExpCech.mem_cechCoboundaryUnits.mp hu
  refine TruncExpCech.mem_cechCoboundaryUnits.mpr
    ⟨Units.map (Polynomial.mapRingHom φ).toMonoidHom v₁,
     Units.map (Polynomial.mapRingHom φ).toMonoidHom v₂, ?_⟩
  apply Units.ext
  have hcoe : ((Units.map (laurentMap φ).toMonoidHom u : (LaurentPolynomial B)ˣ)
      : LaurentPolynomial B) = laurentMap φ (u : LaurentPolynomial A) := by
    rw [Units.coe_map]; rfl
  rw [hcoe, ← hv]
  simp [map_mul, laurentMap_toLaurent, laurentMap_rightChart]

/-- **THE REDUCTION**: a Laurent unit whose image in `(A ⧸ nilradical A)[T;T⁻¹]` is a coboundary
is itself a coboundary over `A`.

Since `A ⧸ nilradical A` is reduced, `mem_laurentCoboundaryUnits_iff_reduced` presents the image
as a constant unit `C c̄`; lift `c̄` to a unit `c` of `A` (`isUnit_of_isUnit_map`), and then
`z := u · (C c)⁻¹ − 1` maps to `0`, hence is nilpotent, so `u = C c · (1 + z)` is a coboundary by
`mem_laurentCoboundaryUnits_iff_general`.  This is the direction that carries content — the
converse `laurentCoboundaryUnits_map` is free — so the ℙ¹ coboundary question at an *arbitrary*
commutative ring reduces to the same question at *reduced* rings, which the domain/reduced
characterisation already settles. -/
theorem mem_laurentCoboundaryUnits_of_map_reduced {A : Type u} [CommRing A]
    {u : (LaurentPolynomial A)ˣ}
    (h : Units.map (laurentMap (Ideal.Quotient.mk (nilradical A))).toMonoidHom u
      ∈ laurentCoboundaryUnits (A ⧸ nilradical A)) :
    u ∈ laurentCoboundaryUnits A := by
  set φ := Ideal.Quotient.mk (nilradical A) with hφ
  haveI : _root_.IsReduced (A ⧸ nilradical A) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical 0)
  obtain ⟨cbar, hcbar, hval⟩ := (mem_laurentCoboundaryUnits_iff_reduced).mp h
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective cbar
  have hcunit : IsUnit c :=
    isUnit_of_isUnit_map φ Ideal.Quotient.mk_surjective (le_of_eq Ideal.mk_ker) (hc ▸ hcbar)
  obtain ⟨cu, hcu⟩ := hcunit
  set d : A := (↑cu⁻¹ : A) with hd
  have hcd : c * d = 1 := by rw [hd, ← hcu, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine (mem_laurentCoboundaryUnits_iff_general).mpr
    ⟨c, (u : LaurentPolynomial A) * LaurentPolynomial.C d - 1, ⟨cu, hcu⟩, ?_, ?_⟩
  · -- `z` is nilpotent: it maps to `0` downstairs, so each coefficient is nilpotent
    refine isNilpotent_of_forall_coeff (coeff_isNilpotent_of_laurentMap_nilradical_eq_zero ?_)
    rw [map_sub, map_one, map_mul, laurentMap_C]
    have hmu : laurentMap φ (u : LaurentPolynomial A) = LaurentPolynomial.C cbar := by
      have := hval; simpa [Units.coe_map] using this
    rw [hmu]
    have hmul : cbar * φ d = 1 := by rw [← hc, ← map_mul, hcd, map_one]
    rw [← map_mul (LaurentPolynomial.C : (A ⧸ nilradical A) →+* _), hmul, map_one, sub_self]
  · -- the presentation equation `u = C c · (1 + z)`
    have hccancel : (LaurentPolynomial.C c : LaurentPolynomial A) * LaurentPolynomial.C d = 1 := by
      rw [← map_mul, hcd, map_one]
    rw [mul_add, mul_one, mul_sub, mul_one, ← mul_assoc, mul_comm (LaurentPolynomial.C c),
      mul_assoc, hccancel, mul_one]
    ring

/-- **THE REDUCTION, bundled with its free converse**: the ℙ¹ coboundary property at `A` is
*equivalent* to the same property after killing the nilradical.  The forward implication is
`laurentCoboundaryUnits_map` (a coboundary pushes forward, no reducedness needed); the backward
one is `mem_laurentCoboundaryUnits_of_map_reduced` and carries the content.  Recorded as an `iff`
so "the coboundary question is a question about reduced rings" is a proved statement, and so the
direction that is not free is visible. -/
theorem mem_laurentCoboundaryUnits_iff_map_reduced {A : Type u} [CommRing A]
    {u : (LaurentPolynomial A)ˣ} :
    u ∈ laurentCoboundaryUnits A
      ↔ Units.map (laurentMap (Ideal.Quotient.mk (nilradical A))).toMonoidHom u
          ∈ laurentCoboundaryUnits (A ⧸ nilradical A) :=
  ⟨laurentCoboundaryUnits_map _ u, mem_laurentCoboundaryUnits_of_map_reduced⟩

/-- **`t` IS NOT A COBOUNDARY over an ARBITRARY nontrivial ring** — the generator of
`Pic(ℙ¹_A) = ℤ`, now with no domain *or* reducedness hypothesis.  If it were a coboundary its
image in `(A ⧸ nilradical A)[T;T⁻¹]` would be one (`laurentCoboundaryUnits_map`), and its image
is `t` again (`laurentMap_tUnit`), contradicting `not_tUnit_mem_laurentCoboundaryUnits_reduced`
over the reduced nontrivial quotient.  This is the refutation of the *universal* form of the
two-chart criterion at every commutative test ring the representability route meets, not merely
the domains and reduced rings the earlier files covered. -/
theorem not_tUnit_mem_laurentCoboundaryUnits_general {A : Type u} [CommRing A] [Nontrivial A] :
    LaurentPolynomial.tUnit (R := A) 1 ∉ laurentCoboundaryUnits A := by
  intro hmem
  haveI : _root_.IsReduced (A ⧸ nilradical A) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical 0)
  haveI : Nontrivial (A ⧸ nilradical A) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [Ideal.ne_top_iff_one, mem_nilradical]
    rintro ⟨n, hn⟩
    rw [one_pow] at hn
    exact one_ne_zero (α := A) hn
  have himg := (mem_laurentCoboundaryUnits_iff_map_reduced).mp hmem
  rw [laurentMap_tUnit] at himg
  exact not_tUnit_mem_laurentCoboundaryUnits_reduced himg

end AlgebraicGeometry
