/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.LaurentTwoChartCoboundary
import AlgebraicJacobian.Curve.P1

/-!
# NILPOTENT LAURENT UNITS ARE COBOUNDARIES — THE NON-REDUCED HALF, WITH NO DOMAIN HYPOTHESIS

`Picard/LaurentTwoChartCoboundary.lean` characterizes the ℙ¹ coboundary subgroup
`laurentCoboundaryUnits A` **over a domain**: a Laurent unit is a coboundary exactly when it is
`C` of a unit of `A`.  That binder is not cosmetic and both its author and
`Algebra/LaurentUnits.lean` record why it cannot simply be dropped: whenever `e² = 0` the element
`1 + C e * T 1` is a unit of `A[t]`, so at a non-reduced `A` the chart unit groups are strictly
bigger than the constants and `Polynomial.isUnit_iff` — the engine of that characterization — is
false.

**Every test ring in the `pic⁰` vanishing obligation is arbitrary**, `k[ε]` included.  So the
domain-only characterization does not reach the obligation, and the gap is exactly the
non-reduced directions.  This file closes those directions, in the direction a consumer needs:

> a Laurent unit congruent to `1` modulo a nilpotent **is** a coboundary,
> over an arbitrary commutative ring.

## Why this is the good direction, and not a repricing of the domain result

The domain characterization and this file point opposite ways and neither implies the other:

* over a domain, `eq_C_of_mem_laurentCoboundaryUnits` says the coboundary subgroup is *small*
  (only constants), which is what makes `Pic(ℙ¹_A) = ℤ` nonzero — `t` escapes it;
* here the coboundary subgroup is shown to *contain* every nilpotent deformation of `1`.  There
  is no tension: at a non-reduced ring the extra chart units are precisely the nilpotent
  deformations, and they are coboundaries because they deform `1` on *each chart separately*.

The mechanism is the **additive** Laurent span `LaurentPolynomial.exists_toLaurent_add_aeval`
(`Curve/P1.lean:62`, stated over an arbitrary `CommSemiring`) — i.e. `H¹(ℙ¹, 𝒪) = 0`, the same
input that computes the ℙ¹ cohomology.  Splitting the nilpotent part `z = p(T) + q(T⁻¹)`
additively and exponentiating gives chart units `1 + p` and `1 + q` whose product is `1 + z`,
because the cross term `p·q` carries `e²`.  That is the classical statement that a line bundle
trivial on the reduction, on a curve with vanishing `H¹`, is trivial: **the obstruction to
deforming a trivialization lives in `H¹` and there is none.**

## The nilpotency index: the cross term is fed back, not discarded

At a square-zero `e` the cross term `p·q` carries `e²` and vanishes, so the split is exact in one
step.  At a general nilpotent it does *not* vanish, and the naive "peel one layer at a time"
induction does not close — the residual is not smaller in any order that decreases.  What does
work is **halving**: the residual after dividing by the chart units is a deformation along
`e·e`, so an induction indexed by `2 ^ n` closes, each step squaring the deforming element
(`pow_two_isUnit_mem_laurentCoboundaryUnits`).  Newton-style convergence, and it is why the
arbitrary-nilpotent statement costs one induction rather than a different argument.

The square-zero case is kept as its own declaration
(`sqZero_isUnit_mem_laurentCoboundaryUnits`) because it is what a tangent-space consumer
(`k[ε]`) meets and it needs no index at all.

## What this does NOT do

It does **not** close the ring case of the `pic⁰` vanishing, and it adds no hypothesis to any
existing statement.  What it removes is one specific blocker: "the chart computation is only
available over a domain".  It is now available at every ring *for the classes congruent to `1`
modulo nilpotents*.

Two things remain, and neither is touched here:

* the **reduced** case.  A reduced ring is not a domain, and the exponent of a Laurent unit is
  only locally constant on `Spec A`, so the domain characterization does not extend to it by
  this route either.  Note what that means jointly with this file: nilpotents are *no longer*
  the obstruction, which is a change of where the ring case is blocked, not a discharge of it;
* the bridge from a **degree-zero hypothesis to a presenting unit**, unchanged and logically
  prior to all of this.  `Picard/TwoChartCechPicTrivial.lean`'s
  `cechPic_eq_one_of_forall_presenting_coboundary` is the form to aim at; the *universal* form
  is false already over a domain, by `not_tUnit_mem_laurentCoboundaryUnits`.

## Main declarations

* `AlgebraicGeometry.isUnit_one_add_C_mul_of_sqZero` — `1 + C e * p` is a unit of `A[X]` when
  `e² = 0`, over any commutative ring (the chart-unit supply).
* `AlgebraicGeometry.exists_chart_units_of_sqZero` — the **split**: `1 + C e * f` is a product
  of a unit of `A[T]` and a unit of `A[T⁻¹]`, by the additive Laurent span.
* `AlgebraicGeometry.sqZero_isUnit_mem_laurentCoboundaryUnits` — the same in the landed
  coboundary subgroup `laurentCoboundaryUnits`, the form the ℙ¹ Picard computation consumes.
* `AlgebraicGeometry.isUnit_one_add_C_mul_of_nilpotent` — the chart-unit supply at an arbitrary
  nilpotent.
* `AlgebraicGeometry.pow_two_isUnit_mem_laurentCoboundaryUnits` — the **halving induction**.
* `AlgebraicGeometry.nilpotent_isUnit_mem_laurentCoboundaryUnits` — **the headline**: an
  arbitrary nilpotent deformation of `1` is a coboundary, over an arbitrary commutative ring.
-/

set_option autoImplicit false

universe u

open Polynomial LaurentPolynomial

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A]

/-! ## Chart units from a square-zero element -/

/-- **A square-zero deformation of `1` is a unit of the chart ring** `A[X]`, over an arbitrary
commutative ring: `(1 + C e * p)(1 - C e * p) = 1` because the cross term carries `e²`.

This is the supply of chart units that `Polynomial.isUnit_iff` cannot see, and the reason that
lemma needs a domain: at `e ≠ 0` this unit is not a constant. -/
theorem isUnit_one_add_C_mul_of_sqZero {e : A} (he : e * e = 0) (p : Polynomial A) :
    IsUnit (1 + Polynomial.C e * p) := by
  have h0 : (Polynomial.C e * p) * (Polynomial.C e * p) = 0 := by
    calc (Polynomial.C e * p) * (Polynomial.C e * p)
        = (Polynomial.C e * Polynomial.C e) * (p * p) := by ring
      _ = 0 := by rw [← Polynomial.C_mul, he, map_zero, zero_mul]
  have hmul : (1 + Polynomial.C e * p) * (1 - Polynomial.C e * p) = 1 := by
    calc (1 + Polynomial.C e * p) * (1 - Polynomial.C e * p)
        = 1 - (Polynomial.C e * p) * (Polynomial.C e * p) := by ring
      _ = 1 := by rw [h0, sub_zero]
  exact IsUnit.of_mul_eq_one _ hmul

/-- **THE SPLIT**: a square-zero deformation of `1` in the overlap ring is the product of a
chart-`0` unit and a chart-`1` unit, over an arbitrary commutative ring.

The witnesses are `1 + C e * p` and `1 + C e * q` for the *additive* Laurent decomposition
`f = p(T) + q(T⁻¹)` (`LaurentPolynomial.exists_toLaurent_add_aeval`, i.e. `H¹(ℙ¹, 𝒪) = 0`).
Their product is `1 + C e * f` on the nose: the cross term is `C e * C e * (…) = 0`. -/
theorem exists_chart_units_of_sqZero {e : A} (he : e * e = 0) (f : LaurentPolynomial A) :
    ∃ v w : Polynomial A, IsUnit v ∧ IsUnit w ∧
      (1 + LaurentPolynomial.C e * f)
        = Polynomial.toLaurent v * rightChart A w := by
  obtain ⟨p, q, hf⟩ := LaurentPolynomial.exists_toLaurent_add_aeval f
  refine ⟨1 + Polynomial.C e * p, 1 + Polynomial.C e * q,
    isUnit_one_add_C_mul_of_sqZero he p, isUnit_one_add_C_mul_of_sqZero he q, ?_⟩
  have hCC : (LaurentPolynomial.C e : LaurentPolynomial A) * LaurentPolynomial.C e = 0 := by
    rw [← map_mul, he, map_zero]
  have hrq : rightChart A (1 + Polynomial.C e * q)
      = 1 + LaurentPolynomial.C e
          * Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial A) q := by
    rw [map_add, map_one, map_mul, rightChart_C, rightChart, Polynomial.aeval_def]
    simp only [Polynomial.coe_eval₂RingHom]
    congr 1
  have hlp : Polynomial.toLaurent (1 + Polynomial.C e * p)
      = 1 + LaurentPolynomial.C e * Polynomial.toLaurent p := by
    rw [map_add, map_one, map_mul, Polynomial.toLaurent_C]
  rw [hf, hrq, hlp]
  symm
  calc (1 + LaurentPolynomial.C e * Polynomial.toLaurent p)
        * (1 + LaurentPolynomial.C e
            * Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial A) q)
      = 1 + LaurentPolynomial.C e * Polynomial.toLaurent p
          + LaurentPolynomial.C e
            * Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial A) q
          + (LaurentPolynomial.C e * LaurentPolynomial.C e)
            * (Polynomial.toLaurent p
              * Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial A) q) := by
        ring
    _ = 1 + LaurentPolynomial.C e
          * (Polynomial.toLaurent p
            + Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial A) q) := by
        rw [hCC, zero_mul]; ring

/-! ## The coboundary-subgroup form -/

/-- **The square-zero case in the coboundary subgroup** — the form the ℙ¹ Picard computation
consumes, and the one that is *false* if you try to get it from the domain characterization.

Over a domain `eq_C_of_mem_laurentCoboundaryUnits` forces a coboundary to be a constant; here
`1 + C e * f` is a coboundary and is not constant.  There is no contradiction: at `e ≠ 0` the
ring is not a domain, which is exactly the case that lemma excludes. -/
theorem sqZero_isUnit_mem_laurentCoboundaryUnits {e : A} (he : e * e = 0)
    (f : LaurentPolynomial A) (u : (LaurentPolynomial A)ˣ)
    (hu : (u : LaurentPolynomial A) = 1 + LaurentPolynomial.C e * f) :
    u ∈ laurentCoboundaryUnits A := by
  obtain ⟨v, w, hv, hw, hvw⟩ := exists_chart_units_of_sqZero he f
  refine TruncExpCech.mem_cechCoboundaryUnits.mpr ⟨hv.unit, hw.unit, Units.ext ?_⟩
  simp only [Units.val_mul, Units.coe_map, IsUnit.unit_spec]
  rw [hu, hvw]
  rfl

/-! ## An arbitrary nilpotent, by halving the nilpotency index -/

/-- **The chart-unit supply for an arbitrary nilpotent**: `1 + C e * p` is a unit of `A[X]`
whenever `e` is nilpotent, since then `C e * p` is.  The square-zero case
(`isUnit_one_add_C_mul_of_sqZero`) is kept separately because it is the one a tangent-space
consumer meets and it needs no nilpotency index. -/
theorem isUnit_one_add_C_mul_of_nilpotent {e : A} (he : IsNilpotent e) (p : Polynomial A) :
    IsUnit (1 + Polynomial.C e * p) :=
  (Commute.isNilpotent_mul_right (Commute.all _ _)
    (he.map (Polynomial.C : A →+* Polynomial A))).isUnit_one_add

/-- **THE HALVING INDUCTION**: a Laurent unit of the form `1 + C e * f` with `e ^ (2 ^ n) = 0`
is a coboundary, over an arbitrary commutative ring.

The step is the reason the statement is indexed by `2 ^ n` rather than by a bare nilpotency
order.  Additively splitting `f = p(T) + q(T⁻¹)` and forming the chart units `1 + C e * p`,
`1 + C e * q` gives a coboundary `c` with

`c = u + C (e * e) * m`,   `m = p̃ · q̃`,

so the residual `c⁻¹ * u` is `1 + C (e * e) * (-(c⁻¹ m))` — a deformation along `e * e`, whose
index is *halved*: `(e * e) ^ (2 ^ n) = e ^ (2 ^ (n+1))`.  The induction hypothesis applies to it
and coboundaries are a subgroup, so `u = c * (c⁻¹ * u)` is one.

This is Newton-style convergence, and it is what makes the result available at every nilpotent
rather than only at a square-zero one: the cross term is not thrown away, it is fed back in at
twice the order. -/
theorem pow_two_isUnit_mem_laurentCoboundaryUnits (n : ℕ) : ∀ (e : A), e ^ (2 ^ n) = 0 →
    ∀ (f : LaurentPolynomial A) (u : (LaurentPolynomial A)ˣ),
      (u : LaurentPolynomial A) = 1 + LaurentPolynomial.C e * f →
      u ∈ laurentCoboundaryUnits A := by
  induction n with
  | zero =>
    intro e he f u hu
    have he0 : e = 0 := by simpa using he
    have hu1 : (u : LaurentPolynomial A) = 1 := by
      rw [hu, he0, map_zero, zero_mul, add_zero]
    have : u = 1 := Units.ext (by rw [hu1, Units.val_one])
    rw [this]
    exact Subgroup.one_mem _
  | succ n ih =>
    intro e he f u hu
    obtain ⟨p, q, hf⟩ := LaurentPolynomial.exists_toLaurent_add_aeval f
    have hen : IsNilpotent e := ⟨2 ^ (n + 1), he⟩
    set v : Polynomial A := 1 + Polynomial.C e * p with hv
    set w : Polynomial A := 1 + Polynomial.C e * q with hw
    have hvu : IsUnit v := isUnit_one_add_C_mul_of_nilpotent hen p
    have hwu : IsUnit w := isUnit_one_add_C_mul_of_nilpotent hen q
    have hrq : rightChart A w
        = 1 + LaurentPolynomial.C e
            * Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial A) q := by
      rw [hw, map_add, map_one, map_mul, rightChart_C, rightChart, Polynomial.aeval_def]
      simp only [Polynomial.coe_eval₂RingHom]
      congr 1
    have hlv : Polynomial.toLaurent v
        = 1 + LaurentPolynomial.C e * Polynomial.toLaurent p := by
      rw [hv, map_add, map_one, map_mul, Polynomial.toLaurent_C]
    set m : LaurentPolynomial A := Polynomial.toLaurent p
      * Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial A) q with hm
    have hprod : Polynomial.toLaurent v * rightChart A w
        = (1 + LaurentPolynomial.C e * f) + LaurentPolynomial.C (e * e) * m := by
      rw [hlv, hrq, hf, hm, map_mul]
      ring
    set c : (LaurentPolynomial A)ˣ := hvu.unit.map (Polynomial.toLaurent).toMonoidHom
      * hwu.unit.map (rightChart A).toMonoidHom with hc
    have hcval : (c : LaurentPolynomial A) = Polynomial.toLaurent v * rightChart A w := by
      simp only [hc, Units.val_mul, Units.coe_map, IsUnit.unit_spec]; rfl
    have hcmem : c ∈ laurentCoboundaryUnits A :=
      TruncExpCech.mem_cechCoboundaryUnits.mpr ⟨hvu.unit, hwu.unit, rfl⟩
    suffices hr : c⁻¹ * u ∈ laurentCoboundaryUnits A by
      have hu' : u = c * (c⁻¹ * u) := by group
      rw [hu']
      exact Subgroup.mul_mem _ hcmem hr
    have hsq : (e * e) ^ (2 ^ n) = 0 := by
      rw [← sq, ← pow_mul, ← pow_succ']
      exact he
    have hcu : (c : LaurentPolynomial A)
        = (u : LaurentPolynomial A) + LaurentPolynomial.C (e * e) * m := by
      rw [hcval, hprod, hu]
    refine ih (e * e) hsq (-((↑c⁻¹ : LaurentPolynomial A) * m)) (c⁻¹ * u) ?_
    have hinv : (↑c⁻¹ : LaurentPolynomial A) * (c : LaurentPolynomial A) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((c⁻¹ * u : (LaurentPolynomial A)ˣ) : LaurentPolynomial A)
        = (↑c⁻¹ : LaurentPolynomial A) * (u : LaurentPolynomial A) := by rw [Units.val_mul]
      _ = (↑c⁻¹ : LaurentPolynomial A)
            * ((c : LaurentPolynomial A) - LaurentPolynomial.C (e * e) * m) := by
          rw [hcu]; ring
      _ = 1 + LaurentPolynomial.C (e * e) * (-((↑c⁻¹ : LaurentPolynomial A) * m)) := by
          rw [mul_sub, hinv]; ring

/-- **THE HEADLINE, at an arbitrary nilpotent**: a Laurent unit congruent to `1` modulo a
nilpotent element is a coboundary, over an arbitrary commutative ring.

Any nilpotency order `e ^ N = 0` is absorbed by `N ≤ 2 ^ N`, so this follows from
`pow_two_isUnit_mem_laurentCoboundaryUnits` with no extra content. -/
theorem nilpotent_isUnit_mem_laurentCoboundaryUnits {e : A} (he : IsNilpotent e)
    (f : LaurentPolynomial A) (u : (LaurentPolynomial A)ˣ)
    (hu : (u : LaurentPolynomial A) = 1 + LaurentPolynomial.C e * f) :
    u ∈ laurentCoboundaryUnits A := by
  obtain ⟨N, hN⟩ := he
  refine pow_two_isUnit_mem_laurentCoboundaryUnits N e ?_ f u hu
  obtain ⟨j, hj⟩ : ∃ j, 2 ^ N = N + j :=
    ⟨2 ^ N - N, by have := Nat.lt_two_pow_self (n := N); omega⟩
  rw [hj, pow_add, hN, zero_mul]

end AlgebraicGeometry
