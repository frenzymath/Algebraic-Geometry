/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.TwoChartCechPicTrivial
import AlgebraicJacobian.Algebra.LaurentUnits

/-!
# THE ℙ¹ TWO-CHART COBOUNDARY SUBGROUP OVER A DOMAIN IS EXACTLY THE CONSTANTS

`Picard/TwoChartCechPicTrivial.lean` reduces triviality of a chart-trivial Picard class on a
two-chart cover to the purely algebraic question *are the overlap units all coboundaries?*.  This
file answers that question for the pinned ℙ¹ chart data — overlap ring `A[t,t⁻¹]`, chart rings
`A[t]` and `A[t⁻¹]` — over a **domain** `A`, in both directions:

> a Laurent unit is a coboundary **iff** it is `C c` for a unit `c` of `A`.

## Read this before using it: the answer is NO, and that is the correct answer

The criterion of the previous file asks for *every* overlap unit to be a coboundary.  Over a
domain that is **false**, and this file is what proves it false: `T 1 = t` is a unit of
`A[t,t⁻¹]` and is *not* a coboundary, because `t` is a unit of neither chart ring
(`Polynomial.isUnit_iff`: a unit of `A[t]` over a domain is a constant).

That is not an obstruction to the route — it is the statement that

```
Pic(ℙ¹_A)  =  A[t,t⁻¹]ˣ ⧸ (A[t]ˣ · A[t⁻¹]ˣ)  =  ℤ,
```

the classical computation, with the class of `t` generating.  The consequence for the
representability route is the useful one, and it is a *sharpening* rather than a defeat: the
hypothesis that must be supplied is not "all overlap units are coboundaries" but "the overlap
unit presenting **this** class has exponent zero" — i.e. exactly a degree-zero condition, which
is what `pic0Subgroup` cuts out in the first place.  A lane pricing the ring case should price
that, not the false universal form.

## Where `IsDomain` is used, and where it is not

* the **forward** direction (a coboundary is a constant) uses it, through
  `Polynomial.isUnit_iff` on each chart — over a general ring `A[t]` has non-constant units
  (`1 + εt` with `ε² = 0`) and the direction genuinely fails;
* the **converse** (a constant unit is a coboundary) uses **no** hypothesis on `A`: `C c` is the
  left chart's image of the polynomial unit `C c`.  The `omit` marker records that.

`Algebra/LaurentUnits.lean` already proves the necessity of `IsDomain` for the Laurent unit
classification as a theorem rather than a remark; this file is the two-chart-cohomological
consequence of that classification.

## Main declarations

* `AlgebraicGeometry.rightChart` — the second chart map `A[t] → A[t,t⁻¹]`, `t ↦ T (-1)`.  The
  two charts of ℙ¹ are both polynomial rings; they differ by which of `t, t⁻¹` they send `X` to.
* `AlgebraicGeometry.C_unit_mem_laurentCoboundaryUnits` — a constant unit is a coboundary, over
  any commutative ring.
* `AlgebraicGeometry.eq_C_of_mem_laurentCoboundaryUnits` — over a domain, a coboundary is a
  constant unit.
* `AlgebraicGeometry.mem_laurentCoboundaryUnits_iff` — the two together, as an `iff`.
* `AlgebraicGeometry.not_tUnit_mem_laurentCoboundaryUnits` — `t` is **not** a coboundary over a
  domain: the generator of `Pic(ℙ¹_A) = ℤ`, and the refutation of the universal form of the
  criterion's hypothesis.  `IsDomain` alone suffices — a separate `Nontrivial` binder was
  redundant (the `overlappingInstances` linter caught it), which is worth noting because the
  statement *is* false at the zero ring for the trivial reason that `t = 1` there.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A]

/-- The second ℙ¹ chart map `A[t] → A[t,t⁻¹]`, sending the coordinate to `t⁻¹`.  The first is
mathlib's `Polynomial.toLaurent` (`X ↦ T 1`); both chart rings are polynomial rings, and the
cover is recorded by *which* Laurent monomial the coordinate goes to. -/
noncomputable def rightChart (A : Type u) [CommRing A] :
    Polynomial A →+* LaurentPolynomial A :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))

@[simp]
lemma rightChart_X : (rightChart A) Polynomial.X = LaurentPolynomial.T (-1) := by
  simp [rightChart]

@[simp]
lemma rightChart_C (c : A) : (rightChart A) (Polynomial.C c) = LaurentPolynomial.C c := by
  simp [rightChart]

/-- The coboundary subgroup of the ℙ¹ overlap units: products of images of the two chart unit
groups.  Abbreviation for the `TruncExpCech` subgroup at the two chart maps. -/
noncomputable abbrev laurentCoboundaryUnits (A : Type u) [CommRing A] :
    Subgroup (LaurentPolynomial A)ˣ :=
  TruncExpCech.cechCoboundaryUnits
    (Polynomial.toLaurent : Polynomial A →+* LaurentPolynomial A) (rightChart A)

/-- **A constant unit is a coboundary** — no hypothesis on `A`.

`LaurentPolynomial.C c` is the left chart's image of the polynomial unit `Polynomial.C c`. -/
theorem C_unit_mem_laurentCoboundaryUnits (c : Aˣ) :
    (Units.map (LaurentPolynomial.C : A →+* LaurentPolynomial A).toMonoidHom c)
      ∈ laurentCoboundaryUnits A := by
  have h : Units.map (LaurentPolynomial.C : A →+* LaurentPolynomial A).toMonoidHom c
      = Units.map (Polynomial.toLaurent : Polynomial A →+* LaurentPolynomial A).toMonoidHom
          (Units.map (Polynomial.C : A →+* Polynomial A).toMonoidHom c) := by
    ext; simp
  rw [h]
  exact TruncExpCech.unitsMap_mem_cechCoboundaryUnits_left _ _ _

/-- **Over a domain, a coboundary is a constant unit.**

Both chart unit groups consist of constants (`Polynomial.isUnit_iff`, which needs `IsDomain`),
and both chart maps send `Polynomial.C c` to `LaurentPolynomial.C c`, so a product of chart
images is `C` of the product.

This is the direction that fails over a general ring: `1 + εt` is a unit of `A[t]` whenever
`ε² = 0`, so `A[t]ˣ` is bigger than the constants there. -/
theorem eq_C_of_mem_laurentCoboundaryUnits [IsDomain A] {u : (LaurentPolynomial A)ˣ}
    (hu : u ∈ laurentCoboundaryUnits A) :
    ∃ c : A, IsUnit c ∧ (u : LaurentPolynomial A) = LaurentPolynomial.C c := by
  obtain ⟨v, w, hvw⟩ := TruncExpCech.mem_cechCoboundaryUnits.mp hu
  obtain ⟨cv, hcv, hv⟩ := Polynomial.isUnit_iff.mp v.isUnit
  obtain ⟨cw, hcw, hw⟩ := Polynomial.isUnit_iff.mp w.isUnit
  refine ⟨cv * cw, hcv.mul hcw, ?_⟩
  rw [← hvw]
  change Polynomial.toLaurent (v : Polynomial A) * (rightChart A) (w : Polynomial A)
    = LaurentPolynomial.C (cv * cw)
  rw [← hv, ← hw]
  simp [rightChart, map_mul]

/-- **THE CHARACTERIZATION**: over a domain, the coboundary subgroup is exactly the constants.

So the two-chart Čech Picard group of `ℙ¹_A` is the Laurent units modulo the constants, which by
`LaurentPolynomial.unitsEquiv` (`Aˣ × ℤ`) is `ℤ`. -/
theorem mem_laurentCoboundaryUnits_iff [IsDomain A] {u : (LaurentPolynomial A)ˣ} :
    u ∈ laurentCoboundaryUnits A
      ↔ ∃ c : A, IsUnit c ∧ (u : LaurentPolynomial A) = LaurentPolynomial.C c := by
  refine ⟨eq_C_of_mem_laurentCoboundaryUnits, ?_⟩
  rintro ⟨c, hc, hu⟩
  obtain ⟨cu, rfl⟩ := hc
  have h : u = Units.map (LaurentPolynomial.C : A →+* LaurentPolynomial A).toMonoidHom cu :=
    Units.ext hu
  rw [h]
  exact C_unit_mem_laurentCoboundaryUnits cu

/-- **`t` IS NOT A COBOUNDARY** over a nontrivial domain — the generator of
`Pic(ℙ¹_A) = ℤ`, and the refutation of the *universal* form of the criterion's hypothesis in
`Picard/TwoChartCechPicTrivial.lean`.

If it were, it would be a constant by `eq_C_of_mem_laurentCoboundaryUnits`; but `T 1` has its
support in degree `1`, and comparing coefficients at `0` gives `0 = c` while at `1` gives
`1 = 0`.

Recorded as a theorem rather than a remark because the previous file's criterion asks for *every*
overlap unit to be a coboundary, and a consumer must know that that hypothesis is FALSE here — so
the thing to supply is a degree-zero condition on the presenting unit, not the universal form. -/
theorem not_tUnit_mem_laurentCoboundaryUnits [IsDomain A] :
    LaurentPolynomial.tUnit (R := A) 1 ∉ laurentCoboundaryUnits A := by
  intro hmem
  obtain ⟨c, hcu, hc⟩ := eq_C_of_mem_laurentCoboundaryUnits hmem
  rw [LaurentPolynomial.tUnit_coe] at hc
  -- `T 1 = C 1 * T 1` and `C c = C c * T 0`, so `exp_unique` gives `1 = 0`
  have h : (LaurentPolynomial.C (1 : A) * LaurentPolynomial.T (1 : ℤ))
      = LaurentPolynomial.C c * LaurentPolynomial.T (0 : ℤ) := by
    rw [map_one, one_mul, LaurentPolynomial.T_zero, mul_one]
    exact hc
  exact absurd (LaurentPolynomial.exp_unique (one_ne_zero (α := A)) h) one_ne_zero

end AlgebraicGeometry
