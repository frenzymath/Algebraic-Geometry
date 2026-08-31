/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.LaurentTwoChartCoboundary

/-!
# THE ℙ¹ TWO-CHART COBOUNDARY SUBGROUP: THE REDUCED CASE, AND THE GENERAL-RING EXPONENT

`Picard/LaurentTwoChartCoboundary.lean` characterises the ℙ¹ two-chart coboundary subgroup
`laurentCoboundaryUnits A` — a Laurent unit is a coboundary **iff** it is `C c` for a unit `c` —
**over a domain**, and records why the forward direction (a coboundary is a constant) needs the
domain: `Polynomial.isUnit_iff` sees only constant units of `A[X]`, but at a non-reduced ring
`1 + C e · p` with `e² = 0` is a non-constant unit.  `Algebra/LaurentNilpotentCoboundary.lean`
then handles the opposite extreme — a unit congruent to `1` modulo a **nilpotent** is a
coboundary, over an arbitrary ring — leaving the two remaining pieces named in its header: the
**reduced** case, and the general-ring bridge from a degree/exponent-zero condition to the
constant-modulo-nilpotent normal form.

This file supplies both, **adding no hypothesis to any existing statement** — it weakens
`IsDomain` to `IsReduced` (a strict weakening: `k × k` is reduced and not a domain), and it
states the general-ring forward structure with no ring hypothesis at all.

## 1. Over a reduced ring, a coboundary is a constant unit

`Polynomial.isUnit_iff_coeff_isUnit_isNilpotent` classifies units of `A[X]` over *any* commutative
ring — unit constant term, nilpotent higher coefficients.  Over a **reduced** ring the nilpotents
are `0`, so a polynomial unit is a constant unit, and the exact argument of
`eq_C_of_mem_laurentCoboundaryUnits` goes through with `IsReduced A` in place of `IsDomain A`.
This closes the reduced case: for reduced `A`,

```
Pic(ℙ¹_A)  =  A[t,t⁻¹]ˣ ⧸ (A[t]ˣ · A[t⁻¹]ˣ)  =  ℤ,
```

and `t` is the generator (`not_tUnit_mem_laurentCoboundaryUnits_reduced`).

## 2. Over an arbitrary ring, a coboundary is `C c · (1 + z)` with `z` nilpotent

This is the general-ring **exponent-zero** structure.
`Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`
factors each chart unit as `C cᵢ · (1 + Nᵢ)` with `Nᵢ` nilpotent, and the product of the two chart
images is `C (c₀c₁) · (1 + z)` with `z` a nilpotent Laurent element (sum and product of the two
nilpotent transported parts).  A coboundary therefore has *no `T`-exponent*: its class in the
`ℤ` of the domain computation is `0`, and the deviation from a constant is a nilpotent — exactly
the direction a "degree map to `ℤ`" would record, without needing the map (which does not exist
over a general ring).  The matching converse — that *every* such `C c · (1 + z)` with `z` an
**arbitrary** nilpotent Laurent element is a coboundary — is
`C_mul_one_add_nilpotent_mem_laurentCoboundaryUnits` (`LaurentCoboundaryGeneral.lean`), resting on
the multi-generator `nilpotent_one_add_mem_laurentCoboundaryUnits`
(`LaurentGeneralNilpotentCoboundary.lean`); the single-generator
`nilpotent_isUnit_mem_laurentCoboundaryUnits` (`LaurentNilpotentCoboundary.lean`) covers only the
scalar case `1 + C e · f` and does **not** by itself pin the subgroup.  Together the forward
direction here and that general converse give the arbitrary-ring characterisation
`mem_laurentCoboundaryUnits_iff_general`: the coboundary subgroup is *exactly*
`{C c · (1 + z) : c ∈ Aˣ, z nilpotent}`.

## Main declarations

* `AlgebraicGeometry.polyUnit_eq_C_of_reduced` — a polynomial unit over a reduced ring is a
  constant unit.
* `AlgebraicGeometry.eq_C_of_mem_laurentCoboundaryUnits_reduced` — over a reduced ring, a
  coboundary is a constant unit (the forward direction, with `IsDomain` weakened to `IsReduced`).
* `AlgebraicGeometry.mem_laurentCoboundaryUnits_iff_reduced` — the reduced-ring characterisation
  as an `iff`.
* `AlgebraicGeometry.not_tUnit_mem_laurentCoboundaryUnits_reduced` — `t` is not a coboundary over
  a nontrivial reduced ring: `Pic(ℙ¹_A) = ℤ` over reduced `A`.
* `AlgebraicGeometry.polyUnit_eq_C_mul_one_add_nilpotent` — a polynomial unit over an arbitrary
  ring is `C c · (1 + N)`, `c` a unit and `N` nilpotent.
* `AlgebraicGeometry.eq_C_mul_one_add_nilpotent_of_mem_laurentCoboundaryUnits` — the general-ring
  forward structure: a coboundary is `C c · (1 + z)`, `c` a unit and `z` a nilpotent Laurent
  element (the exponent-zero normal form).
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A]

/-! ## The reduced case: a coboundary is a constant unit -/

/-- **A unit of `A[X]` over a reduced ring is a constant unit.**

`Polynomial.isUnit_iff_coeff_isUnit_isNilpotent` gives a unit constant term and nilpotent higher
coefficients; over a reduced ring the latter are `0`, so `P = C (P.coeff 0)`.  This is the reduced
replacement for `Polynomial.isUnit_iff` (which needs `IsDomain`). -/
theorem polyUnit_eq_C_of_reduced [_root_.IsReduced A] {P : Polynomial A} (hP : IsUnit P) :
    ∃ c : A, IsUnit c ∧ P = Polynomial.C c := by
  rw [Polynomial.isUnit_iff_coeff_isUnit_isNilpotent] at hP
  obtain ⟨h0, hn⟩ := hP
  refine ⟨P.coeff 0, h0, ?_⟩
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · simp only [Polynomial.coeff_C, if_neg hi]
    exact (hn i hi).eq_zero

/-- **Over a reduced ring, a coboundary is a constant unit.**

The forward direction of the characterisation, with `IsDomain` weakened to `IsReduced`: both chart
unit groups consist of constants (`polyUnit_eq_C_of_reduced`), and both chart maps send
`Polynomial.C c` to `LaurentPolynomial.C c`.  This is exactly the argument of
`eq_C_of_mem_laurentCoboundaryUnits`, run over the strictly larger class of reduced rings. -/
theorem eq_C_of_mem_laurentCoboundaryUnits_reduced [_root_.IsReduced A]
    {u : (LaurentPolynomial A)ˣ} (hu : u ∈ laurentCoboundaryUnits A) :
    ∃ c : A, IsUnit c ∧ (u : LaurentPolynomial A) = LaurentPolynomial.C c := by
  obtain ⟨v, w, hvw⟩ := TruncExpCech.mem_cechCoboundaryUnits.mp hu
  obtain ⟨cv, hcv, hv⟩ := polyUnit_eq_C_of_reduced v.isUnit
  obtain ⟨cw, hcw, hw⟩ := polyUnit_eq_C_of_reduced w.isUnit
  refine ⟨cv * cw, hcv.mul hcw, ?_⟩
  rw [← hvw]
  change Polynomial.toLaurent (v : Polynomial A) * (rightChart A) (w : Polynomial A)
    = LaurentPolynomial.C (cv * cw)
  rw [hv, hw]
  simp [rightChart, map_mul]

/-- **THE REDUCED-RING CHARACTERISATION**: over a reduced ring the coboundary subgroup is exactly
the constants, so the two-chart Čech Picard group of `ℙ¹_A` is `A[t,t⁻¹]ˣ ⧸ Aˣ = ℤ`. -/
theorem mem_laurentCoboundaryUnits_iff_reduced [_root_.IsReduced A] {u : (LaurentPolynomial A)ˣ} :
    u ∈ laurentCoboundaryUnits A
      ↔ ∃ c : A, IsUnit c ∧ (u : LaurentPolynomial A) = LaurentPolynomial.C c := by
  refine ⟨eq_C_of_mem_laurentCoboundaryUnits_reduced, ?_⟩
  rintro ⟨c, hc, hu⟩
  obtain ⟨cu, rfl⟩ := hc
  have h : u = Units.map (LaurentPolynomial.C : A →+* LaurentPolynomial A).toMonoidHom cu :=
    Units.ext hu
  rw [h]
  exact C_unit_mem_laurentCoboundaryUnits cu

/-- **`t` IS NOT A COBOUNDARY** over a nontrivial reduced ring — the generator of
`Pic(ℙ¹_A) = ℤ`, and the refutation of the universal form of the two-chart criterion, now over
the strictly larger class of reduced rings.  Same coefficient comparison as the domain case:
if `T 1` were a constant, `exp_unique` would force `1 = 0`. -/
theorem not_tUnit_mem_laurentCoboundaryUnits_reduced [_root_.IsReduced A] [Nontrivial A] :
    LaurentPolynomial.tUnit (R := A) 1 ∉ laurentCoboundaryUnits A := by
  intro hmem
  obtain ⟨c, _, hc⟩ := eq_C_of_mem_laurentCoboundaryUnits_reduced hmem
  rw [LaurentPolynomial.tUnit_coe] at hc
  have h : (LaurentPolynomial.C (1 : A) * LaurentPolynomial.T (1 : ℤ))
      = LaurentPolynomial.C c * LaurentPolynomial.T (0 : ℤ) := by
    rw [map_one, one_mul, LaurentPolynomial.T_zero, mul_one]
    exact hc
  exact absurd (LaurentPolynomial.exp_unique (one_ne_zero (α := A)) h) one_ne_zero

/-! ## The general ring: a coboundary has exponent zero (constant times unipotent) -/

/-- **A unit of `A[X]` over an arbitrary ring is `C c · (1 + N)`**, `c` a unit and `N` nilpotent.

`Polynomial.isUnit_iff_coeff_isUnit_isNilpotent` gives a unit constant term `c = P.coeff 0` and
nilpotent higher part `P - C c`; dividing by `C c` leaves `1 + C c⁻¹ · (P - C c)`, and the second
summand is nilpotent (a nilpotent times anything, in a commutative ring). -/
theorem polyUnit_eq_C_mul_one_add_nilpotent {P : Polynomial A} (hP : IsUnit P) :
    ∃ (c : A) (N : Polynomial A), IsUnit c ∧ IsNilpotent N ∧ P = Polynomial.C c * (1 + N) := by
  obtain ⟨h0, hn⟩ := (Polynomial.isUnit_iff_coeff_isUnit_isNilpotent).mp hP
  obtain ⟨cu, hcu⟩ := h0
  have hND : IsNilpotent (P - Polynomial.C (P.coeff 0)) := by
    rw [Polynomial.isNilpotent_iff]
    intro i
    rcases eq_or_ne i 0 with rfl | hi
    · simp
    · rw [Polynomial.coeff_sub, Polynomial.coeff_C, if_neg hi, sub_zero]
      exact hn i hi
  refine ⟨P.coeff 0, Polynomial.C (↑cu⁻¹ : A) * (P - Polynomial.C (P.coeff 0)),
    ⟨cu, hcu⟩, (Commute.all _ _).isNilpotent_mul_left hND, ?_⟩
  have hccu : Polynomial.C (P.coeff 0) * Polynomial.C (↑cu⁻¹ : A) = 1 := by
    rw [← Polynomial.C_mul, ← hcu, ← Units.val_mul, mul_inv_cancel, Units.val_one, Polynomial.C_1]
  rw [mul_add, mul_one, ← mul_assoc, hccu, one_mul, add_sub_cancel]

/-- **THE GENERAL-RING FORWARD STRUCTURE**: over an arbitrary commutative ring a coboundary is
`C c · (1 + z)` with `c` a unit and `z` a **nilpotent** Laurent element.

Factor each chart unit as `C cᵢ · (1 + Nᵢ)` (`polyUnit_eq_C_mul_one_add_nilpotent`); transporting
`Nᵢ` through the two chart maps gives nilpotent Laurent elements `tv, tw`, and the product of the
two chart images is `C (cv·cw) · (1 + (tv + tw + tv·tw))`, whose deviation from the constant
`C (cv·cw)` is the nilpotent `z = tv + tw + tv·tw`.

This is the **exponent-zero** statement in the direction a consumer needs: a coboundary has no
`T`-exponent, and its class over the reduction is `1`.  There is no `ℤ`-valued degree map over a
general ring to say this with, so it is stated as a normal form; combined with
`nilpotent_isUnit_mem_laurentCoboundaryUnits` (the converse) it characterises the coboundary
subgroup at an arbitrary ring. -/
theorem eq_C_mul_one_add_nilpotent_of_mem_laurentCoboundaryUnits
    {u : (LaurentPolynomial A)ˣ} (hu : u ∈ laurentCoboundaryUnits A) :
    ∃ (c : A) (z : LaurentPolynomial A), IsUnit c ∧ IsNilpotent z ∧
      (u : LaurentPolynomial A) = LaurentPolynomial.C c * (1 + z) := by
  obtain ⟨v, w, hvw⟩ := TruncExpCech.mem_cechCoboundaryUnits.mp hu
  obtain ⟨cv, Nv, hcv, hNv, hv⟩ := polyUnit_eq_C_mul_one_add_nilpotent v.isUnit
  obtain ⟨cw, Nw, hcw, hNw, hw⟩ := polyUnit_eq_C_mul_one_add_nilpotent w.isUnit
  set tv : LaurentPolynomial A := Polynomial.toLaurent Nv with htv
  set tw : LaurentPolynomial A := rightChart A Nw with htw
  have htvN : IsNilpotent tv :=
    hNv.map (Polynomial.toLaurent : Polynomial A →+* LaurentPolynomial A)
  have htwN : IsNilpotent tw := hNw.map (rightChart A)
  refine ⟨cv * cw, tv + tw + tv * tw, hcv.mul hcw, ?_, ?_⟩
  · have h1 : IsNilpotent (tv + tw) := (Commute.all _ _).isNilpotent_add htvN htwN
    have h2 : IsNilpotent (tv * tw) := (Commute.all _ _).isNilpotent_mul_left htwN
    exact (Commute.all _ _).isNilpotent_add h1 h2
  · rw [← hvw]
    change Polynomial.toLaurent (v : Polynomial A) * (rightChart A) (w : Polynomial A) = _
    rw [hv, hw, map_mul, map_mul, Polynomial.toLaurent_C, rightChart_C,
      map_add, map_one, map_add, map_one, ← htv, ← htw, map_mul]
    ring

end AlgebraicGeometry
