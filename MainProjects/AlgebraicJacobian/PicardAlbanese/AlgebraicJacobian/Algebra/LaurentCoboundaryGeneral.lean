/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.LaurentGeneralNilpotentCoboundary
import AlgebraicJacobian.Algebra.LaurentCoboundaryReduced

/-!
# THE ℙ¹ TWO-CHART COBOUNDARY SUBGROUP OVER AN ARBITRARY RING

Assembling the three landed pieces, the ℙ¹ two-chart coboundary subgroup `laurentCoboundaryUnits A`
is now characterised over an **arbitrary** commutative ring — no domain, reducedness, or field
hypothesis:

> a Laurent unit is a coboundary **iff** it is `C c · (1 + z)` for a unit `c` of `A` and a
> **nilpotent** Laurent polynomial `z`.

Equivalently: the coboundary subgroup is exactly the **exponent-zero** units — those with no
`T`-degree, i.e. a constant unit deformed by a nilpotent.  This is `Pic(ℙ¹_A) = ℤ` in the sharp
form that survives base change to a non-reduced ring: the class of a Laurent unit is its exponent,
and a unit presents the trivial class iff its exponent is `0`.

The two directions:

* **forward** (a coboundary is `C c · (1 + z)`): `eq_C_mul_one_add_nilpotent_of_mem_…`
  (`Algebra/LaurentCoboundaryReduced.lean`) — a product of chart units is a constant times a
  unipotent;
* **backward** (`C c · (1 + z)` is a coboundary): `C c` is a coboundary
  (`C_unit_mem_laurentCoboundaryUnits`) and `1 + z` is a coboundary for nilpotent `z`
  (`nilpotent_one_add_mem_laurentCoboundaryUnits`), and coboundaries are a subgroup.

## Main declarations

* `AlgebraicGeometry.C_mul_one_add_nilpotent_mem_laurentCoboundaryUnits` — the backward direction.
* `AlgebraicGeometry.mem_laurentCoboundaryUnits_iff_general` — the arbitrary-ring characterisation.
-/

set_option autoImplicit false

universe u

open CategoryTheory LaurentPolynomial

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A]

/-- **`C c · (1 + z)` is a coboundary** for a unit `c` and a nilpotent Laurent polynomial `z`.

`C c` is a coboundary (`C_unit_mem_laurentCoboundaryUnits`), `1 + z` is a coboundary
(`nilpotent_one_add_mem_laurentCoboundaryUnits`), and coboundaries form a subgroup. -/
theorem C_mul_one_add_nilpotent_mem_laurentCoboundaryUnits {c : A} (hc : IsUnit c)
    {z : LaurentPolynomial A} (hz : IsNilpotent z) (u : (LaurentPolynomial A)ˣ)
    (hu : (u : LaurentPolynomial A) = LaurentPolynomial.C c * (1 + z)) :
    u ∈ laurentCoboundaryUnits A := by
  obtain ⟨cu, rfl⟩ := hc
  have hzu : IsUnit (1 + z) := hz.isUnit_one_add
  have hfact : u = (Units.map (LaurentPolynomial.C : A →+* LaurentPolynomial A).toMonoidHom cu)
      * hzu.unit := by
    apply Units.ext
    rw [hu]; simp [Units.coe_map]
  rw [hfact]
  exact Subgroup.mul_mem _ (C_unit_mem_laurentCoboundaryUnits cu)
    (nilpotent_one_add_mem_laurentCoboundaryUnits hz hzu.unit rfl)

/-- **THE ARBITRARY-RING CHARACTERISATION**: a Laurent unit is a two-chart coboundary **iff** it
is `C c · (1 + z)` for a unit `c` and a nilpotent `z` — a constant unit times a unipotent, i.e.
exponent zero.  Holds over an arbitrary commutative ring, with no domain, reducedness, or field
hypothesis. -/
theorem mem_laurentCoboundaryUnits_iff_general {u : (LaurentPolynomial A)ˣ} :
    u ∈ laurentCoboundaryUnits A
      ↔ ∃ (c : A) (z : LaurentPolynomial A), IsUnit c ∧ IsNilpotent z ∧
          (u : LaurentPolynomial A) = LaurentPolynomial.C c * (1 + z) := by
  refine ⟨eq_C_mul_one_add_nilpotent_of_mem_laurentCoboundaryUnits, ?_⟩
  rintro ⟨c, z, hc, hz, hu⟩
  exact C_mul_one_add_nilpotent_mem_laurentCoboundaryUnits hc hz u hu

end AlgebraicGeometry
