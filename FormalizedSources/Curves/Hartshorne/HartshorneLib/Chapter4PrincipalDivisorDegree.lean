/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4PrincipalDivisors

/-!
# Hartshorne II.6: the degree obstruction for principal divisors

The global product formula is the geometric input still missing from the
library.  This file isolates the algebraic part of that input: the degree of a
principal divisor is an additive obstruction on the multiplicative function
field, and pointwise order-one data force the principal divisor (and hence its
degree) to vanish.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-! ### Degree identities -/

theorem degree_principalDivisor_mul (g h : X.left.functionFieldˣ) :
    CurveDivisor.degree (principalDivisor (g * h)) =
      CurveDivisor.degree (principalDivisor g) +
        CurveDivisor.degree (principalDivisor h) := by
  rw [principalDivisor_mul, CurveDivisor.degree_add]

@[simp]
theorem degree_principalDivisor_one :
    CurveDivisor.degree (principalDivisor (1 : X.left.functionFieldˣ)) = 0 := by
  rw [principalDivisor_one, CurveDivisor.degree_zero]

theorem degree_principalDivisor_inv (g : X.left.functionFieldˣ) :
    CurveDivisor.degree (principalDivisor g⁻¹) =
      -CurveDivisor.degree (principalDivisor g) := by
  rw [principalDivisor_inv, CurveDivisor.degree_neg]

theorem degree_principalDivisor_div (g h : X.left.functionFieldˣ) :
    CurveDivisor.degree (principalDivisor (g / h)) =
      CurveDivisor.degree (principalDivisor g) -
        CurveDivisor.degree (principalDivisor h) := by
  rw [principalDivisor_div, CurveDivisor.degree_sub]

/- The additive degree law iterates over powers of a rational function. -/
theorem degree_principalDivisor_pow (g : X.left.functionFieldˣ) (n : ℕ) :
    CurveDivisor.degree (principalDivisor (g ^ n)) =
      (n : ℤ) * CurveDivisor.degree (principalDivisor g) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, principalDivisor_mul, CurveDivisor.degree_add, ih]
      push_cast
      ring

/-- The degree of a principal divisor is the finite sum of its local orders.

This is the finite-support normal form used by the global product formula;
the vanishing of this sum is the separate geometric input of II.6.10. -/
theorem degree_principalDivisor_eq_sum_orderZAt
    (g : X.left.functionFieldˣ) :
    CurveDivisor.degree (principalDivisor g) =
      ∑ p ∈ (orderZAt_support_finite X.hom g).toFinset,
        Multiplicative.toAdd (orderZAt X.hom p.2 g) := by
  simp only [CurveDivisor.degree, principalDivisor]
  rw [Finsupp.onFinset_sum]
  simp

/-! ### The degree obstruction as a homomorphism -/

/-- The degree of a principal divisor, viewed as an additive obstruction on
the multiplicative group of nonzero rational functions. -/
noncomputable def principalDivisorDegreeHom :
    Additive (X.left.functionFieldˣ) →+ ℤ :=
  (CurveDivisor.degreeHom (k := k) (X := X)).comp principalDivisorAddHom

@[simp]
theorem principalDivisorDegreeHom_apply
    (g : Additive (X.left.functionFieldˣ)) :
    principalDivisorDegreeHom g =
      CurveDivisor.degree (principalDivisor (Additive.toMul g)) := by
  change CurveDivisor.degreeHom (principalDivisor (Additive.toMul g)) = _
  rw [CurveDivisor.degreeHom_apply]

@[simp]
theorem principalDivisorDegreeHom_zero :
    principalDivisorDegreeHom (0 : Additive (X.left.functionFieldˣ)) = 0 :=
  map_zero principalDivisorDegreeHom

theorem principalDivisorDegreeHom_add
    (g h : Additive (X.left.functionFieldˣ)) :
    principalDivisorDegreeHom (g + h) =
      principalDivisorDegreeHom g + principalDivisorDegreeHom h :=
  map_add principalDivisorDegreeHom g h

/-! ### Pointwise vanishing -/

/-- If a rational function has order one at every non-generic point, its
principal divisor is zero. -/
theorem principalDivisor_eq_zero_of_orderZAt_eq_one
    (g : X.left.functionFieldˣ)
    (h : ∀ x : X.left, ∀ hx : x ≠ genericPoint X.left,
      orderZAt X.hom hx g = 1) :
    principalDivisor g = 0 := by
  apply CurveDivisor.ext_coeffAt
  intro x hx
  rw [coeffAt_principalDivisor, h x hx]
  simp [CurveDivisor.coeffAt_zero]

/-- A principal divisor is zero exactly when all of its local orders are
trivial. -/
theorem principalDivisor_eq_zero_iff_orderZAt_eq_one
    (g : X.left.functionFieldˣ) :
    principalDivisor g = 0 ↔
      ∀ x : X.left, ∀ hx : x ≠ genericPoint X.left,
        orderZAt X.hom hx g = 1 := by
  constructor
  · intro hg x hx
    apply Multiplicative.toAdd.injective
    have hc := congrArg (CurveDivisor.coeffAt hx) hg
    simpa only [coeffAt_principalDivisor, CurveDivisor.coeffAt_zero, toAdd_one] using hc
  · intro h
    exact principalDivisor_eq_zero_of_orderZAt_eq_one g h

theorem degree_principalDivisor_eq_zero_of_orderZAt_eq_one
    (g : X.left.functionFieldˣ)
    (h : ∀ x : X.left, ∀ hx : x ≠ genericPoint X.left,
      orderZAt X.hom hx g = 1) :
    CurveDivisor.degree (principalDivisor g) = 0 := by
  rw [principalDivisor_eq_zero_of_orderZAt_eq_one g h]
  exact CurveDivisor.degree_zero

/-! ### Global units -/

/-- A global unit has trivial principal divisor.

The germ of a global unit is a unit at every stalk, so its order is one at
every non-generic point.  This is the concrete geometric case of the
pointwise vanishing criterion above. -/
theorem principalDivisor_globalUnit (s : Γ(X.left, ⊤)ˣ) :
    principalDivisor
        (Units.map
          ((X.left.presheaf.germ ⊤ (genericPoint X.left) trivial).hom.toMonoidHom)
          s) = 0 := by
  let g : X.left.functionFieldˣ :=
    Units.map
      ((X.left.presheaf.germ ⊤ (genericPoint X.left) trivial).hom.toMonoidHom) s
  apply CurveDivisor.ext_coeffAt
  intro x hx
  rw [coeffAt_principalDivisor]
  have hord : orderZAt X.hom hx g = 1 := by
    rw [orderZAt_eq_one_iff]
    change orderAt X.hom hx
      ((X.left.presheaf.germ ⊤ (genericPoint X.left) trivial).hom
        (s : Γ(X.left, ⊤))) = 1
    apply orderAt_eq_one_of_mem_basicOpen X.hom hx
      (s : Γ(X.left, ⊤)) trivial
    rw [X.left.mem_basicOpen_top]
    exact IsUnit.map (X.left.presheaf.germ ⊤ x trivial).hom s.isUnit
  change Multiplicative.toAdd (orderZAt X.hom hx g) = _
  rw [hord, toAdd_one, CurveDivisor.coeffAt_zero]

/-- Consequently, the degree obstruction vanishes on global units. -/
theorem degree_principalDivisor_globalUnit (s : Γ(X.left, ⊤)ˣ) :
    CurveDivisor.degree
        (principalDivisor
          (Units.map
            ((X.left.presheaf.germ ⊤ (genericPoint X.left) trivial).hom.toMonoidHom)
            s)) = 0 := by
  rw [principalDivisor_globalUnit s, CurveDivisor.degree_zero]

end Hartshorne
