/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4PrincipalDivisorDegree
import HartshorneLib.Chapter4ProductFormulaBridge

/-!
# Hartshorne II.6: finite order-sum product-formula interface

The geometric product formula for a complete nonsingular curve is deliberately
kept as an explicit input in `Chapter4DegreeClass`.  This file names the
finite-support sum of local orders and records the algebraic interface around
that input.  In particular, the order sum agrees with divisor degree, and its
zero predicate is equivalent to the degree-zero predicate used by the divisor
class group.  No global vanishing assertion is introduced here.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-! ### The finite local-order sum -/

/-- The finite sum of the additive local orders of a rational function. -/
noncomputable def principalOrderSum (g : X.left.functionFieldˣ) : ℤ :=
  ∑ p ∈ (orderZAt_support_finite X.hom g).toFinset,
    Multiplicative.toAdd (orderZAt X.hom p.2 g)

/-- The local-order sum is exactly the degree of the associated principal divisor. -/
theorem principalOrderSum_eq_degree (g : X.left.functionFieldˣ) :
    principalOrderSum (X := X) g = CurveDivisor.degree (principalDivisor g) := by
  unfold principalOrderSum
  exact (degree_principalDivisor_eq_sum_orderZAt g).symm

/-! ### Algebraic laws -/

theorem principalOrderSum_mul (g h : X.left.functionFieldˣ) :
    principalOrderSum (X := X) (g * h) =
      principalOrderSum g + principalOrderSum h := by
  calc
    principalOrderSum (X := X) (g * h) =
        CurveDivisor.degree (principalDivisor (g * h)) :=
      principalOrderSum_eq_degree (X := X) (g * h)
    _ = CurveDivisor.degree (principalDivisor g) +
        CurveDivisor.degree (principalDivisor h) :=
      degree_principalDivisor_mul g h
    _ = principalOrderSum g + principalOrderSum h := by
      rw [← principalOrderSum_eq_degree (X := X) g,
        ← principalOrderSum_eq_degree (X := X) h]

@[simp]
theorem principalOrderSum_one :
    principalOrderSum (X := X) (1 : X.left.functionFieldˣ) = 0 := by
  rw [principalOrderSum_eq_degree, degree_principalDivisor_one]

theorem principalOrderSum_inv (g : X.left.functionFieldˣ) :
    principalOrderSum (X := X) g⁻¹ = -principalOrderSum g := by
  calc
    principalOrderSum (X := X) g⁻¹ =
        CurveDivisor.degree (principalDivisor g⁻¹) :=
      principalOrderSum_eq_degree (X := X) g⁻¹
    _ = -CurveDivisor.degree (principalDivisor g) :=
      degree_principalDivisor_inv g
    _ = -principalOrderSum g := by
      rw [principalOrderSum_eq_degree (X := X) g]

theorem principalOrderSum_div (g h : X.left.functionFieldˣ) :
    principalOrderSum (X := X) (g / h) =
      principalOrderSum g - principalOrderSum h := by
  calc
    principalOrderSum (X := X) (g / h) =
        CurveDivisor.degree (principalDivisor (g / h)) :=
      principalOrderSum_eq_degree (X := X) (g / h)
    _ = CurveDivisor.degree (principalDivisor g) -
        CurveDivisor.degree (principalDivisor h) :=
      degree_principalDivisor_div g h
    _ = principalOrderSum g - principalOrderSum h := by
      rw [principalOrderSum_eq_degree (X := X) g,
        principalOrderSum_eq_degree (X := X) h]

theorem principalOrderSum_pow (g : X.left.functionFieldˣ) (n : ℕ) :
    principalOrderSum (X := X) (g ^ n) =
      (n : ℤ) * principalOrderSum g := by
  calc
    principalOrderSum (X := X) (g ^ n) =
        CurveDivisor.degree (principalDivisor (g ^ n)) :=
      principalOrderSum_eq_degree (X := X) (g ^ n)
    _ = (n : ℤ) * CurveDivisor.degree (principalDivisor g) :=
      degree_principalDivisor_pow g n
    _ = (n : ℤ) * principalOrderSum g := by
      rw [principalOrderSum_eq_degree (X := X) g]

/-! ### Equivalent zero predicates -/

/-- The finite order-sum form of the principal-divisor product formula. -/
def HasPrincipalOrderSumZero : Prop :=
  ∀ g : X.left.functionFieldˣ, principalOrderSum (X := X) g = 0

/-- The finite order-sum formulation is equivalent to degree zero for principal divisors. -/
theorem hasPrincipalOrderSumZero_iff_principalDivisorsHaveDegreeZero :
    HasPrincipalOrderSumZero (X := X) ↔
      PrincipalDivisorsHaveDegreeZero (k := k) (X := X) := by
  constructor
  · intro h g
    rw [← principalOrderSum_eq_degree (X := X) g]
    exact h g
  · intro h g
    rw [principalOrderSum_eq_degree (X := X) g]
    exact h g

/-- A residue-weighted product formula implies the finite order-sum formula. -/
theorem hasPrincipalOrderSumZero_of_residueWeightedProductFormula
    (hformula : ∀ g : X.left.functionFieldˣ,
      CurveDivisor.residueWeightedDegree (principalDivisor g) = 0) :
    HasPrincipalOrderSumZero (X := X) := by
  intro g
  rw [principalOrderSum_eq_degree (X := X) g,
    ← CurveDivisor.residueWeightedDegree_eq_degree]
  exact hformula g

/-- Conversely, the finite order-sum formula gives the residue-weighted one on
an algebraically closed curve. -/
theorem residueWeightedProductFormula_of_hasPrincipalOrderSumZero
    (hzero : HasPrincipalOrderSumZero (X := X)) :
    ∀ g : X.left.functionFieldˣ,
      CurveDivisor.residueWeightedDegree (principalDivisor g) = 0 := by
  intro g
  rw [CurveDivisor.residueWeightedDegree_eq_degree,
    ← principalOrderSum_eq_degree (X := X) g]
  exact hzero g

end Hartshorne
