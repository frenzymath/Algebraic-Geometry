/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4PrincipalDivisorDegree
import HartshorneLib.Chapter4DivisorSupport

/-!
# Support of a principal divisor

The finite support used to define a principal divisor is exactly its divisor
support.  This file records that correspondence and rewrites the degree as a
sum indexed by the resulting divisor support.  No global product formula is
used: the statements are finite-support consequences of the local order API.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

namespace CurveDivisor

section
  classical

/-! ## Local support -/

/- The coefficient-level form is useful when a divisor is compared pointwise. -/
theorem coeffAt_principalDivisor_eq_zero_iff
    (g : X.left.functionFieldˣ)
    {x : X.left} (hx : x ≠ genericPoint X.left) :
    coeffAt hx (principalDivisor g) = 0 ↔
      orderZAt X.hom hx g = 1 := by
  rw [coeffAt_principalDivisor]
  constructor
  · intro h
    apply Multiplicative.toAdd.injective
    simp [h]
  · intro h
    rw [h, toAdd_one]

/-- A point belongs to the support of a principal divisor exactly when the
corresponding local order is nontrivial. -/
theorem mem_support_principalDivisor_iff
    (g : X.left.functionFieldˣ)
    (p : {x : X.left // x ≠ genericPoint X.left}) :
    p ∈ support (principalDivisor g) ↔
      orderZAt X.hom p.2 g ≠ 1 := by
  rw [mem_support_iff, coeffAt_principalDivisor]
  constructor
  · intro h horder
    apply h
    rw [horder, toAdd_one]
  · intro h hcoeff
    apply h
    apply Multiplicative.toAdd.injective
    rw [hcoeff, toAdd_one]

/-! ## Finite support -/

/-- The support of a principal divisor is the finite set of points where its
local order is nontrivial. -/
theorem support_principalDivisor
    (g : X.left.functionFieldˣ) :
    support (principalDivisor g) =
      (orderZAt_support_finite X.hom g).toFinset := by
  ext p
  rw [mem_support_principalDivisor_iff]
  rw [Set.Finite.mem_toFinset]
  rfl

@[simp]
theorem support_principalDivisor_one :
    support (principalDivisor (1 : X.left.functionFieldˣ)) = ∅ := by
  rw [principalDivisor_one, support_zero]

theorem support_principalDivisor_inv
    (g : X.left.functionFieldˣ) :
    support (principalDivisor g⁻¹) = support (principalDivisor g) := by
  rw [principalDivisor_inv, support_neg_eq]

@[simp]
theorem support_principalDivisor_eq_empty_iff
    (g : X.left.functionFieldˣ) :
    support (principalDivisor g) = ∅ ↔
      (orderZAt_support_finite X.hom g).toFinset = ∅ := by
  rw [support_principalDivisor]

theorem principalDivisor_eq_zero_iff_support_eq_empty
    (g : X.left.functionFieldˣ) :
    principalDivisor g = 0 ↔ support (principalDivisor g) = ∅ := by
  rw [support_eq_empty_iff]

/-! ## Degree in support form -/

/-- The degree of a principal divisor is the sum of its local orders over its
actual divisor support. -/
theorem degree_principalDivisor_eq_sum_support
    (g : X.left.functionFieldˣ) :
    degree (principalDivisor g) =
      ∑ p ∈ support (principalDivisor g),
        Multiplicative.toAdd (orderZAt X.hom p.2 g) := by
  rw [support_principalDivisor]
  exact degree_principalDivisor_eq_sum_orderZAt g

end classical

end CurveDivisor

end Hartshorne
