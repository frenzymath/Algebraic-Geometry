/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4ProductFormulaAPI
import HartshorneLib.Chapter4SmoothProperConsequences

/-!
# Finite order sums on smooth proper curves

The product formula is already available as degree-zero for principal divisors
on a smooth proper integral curve.  This file exposes the equivalent finite
sum of local orders, which is the form used by valuation-theoretic arguments.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The finite sum of local orders of every rational function vanishes on a
smooth proper integral curve over an algebraically closed field. -/
theorem principalOrderSum_eq_zero_of_smoothProperIntegralCurve
    (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    ∀ g : X.left.functionFieldˣ, principalOrderSum (X := X) g = 0 := by
  intro g
  rw [principalOrderSum_eq_degree (X := X) g]
  exact principalDivisorsHaveDegreeZero_of_smoothProperIntegralCurve X g

/-- Equivalently, the additive degree obstruction on nonzero rational
functions is the zero homomorphism. -/
theorem principalDivisorDegreeHom_eq_zero_of_smoothProperIntegralCurve
    (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    principalDivisorDegreeHom (k := k) (X := X) = 0 := by
  apply AddMonoidHom.ext
  intro g
  rw [principalDivisorDegreeHom_apply, AddMonoidHom.zero_apply]
  exact principalDivisorsHaveDegreeZero_of_smoothProperIntegralCurve X
    (Additive.toMul g)

end Hartshorne
