/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4P1Overlap

/-!
# Basic identities for the standard coordinates on `P1`

This file collects the small coordinate identities used by later curve arguments.  The
underlying chart rings and the overlap maps are defined in `Chapter4P1Charts` and
`Chapter4P1Overlap`; this API only exposes their elementary algebraic compatibilities.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry
open MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

namespace P1

variable (k : Type u) [Field k]

/-- The homogeneous coordinate divided by itself is the unit on its chart. -/
@[simp] theorem chartCoord_self (i : Fin 2) :
    P1.chartCoord k i i = 1 := by
  rw [P1.chartCoord_eq]
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk, val_one]
  simp

/-- The two cross-chart coordinates become mutual inverses after restriction to the overlap. -/
theorem chartCoord_cross_mul_eq_one :
    P1.awayToOverlapLeft k (P1.chartCoord k 0 1) *
        P1.awayToOverlapRight k (P1.chartCoord k 1 0) = 1 :=
  P1.awayToOverlap_mul_eq_one k

/-- Under the overlap coordinate `T = X₁/X₀`, the opposite chart coordinate is `T⁻¹`. -/
theorem chartCoord_cross_inverse :
    P1.overlapAlgEquiv k
        (P1.awayToOverlapRight k (P1.chartCoord k 1 0)) =
      LaurentPolynomial.T (-1) :=
  P1.overlapAlgEquiv_awayToOverlapRight_chartCoord k

/-- Dehomogenization computes a chart coordinate through the localization map. -/
theorem awayToPoly_chartCoord_eq_dehomogenize (i j : Fin 2) :
    P1.awayToPoly k i (P1.chartCoord k i j) =
      P1.dehomogenize k i (MvPolynomial.X j) := by
  exact P1.awayToPoly_mk k i 1 (MvPolynomial.X j)
    (by simpa using P1.X_mem k j)

end P1

end AlgebraicGeometry
