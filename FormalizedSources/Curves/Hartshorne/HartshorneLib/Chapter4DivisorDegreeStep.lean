/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorInduction

/-!
# Degree bookkeeping for one-point dévissage

The divisor induction step removes one copy of a non-generic point.  Over an
algebraically closed field every such point has residue degree one, so the
integer-valued degree drops by exactly one.  These identities are the numeric
part of the curve dévissage used by the later cohomology ledger.
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

@[simp]
theorem degree_single_one
    (x : {x : X.left // x ≠ genericPoint X.left}) :
    degree (single x.2 1) = 1 := by
  change degree (Finsupp.single x 1) = 1
  exact degree_single x 1

theorem degree_single_add
    (D : CurveDivisor k X) (x : {x : X.left // x ≠ genericPoint X.left})
    (n : ℤ) :
    degree (D + single x.2 n) = degree D + n := by
  rw [degree_add]
  change degree D + degree (Finsupp.single x n) = degree D + n
  rw [degree_single]

theorem degree_devissageDivisor
    {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X) :
    degree (devissageDivisor hx D) = degree D - 1 := by
  rw [devissageDivisor_eq_sub, degree_sub]
  change degree D - degree (Finsupp.single (⟨x, hx⟩) 1) = degree D - 1
  rw [degree_single]

theorem degree_devissageDivisor_add_single
    {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X) :
    degree (devissageDivisor hx D) + 1 = degree D := by
  rw [degree_devissageDivisor]
  omega

theorem degree_single_zsmul
    (x : {x : X.left // x ≠ genericPoint X.left}) (n : ℤ) :
    degree (n • single x.2 1) = n := by
  rw [degree_zsmul]
  change n • degree (Finsupp.single x 1) = n
  rw [degree_single]
  simp

end CurveDivisor

end Hartshorne
