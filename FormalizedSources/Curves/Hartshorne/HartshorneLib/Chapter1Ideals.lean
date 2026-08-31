/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1

/-!
# Hartshorne I.1: elementary affine vanishing-ideal laws

This file collects the ideal-theoretic unit laws for the affine construction
defined in `Chapter1`.  They are deliberately stated without any
Nullstellensatz hypotheses.
-/

namespace Hartshorne

noncomputable section

section AffineSpace

variable (k : Type*) [Field k] (n : Nat)

@[simp]
theorem vanishingIdeal_empty :
    vanishingIdeal k n (∅ : Set (AffinePoint k n)) = ⊤ := by
  ext f
  simp [vanishingIdeal]

/-- Intersecting point sets enlarges their vanishing ideals; hence the sum of
the two original ideals is contained in the ideal of the intersection. -/
theorem vanishingIdeal_inter_sup (Y Z : Set (AffinePoint k n)) :
    vanishingIdeal k n Y ⊔ vanishingIdeal k n Z ≤
      vanishingIdeal k n (Y ∩ Z) := by
  refine sup_le ?_ ?_
  · exact vanishingIdeal_mono k n (by intro P hP; exact hP.1)
  · exact vanishingIdeal_mono k n (by intro P hP; exact hP.2)

/-- Every polynomial in a family vanishes on the common zero set of that
family. -/
theorem subset_vanishingIdeal_commonZeroSet
    (T : Set (AffinePolynomial k n)) :
    T ⊆ vanishingIdeal k n (commonZeroSet k n T) := by
  intro f hf P hP
  exact hP f hf

/-- A point set is contained in the common zero set of its vanishing ideal. -/
theorem subset_commonZeroSet_vanishingIdeal
    (Y : Set (AffinePoint k n)) :
    Y ⊆ commonZeroSet k n (vanishingIdeal k n Y) := by
  intro P hP f hf
  exact hf P hP

end AffineSpace

end

end Hartshorne
