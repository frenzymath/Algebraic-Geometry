/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1CoordinateRing
import HartshorneLib.Chapter1Ideals

/-!
# Hartshorne I.1: closure from vanishing ideals

The affine Zariski topology was defined by algebraic sets.  This file proves
the source-facing closure identity from that definition and the elementary
containment of a set in the zero locus of its vanishing ideal.
-/

namespace Hartshorne

noncomputable section

section AffineClosure

variable (k : Type*) [Field k] (n : Nat)

/-- The common zero set of the vanishing ideal is the Zariski closure. -/
theorem commonZeroSet_vanishingIdeal_eq_closure
    (Y : Set (AffinePoint k n)) :
    commonZeroSet k n (vanishingIdeal k n Y) = closure Y := by
  apply Set.Subset.antisymm
  · intro P hP
    have hclosed : IsClosed (closure Y) := isClosed_closure
    rcases (isClosed_iff_isAlgebraicSet k n (closure Y)).1 hclosed with ⟨T, hT⟩
    have hTY : T ⊆ vanishingIdeal k n Y := by
      intro f hf P' hP'
      have hP'cl : P' ∈ closure Y := subset_closure hP'
      rw [← hT] at hP'cl
      exact hP'cl f hf
    have hzero : P ∈ commonZeroSet k n T :=
      (commonZeroSet_mono k n hTY) hP
    rw [hT] at hzero
    exact hzero
  · exact closure_minimal
      (subset_commonZeroSet_vanishingIdeal k n Y)
      (isClosed_commonZeroSet k n (vanishingIdeal k n Y))

/-- Algebraic sets are already closed, so the preceding closure formula
specializes to the usual zero-locus identity. -/
theorem commonZeroSet_vanishingIdeal_eq_self
    {Y : Set (AffinePoint k n)} (hY : IsAlgebraicSet k n Y) :
    commonZeroSet k n (vanishingIdeal k n Y) = Y := by
  rw [commonZeroSet_vanishingIdeal_eq_closure]
  exact ((isClosed_iff_isAlgebraicSet k n Y).2 hY).closure_eq

end AffineClosure

end

end Hartshorne
