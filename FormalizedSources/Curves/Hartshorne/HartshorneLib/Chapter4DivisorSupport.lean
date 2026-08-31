/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4Curves

/-!
# Hartshorne IV.1: finite support of curve divisors

This file gives the support API for the finite formal-sum model of curve
divisors.  The geometric point type is kept explicit in the statements, while
the proofs use the finite-support API already provided by `Finsupp`.
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

/-- The finite set of non-generic points occurring in a curve divisor. -/
abbrev support (D : CurveDivisor k X) :
    Finset {x : X.left // x ≠ genericPoint X.left} :=
  (show PointDivisor X.left from D).support

@[simp]
theorem mem_support_iff {D : CurveDivisor k X}
    (p : {x : X.left // x ≠ genericPoint X.left}) :
    p ∈ support D ↔ coeffAt p.2 D ≠ 0 := by
  exact Finsupp.mem_support_iff

theorem support_add_subset (D E : CurveDivisor k X) :
    ∀ p, p ∈ support (D + E) → p ∈ support D ∨ p ∈ support E := by
  intro p hp
  classical
  exact Finset.mem_union.mp (Finsupp.support_add hp)

theorem support_sub_subset (D E : CurveDivisor k X) :
    ∀ p, p ∈ support (D - E) → p ∈ support D ∨ p ∈ support E := by
  intro p hp
  classical
  exact Finset.mem_union.mp (Finsupp.support_sub hp)

theorem support_neg_eq (D : CurveDivisor k X) :
    support (-D) = support D := by
  exact Finsupp.support_neg D

theorem support_single_subset
    (p : {x : X.left // x ≠ genericPoint X.left}) (n : ℤ) :
    support (Finsupp.single p n : CurveDivisor k X) ⊆ {p} := by
  classical
  exact Finsupp.support_single_subset

theorem support_single_ne_zero
    (p : {x : X.left // x ≠ genericPoint X.left}) {n : ℤ} (hn : n ≠ 0) :
    support (Finsupp.single p n : CurveDivisor k X) = {p} := by
  classical
  exact Finsupp.support_single p hn

@[simp]
theorem support_zero : support (0 : CurveDivisor k X) = ∅ := by
  exact Finsupp.support_zero

@[simp]
theorem support_eq_empty_iff (D : CurveDivisor k X) :
    support D = ∅ ↔ D = 0 := by
  exact Finsupp.support_eq_empty

theorem support_nonempty_iff (D : CurveDivisor k X) :
    (support D).Nonempty ↔ D ≠ 0 := by
  exact Finsupp.support_nonempty_iff

end classical

end CurveDivisor

end Hartshorne
