/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4EffectiveBounds
import HartshorneLib.Chapter4DivisorSupport

/-!
# Coefficient and support calculus for divisor sign parts

The positive and negative parts of a curve divisor form a canonical partition
of its finite support.  This file exposes the pointwise formulas and the
resulting support and degree identities used by effective-divisor arguments.
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

/-! ### Pointwise sign-part formulas -/

@[simp]
theorem coeffAt_positivePart {D : CurveDivisor k X}
    {x : X.left} (hx : x ≠ genericPoint X.left) :
    coeffAt hx (positivePart D) = max (coeffAt hx D) 0 := by
  rw [positivePart, coeffAt_sup, coeffAt_zero]

@[simp]
theorem coeffAt_negativePart {D : CurveDivisor k X}
    {x : X.left} (hx : x ≠ genericPoint X.left) :
    coeffAt hx (negativePart D) = max (-coeffAt hx D) 0 := by
  rw [negativePart, coeffAt_sup, coeffAt_zero, coeffAt_neg]

theorem coeffAt_positivePart_eq_zero_iff {D : CurveDivisor k X}
    {x : X.left} (hx : x ≠ genericPoint X.left) :
    coeffAt hx (positivePart D) = 0 ↔ coeffAt hx D ≤ 0 := by
  rw [coeffAt_positivePart]
  omega

theorem coeffAt_negativePart_eq_zero_iff {D : CurveDivisor k X}
    {x : X.left} (hx : x ≠ genericPoint X.left) :
    coeffAt hx (negativePart D) = 0 ↔ 0 ≤ coeffAt hx D := by
  rw [coeffAt_negativePart]
  omega

theorem coeffAt_positivePart_ne_zero_iff {D : CurveDivisor k X}
    {x : X.left} (hx : x ≠ genericPoint X.left) :
    coeffAt hx (positivePart D) ≠ 0 ↔ 0 < coeffAt hx D := by
  rw [ne_eq, coeffAt_positivePart_eq_zero_iff]
  omega

theorem coeffAt_negativePart_ne_zero_iff {D : CurveDivisor k X}
    {x : X.left} (hx : x ≠ genericPoint X.left) :
    coeffAt hx (negativePart D) ≠ 0 ↔ coeffAt hx D < 0 := by
  rw [ne_eq, coeffAt_negativePart_eq_zero_iff]
  omega

/-! ### The finite support partition -/

theorem mem_support_positivePart_iff {D : CurveDivisor k X}
    (p : {x : X.left // x ≠ genericPoint X.left}) :
    p ∈ support (positivePart D) ↔ 0 < coeffAt p.2 D := by
  rw [mem_support_iff, coeffAt_positivePart_ne_zero_iff]

theorem mem_support_negativePart_iff {D : CurveDivisor k X}
    (p : {x : X.left // x ≠ genericPoint X.left}) :
    p ∈ support (negativePart D) ↔ coeffAt p.2 D < 0 := by
  rw [mem_support_iff, coeffAt_negativePart_ne_zero_iff]

theorem support_positivePart_subset (D : CurveDivisor k X) :
    support (positivePart D) ⊆ support D := by
  intro p hp
  rw [mem_support_iff]
  have hpos : 0 < coeffAt p.2 D :=
    mem_support_positivePart_iff (D := D) p |>.mp hp
  omega

theorem support_negativePart_subset (D : CurveDivisor k X) :
    support (negativePart D) ⊆ support D := by
  intro p hp
  rw [mem_support_iff]
  have hneg : coeffAt p.2 D < 0 :=
    mem_support_negativePart_iff (D := D) p |>.mp hp
  omega

theorem disjoint_support_positivePart_negativePart (D : CurveDivisor k X) :
    Disjoint (support (positivePart D)) (support (negativePart D)) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  have hpos : 0 < coeffAt p.2 D :=
    mem_support_positivePart_iff (D := D) p |>.mp hp
  have hneg : coeffAt p.2 D < 0 :=
    mem_support_negativePart_iff (D := D) p |>.mp hq
  omega

open Classical in
theorem support_positivePart_union_negativePart (D : CurveDivisor k X) :
    support (positivePart D) ∪ support (negativePart D) = support D := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact support_positivePart_subset D hp
    · exact support_negativePart_subset D hp
  · intro hp
    rw [mem_support_iff] at hp
    have hsplit : 0 < coeffAt p.2 D ∨ coeffAt p.2 D < 0 := by
      omega
    rcases hsplit with hpos | hneg
    · exact Finset.mem_union.mpr <| Or.inl
        (mem_support_positivePart_iff (D := D) p |>.mpr hpos)
    · exact Finset.mem_union.mpr <| Or.inr
        (mem_support_negativePart_iff (D := D) p |>.mpr hneg)

/-! ### Degree consequences -/

theorem degree_positivePart_add_negativePart (D : CurveDivisor k X) :
    degree (positivePart D) + degree (negativePart D) =
      degree D + 2 * degree (negativePart D) := by
  have h := degree_positivePart_sub_negativePart D
  omega

theorem degree_positivePart_eq_degree_add_negativePart (D : CurveDivisor k X) :
    degree (positivePart D) = degree D + degree (negativePart D) := by
  have h := degree_positivePart_sub_negativePart D
  omega

theorem degree_negativePart_eq_degree_positivePart_sub_degree (D : CurveDivisor k X) :
    degree (negativePart D) = degree (positivePart D) - degree D := by
  have h := degree_positivePart_sub_negativePart D
  omega

theorem degree_eq_zero_iff_signParts_eq_zero (D : CurveDivisor k X) :
    degree D = 0 ↔ degree (positivePart D) = degree (negativePart D) := by
  have h := degree_positivePart_sub_negativePart D
  omega

end classical

end CurveDivisor

end Hartshorne
