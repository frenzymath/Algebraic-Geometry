/-
Copyright (c) 2026 The StacksPart03Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart03Lib Contributors
-/

import Mathlib.Topology.LocallyFinsupp

/-!
# Pointwise cycles

The cycles chapter describes a cycle pointwise as an integer-valued function on
the underlying points whose nonzero locus is locally finite.  Mathlib's
`Function.locallyFinsupp` is precisely this locally finite-support carrier.
This file records the homogeneous and effective predicates used for the
pointwise description of Chow cycles.  Scheme-specific predicates (integral
closed subschemes and their multiplicities) can be layered on this carrier
without changing its additive core.
-/

namespace StacksPart03

open Set

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The locally finite integer-valued coefficient functions on a space.

This is the pointwise model for the cycle group in the blueprint's
`chow-remark-cycles-pointwise`: the support is locally finite in the topology
of `X`, while coefficients are integers.
-/
abbrev PointCycle (X : Type u) [TopologicalSpace X] :=
  Function.locallyFinsupp X ℤ

namespace PointCycle

/-- The coefficient support of a pointwise cycle. -/
abbrev support (c : PointCycle X) : Set X := Function.support c

/-- A pointwise cycle is homogeneous of dimension `k` when every nonzero
coefficient occurs at a point of dimension `k`. -/
def IsKCycle (δ : X → ℤ) (k : ℤ) (c : PointCycle X) : Prop :=
  ∀ ⦃x : X⦄, c x ≠ 0 → δ x = k

/-- A cycle is effective when all of its coefficients are nonnegative. -/
def IsEffective (c : PointCycle X) : Prop :=
  ∀ x : X, 0 ≤ c x

@[simp]
theorem isKCycle_zero (δ : X → ℤ) (k : ℤ) :
    IsKCycle δ k (0 : PointCycle X) := by
  intro x hx
  exact (hx (by simp)).elim

theorem isKCycle_add {δ : X → ℤ} {k : ℤ} {c d : PointCycle X}
    (hc : IsKCycle δ k c) (hd : IsKCycle δ k d) :
    IsKCycle δ k (c + d) := by
  intro x hx
  by_cases hcx : c x = 0
  · have hdx : d x ≠ 0 := by
      intro hdx
      apply hx
      change c x + d x = 0
      simp [hcx, hdx]
    exact hd hdx
  · exact hc hcx

theorem isKCycle_neg {δ : X → ℤ} {k : ℤ} {c : PointCycle X}
    (hc : IsKCycle δ k c) :
    IsKCycle δ k (-c) := by
  intro x hx
  apply hc
  intro hcx
  apply hx
  change -c x = 0
  simp [hcx]

theorem isKCycle_sub {δ : X → ℤ} {k : ℤ} {c d : PointCycle X}
    (hc : IsKCycle δ k c) (hd : IsKCycle δ k d) :
    IsKCycle δ k (c - d) := by
  exact isKCycle_add hc (isKCycle_neg hd)

theorem isKCycle_iff_support_subset {δ : X → ℤ} {k : ℤ} {c : PointCycle X} :
    IsKCycle δ k c ↔ ∀ x ∈ c.support, δ x = k := by
  constructor
  · intro h x hx
    exact h hx
  · intro h x hx
    exact h x hx

@[simp]
theorem isEffective_zero : IsEffective (0 : PointCycle X) := by
  intro x
  simp

theorem isEffective_add {c d : PointCycle X}
    (hc : IsEffective c) (hd : IsEffective d) :
    IsEffective (c + d) := by
  intro x
  change 0 ≤ c x + d x
  exact add_nonneg (hc x) (hd x)

theorem isEffective_of_forall {c : PointCycle X}
    (h : ∀ x, 0 ≤ c x) : IsEffective c :=
  h

theorem locallyFiniteSupport (c : PointCycle X) :
    LocallyFiniteSupport c :=
  Function.locallyFinsupp.locallyFiniteSupport c

theorem finite_inter_support_of_isCompact (c : PointCycle X) {K : Set X}
    (hK : IsCompact K) : (K ∩ c.support).Finite := by
  exact c.locallyFiniteSupport.finite_inter_support_of_isCompact hK

/-- The additive subgroup of pointwise cycles homogeneous of dimension `k`.

This packages the coefficient-level part of the blueprint's `Z_k(X)` while
leaving the integral closed-subscheme generators for a later layer. -/
def homogeneousSubgroup (δ : X → ℤ) (k : ℤ) : AddSubgroup (PointCycle X) where
  carrier := {c | IsKCycle δ k c}
  zero_mem' := isKCycle_zero δ k
  add_mem' := by
    intro c d hc hd
    exact isKCycle_add hc hd
  neg_mem' := by
    intro c hc
    exact isKCycle_neg hc

/-- The type of coefficient-level `k`-cycles. -/
abbrev KCycle (δ : X → ℤ) (k : ℤ) := homogeneousSubgroup δ k

@[simp]
theorem mem_homogeneousSubgroup {δ : X → ℤ} {k : ℤ} {c : PointCycle X} :
    c ∈ homogeneousSubgroup δ k ↔ IsKCycle δ k c :=
  Iff.rfl

theorem KCycle.isKCycle {δ : X → ℤ} {k : ℤ} (c : KCycle δ k) :
    IsKCycle δ k (c : PointCycle X) :=
  c.property

theorem KCycle.finite_inter_support_of_isCompact
    {δ : X → ℤ} {k : ℤ} (c : KCycle δ k) {K : Set X}
    (hK : IsCompact K) : (K ∩ (c : PointCycle X).support).Finite := by
  exact PointCycle.finite_inter_support_of_isCompact (c : PointCycle X) hK

end PointCycle

end StacksPart03
