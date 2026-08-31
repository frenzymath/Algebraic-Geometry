/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Order.Basic
import Mathlib.SetTheory.Cardinal.Regular

/-!
# StacksPart01Lib.SetTheory

Elementary cofinality facts used in the set-theoretic size arguments of
Chapter 3 of the Stacks Project's Part 1 preliminaries.
-/

namespace StacksPart01Lib

/-- A subset of a preorder is cofinal if every element lies below one of its
elements, as in the cofinality section of the Stacks Project's set theory
chapter. -/
def IsCofinal {α : Type*} [Preorder α] (s : Set α) : Prop :=
  ∀ a, ∃ b ∈ s, a ≤ b

/-- The whole preorder is cofinal. -/
theorem isCofinal_univ {α : Type*} [Preorder α] :
    IsCofinal (Set.univ : Set α) := by
  intro a
  exact ⟨a, Set.mem_univ a, le_rfl⟩

/-- A superset of a cofinal subset is cofinal. -/
theorem IsCofinal.mono {α : Type*} [Preorder α] {s t : Set α}
    (hs : IsCofinal s) (hst : s ⊆ t) : IsCofinal t := by
  intro a
  obtain ⟨b, hb, hab⟩ := hs a
  exact ⟨b, hst hb, hab⟩

/-- A union containing a cofinal subset is cofinal. -/
theorem IsCofinal.union_left {α : Type*} [Preorder α] {s : Set α}
    (hs : IsCofinal s) (t : Set α) : IsCofinal (s ∪ t) :=
  hs.mono Set.subset_union_left

/-- Cofinality of a range is the pointwise upper-bound formulation. -/
theorem isCofinal_range_iff {ι α : Type*} [Preorder α] (f : ι → α) :
    IsCofinal (Set.range f) ↔ ∀ a, ∃ i, a ≤ f i := by
  constructor
  · intro h a
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := h a
    exact ⟨i, hi⟩
  · intro h a
    obtain ⟨i, hi⟩ := h a
    exact ⟨f i, ⟨i, rfl⟩, hi⟩

/-- In a linear order, failure of cofinality is exactly strict boundedness
above. -/
theorem not_isCofinal_range_iff {ι α : Type*} [LinearOrder α] (f : ι → α) :
    ¬ IsCofinal (Set.range f) ↔ ∃ a, ∀ i, f i < a := by
  rw [isCofinal_range_iff]
  simp only [not_forall, not_exists, not_le]

/-- The boundedness step in the proof of Stacks Tag 05N2 (`Map from set
lifts`). -/
theorem map_from_set_bounded {ι α : Type*} [LinearOrder α] (f : ι → α)
    (h : ¬ IsCofinal (Set.range f)) : ∃ a, ∀ i, f i < a :=
  (not_isCofinal_range_iff f).mp h

/-- For every cardinal there is an ordinal with strictly larger cofinality.

This is the existence statement in Stacks Project Tag 05N3. -/
theorem exists_ordinal_with_large_cofinality (κ : Cardinal) :
    ∃ o : Ordinal, κ < o.cof := by
  let c : Cardinal := max κ Cardinal.aleph0
  refine ⟨(Order.succ c).ord, ?_⟩
  rw [(Cardinal.isRegular_succ (le_max_right κ Cardinal.aleph0)).cof_ord]
  exact (le_max_left κ Cardinal.aleph0).trans_lt (Order.lt_succ c)

end StacksPart01Lib
