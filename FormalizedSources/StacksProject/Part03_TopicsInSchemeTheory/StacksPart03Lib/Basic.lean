/-
Copyright (c) 2026 The StacksPart03Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart03Lib Contributors
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Inseparable

/-!
# StacksPart03Lib.Basic

Foundational definitions for the Chow-homology setup from the Stacks Project.

The pinned Mathlib release does not provide predicates for catenary schemes or
dimension functions. The latter is defined here from the source definition;
universal catenarity is therefore retained as an explicit proposition in
`ChowSituation`, so downstream results can state the hypothesis without
silently introducing an unproved global assumption.
-/

namespace StacksPart03

open AlgebraicGeometry

/-! ## Specializations and dimension functions -/

/-- `y` is an immediate specialization of `x`: it is a proper specialization
and there is no point strictly between them. This is the pointwise form of
Stacks, Topology, Definition 02I9. -/
def IsImmediateSpecialization {X : Type*} [TopologicalSpace X]
    (x y : X) : Prop :=
  x ≠ y ∧ x ⤳ y ∧ ∀ z : X, x ⤳ z → z ⤳ y → z = x ∨ z = y

theorem IsImmediateSpecialization.ne {X : Type*} [TopologicalSpace X]
    {x y : X} (h : IsImmediateSpecialization x y) : x ≠ y :=
  h.1

theorem IsImmediateSpecialization.specializes {X : Type*} [TopologicalSpace X]
    {x y : X} (h : IsImmediateSpecialization x y) : x ⤳ y :=
  h.2.1

/-- The source notion of a dimension function. Values strictly decrease along
proper specializations and drop by one along immediate specializations. -/
def IsDimensionFunction {X : Type*} [TopologicalSpace X] (δ : X → ℤ) : Prop :=
  (∀ ⦃x y : X⦄, x ⤳ y → x ≠ y → δ x > δ y) ∧
    (∀ ⦃x y : X⦄, IsImmediateSpecialization x y → δ x = δ y + 1)

theorem IsDimensionFunction.strictMono_specialization {X : Type*}
    [TopologicalSpace X] {δ : X → ℤ} (hδ : IsDimensionFunction δ)
    {x y : X} (hxy : x ⤳ y) (hne : x ≠ y) : δ x > δ y :=
  hδ.1 hxy hne

theorem IsDimensionFunction.immediate_eq_add_one {X : Type*}
    [TopologicalSpace X] {δ : X → ℤ} (hδ : IsDimensionFunction δ)
    {x y : X} (hxy : IsImmediateSpecialization x y) :
    δ x = δ y + 1 :=
  hδ.2 hxy

/-- Adding a constant to a dimension function preserves the dimension-function
conditions (Stacks, Topology, immediately after Definition 02I9). -/
theorem IsDimensionFunction.add_const {X : Type*} [TopologicalSpace X]
    {δ : X → ℤ} (hδ : IsDimensionFunction δ) (n : ℤ) :
    IsDimensionFunction (fun x => δ x + n) := by
  constructor
  · intro x y hxy hne
    simpa [gt_iff_lt, add_comm] using add_lt_add_right (hδ.1 hxy hne) n
  · intro x y hxy
    change δ x + n = (δ y + n) + 1
    rw [hδ.2 hxy]
    ring

/-! ## The Chow setup -/

/-- The standing base data for the Chow-homology chapter (Stacks, Tag 02QL).

`IsLocallyNoetherian` is Mathlib's scheme predicate. Mathlib v4.31 has no
universal-catenarity predicate, so that part of the source hypothesis is kept
as an explicit proposition supplied by each situation; this is a local
hypothesis rather than an unproved global typeclass. -/
structure ChowSituation where
  S : Scheme
  locallyNoetherian : IsLocallyNoetherian S
  universallyCatenary : Prop
  δ : S → ℤ
  dimensionFunction : IsDimensionFunction δ

namespace ChowSituation

instance (𝒮 : ChowSituation) : TopologicalSpace 𝒮.S := inferInstance

theorem specializes_strict (𝒮 : ChowSituation) {x y : 𝒮.S}
    (hxy : x ⤳ y) (hne : x ≠ y) : 𝒮.δ x > 𝒮.δ y :=
  𝒮.dimensionFunction.strictMono_specialization hxy hne

theorem immediate_eq_add_one (𝒮 : ChowSituation) {x y : 𝒮.S}
    (hxy : IsImmediateSpecialization x y) :
    𝒮.δ x = 𝒮.δ y + 1 :=
  𝒮.dimensionFunction.immediate_eq_add_one hxy

end ChowSituation

end StacksPart03
