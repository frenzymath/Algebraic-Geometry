/-
Copyright (c) 2026 The StacksPart02Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart02Lib Contributors
-/

import StacksPart02Lib.AffineOpens

/-!
# Finite standard-open refinements

The affine communication arguments in the Schemes chapter repeatedly replace an
affine open cover by finitely many standard opens.  This file packages the
pointwise two-affine refinement from Mathlib together with compactness of an
affine open.
-/

namespace StacksPart02

open AlgebraicGeometry TopologicalSpace

universe u v

/-- A standard open of `V` which is also presented as a standard open of one
member of an affine cover. -/
structure StandardOpenRefinement {X : Scheme.{u}} (V : X.Opens)
    {ι : Type v} (U : ι → X.Opens) where
  /-- The member of the affine cover in which the open is also standard. -/
  index : ι
  /-- The defining section on `V`. -/
  sectionV : Γ(X, V)
  /-- The defining section on the chosen member of the cover. -/
  sectionU : Γ(X, U index)
  /-- The two presentations define the same open of `X`. -/
  eq_basicOpen : X.basicOpen sectionV = X.basicOpen sectionU

namespace StandardOpenRefinement

variable {X : Scheme.{u}} {V : X.Opens} {ι : Type v} {U : ι → X.Opens}

/-- The refined open lies in the affine open from which its section came. -/
theorem le_source (w : StandardOpenRefinement V U) :
    X.basicOpen w.sectionV ≤ V := by
  exact X.basicOpen_le w.sectionV

/-- The refined open lies in the selected member of the original cover. -/
theorem le_cover_member (w : StandardOpenRefinement V U) :
    X.basicOpen w.sectionV ≤ U w.index := by
  rw [w.eq_basicOpen]
  exact X.basicOpen_le w.sectionU

/-- Every refined open is affine when `V` is affine. -/
theorem isAffineOpen (hV : IsAffineOpen V)
    (w : StandardOpenRefinement V U) :
    IsAffineOpen (X.basicOpen w.sectionV) := by
  exact hV.basicOpen w.sectionV

end StandardOpenRefinement

/-- An affine open in a scheme covered by affine opens admits a finite cover by
standard opens, each of which is standard in one member of the given cover.

The finite family is indexed by the subtype of matching pairs of sections; the
`le_source` and `le_cover_member` lemmas expose its two containment properties.
-/
theorem exists_finset_standardOpen_refinement
    {X : Scheme.{u}} {ι : Type v} (V : X.Opens)
    (hV : IsAffineOpen V) (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) :
    ∃ s : Finset (StandardOpenRefinement V U),
      (V : Set X) ⊆ ⋃ w ∈ s, (X.basicOpen w.sectionV : Set X) := by
  classical
  let W : StandardOpenRefinement V U → Set X :=
    fun w => (X.basicOpen w.sectionV : Set X)
  have hWopen : ∀ w, IsOpen (W w) := by
    intro w
    exact (X.basicOpen w.sectionV).isOpen
  have hWcover : (V : Set X) ⊆ ⋃ w, W w := by
    intro x hx
    have hxU : (x : X) ∈ (⨆ i, U i) := by
      rw [hcover]
      exact trivial
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxU
    obtain ⟨f, g, hfg, hxf⟩ :=
      AlgebraicGeometry.exists_basicOpen_le_affine_inter
        hV (hU i) (x : X) ⟨hx, hxi⟩
    let w : StandardOpenRefinement V U :=
      { index := i
        sectionV := f
        sectionU := g
        eq_basicOpen := hfg }
    exact Set.mem_iUnion.mpr ⟨w, hxf⟩
  obtain ⟨s, hs⟩ := hV.isCompact.elim_finite_subcover W hWopen hWcover
  exact ⟨s, hs⟩

/-- The finite standard-open refinement covers the affine open exactly. -/
theorem exists_finset_standardOpen_refinement_eq
    {X : Scheme.{u}} {ι : Type v} (V : X.Opens)
    (hV : IsAffineOpen V) (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) :
    ∃ s : Finset (StandardOpenRefinement V U),
      (V : Set X) = ⋃ w ∈ s, (X.basicOpen w.sectionV : Set X) := by
  obtain ⟨s, hs⟩ := exists_finset_standardOpen_refinement V hV U hU hcover
  refine ⟨s, Set.Subset.antisymm hs ?_⟩
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨w, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hw, hx⟩
  exact w.le_source hx

end StacksPart02
