/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamily
import AlgebraicJacobian.Picard.Separatedness

/-!
# The widened cover datum: arbitrary affine opens (R2, human decision I-0492)

`FinCoverData` (`Picard/DivisorFamily.lean`) types its pieces INTO a fixed pair of pinned
`P¹` charts — `h₀ : Fin m₀ → Γ(V₀)`, `h₁ : Fin m₁ → Γ(V₁)`, `pieces = Sum.elim (basicOpen ∘
h₀) (basicOpen ∘ h₁)` — with a partition of unity on EACH chart.  Per-piece swallow-or-miss
needs only openness (`DivSchemeCertZarConn.lean`), and it is the chart-wise partitions that
upgrade "inside one piece" to "inside one chart"; that upgrade is the obstruction, and no
repair keeping the pieces inside the preimages of a fixed pair of points of `P¹` can work
(`informal/spec-dd-r.md` ADDENDUM 3 §2, ADDENDUM 4 §4.4).

This file carries the widened datum.  A piece is an **arbitrary affine open** of the
relative curve, the index is a bare `Fin m`, and the covering condition is **joint**
(`⨆ j, pieces j = ⊤`) rather than chart-wise.  Nothing types a piece into a chart.

Justification for the shape, used and not re-derived (I-0492 clause 2): `supp D` is finite
over `R`, hence lies in a single affine open of `C ×_k Spec R` (Stacks `0B8B`), so a cover
with one straddling piece always exists.

## What the widening RELOCATES rather than removes (I-0492 clause 4(ii))

The old typing was silently supplying two things that now have to be earned:

* **every point lies in a piece** — was `relCover_sup` plus the two partitions; now it is
  exactly the joint covering field (`AffCoverData.exists_mem_pieces`);
* **`Γ(pieces j)` is `R`-flat** — was `flat_sections_basicOpen` over
  `flat_sections_relPinnedChart`, i.e. it rested on `Γ(V_bᴿ) ≅ R ⊗[k] Γ(C, V_b)` being FREE.
  For an arbitrary affine open that route is gone.  Replacement, and it is the one genuinely
  new commutative-algebra input the widening costs: `relCurve C R ↘ Spec R` is flat (it is
  the base change of `C.hom` along `overSpec k R`, and a morphism to a field spectrum is
  flat), and a flat morphism has `R`-flat sections on every affine open
  (`flat_sections_of_flat_hom`).  Unconditional in `R` — no Noetherian, no finiteness.

Fibrewise-finite support (I-0492 clause 4(i)) is deliberately NOT here: it is not a property
of a cover, it must come from the seed's own degree data, and it may not hide inside a
`LocalEquations` or an adaptation field.

## Main declarations

* `AlgebraicGeometry.flat_sections_of_flat_hom` — sections of an arbitrary affine open of a
  scheme flat over the base ring are flat.
* `AlgebraicGeometry.instFlatRelCurveHom` — the relative curve is flat over its test base.
* `AlgebraicGeometry.AffCoverData` — the widened cover datum.
* `AffCoverData.exists_mem_pieces`, `isAffineOpen_pieces`, `flat_sections_pieces`,
  `flat_sections_pieces_inf` — the derived replacements for what the chart typing supplied.
* `AlgebraicGeometry.FinCoverData.toAffCoverData` — the migration: old data instantiates the
  widened datum, so nothing landed becomes unreachable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## Flat sections on an arbitrary affine open

The engine that replaces the pinned-chart freeness argument. -/

section FlatSections

variable (K : Type u) [CommRing K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- **Sections of an arbitrary affine open are flat, for a scheme flat over the base ring.**
`Scheme.overAlgebraMap` factors as `ΓSpecIso.inv` followed by the structure morphism's
`appLE ⊤ V`; the second is `RingHom.Flat` because `AlgebraicGeometry.Flat` is a
`HasRingHomProperty` for `RingHom.Flat` and `V` is affine, the first is flat because it is a
ring isomorphism, and `RingHom.Flat` composes.

This is the widened replacement for `flat_sections_basicOpen ∘ flat_sections_relPinnedChart`:
that pair needed the open to be a basic open of a chart whose sections are a FREE base
change, which is exactly what an arbitrary affine open does not give. -/
theorem flat_sections_of_flat_hom [AlgebraicGeometry.Flat (X ↘ Spec (.of K))]
    {V : X.Opens} (hV : IsAffineOpen V) :
    Module.Flat K Γ(X, V) := by
  have happ : RingHom.Flat ((X ↘ Spec (.of K)).appLE ⊤ V (by simp)).hom :=
    HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat)
      (f := X ↘ Spec (.of K)) inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by simp)
  have hiso : RingHom.Flat ((Scheme.ΓSpecIso (.of K)).inv).hom :=
    RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv)
  have hcomp : RingHom.Flat (X.overAlgebraMap K V) := by
    have hfac : X.overAlgebraMap K V
        = ((X ↘ Spec (.of K)).appLE ⊤ V (by simp)).hom.comp
            ((Scheme.ΓSpecIso (.of K)).inv).hom := by
      rw [Scheme.overAlgebraMap, Scheme.Hom.appLE]
      rfl
    rw [hfac]
    exact RingHom.Flat.comp hiso happ
  exact (RingHom.flat_algebraMap_iff (R := K) (S := Γ(X, V))).mp hcomp

end FlatSections

section RelCurveFlat

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]

/-- **The relative curve is flat over its test base.** `(snd C (overSpec k R)).left` is the
base change of `C.hom` along `(overSpec k R).hom` (`Over.isPullback_left`), and every
structure morphism to the spectrum of a field is flat (`flat_hom_over_field`). -/
instance instFlatRelCurveHom : AlgebraicGeometry.Flat (relCurve C R ↘ Spec (.of R)) :=
  AlgebraicGeometry.Flat.isStableUnderBaseChange.of_isPullback
    (Over.isPullback_left C (overSpec k R)) inferInstance

/-- **Flat sections on an arbitrary affine open of the relative curve** — the widened
(c1)-flatness input, with no chart and no freeness. -/
theorem flat_sections_isAffineOpen {V : (relCurve C R).Opens} (hV : IsAffineOpen V) :
    Module.Flat R Γ(relCurve C R, V) :=
  flat_sections_of_flat_hom R (relCurve C R) hV

end RelCurveFlat

/-! ## The widened cover datum -/

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k)

/-- **The widened cover datum** (R2, human decision I-0492): finitely many **arbitrary
affine opens** of the relative curve that **jointly** cover it.

Contrast with `FinCoverData`, which this replaces on the certificate side: there is no `h₀`,
no `h₁`, no `a₀`/`a₁`, no `partition₀`/`partition₁`, no `Sum` index, and above all no typing
of a piece into a pinned chart.  The chart-wise partitions of unity are exactly what upgraded
per-piece swallow-or-miss to a chart statement, and they are gone deliberately; the two-chart
structure the Θ-layer needs is carried separately (see `ChartTyping` below), never by the
certificate clauses.

`Type u`, like `FinCoverData`, so a functor value can quotient it. -/
structure AffCoverData : Type u where
  /-- The number of pieces. -/
  m : ℕ
  /-- The pieces: arbitrary opens of the relative curve, made affine by `isAffineOpen`. -/
  pieces : Fin m → (relCurve C R).Opens
  /-- Every piece is affine — the only geometric demand the certificate layer makes. -/
  isAffineOpen : ∀ j, IsAffineOpen (pieces j)
  /-- The pieces cover the curve JOINTLY.  This replaces the two chart-wise partitions of
  unity, and it is the whole structural content of the widening. -/
  cover : (⨆ j, pieces j) = ⊤

namespace AffCoverData

variable {C R π} (D : AffCoverData C R)

/-- The gluing index of the widened datum: a bare `Fin`, with no two-sided structure. -/
abbrev index : Type := Fin D.m

/-- **Every point lies in a piece.** Under `FinCoverData` this came from `relCover_sup`
together with the two partitions of unity; here it is exactly the joint covering field —
obligation I-0492 4(ii) discharged in one line rather than silently supplied by the typing. -/
lemma exists_mem_pieces (z : relCurve C R) : ∃ j : D.index, z ∈ D.pieces j := by
  have hz : z ∈ (⨆ j, D.pieces j) := by rw [D.cover]; trivial
  exact Opens.mem_iSup.mp hz

/-- The pieces are affine opens — by fiat now, rather than as basic opens of an affine
chart. -/
lemma isAffineOpen_pieces (j : D.index) : IsAffineOpen (D.pieces j) :=
  D.isAffineOpen j

/-- **Flatness of the piece section rings over the test ring.** The widened replacement for
`FinCoverData.flat_sections_pieces`, which localized a FREE pinned-chart ring; here it is the
flat structure morphism of the relative curve read on an affine open. -/
theorem flat_sections_pieces (j : D.index) :
    Module.Flat R Γ(relCurve C R, D.pieces j) :=
  flat_sections_isAffineOpen C R (D.isAffineOpen j)

/-- Piece overlaps are affine (the relative curve is separated over `Spec R`, being proper),
so the overlap section rings are flat too — the widened
`FinCoverData.flat_sections_pieces_inf`. -/
theorem flat_sections_pieces_inf (i j : D.index)
    (hinf : IsAffineOpen (D.pieces i ⊓ D.pieces j)) :
    Module.Flat R Γ(relCurve C R, D.pieces i ⊓ D.pieces j) :=
  flat_sections_isAffineOpen C R hinf

end AffCoverData

/-! ## The optional chart typing, for the Θ-layer only -/

/-- The pinned chart of a given side, spelled here so this file needs no import from the
Θ-layer (it agrees with `relPinnedChart` by `rfl`). -/
noncomputable def pinnedChartOfSide [IsAffineHom π] (b : Bool) : (relCurve C R).Opens :=
  bif b then (relCover C R (fiberTwoCover π)).V₁ else (relCover C R (fiberTwoCover π)).V₀

/-- **A chart typing of a widened cover**: an assignment of each piece to one of the two
pinned `P¹` charts, containing it.  This is what the Θ-twisting unit genuinely needs (the
theta cocycle lives on `V₀ ⊓ V₁`), and it is deliberately a SEPARATE datum: no certificate
clause and no locally-certified predicate may require it.  Keeping it separate is what stops
the old fixed-pair typing from being smuggled back in through a field. -/
structure ChartTyping [IsAffineHom π] (D : AffCoverData C R) where
  /-- Which pinned chart the piece is assigned to. -/
  side : D.index → Bool
  /-- The piece is contained in its assigned chart. -/
  piece_le : ∀ j, D.pieces j ≤ pinnedChartOfSide C R π (side j)

/-! ## Migration: old cover data instantiates the widened datum -/

namespace FinCoverData

variable {C R π} [IsAffineHom π] (D : FinCoverData C R π)

/-- **The migration map.** An old chart-typed `FinCoverData` gives a widened
`AffCoverData`: reindex `Fin m₀ ⊕ Fin m₁` through `finSumFinEquiv`, the pieces are affine as
basic opens of the affine pinned charts, and the joint cover follows from the two chart-wise
covers together with `relCover_sup`.

The point of this lemma is that widening costs nothing landed: every existing construction of
cover data still produces a legal widened datum.  The converse fails, and that is exactly the
content of R2. -/
noncomputable def toAffCoverData : AffCoverData C R where
  m := D.m₀ + D.m₁
  pieces := fun j => D.pieces (finSumFinEquiv.symm j)
  isAffineOpen := fun j => by
    rcases finSumFinEquiv.symm j with i | i
    · rw [FinCoverData.pieces_inl]
      exact (relCover_isAffineOpen₀ C R (fiberTwoCover π)).basicOpen _
    · rw [FinCoverData.pieces_inr]
      exact (relCover_isAffineOpen₁ C R (fiberTwoCover π)).basicOpen _
  cover := by
    refine top_le_iff.mp fun z _ => ?_
    -- every point is in a pinned chart, and each chart is covered by its own pieces
    have hz : z ∈ (relCover C R (fiberTwoCover π)).V₀
        ⊔ (relCover C R (fiberTwoCover π)).V₁ := by
      rw [relCover_sup]; trivial
    have key : ∃ i : D.index, z ∈ D.pieces i := by
      rcases Opens.mem_sup.mp hz with h | h
      · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (D.cover₀ h)
        exact ⟨Sum.inl i, hi⟩
      · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (D.cover₁ h)
        exact ⟨Sum.inr i, hi⟩
    obtain ⟨i, hi⟩ := key
    exact Opens.mem_iSup.mpr ⟨finSumFinEquiv i, by
      simpa only [Equiv.symm_apply_apply] using hi⟩

@[simp]
lemma toAffCoverData_pieces (j : Fin (D.m₀ + D.m₁)) :
    D.toAffCoverData.pieces j = D.pieces (finSumFinEquiv.symm j) := rfl

/-- The canonical chart typing of a migrated datum: chart-0 pieces are basic opens of `V₀`,
chart-1 pieces of `V₁`. -/
noncomputable def toChartTyping : ChartTyping C R π D.toAffCoverData where
  side := fun j => (finSumFinEquiv.symm j).isRight
  piece_le := fun j => by
    rw [toAffCoverData_pieces]
    rcases h : finSumFinEquiv.symm j with i | i
    · rw [FinCoverData.pieces_inl]
      exact (relCurve C R).basicOpen_le (D.h₀ i)
    · rw [FinCoverData.pieces_inr]
      exact (relCurve C R).basicOpen_le (D.h₁ i)

end FinCoverData

end AlgebraicGeometry
