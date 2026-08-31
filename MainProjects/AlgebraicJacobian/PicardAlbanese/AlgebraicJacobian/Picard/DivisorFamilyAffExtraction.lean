/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffAdaptation

/-!
# Widened-adaptation extraction (R2, human decision I-0492)

**Every** local-equation system on the relative curve refines to a widened adaptation, with no
chart input whatsoever: `AffAdaptation.exists` below is the R2 counterpart of
`exists_divisorAdaptation` (`Picard/DivisorFamilyExtraction.lean`).

## Why this is the shape the widening was for

The chart-typed extraction runs the affine-refinement engine **on each of the two pinned
charts** and glues the results with a partition of unity per chart — the partitions are what
`exists_finite_basicOpen_refinement` produces, and they are exactly what protection I-0492
ordered deleted.  Here there is nothing to glue: affine opens form a basis of any scheme
(`Scheme.isBasis_affineOpens`), the relative curve is quasi-compact when `C` is (being a base
change of `C.left`), so one pass gives a finite affine-open cover subordinated to `d.cover`.
No `π`, no charts, no partitions, no `Sum` index.

The comparison unit is `1` at every piece, as in the chart-typed extraction: the equation is
literally the restriction of `d`'s equation at the anchor.

## Main declarations

* `AlgebraicGeometry.instQuasiCompactRelCurveHom`, `instCompactSpaceRelCurve` — the relative
  curve over a proper `C` is quasi-compact over its test base, hence compact.
* `AlgebraicGeometry.exists_affCoverData_subordinate` — a finite affine-open cover with, per
  piece, an anchor point of `d.cover` whose member contains the piece.
* `AlgebraicGeometry.exists_affAdaptation` — hence a widened adaptation of `d`.
* `AlgebraicGeometry.exists_affAdaptation_of_isProper` — the same with the compactness
  hypothesis discharged, so with NO hypothesis on the system.

## What this does and does not close

It closes the *adaptation* half of the widened lane's producer gap: before this file, the only
way to obtain an `AffAdaptation` was `FinCoverData.toAffCoverData` plus
`DivisorAdaptation.toAff` — i.e. through the chart-typed predicate, which is exactly the route
R2 exists to avoid.  Now a widened adaptation exists for every system, directly.

It does NOT produce a *certificate*.  The two obligations protection I-0492 clause 4 relocated
— fibrewise-finite support and `SwallowedBy` — remain obligations, and a cover produced by this
extraction has no reason to have a straddling piece.  Producing one that does is where the
Stacks `0B8B` input enters, and that is still owed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]

/-- **The relative curve over a proper `C` is quasi-compact over its test base.**  `IsProper`
implies `QuasiCompact`, and quasi-compactness is stable under base change along
`Over.isPullback_left`. -/
instance instQuasiCompactRelCurveHom [IsProper C.hom] :
    QuasiCompact (relCurve C R ↘ Spec (.of R)) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact)
    (Over.isPullback_left C (overSpec k R)) inferInstance

/-- **The relative curve over a proper `C` has a compact space.**  `Spec R` is compact and the
structure morphism is quasi-compact, so this is
`QuasiCompact.compactSpace_of_compactSpace`.

This is what makes the extraction below hypothesis-free in the case of interest: the finite
subcover it extracts exists because the curve is quasi-compact, and nothing else about it
matters. -/
instance instCompactSpaceRelCurve [IsProper C.hom] : CompactSpace (relCurve C R) :=
  QuasiCompact.compactSpace_of_compactSpace (relCurve C R ↘ Spec (.of R))

/-- **A finite affine-open cover subordinated to `d.cover`**, with an anchor point per piece.
Affine opens are a basis, so every point `z` has an affine open `W z` with
`z ∈ W z ≤ d.cover.opens z`; quasi-compactness of the relative curve extracts a finite
subfamily that still covers.

This is where the chart-typed extraction needed the two pinned charts and their partitions of
unity, and it needs neither. -/
theorem exists_affCoverData_subordinate [CompactSpace (relCurve C R)]
    (d : (relCurve C R).LocalEquations) :
    ∃ (D : AffCoverData C R) (pt : D.index → relCurve C R),
      ∀ j, D.pieces j ≤ d.cover.opens (pt j) := by
  classical
  -- an affine open around each point, inside that point's member of `d.cover`
  have hW : ∀ z : relCurve C R, ∃ W : (relCurve C R).Opens,
      IsAffineOpen W ∧ z ∈ W ∧ W ≤ d.cover.opens z := by
    intro z
    obtain ⟨W, hWmem, hzW, hWle⟩ :=
      Opens.isBasis_iff_nbhd.mp (relCurve C R).isBasis_affineOpens (d.cover.mem_opens z)
    exact ⟨W, hWmem, hzW, hWle⟩
  choose W hWaff hzW hWle using hW
  -- extract a finite subcover
  have hcover : (Set.univ : Set (relCurve C R)) ⊆ ⋃ z, (W z : Set (relCurve C R)) :=
    fun z _ => Set.mem_iUnion.mpr ⟨z, hzW z⟩
  obtain ⟨t, ht⟩ := (isCompact_univ (X := relCurve C R)).elim_finite_subcover
    (fun z : relCurve C R => (W z : Set (relCurve C R))) (fun z => (W z).isOpen) hcover
  -- reindex the finite set by a `Fin`
  set e : Fin (Fintype.card {z // z ∈ t}) ≃ {z // z ∈ t} :=
    (Fintype.equivFin {z // z ∈ t}).symm with he
  refine ⟨{ m := Fintype.card {z // z ∈ t}
            pieces := fun j => W (e j).1
            isAffineOpen := fun j => hWaff (e j).1
            cover := ?_ },
    fun j => (e j).1, fun j => hWle (e j).1⟩
  refine top_le_iff.mp fun z _ => ?_
  obtain ⟨s, hs, hzs⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  exact Opens.mem_iSup.mpr ⟨e.symm ⟨s, hs⟩, by rw [Equiv.apply_symm_apply]; exact hzs⟩

/-- **Widened-adaptation extraction**: every local-equation system on the relative curve
refines to an adaptation over an arbitrary-affine-open cover.  The R2 counterpart of
`exists_divisorAdaptation`, and it consumes no chart, no `π`, and no partition of unity —
`AffAdaptation.ofAnchors` with comparison unit `1` at every piece. -/
theorem exists_affAdaptation [CompactSpace (relCurve C R)]
    (d : (relCurve C R).LocalEquations) :
    ∃ D : AffCoverData C R, Nonempty (AffAdaptation D d) := by
  obtain ⟨D, pt, hle⟩ := exists_affCoverData_subordinate C R d
  exact ⟨D, ⟨AffAdaptation.ofAnchors
    (fun j => ((relCurve C R).presheaf.map (homOfLE (hle j)).op).hom (d.eqn (pt j)))
    pt hle (fun _ => 1) (fun _ => by rw [Units.val_one, one_mul])⟩⟩

/-- **Widened-adaptation extraction for a proper `C`**, the form the DD-R lane consumes: the
`CompactSpace` hypothesis is discharged by `instCompactSpaceRelCurve`, so this has NO
hypothesis on the system at all.

Compare `exists_divisorAdaptation`: same conclusion shape, but that one produces a
`FinCoverData`, i.e. it pins the pieces into the two `π`-charts and carries a partition of
unity per chart.  This one mentions neither. -/
theorem exists_affAdaptation_of_isProper [IsProper C.hom]
    (d : (relCurve C R).LocalEquations) :
    ∃ D : AffCoverData C R, Nonempty (AffAdaptation D d) :=
  exists_affAdaptation C R d

end AlgebraicGeometry
