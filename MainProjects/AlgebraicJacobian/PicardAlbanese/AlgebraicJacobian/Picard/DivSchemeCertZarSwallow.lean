/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarChartTrace

/-!
# Swallow or miss: the shape of an adaptation that can be certified

`DivSchemeCertZarChartTrace.lean` shows that the assembler's per-piece no-leak clause
*forces* the chart traces `supportLocus ∩ V_b` to be closed.  This file gives the matching
sufficient condition, and it is deliberately crude:

> if every piece either **swallows** the support (`supportLocus ⊆ pieces j`) or **misses**
> it (`Disjoint supportLocus (pieces j)`), then no-leak holds at every piece.

For a swallowing piece the trace is the whole support, which is closed by construction
(`isClosed_supportLocus`); for a missing piece the trace is empty.  Neither case needs a
fibre, a tube, or an idempotent.

The crudeness is not a defect, because the necessity lemma pins down exactly how much
freedom is left.  Both pinned charts are covered by their pieces, so

* if some chart-`b` piece meets the support it must swallow it, whence `supportLocus ⊆ V_b`;
* otherwise every chart-`b` piece misses the support, whence `supportLocus ∩ V_b = ∅`.

Since `V₀ ⊔ V₁` is the whole relative curve, a nonempty support therefore lies in
`V₀ ⊓ V₁` — the divisor must avoid **both** vertical fibres `pi⁻¹(0)` and `pi⁻¹(∞)` — or be
confined to one of them.  That is the honest chart-design hypothesis of the lane, and it is
where the DD-R atlas has to do its work; it is not something a support tube, a packet
idempotent, or a shrink of the base can manufacture.

A missing piece contributes nothing at all: its equation is a unit, so its colength module
vanishes (`subsingleton_colength_of_disjoint_supportLocus`) and clauses (c1) hold there for
free — no fibrewise regularity input.  So the certificate of a swallow-or-miss adaptation is
carried entirely by the swallowing pieces, at most one per chart.

## Main declarations

* `AlgebraicGeometry.DivisorAdaptation.subsingleton_colength_of_disjoint_supportLocus` — a
  piece missing the support has a vanishing colength.
* `AlgebraicGeometry.DivisorAdaptation.supportLeak_eq_empty_of_subset_or_disjoint` — swallow
  or miss gives no-leak at that piece.
* `AlgebraicGeometry.DivisorAdaptation.forall_noLeak_of_forall_subset_or_disjoint` — the
  assembler-shaped `hnoLeak`, with no fibre analysis.
* `AlgebraicGeometry.DivisorAdaptation.forall_finite_colength_of_forall_subset_or_disjoint` —
  clause (c1)-finite at every piece.
* `AlgebraicGeometry.DivisorAdaptation.subset_chart₀_or_disjoint_chart₀` /
  `…_chart₁_…` — the design constraint the shape imposes on the divisor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace DivisorAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R π d)

/-! ## A piece missing the support contributes nothing -/

/-- **A piece that misses the support has a vanishing colength.** Its equation has a unit
germ at every point of the piece (`isUnit_germ_eqn_iff` read through the unit locus), hence
is a unit (`RingedSpace.isUnit_of_isUnit_germ`), hence spans the unit ideal.

This is the colength companion of `subsingleton_ovlColength_of_disjoint_supportLocus`: on
such a piece the certificate's clauses (c1) are free, with no fibrewise regularity input. -/
lemma subsingleton_colength_of_disjoint_supportLocus (j : A.index)
    (hdisj : ∀ z : relCurve C R, z ∈ A.pieces j → z ∉ d.supportLocus) :
    Subsingleton (A.colength j) := by
  have hunit : IsUnit (A.eqn j) := by
    apply (relCurve C R).toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    have hU : z ∈ d.unitLocus := not_not.mp (hdisj z hz)
    exact (A.isUnit_germ_eqn_iff j hz).mpr
      ((d.mem_unitLocus_iff_isUnit_germ (d.cover.mem_opens z)).mp hU)
  exact Ideal.Quotient.subsingleton_iff.mpr
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span rfl) hunit)

/-! ## Swallow or miss gives no-leak -/

/-- **Swallow or miss gives no-leak at that piece.** If the piece contains the whole support
its trace is the support, closed by `isClosed_supportLocus`; if the piece misses the support
its trace is empty.  In neither case is a fibre, a tube or an idempotent involved. -/
theorem supportLeak_eq_empty_of_subset_or_disjoint (j : A.index)
    (h : d.supportLocus ⊆ (A.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (A.pieces j : Set (relCurve C R))) :
    d.supportLeak (A.pieces j) = ∅ := by
  refine (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty (A.pieces j)).mp ?_
  rcases h with hsub | hdisj
  · rw [Set.inter_eq_left.mpr hsub]
    exact d.isClosed_supportLocus
  · rw [Set.disjoint_iff_inter_eq_empty.mp hdisj]
    exact isClosed_empty

/-- **The assembler-shaped `hnoLeak` from swallow-or-miss.** This is the hypothesis of
`isCertified_of_noLeak_kernel_spanning` /
`isCertified_of_noLeak_of_forall_liftQ_injective` /
`divisorAdaptation_isCertified_of_noLeak_liftQ_degree`, produced with no fibre analysis. -/
theorem forall_noLeak_of_forall_subset_or_disjoint
    (h : ∀ j : A.index, d.supportLocus ⊆ (A.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (A.pieces j : Set (relCurve C R))) :
    ∀ (j : A.index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces j : Set (relCurve C R))) ⊆
        (A.pieces j : Set (relCurve C R)) := by
  intro j s x hx
  have hleak := A.supportLeak_eq_empty_of_subset_or_disjoint j (h j)
  by_contra hxU
  exact Set.eq_empty_iff_forall_notMem.mp hleak x ⟨hx.2, hxU⟩

section Finite

/- The finiteness engine consumes the properness licence on the relative curve
(`instIsProperRelCurveHom`), so this clause — and only this clause — needs `IsProper`. -/
variable [IsProper C.hom]

/-- **Clause (c1)-finite at every piece, from swallow-or-miss.** -/
theorem forall_finite_colength_of_forall_subset_or_disjoint
    (h : ∀ j : A.index, d.supportLocus ⊆ (A.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (A.pieces j : Set (relCurve C R))) :
    ∀ j : A.index, Module.Finite R (A.colength j) := fun j =>
  A.finite_colength_of_supportLeak_eq_empty j
    (A.supportLeak_eq_empty_of_subset_or_disjoint j (h j))

end Finite

/-! ## What the shape forces on the divisor

The necessity direction of `DivSchemeCertZarChartTrace.lean` is sharpened here: because the
chart-`b` pieces cover `V_b`, a swallow-or-miss adaptation exists only for a divisor that is
either inside a pinned chart or disjoint from it.  Combined with `V₀ ⊔ V₁ = ⊤` this says a
nonempty support lies in `V₀ ⊓ V₁`, or is confined to one vertical fibre of `pi`.

This is the statement the DD-R atlas owes: **the chart's divisors avoid `pi⁻¹(0)` and
`pi⁻¹(∞)`.**  It is a hypothesis about the chart, and it is the only remaining geometric
input of the (c1) side of the certificate. -/

/-- **Chart-0 dichotomy.** A swallow-or-miss adaptation forces the support either inside the
pinned chart `V₀` or disjoint from it. -/
theorem subset_chart₀_or_disjoint_chart₀
    (h : ∀ j : A.index, d.supportLocus ⊆ (A.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (A.pieces j : Set (relCurve C R))) :
    d.supportLocus ⊆ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R))
      ∨ Disjoint d.supportLocus
        ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R)) := by
  by_cases hmeet : ∃ j : Fin A.m₀, d.supportLocus ⊆ (A.pieces (Sum.inl j) : Set (relCurve C R))
  · obtain ⟨j, hj⟩ := hmeet
    exact Or.inl (hj.trans fun x hx => (relCurve C R).basicOpen_le (A.h₀ j) hx)
  · refine Or.inr (Set.disjoint_iff_inter_eq_empty.mpr ?_)
    rw [A.supportLocus_inter_chart₀_eq_iUnion]
    refine Set.iUnion_eq_empty.mpr fun j => Set.disjoint_iff_inter_eq_empty.mp ?_
    exact (h (Sum.inl j)).resolve_left fun hsub => hmeet ⟨j, hsub⟩

/-- **Chart-1 dichotomy.** -/
theorem subset_chart₁_or_disjoint_chart₁
    (h : ∀ j : A.index, d.supportLocus ⊆ (A.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (A.pieces j : Set (relCurve C R))) :
    d.supportLocus ⊆ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R))
      ∨ Disjoint d.supportLocus
        ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R)) := by
  by_cases hmeet : ∃ j : Fin A.m₁, d.supportLocus ⊆ (A.pieces (Sum.inr j) : Set (relCurve C R))
  · obtain ⟨j, hj⟩ := hmeet
    exact Or.inl (hj.trans fun x hx => (relCurve C R).basicOpen_le (A.h₁ j) hx)
  · refine Or.inr (Set.disjoint_iff_inter_eq_empty.mpr ?_)
    rw [A.supportLocus_inter_chart₁_eq_iUnion]
    refine Set.iUnion_eq_empty.mpr fun j => Set.disjoint_iff_inter_eq_empty.mp ?_
    exact (h (Sum.inr j)).resolve_left fun hsub => hmeet ⟨j, hsub⟩

end DivisorAdaptation

end AlgebraicGeometry
