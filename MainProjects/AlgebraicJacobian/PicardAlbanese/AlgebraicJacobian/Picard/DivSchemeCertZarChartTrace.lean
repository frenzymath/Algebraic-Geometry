/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarLeak

/-!
# The chart trace is what no-leak really asks for

The certificate assemblers consume, per piece `j`, the fibrewise no-leak clause, which is
emptiness of the leak locus, which is closedness of the piece trace
`supportLocus ∩ pieces j` (`isClosed_supportLocus_inter_iff_supportLeak_eq_empty`), which
is clopen-ness of that trace inside the support (`isClopen_trace_of_supportLeak_eq_empty`).

This file records the consequence that had been missed for the whole lifetime of the lane:
**the per-piece clause cannot be produced piece by piece.**  A `FinCoverData` carries a
partition of unity on each pinned chart, so the chart-`b` pieces cover the *whole* pinned
chart `V_b` — hence the union of their traces is the whole chart trace
`supportLocus ∩ V_b`.  A finite union of closed sets is closed, so

> no-leak at every chart-`b` piece **forces** `supportLocus ∩ V_b` to be closed in the
> relative curve, i.e. the chart trace to be clopen in the support.

That is a property of the *system and the pinned charts alone*: no choice of adaptation, and
no shrinking of the base, can produce no-leak for a system whose chart trace is not closed.
It is therefore the honest gate of the lane, and it replaces the refuted `tube-fibre`
framing (put the support inside one piece — impossible once the support meets both charts,
`not_exists_unique_support_piece`) and the refuted separated framing
(`DivSchemeCertZarSep.lean`) with a single geometric statement about the divisor.

Read positively, it says where to aim, but the converse is **not** the mirror image and this
file does not claim it: closed chart traces alone do not produce a leak-free adaptation.  What
does is `DivSchemeCertZarChartPair.lean`, and it needs two further inputs — the support inside
the chart *overlap* `V₀ ⊓ V₁`, and a chart-principality datum making the two pinned charts
themselves legal pieces.  Both are recorded there and on the roadmap
(`…certificate.chart-avoid`, `…certificate.swallow-adapt`).

## Main declarations

* `AlgebraicGeometry.DivisorAdaptation.supportLocus_inter_chart₀_eq_iUnion` /
  `…_chart₁_…` — the chart trace is the finite union of the chart's piece traces.
* `DivisorAdaptation.isClosed_supportLocus_inter_chart₀_of_forall_supportLeak_eq_empty`
  and its chart-1 twin — no-leak at every piece of a chart forces the chart trace closed.
* `AlgebraicGeometry.DivisorAdaptation.isClosed_supportLocus_inter_chart_of_forall_noLeak` —
  the assembler-shaped form: the `hnoLeak` hypothesis of
  `isCertified_of_noLeak_kernel_spanning` forces both chart traces closed.
* `AlgebraicGeometry.DivisorAdaptation.not_forall_noLeak_of_not_isClosed_chart₀` — the
  obstruction, contrapositive: a system with a non-closed chart-0 trace admits **no**
  adaptation satisfying the assembler's no-leak clause.
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
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R π d)

/-! ## The chart trace is the union of the piece traces -/

/-- **The chart-0 trace is the finite union of the chart-0 piece traces.** `⊆` is the
partition-of-unity cover `FinCoverData.cover₀`; `⊇` is `Scheme.basicOpen_le`, each piece
being a basic open *of* the pinned chart. -/
lemma supportLocus_inter_chart₀_eq_iUnion :
    d.supportLocus ∩ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R))
      = ⋃ j : Fin A.m₀, d.supportLocus ∩ (A.pieces (Sum.inl j) : Set (relCurve C R)) := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨hxs, hxV⟩
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (A.toFinCoverData.cover₀ hxV)
    exact Set.mem_iUnion.mpr ⟨j, hxs, hj⟩
  · refine Set.iUnion_subset fun j x hx => ⟨hx.1, ?_⟩
    exact (relCurve C R).basicOpen_le (A.h₀ j) hx.2

/-- **The chart-1 trace is the finite union of the chart-1 piece traces.** -/
lemma supportLocus_inter_chart₁_eq_iUnion :
    d.supportLocus ∩ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R))
      = ⋃ j : Fin A.m₁, d.supportLocus ∩ (A.pieces (Sum.inr j) : Set (relCurve C R)) := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨hxs, hxV⟩
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (A.toFinCoverData.cover₁ hxV)
    exact Set.mem_iUnion.mpr ⟨j, hxs, hj⟩
  · refine Set.iUnion_subset fun j x hx => ⟨hx.1, ?_⟩
    exact (relCurve C R).basicOpen_le (A.h₁ j) hx.2

/-! ## No-leak forces the chart trace closed -/

/-- **No-leak at every chart-0 piece forces the chart-0 trace closed.** The trace of the
whole pinned chart is the finite union of the piece traces, each of which is closed exactly
when nothing leaks out of it. -/
theorem isClosed_supportLocus_inter_chart₀_of_forall_supportLeak_eq_empty
    (h : ∀ j : Fin A.m₀, d.supportLeak (A.pieces (Sum.inl j)) = ∅) :
    IsClosed (d.supportLocus
      ∩ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R))) := by
  rw [A.supportLocus_inter_chart₀_eq_iUnion]
  exact isClosed_iUnion_of_finite fun j =>
    (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty _).mpr (h j)

/-- **No-leak at every chart-1 piece forces the chart-1 trace closed.** -/
theorem isClosed_supportLocus_inter_chart₁_of_forall_supportLeak_eq_empty
    (h : ∀ j : Fin A.m₁, d.supportLeak (A.pieces (Sum.inr j)) = ∅) :
    IsClosed (d.supportLocus
      ∩ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R))) := by
  rw [A.supportLocus_inter_chart₁_eq_iUnion]
  exact isClosed_iUnion_of_finite fun j =>
    (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty _).mpr (h j)

/-- **The assembler's `hnoLeak` hypothesis forces both chart traces closed.** This is the
gate of the certificate lane in its irreducible form: the hypothesis of
`isCertified_of_noLeak_kernel_spanning` (equivalently of
`isCertified_of_noLeak_of_forall_liftQ_injective`,
`divisorAdaptation_isCertified_of_noLeak_liftQ_degree`) implies a statement that mentions
neither the adaptation nor its pieces — only the system and the two pinned charts. -/
theorem isClosed_supportLocus_inter_chart_of_forall_noLeak
    (hnoLeak : ∀ (j : A.index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces j : Set (relCurve C R))) ⊆
        (A.pieces j : Set (relCurve C R))) :
    IsClosed (d.supportLocus
        ∩ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R)))
      ∧ IsClosed (d.supportLocus
        ∩ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R))) := by
  have hleak : ∀ j : A.index, d.supportLeak (A.pieces j) = ∅ := fun j =>
    d.supportLeak_eq_empty_of_forall_fibre
      ((relCurve C R) ↘ Spec (CommRingCat.of R)) (hnoLeak j)
  exact ⟨A.isClosed_supportLocus_inter_chart₀_of_forall_supportLeak_eq_empty
      fun j => hleak (Sum.inl j),
    A.isClosed_supportLocus_inter_chart₁_of_forall_supportLeak_eq_empty
      fun j => hleak (Sum.inr j)⟩

/-! ## The obstruction

The contrapositive is the statement the lane needed: for a system whose chart trace is not
closed there is *nothing to prove* — the assembler's hypothesis is false for every
adaptation, so no support-tube refinement, no idempotent packet extraction and no shrinking
of the base can supply it.  The tube mechanism (`exists_basicOpen_supportLeak_eq_empty`)
is not a counterexample: it shrinks the base, and shrinking the base shrinks the system's
support too, so what it proves is the chart-trace statement over the smaller base. -/

/-- **The obstruction.** If the chart-0 trace of the system is not closed in the relative
curve, then no adaptation of that system satisfies the assembler's no-leak clause. -/
theorem not_forall_noLeak_of_not_isClosed_chart₀
    (hnc : ¬ IsClosed (d.supportLocus
      ∩ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R)))) :
    ¬ ∀ (j : A.index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces j : Set (relCurve C R))) ⊆
        (A.pieces j : Set (relCurve C R)) :=
  fun h => hnc (A.isClosed_supportLocus_inter_chart_of_forall_noLeak h).1

/-- **The obstruction, chart 1.** -/
theorem not_forall_noLeak_of_not_isClosed_chart₁
    (hnc : ¬ IsClosed (d.supportLocus
      ∩ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R)))) :
    ¬ ∀ (j : A.index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces j : Set (relCurve C R))) ⊆
        (A.pieces j : Set (relCurve C R)) :=
  fun h => hnc (A.isClosed_supportLocus_inter_chart_of_forall_noLeak h).2

end DivisorAdaptation

end AlgebraicGeometry
