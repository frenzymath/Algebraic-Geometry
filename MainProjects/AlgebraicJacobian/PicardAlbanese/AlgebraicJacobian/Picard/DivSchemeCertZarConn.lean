/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarSwallow

/-!
# A connected divisor can be certified only inside a single pinned chart

The two preceding files bracket the certificate assembler's per-piece no-leak clause:
`DivSchemeCertZarChartTrace.lean` shows it forces the chart traces `supportLocus ∩ V_b` to
be closed, and `DivSchemeCertZarSwallow.lean` shows the "swallow or miss" shape produces it.
This file closes the bracket, and thereby decides the lane's satisfiability question.

The observation is that leak-freeness *plus connectedness of the divisor* already implies
swallow-or-miss.  For each piece the trace `supportLocus ∩ pieces j` is open in the support
(the piece is open) and closed in it (that is leak-freeness), so a connected support leaves
only the two degenerate values: the trace is empty, or it is everything.  Feeding this into
the chart dichotomies of `DivSchemeCertZarSwallow.lean` and `relCover_sup` gives

> **a connected divisor whose adaptation is leak-free at every piece lies inside `V₀` or
> inside `V₁`.**

That is the verdict the lane never obtained.  It is not a statement about pieces, adaptations,
tubes or fibres: it says the **assembler route** — every landed producer of `IsCertified` goes
through the per-piece no-leak clause — can only ever be driven for divisors confined to one
pinned chart of `pi`, a **chart-design** condition.

Scope, stated precisely so it is not overread.  What is proved here constrains *leak-freeness*,
which is the hypothesis `hnoLeak` of `isCertified_of_noLeak_kernel_spanning` and of every
assembler downstream of it.  It does **not** yet constrain `IsCertified` itself, because the
converse implication

  `(∀ j, Module.Finite R (A.colength j))  →  ∀ j, d.supportLeak (A.pieces j) = ∅`

is **not proved anywhere in this project**: only the three sufficient directions exist
(`finite_colength_of_supportLeak_eq_empty`, `finite_colength_of_isClosed_supportLocus_inter`,
`finite_colength_of_isClopen_trace`).  Its expected proof is that a finite `R`-algebra has a
universally closed spectrum, so the locally closed image `supportLocus ∩ pieces j` of
`Spec (Γ(pieces j) ⧸ (eqn j))` in the separated `relCurve C R` is closed — real mathlib
plumbing, not a corollary.  Until it lands, "`IsCertified` is unsatisfiable off the charts" is a
conjecture; "the assembler route is unavailable off the charts" is a theorem.  Roadmap:
`…certificate.c1-necessity`.

Nor can a shrink of the base repair it, because base localization does not disconnect the
divisor: `Spec (R[x]/(x² − t))` over `R = k[t]` is connected over every basic open of
`Spec R`, so no Zariski neighbourhood of `t = 0` splits the divisor into clopen packets.
Hence the "clopen packet extraction" programme (memory I-0209) is available exactly when the
divisor is already chart-confined, and the honest obligation of the lane is to make the
DD-R atlas produce chart-confined divisors.

## Main declarations

* `AlgebraicGeometry.DivisorAdaptation.subset_or_disjoint_of_isPreconnected_of_supportLeak` —
  leak-freeness at a piece plus a connected support forces swallow-or-miss at that piece.
* `AlgebraicGeometry.DivisorAdaptation.forall_subset_or_disjoint_of_isPreconnected` — the
  same for every piece at once, i.e. leak-free + connected ⟹ swallow-or-miss.
* `AlgebraicGeometry.DivisorAdaptation.supportLocus_subset_chart_of_isPreconnected` — **the
  satisfiability verdict**: a connected support with a leak-free adaptation lies inside one
  of the two pinned charts (no nonemptiness needed — the empty support is chart-confined).
* `AlgebraicGeometry.DivisorAdaptation.not_forall_supportLeak_eq_empty_of_isPreconnected` —
  the contrapositive obstruction: a connected divisor confined to neither pinned chart admits
  no adaptation that is leak-free at every piece.
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

/-! ## Connectedness turns leak-freeness into swallow-or-miss -/

/-- **A connected support leaves a leak-free piece no middle ground.** The trace
`supportLocus ∩ pieces j` is open in the support because the piece is open, and closed in it
because nothing leaks; a preconnected support therefore has the trace empty or total.

Stated with `IsPreconnected` on the ambient set (rather than `ConnectedSpace` on the
subtype) so that no coercion bookkeeping is needed: the two separating opens are the piece
itself and the complement of the — closed — trace. -/
theorem subset_or_disjoint_of_isPreconnected_of_supportLeak (j : A.index)
    (hconn : _root_.IsPreconnected d.supportLocus)
    (hleak : d.supportLeak (A.pieces j) = ∅) :
    d.supportLocus ⊆ (A.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (A.pieces j : Set (relCurve C R)) := by
  classical
  have hclosed : IsClosed (d.supportLocus ∩ (A.pieces j : Set (relCurve C R))) :=
    (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty (A.pieces j)).mpr hleak
  -- the two separating opens: the piece, and the complement of the (closed) trace
  by_cases hdisj : Disjoint d.supportLocus (A.pieces j : Set (relCurve C R))
  · exact Or.inr hdisj
  refine Or.inl ?_
  by_contra hnsub
  -- both halves are nonempty, so preconnectedness produces a point in their intersection
  obtain ⟨x, hx⟩ := Set.not_disjoint_iff.mp hdisj
  obtain ⟨y, hyS, hyU⟩ := Set.not_subset.mp hnsub
  obtain ⟨z, hzS, hzu, hzv⟩ :=
    hconn (A.pieces j : Set (relCurve C R))
      (d.supportLocus ∩ (A.pieces j : Set (relCurve C R)))ᶜ
      (A.pieces j).isOpen hclosed.isOpen_compl
      (fun w hw => by
        by_cases hwU : w ∈ (A.pieces j : Set (relCurve C R))
        · exact Or.inl hwU
        · exact Or.inr fun hc => hwU hc.2)
      ⟨x, hx.1, hx.2⟩ ⟨y, hyS, fun hc => hyU hc.2⟩
  exact hzv ⟨hzS, hzu⟩

/-- **Leak-free at every piece plus a connected support ⟹ swallow-or-miss.** So the
hypothesis of `forall_noLeak_of_forall_subset_or_disjoint` is not an extra assumption for a
connected divisor: it is what leak-freeness already says. -/
theorem forall_subset_or_disjoint_of_isPreconnected
    (hconn : _root_.IsPreconnected d.supportLocus)
    (hleak : ∀ j : A.index, d.supportLeak (A.pieces j) = ∅) :
    ∀ j : A.index, d.supportLocus ⊆ (A.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (A.pieces j : Set (relCurve C R)) := fun j =>
  A.subset_or_disjoint_of_isPreconnected_of_supportLeak j hconn (hleak j)

/-! ## The satisfiability verdict -/

/-- **A connected divisor with a leak-free adaptation lies inside one pinned chart.** The
verdict the certificate lane needed: the chart-0 dichotomy of `DivSchemeCertZarSwallow.lean`
either puts the support in `V₀` outright, or makes it miss `V₀` entirely — and then
`V₀ ⊔ V₁ = ⊤` (`relCover_sup`) puts it in `V₁`.  No nonemptiness is required.

Consequently every landed route to `IsCertified` — all of which go through the per-piece
no-leak clause — is available for a connected divisor **only** if that divisor avoids
`pi⁻¹(∞)` (so it sits in `V₀`) or avoids `pi⁻¹(0)` (so it sits in `V₁`).  This is a
condition on the divisor and the chosen `pi`; the adaptation, the support tube, the packet
idempotents and the base shrink are all irrelevant to it.  Whether `IsCertified` itself (as
opposed to its only known producers) is likewise constrained needs the unproved converse
`(c1) → leak-free` discussed in this file's header. -/
theorem supportLocus_subset_chart_of_isPreconnected
    (hconn : _root_.IsPreconnected d.supportLocus)
    (hleak : ∀ j : A.index, d.supportLeak (A.pieces j) = ∅) :
    d.supportLocus ⊆ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R))
      ∨ d.supportLocus ⊆ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R)) := by
  have hswallow := A.forall_subset_or_disjoint_of_isPreconnected hconn hleak
  rcases A.subset_chart₀_or_disjoint_chart₀ hswallow with h₀ | h₀
  · exact Or.inl h₀
  -- the support misses `V₀`, so `V₀ ⊔ V₁ = ⊤` puts all of it in `V₁`
  refine Or.inr fun x hx => ?_
  have hmem : x ∈ ((relCover C R (fiberTwoCover π)).V₀
      ⊔ (relCover C R (fiberTwoCover π)).V₁ : (relCurve C R).Opens) := by
    rw [relCover_sup]; trivial
  rcases (Opens.mem_sup ..).mp hmem with h | h
  · exact (Set.disjoint_left.mp h₀ hx h).elim
  · exact h

/-- **The obstruction.** A connected divisor lying in neither pinned chart — i.e. meeting
both `pi⁻¹(0)` and `pi⁻¹(∞)` — admits **no** adaptation that is leak-free at every piece, over
any base and after any shrink; so no landed assembler can certify it.

Model to keep in mind: the degree-two relative divisor `V(t x² + x y + t y²) ⊆ ℙ¹` over
`k[t]`, whose section ring is a domain (so it is connected over every basic open of
`Spec k[t]`) and whose fibre at `t = 0` is `{0, ∞}`. -/
theorem not_forall_supportLeak_eq_empty_of_isPreconnected
    (hconn : _root_.IsPreconnected d.supportLocus)
    (h₀ : ¬ d.supportLocus ⊆ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R)))
    (h₁ : ¬ d.supportLocus ⊆ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R))) :
    ¬ ∀ j : A.index, d.supportLeak (A.pieces j) = ∅ := fun hleak =>
  (A.supportLocus_subset_chart_of_isPreconnected hconn hleak).elim h₀ h₁

end DivisorAdaptation

end AlgebraicGeometry
