/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffCollapse

/-!
# swallow-adapt on the widened cover: the straddling piece

Roadmap leaf `AJCR.w4-rep.datum.dat-d.ddr.certificate.swallow-adapt`, restated over
`AffCoverData`.  The chart-pair version (`DivSchemeCertZarChartPair.lean`) is landed but
consumes chart principality, which is false for an arbitrary degree-`n` divisor on a curve of
genus `≥ 1` (`informal/spec-dd-r.md` ADDENDUM 3 corrigendum C4(i)): `Cl(V_b) ≠ 0` and
shrinking `Spec R` does not change a fibre class.  Over a widened cover the shape is
different and the obstruction does not arise: **one piece swallows the support and every
other piece misses it.**

## The geometric input, supplied as a HYPOTHESIS and not re-derived

The decision (I-0492 clause 2) says to USE, not re-derive: `supp D` is finite over `R`, hence
lies in a single affine open of `C ×_k Spec R` (Stacks `0B8B`).  Mathlib has no form of
`0B8B`, and this project constructs no curve other than `P¹`, so formalising it is out of
scope for this lane.  It therefore appears here as the named, explicit hypothesis
`SwallowedBy` — a *statement to be supplied by the seed*, exactly as
`informal/spec-dd-r.md` ADDENDUM 3 C4(ii) requires: the geometric input is relocated into a
visible obligation rather than hidden inside a `LocalEquations` or an adaptation field.

`SwallowedBy` is deliberately NOT bundled into `AffCoverData` or `AffAdaptation`.  A reader
can see, from any theorem's signature, whether it assumes confinement.

## What the shape buys

For a cover with a straddling piece, swallow-or-miss holds by construction rather than by a
connectivity argument, so — with no fibre, no tube, and no packet idempotent —
`hnoLeak` holds at every piece, clause (c1)-finite holds at every piece, and every
non-swallowing piece contributes a vanishing colength (`cert-collapse`).  Crucially there is
no dichotomy step, hence no appeal to `V₀ ⊔ V₁ = ⊤`, hence no chart.

## Main declarations

* `AlgebraicGeometry.AffCoverData.SwallowedBy` — the straddling-piece hypothesis.
* `AffAdaptation.forall_subset_or_disjoint_of_swallowedBy` — swallow-or-miss from it.
* `AffAdaptation.forall_noLeak_of_swallowedBy` — the assembler's `hnoLeak`.
* `AffAdaptation.forall_finite_colength_of_swallowedBy` — clause (c1)-finite everywhere.
* `AffCoverData.ofSwallowingPiece` — the two-piece widened cover from a straddling affine
  open together with an affine open cover of the rest.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]

namespace AffCoverData

/-- **The straddling-piece hypothesis** (the Stacks `0B8B` input, supplied not derived): some
piece of the cover contains the whole support locus, and every other piece is disjoint from
it.

This is the widened replacement for "the support lies in `V₀ ⊓ V₁`".  The difference that
matters: `V₀ ⊓ V₁` is the complement of a FIXED PAIR of vertical fibres and provably cannot
always be arranged (ADDENDUM 4 §4.3 exhibits a straddling divisor at every genus `≥ 2`),
whereas an affine open containing a support finite over `R` always exists. -/
def SwallowedBy (D : AffCoverData C R) (d : (relCurve C R).LocalEquations) : Prop :=
  ∃ j₀ : D.index, d.supportLocus ⊆ (D.pieces j₀ : Set (relCurve C R)) ∧
    ∀ j : D.index, j ≠ j₀ → Disjoint d.supportLocus (D.pieces j : Set (relCurve C R))

end AffCoverData

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d)

/-- **Swallow-or-miss, by construction.** With a straddling piece the dichotomy is immediate:
the distinguished piece swallows, the rest miss.  No connectivity hypothesis on the support,
no chart, and — unlike the chart-pair route — no appeal to `V₀ ⊔ V₁ = ⊤`. -/
theorem forall_subset_or_disjoint_of_swallowedBy (h : D.SwallowedBy d) :
    ∀ j : D.index, d.supportLocus ⊆ (D.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)) := by
  obtain ⟨j₀, hsub, hmiss⟩ := h
  intro j
  by_cases hj : j = j₀
  · exact Or.inl (hj ▸ hsub)
  · exact Or.inr (hmiss j hj)

/-- **The assembler's `hnoLeak` from a straddling piece.** -/
theorem forall_noLeak_of_swallowedBy (h : D.SwallowedBy d) :
    ∀ (j : D.index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (D.pieces j : Set (relCurve C R))) ⊆
        (D.pieces j : Set (relCurve C R)) :=
  forall_noLeak_of_forall_subset_or_disjoint
    (forall_subset_or_disjoint_of_swallowedBy h)

section Finite

variable [IsProper C.hom]

/-- **Clause (c1)-finite at every piece, from a straddling piece.**  No fibre analysis, no
support tube, no packet idempotent. -/
theorem forall_finite_colength_of_swallowedBy (h : D.SwallowedBy d) :
    ∀ j : D.index, Module.Finite R (A.colength j) :=
  A.forall_finite_colength_of_forall_subset_or_disjoint
    (forall_subset_or_disjoint_of_swallowedBy h)

end Finite

/-- **Every non-swallowing piece contributes nothing**: its colength vanishes, so clauses
(c1) there are free (`cert-collapse`).  The certificate is carried by the straddling piece
alone. -/
theorem subsingleton_colength_of_ne_swallowing {j₀ : D.index}
    (hmiss : ∀ j : D.index, j ≠ j₀ → Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)))
    (j : D.index) (hj : j ≠ j₀) :
    Subsingleton (A.colength j) :=
  A.subsingleton_colength_of_disjoint_supportLocus j
    (fun _ hz hsupp => (Set.disjoint_left.mp (hmiss j hj)) hsupp hz)

end AffAdaptation

/-! ## Building a widened cover with a straddling piece -/

namespace AffCoverData

/-- **The widened cover from a straddling affine open plus a cover of the rest.** `W` is the
affine open containing the support (the Stacks `0B8B` piece); `Ws` is any finite family of
affine opens which, together with `W`, covers the curve.  The straddling condition itself is
`SwallowedBy` and is a separate hypothesis — this constructor only assembles the cover. -/
noncomputable def ofSwallowingPiece (W : (relCurve C R).Opens) (hW : IsAffineOpen W)
    {m : ℕ} (Ws : Fin m → (relCurve C R).Opens) (hWs : ∀ i, IsAffineOpen (Ws i))
    (hcover : W ⊔ (⨆ i, Ws i) = ⊤) :
    AffCoverData C R where
  m := m + 1
  pieces := Fin.snoc Ws W
  isAffineOpen := fun j => by
    refine Fin.lastCases ?_ ?_ j
    · rw [Fin.snoc_last]; exact hW
    · intro i; rw [Fin.snoc_castSucc]; exact hWs i
  cover := by
    refine top_le_iff.mp fun z _ => ?_
    have hz : z ∈ W ⊔ (⨆ i, Ws i) := by rw [hcover]; trivial
    rcases (Opens.mem_sup ..).mp hz with hzW | hzWs
    · exact Opens.mem_iSup.mpr ⟨Fin.last m, by rw [Fin.snoc_last]; exact hzW⟩
    · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hzWs
      exact Opens.mem_iSup.mpr ⟨i.castSucc, by rw [Fin.snoc_castSucc]; exact hi⟩

end AffCoverData

end AlgebraicGeometry
