/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffAdaptation
import AlgebraicJacobian.Picard.SupportTubeFinite
import AlgebraicJacobian.Picard.SupportTube

/-!
# The per-piece layer transports to arbitrary affine opens (R2, decision I-0492)

This file discharges the load-bearing claim of the widening: **the per-piece certificate
layer needs only openness and affineness of a piece**, so all of it transports from
`FinCoverData`'s basic opens of two pinned charts to `AffCoverData`'s arbitrary affine opens.
What does NOT transport is the (β2) chart-wise upgrade, and that is the no-go rather than a
tool (`informal/spec-dd-r.md` ADDENDUM 3, corrigendum C2).

Proved here, each from the widened carrier alone:

* `supportLocus_inter_pieces` — the piece trace of the support is `pieces j \ D(f_j)`
  (uses `eqn_rel` only);
* `subsingleton_colength_of_disjoint_supportLocus` — a piece missing the support has
  vanishing colength (its equation is a unit);
* `supportLeak_eq_empty_of_subset_or_disjoint` — **swallow or miss gives no-leak**, from
  openness of the piece and closedness of the support;
* `subset_or_disjoint_of_isPreconnected_of_supportLeak` — the clopen-trace argument: a
  preconnected support meets a leak-free piece totally or not at all.  This is
  `DivSchemeCertZarConn.lean:98` with the chart hypotheses deleted, and it is the precise
  sense in which "per-piece swallow-or-miss needs only openness";
* `finite_colength_of_isClosed_supportLocus_inter` and
  `forall_finite_colength_of_forall_subset_or_disjoint` — clause (c1)-finite, from
  affineness through the landed abstract engine
  `IsAffineOpen.finite_quotient_span_singleton_of_isClosed`;
* `flat_colength_of_forall_tmul_residueField` /
  `projective_colength_of_forall_tmul_residueField` — the (c1) junction, now resting on
  `AffCoverData.flat_sections_pieces` (the flat-morphism route) instead of pinned-chart
  freeness.

**Deliberately absent**: any analogue of `subset_chart₀_or_disjoint_chart₀` or
`supportLocus_subset_chart_of_isPreconnected`.  Those consume the chart-wise partitions of
unity, they are what made the fixed-pair design unsatisfiable, and no declaration in the
widened lane may depend on them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace AffAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d)

/-! ## The adaptation reads the same support -/

/-- On a piece, the germ of the adaptation equation is a unit iff the germ of `d`'s
tautological equation is — `eqn_rel` read at germs.  Openness of the piece is all that is
used. -/
lemma isUnit_germ_eqn_iff (j : D.index) {w : relCurve C R} (hwj : w ∈ D.pieces j) :
    IsUnit (((relCurve C R).presheaf.germ (D.pieces j) w hwj).hom (A.eqn j))
      ↔ IsUnit (((relCurve C R).presheaf.germ (d.cover.opens w) w
          (d.cover.mem_opens w)).hom (d.eqn w)) := by
  obtain ⟨u, hu⟩ := A.eqn_rel j w
  have hwW : w ∈ D.pieces j ⊓ d.cover.opens w := ⟨hwj, d.cover.mem_opens w⟩
  have h := congrArg
    (((relCurve C R).presheaf.germ (D.pieces j ⊓ d.cover.opens w) w hwW).hom) hu
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
  rw [h, IsUnit.mul_iff]
  exact and_iff_right (u.isUnit.map _)

/-- On a piece, membership in `d`'s unit locus is membership in the basic open of the
adaptation equation. -/
lemma mem_basicOpen_eqn_iff_mem_unitLocus (j : D.index) {w : relCurve C R}
    (hwj : w ∈ D.pieces j) :
    w ∈ (relCurve C R).basicOpen (A.eqn j) ↔ w ∈ d.unitLocus := by
  rw [(relCurve C R).mem_basicOpen _ w hwj, A.isUnit_germ_eqn_iff j hwj]
  exact (d.mem_unitLocus_iff_isUnit_germ (d.cover.mem_opens w)).symm

/-- The adaptation's basic opens land in `d`'s unit locus. -/
lemma basicOpen_eqn_le_unitLocus (j : D.index) :
    (relCurve C R).basicOpen (A.eqn j) ≤ d.unitLocus := fun _ hw =>
  (A.mem_basicOpen_eqn_iff_mem_unitLocus j
    ((relCurve C R).basicOpen_le (A.eqn j) hw)).mp hw

/-- **The adaptation computes the unit locus.** Uses the JOINT covering field of the
widened datum where the old proof used the two chart-wise partitions of unity — the one
place the covering hypothesis actually enters, and it enters in its weaker joint form. -/
lemma iSup_basicOpen_eqn_eq_unitLocus :
    (⨆ j, (relCurve C R).basicOpen (A.eqn j)) = d.unitLocus := by
  refine le_antisymm (iSup_le fun j => A.basicOpen_eqn_le_unitLocus j) ?_
  intro w hw
  obtain ⟨j, hwj⟩ := D.exists_mem_pieces w
  exact Opens.mem_iSup.mpr ⟨j, (A.mem_basicOpen_eqn_iff_mem_unitLocus j hwj).mpr hw⟩

/-- **The per-piece trace of the support**: on the piece `j`, the support locus is exactly
`pieces j \ D(f_j)` — the underlying set of the colength module. -/
lemma supportLocus_inter_pieces (j : D.index) :
    d.supportLocus ∩ (D.pieces j : Set (relCurve C R))
      = (D.pieces j : Set (relCurve C R))
        \ ((relCurve C R).basicOpen (A.eqn j) : Set (relCurve C R)) := by
  ext w
  constructor
  · rintro ⟨hsupp, hwj⟩
    exact ⟨hwj, fun hwb => hsupp (A.basicOpen_eqn_le_unitLocus j hwb)⟩
  · rintro ⟨hwj, hwb⟩
    exact ⟨fun hwU => hwb ((A.mem_basicOpen_eqn_iff_mem_unitLocus j hwj).mpr hwU), hwj⟩

/-! ## Swallow or miss — openness only -/

/-- **A piece that misses the support has vanishing colength**: its equation has unit germs
throughout, hence is a unit, hence spans the unit ideal.  Clauses (c1) are free there. -/
lemma subsingleton_colength_of_disjoint_supportLocus (j : D.index)
    (hdisj : ∀ z : relCurve C R, z ∈ D.pieces j → z ∉ d.supportLocus) :
    Subsingleton (A.colength j) := by
  have hunit : IsUnit (A.eqn j) := by
    apply (relCurve C R).toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    have hU : z ∈ d.unitLocus := not_not.mp (hdisj z hz)
    exact (A.isUnit_germ_eqn_iff j hz).mpr
      ((d.mem_unitLocus_iff_isUnit_germ (d.cover.mem_opens z)).mp hU)
  exact Ideal.Quotient.subsingleton_iff.mpr
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span rfl) hunit)

/-- **Swallow or miss gives no-leak at that piece.**  Swallowing: the trace is the whole
support, closed by `isClosed_supportLocus`.  Missing: the trace is empty.  No fibre, no
tube, no idempotent, and — the point — no chart.

Note the signature: this does not mention the adaptation at all, only the piece.  That is
the sharpest form of I-0492 clause 3 — swallow-or-miss is a statement about an OPEN SET. -/
theorem supportLeak_eq_empty_of_subset_or_disjoint (U : (relCurve C R).Opens)
    (h : d.supportLocus ⊆ (U : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (U : Set (relCurve C R))) :
    d.supportLeak U = ∅ := by
  refine (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty U).mp ?_
  rcases h with hsub | hdisj
  · rw [Set.inter_eq_left.mpr hsub]
    exact d.isClosed_supportLocus
  · rw [Set.disjoint_iff_inter_eq_empty.mp hdisj]
    exact isClosed_empty

/-- **The clopen-trace argument, chart-free.** A preconnected support meets a leak-free
piece either totally or not at all: the trace is open in the support because the PIECE IS
OPEN, and closed in it because nothing leaks.

This is `DivisorAdaptation.subset_or_disjoint_of_isPreconnected_of_supportLeak`
(`DivSchemeCertZarConn.lean:98`) with the chart structure removed, and it is the precise
statement I-0492 clause 3 rests on: per-piece swallow-or-miss needs only openness. -/
theorem subset_or_disjoint_of_isPreconnected_of_supportLeak
    (U : (relCurve C R).Opens)
    (hconn : _root_.IsPreconnected d.supportLocus)
    (hleak : d.supportLeak U = ∅) :
    d.supportLocus ⊆ (U : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (U : Set (relCurve C R)) := by
  classical
  have hclosed : IsClosed (d.supportLocus ∩ (U : Set (relCurve C R))) :=
    (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty U).mpr hleak
  by_cases hdisj : Disjoint d.supportLocus (U : Set (relCurve C R))
  · exact Or.inr hdisj
  refine Or.inl ?_
  by_contra hnsub
  obtain ⟨x, hx⟩ := Set.not_disjoint_iff.mp hdisj
  obtain ⟨y, hyS, hyU⟩ := Set.not_subset.mp hnsub
  obtain ⟨z, hzS, hzu, hzv⟩ :=
    hconn (U : Set (relCurve C R))
      (d.supportLocus ∩ (U : Set (relCurve C R)))ᶜ
      U.isOpen hclosed.isOpen_compl
      (fun w _ => by
        by_cases hwU : w ∈ (U : Set (relCurve C R))
        · exact Or.inl hwU
        · exact Or.inr fun hc => hwU hc.2)
      ⟨x, hx.1, hx.2⟩ ⟨y, hyS, fun hc => hyU hc.2⟩
  exact hzv ⟨hzS, hzu⟩

/-- Leak-freeness at every piece plus a preconnected support gives swallow-or-miss
everywhere. -/
theorem forall_subset_or_disjoint_of_isPreconnected
    (hconn : _root_.IsPreconnected d.supportLocus)
    (hleak : ∀ j : D.index, d.supportLeak (D.pieces j) = ∅) :
    ∀ j : D.index, d.supportLocus ⊆ (D.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)) := fun j =>
  subset_or_disjoint_of_isPreconnected_of_supportLeak (D.pieces j) hconn (hleak j)

/-- **The assembler-shaped `hnoLeak` from swallow-or-miss**, with no fibre analysis. -/
theorem forall_noLeak_of_forall_subset_or_disjoint
    (h : ∀ j : D.index, d.supportLocus ⊆ (D.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (D.pieces j : Set (relCurve C R))) :
    ∀ (j : D.index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (D.pieces j : Set (relCurve C R))) ⊆
        (D.pieces j : Set (relCurve C R)) := by
  intro j s x hx
  have hleak := supportLeak_eq_empty_of_subset_or_disjoint (D.pieces j) (h j)
  by_contra hxU
  exact Set.eq_empty_iff_forall_notMem.mp hleak x ⟨hx.2, hxU⟩

/-! ## Clause (c1) — affineness only -/

section Finite

variable [IsProper C.hom]

/-- **Clause (c1)-finite from a closed piece trace.** Affineness of the piece feeds the
landed abstract engine `IsAffineOpen.finite_quotient_span_singleton_of_isClosed`; the
properness licence on the relative curve supplies universal closedness. No chart. -/
theorem finite_colength_of_isClosed_supportLocus_inter (j : D.index)
    (hclosed : IsClosed (d.supportLocus ∩ (D.pieces j : Set (relCurve C R)))) :
    Module.Finite R (A.colength j) := by
  rw [A.supportLocus_inter_pieces j] at hclosed
  exact (D.isAffineOpen_pieces j).finite_quotient_span_singleton_of_isClosed
    (A.eqn j) hclosed

/-- Clause (c1)-finite in the leak-locus spelling. -/
theorem finite_colength_of_supportLeak_eq_empty (j : D.index)
    (hleak : d.supportLeak (D.pieces j) = ∅) :
    Module.Finite R (A.colength j) :=
  A.finite_colength_of_isClosed_supportLocus_inter j
    ((d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty (D.pieces j)).mpr hleak)

/-- **Clause (c1)-finite at every piece, from swallow-or-miss.** -/
theorem forall_finite_colength_of_forall_subset_or_disjoint
    (h : ∀ j : D.index, d.supportLocus ⊆ (D.pieces j : Set (relCurve C R))
      ∨ Disjoint d.supportLocus (D.pieces j : Set (relCurve C R))) :
    ∀ j : D.index, Module.Finite R (A.colength j) := fun j =>
  A.finite_colength_of_supportLeak_eq_empty j
    (supportLeak_eq_empty_of_subset_or_disjoint (D.pieces j) (h j))

end Finite

/-! ## The (c1) junction on the widened flatness input -/

section Junction

variable [IsNoetherianRing R]

/-- **(c1) flatness from fibrewise regularity**, now over an arbitrary affine piece: the
`SlicingFlat` keystone applied on the piece ring, whose `R`-flatness is
`AffCoverData.flat_sections_pieces` — the flat-morphism route, not pinned-chart freeness. -/
theorem flat_colength_of_forall_tmul_residueField (j : D.index)
    (hfib : ∀ p : PrimeSpectrum R,
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField)) :
    Module.Flat R (A.colength j) := by
  haveI : Module.Flat R Γ(relCurve C R, D.pieces j) := D.flat_sections_pieces j
  exact Module.Flat.quotient_span_singleton_of_forall_tmul_residueField hfib

/-- **Clause (c1) for the piece `j`**: fibrewise-regular equation + finite colength ⟹
finite projective. -/
theorem projective_colength_of_forall_tmul_residueField (j : D.index)
    (hfib : ∀ p : PrimeSpectrum R,
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField))
    [Module.Finite R (A.colength j)] :
    Module.Projective R (A.colength j) := by
  haveI : Module.Flat R Γ(relCurve C R, D.pieces j) := D.flat_sections_pieces j
  exact Module.Projective.quotient_span_singleton_of_forall_tmul_residueField hfib

end Junction

end AffAdaptation

end AlgebraicGeometry
