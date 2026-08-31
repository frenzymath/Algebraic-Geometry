/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffPerPiece

/-!
# cert-collapse on the widened cover: the diagonal is degenerate, and what that forces

Roadmap leaf `AJCR.w4-rep.datum.dat-d.ddr.certificate.cert-collapse`, restated over
`AffCoverData`.  The leaf's ORIGINAL claim — that (c2)/(c3)/(c4) are FREE for a
swallow-or-miss adaptation — was **refuted** by work-reviewer at I-0340 and must not be
re-derived.  This file lands the structural fact behind the refutation, and the corrected
positive statement, on the widened structure.

## The refutation, now kernel-checked rather than argued

`toOvlLeft i i = toOvlRight i i` holds by `rfl`: at `pieces i ⊓ pieces i` proof irrelevance
makes `inf_le_left` and `inf_le_right` the same proof, so the two arrows are literally the
same map (`toOvl_diag_eq`).  Hence **every diagonal component of `deltaLeft - deltaRight`
is identically zero** (`deltaSub_apply_diag`), for every adaptation over every cover.

The consequence, which is why "free" is false: the cokernel of the difference arrow always
retains the diagonal factor `∏_i ovlColength i i`, so clause (c4) forces flatness of those
overlap colengths — it can never be discharged by a structural observation about which
pieces meet the support.  `away-kerspan` therefore stays blocked rather than rejected.

## The corrected positive statement

What survives is a REDUCTION, not a retirement: on a swallow-or-miss adaptation every piece
either swallows the support or misses it, and a missing piece contributes a VANISHING
colength and vanishing overlap colengths (`subsingleton_colength_of_disjoint_supportLocus`,
`subsingleton_ovlColength_of_disjoint`).  A subsingleton module is free of rank zero, hence
flat and projective, so all the missing-piece factors are free of content and only the
swallowing pieces carry the certificate — at most one per connected component of the
support, rather than one per chart.

## Main declarations

* `AffAdaptation.toOvl_diag_eq` — the two overlap arrows agree on the diagonal, by `rfl`.
* `AffAdaptation.deltaSub_apply_diag` — every diagonal component of the difference vanishes.
* `AffAdaptation.subsingleton_ovlColength_of_disjoint` — a piece missing the support kills
  its overlap colengths too.
* `AffAdaptation.flat_colength_of_disjoint_supportLocus`,
  `projective_colength_of_disjoint_supportLocus` — the missing-piece clauses (c1), free of
  any fibrewise-regularity input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace AffAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d)

/-! ## The diagonal degeneracy (the I-0340 refutation, kernel-checked) -/

/-- **The two overlap arrows agree on the diagonal.**  At `pieces i ⊓ pieces i` the
restrictions `inf_le_left` and `inf_le_right` are the same proof of the same inequality, and
`ovlIdeal i i` is symmetric in its two generators, so the two lifts are the same map — by
`rfl`, no transport.

This is the whole content of the I-0340 refutation of this leaf's original claim. -/
lemma toOvl_diag_eq (i : D.index) : A.toOvlLeft i i = A.toOvlRight i i := rfl

/-- **Every diagonal component of the difference arrow vanishes identically**, for every
adaptation over every cover.  Therefore `coker (deltaLeft - deltaRight)` always retains
`∏_i ovlColength i i` as a direct factor, and clause (c4) can never be free: it forces
flatness of the diagonal overlap colengths.  This is why `cert-collapse` is a reduction and
`away-kerspan` stays blocked. -/
lemma deltaSub_apply_diag (s : A.chartProd) (i : D.index) :
    (A.deltaLeft - A.deltaRight) s (i, i) = 0 := by
  simp only [LinearMap.sub_apply, deltaLeft, deltaRight, LinearMap.pi_apply,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
    AlgHom.toLinearMap_apply, Pi.sub_apply]
  rw [show A.toOvlLeft i i = A.toOvlRight i i from A.toOvl_diag_eq i, sub_self]

/-! ## Missing pieces contribute nothing -/

/-- **A piece missing the support kills its overlap colengths too**: its restricted equation
is a unit on the overlap, and the overlap ideal contains it. -/
lemma subsingleton_ovlColength_of_disjoint (i j : D.index)
    (hdisj : ∀ z : relCurve C R, z ∈ D.pieces i ⊓ D.pieces j → z ∉ d.supportLocus) :
    Subsingleton (A.ovlColength i j) := by
  have hunit : IsUnit (relResAlgHom C R
      (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i)) := by
    rw [relResAlgHom_apply]
    apply (relCurve C R).toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    rw [(relCurve C R).presheaf.germ_res_apply]
    have hU : z ∈ d.unitLocus := not_not.mp (hdisj z hz)
    exact (A.isUnit_germ_eqn_iff i (inf_le_left (α := (relCurve C R).Opens) hz)).mpr
      ((d.mem_unitLocus_iff_isUnit_germ (d.cover.mem_opens z)).mp hU)
  exact Ideal.Quotient.subsingleton_iff.mpr
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _)) hunit)

/-- A missing piece's colength module is flat — it is subsingleton, hence free of rank
zero.  No fibrewise-regularity input, no Noetherian hypothesis. -/
lemma flat_colength_of_disjoint_supportLocus (j : D.index)
    (hdisj : ∀ z : relCurve C R, z ∈ D.pieces j → z ∉ d.supportLocus) :
    Module.Flat R (A.colength j) := by
  haveI := A.subsingleton_colength_of_disjoint_supportLocus j hdisj
  haveI : Module.Free R (A.colength j) := Module.Free.of_subsingleton R (A.colength j)
  exact Module.Flat.of_free

/-- A missing piece's colength module is projective, for the same reason. -/
lemma projective_colength_of_disjoint_supportLocus (j : D.index)
    (hdisj : ∀ z : relCurve C R, z ∈ D.pieces j → z ∉ d.supportLocus) :
    Module.Projective R (A.colength j) := by
  haveI := A.subsingleton_colength_of_disjoint_supportLocus j hdisj
  haveI : Module.Free R (A.colength j) := Module.Free.of_subsingleton R (A.colength j)
  exact Module.Projective.of_free

end AffAdaptation

end AlgebraicGeometry
