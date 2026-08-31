/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarKerSpan

/-!
# The certificate of a support-separated adaptation

The DD-R certificate lane was built around the equalizer `W(d) = ker (δ_left − δ_right)`
of the two overlap-restriction arrows.  Its two flat-cokernel clauses (c3)/(c4), and the
kernel-spanning input of `isCertified_of_noLeak_kernel_spanning`, are the genuinely hard
relative content — `DivSchemeHighWindowSyzygy.lean` shows the kernel-spanning law is
*equivalent* to the flatness one is trying to prove, so no cleverer submodule evades it.

This file records the escape hatch that the *pointwise* gate opens up.  Because
`isLocallyCertified_of_forall_prime_exists_certified_adaptation` accepts **any**
adaptation over the shrunken base, we are free to choose one whose pieces are
**support-separated**: each off-diagonal overlap misses the divisor, so its overlap
colength vanishes.  For such an adaptation

* `δ_left = δ_right` on the nose (`deltaLeft_eq_deltaRight_of_separated`), hence
* `W(d)` is the whole product `∏_j colength j` (`gluedSubmodule_eq_top_of_separated'`), and
* both cokernels are *zero* modules, so (c3)/(c4) hold for free
  (`flat_coker_incl_of_separated`, `flat_coker_diff_of_separated`).

What remains of the certificate is only the (c1) data — chart-local colengths finite
projective — plus the constant-rank reading of their product.  Both are already available:
(c1) from the support tube (`SupportTubeFinite.lean`, `SupportTube.lean`) and the rank as a
sum of the per-piece ranks (`Module.rankAtStalk_pi`).

This is a genuine reduction, not a repackaging: the hypothesis it trades for is the
*geometric separation* of the chosen pieces, which the tube produces one base point at a
time, whereas the discharged hypotheses were fibrewise flatness statements over a
nonreduced base.

## Main declarations

* `AlgebraicGeometry.DivisorAdaptation.gluedSubmodule_eq_top_of_separated'` — the equalizer
  collapses over an arbitrary base ring (the field-level lemma generalized).
* `AlgebraicGeometry.DivisorAdaptation.deltaLeft_eq_deltaRight_of_separated` — the Čech
  difference vanishes.
* `AlgebraicGeometry.DivisorAdaptation.isCertified_of_separated` — the certificate from
  (c1) plus a rank reading, with no kernel-spanning and no flatness input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace DivisorAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R pi d)

omit [IsProper C.hom]

/-- On the diagonal the two overlap-restriction maps coincide: the two `≤`-witnesses
`pieces i ⊓ pieces i ≤ pieces i` are definitionally equal (proof irrelevance).  The
base-ring form of `DivisorFamilyFieldDegree`'s field-level lemma. -/
lemma toOvlLeft_self_eq_toOvlRight_self' (i : A.index) :
    A.toOvlLeft i i = A.toOvlRight i i :=
  rfl

/-- **Support separation collapses the equalizer to the whole product, over any base
ring.** If the overlap colength modules vanish off the diagonal, every element of the
product of chart-local colengths satisfies the equalizer condition.

The field-level statement (`gluedSubmodule_eq_top_of_separated`) never used invertibility;
this is the same argument over `R`, which is what the DD-R gate consumes. -/
lemma gluedSubmodule_eq_top_of_separated'
    (hsep : ∀ i j : A.index, i ≠ j → Subsingleton (A.ovlColength i j)) :
    A.gluedSubmodule = ⊤ := by
  refine eq_top_iff.mpr fun s _ => ?_
  rw [mem_gluedSubmodule_iff]
  rintro ⟨i, j⟩
  by_cases hij : i = j
  · subst hij
    exact congrFun (congrArg (fun f : A.colength i →ₐ[R] A.ovlColength i i => (f : _ → _))
      (A.toOvlLeft_self_eq_toOvlRight_self' i)) (s i)
  · haveI := hsep i j hij
    exact Subsingleton.elim _ _

/-- **The Čech difference vanishes for a support-separated adaptation.** Its kernel is the
whole product, and a linear map whose kernel is everything is zero. -/
lemma deltaLeft_eq_deltaRight_of_separated
    (hsep : ∀ i j : A.index, i ≠ j → Subsingleton (A.ovlColength i j)) :
    A.deltaLeft = A.deltaRight := by
  have h : A.deltaLeft - A.deltaRight = 0 := by
    rw [← LinearMap.ker_eq_top]
    exact A.gluedSubmodule_eq_top_of_separated' hsep
  exact sub_eq_zero.mp h

/-- The equalizer, as a module, is the whole product of chart-local colengths. -/
noncomputable def gluedTopEquiv' (h : A.gluedSubmodule = ⊤) : A.Glued ≃ₗ[R] A.chartProd :=
  (LinearEquiv.ofEq _ _ h).trans Submodule.topEquiv

/-! ## The two flat-cokernel clauses, for free -/

/-- (c3) for a support-separated adaptation: the cokernel of `W(d) ↪ ∏_j colength j` is the
zero module, because the inclusion is onto. -/
lemma flat_coker_incl_of_separated
    (hsep : ∀ i j : A.index, i ≠ j → Subsingleton (A.ovlColength i j)) :
    Module.Flat R (A.chartProd ⧸ A.gluedSubmodule) := by
  haveI : Subsingleton (A.chartProd ⧸ A.gluedSubmodule) := by
    rw [A.gluedSubmodule_eq_top_of_separated' hsep]
    infer_instance
  exact Module.Flat.of_linearEquiv
    (N := A.chartProd ⧸ A.gluedSubmodule) (M := PUnit.{u+1})
    (LinearEquiv.ofSubsingleton _ _)

/-- (c4) for a support-separated adaptation: the Čech difference is the zero map, so its
range is `⊥` and the cokernel is the overlap product itself — flat as soon as the overlap
product is.  In the seed setting that flatness is already landed
(`flat_ovlProd_of_seed`). -/
lemma flat_coker_diff_of_separated [Module.Flat R A.ovlProd]
    (hsep : ∀ i j : A.index, i ≠ j → Subsingleton (A.ovlColength i j)) :
    Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight)) := by
  have hzero : A.deltaLeft - A.deltaRight = 0 :=
    sub_eq_zero.mpr (A.deltaLeft_eq_deltaRight_of_separated hsep)
  rw [hzero, LinearMap.range_zero]
  exact Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot ⊥ rfl)

/-! ## Separation is a statement about the support, not about the equations

The hypothesis `hsep` above is checkable geometrically: an overlap whose points all avoid
the family support carries a unit equation, hence a unit overlap ideal, hence a vanishing
overlap colength.  In particular an adaptation in which **at most one piece meets the
support** is automatically separated. -/

/-- **Overlaps that miss the support are separated.** If no point of `pieces i ⊓ pieces j`
lies in the support locus, then `A.eqn i` restricts to a unit there (its germ is a unit at
every point, `RingedSpace.isUnit_of_isUnit_germ`), so the overlap ideal is the unit ideal
and the overlap colength vanishes. -/
lemma subsingleton_ovlColength_of_disjoint_supportLocus (i j : A.index)
    (hdisj : ∀ z : relCurve C R, z ∈ A.pieces i ⊓ A.pieces j → z ∉ d.supportLocus) :
    Subsingleton (A.ovlColength i j) := by
  have hunit : IsUnit (relResAlgHom C R
      (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i)) := by
    rw [relResAlgHom_apply]
    apply (relCurve C R).toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    rw [(relCurve C R).presheaf.germ_res_apply]
    have hU : z ∈ d.unitLocus := not_not.mp (hdisj z hz)
    exact (A.isUnit_germ_eqn_iff i hz.1).mpr
      ((d.mem_unitLocus_iff_isUnit_germ (d.cover.mem_opens z)).mp hU)
  have htop : A.ovlIdeal i j = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _)) hunit
  exact Ideal.Quotient.subsingleton_iff.mpr htop

/-- **One support-meeting piece suffices.** If every piece other than `j₀` avoids the
support entirely, the adaptation is separated: any off-diagonal overlap involves a piece
missing the support, so the overlap misses it too. -/
lemma forall_subsingleton_ovlColength_of_unique_support_piece (j₀ : A.index)
    (hother : ∀ j : A.index, j ≠ j₀ →
      ∀ z : relCurve C R, z ∈ A.pieces j → z ∉ d.supportLocus) :
    ∀ i j : A.index, i ≠ j → Subsingleton (A.ovlColength i j) := by
  intro i j hij
  refine A.subsingleton_ovlColength_of_disjoint_supportLocus i j fun z hz => ?_
  by_cases hi : i = j₀
  · exact hother j (by rw [← hi]; exact fun h => hij h.symm) z hz.2
  · exact hother i hi z hz.1

/-! ## The scope guard: separation forces a fibre-confined support

The converse direction bounds this route honestly.  Both pinned charts carry a partition
of unity, so a support point lying in `V₀ ⊓ V₁` lies in a piece of **each** chart — an
off-diagonal pair whose overlap then meets the support.  Hence a separated adaptation
exists only for a system whose support avoids the chart overlap, i.e. is confined to the
two vertical fibres of `pi`.  No refinement of the cover repairs this, and the pointwise
gate does not help: shrinking the base deletes fibres, it does not move a support point
out of `V₀ ⊓ V₁`.

The field lane recorded the same obstruction and routed around it
(`DivisorFamilyFieldSurj.lean`, deviation note): over a field every module is free, so the
certificate is discharged on the plain extraction adaptation instead.  Over a nonreduced
base that escape is unavailable, which is exactly why the flat-cokernel content of
`DivSchemeHighWindowSyzygy.lean` is unavoidable for a general degree-`g` system. -/

/-- **Separation confines the support to the chart overlap's complement.** If a support
point `z` lies in both pinned charts, the chart-0 pieces cover `V₀` and the chart-1 pieces
cover `V₁`, so `z` lies in a chart-0 piece `i` and a chart-1 piece `j`; these are distinct
(`Sum.inl ≠ Sum.inr`), and both equations have non-unit germ at `z`, so the overlap ideal
is proper and `ovlColength i j` is **not** subsingleton.

So `isCertified_of_separated` applies only to fibre-confined systems.  It is stated to
record the scope of the separated route, not to suggest the hypothesis is generic. -/
theorem supportLocus_disjoint_chart_inter_of_separated
    (hsep : ∀ i j : A.index, i ≠ j → Subsingleton (A.ovlColength i j))
    {z : relCurve C R} (hz : z ∈ d.supportLocus)
    (hz₀ : z ∈ (relCover C R (fiberTwoCover pi)).V₀)
    (hz₁ : z ∈ (relCover C R (fiberTwoCover pi)).V₁) : False := by
  classical
  -- the two charts' partitions of unity put `z` in a piece of each chart
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.mp (A.toFinCoverData.cover₀ hz₀)
  obtain ⟨j₀, hj₀⟩ := Opens.mem_iSup.mp (A.toFinCoverData.cover₁ hz₁)
  set i : A.index := Sum.inl i₀ with hi
  set j : A.index := Sum.inr j₀ with hj
  have hzi : z ∈ A.pieces i := hi₀
  have hzj : z ∈ A.pieces j := hj₀
  -- the germs of both equations at `z` are non-units, since `z` is in the support
  have hnu : ∀ l : A.index, ∀ hzl : z ∈ A.pieces l,
      ¬ IsUnit (((relCurve C R).presheaf.germ (A.pieces l) z hzl).hom (A.eqn l)) := by
    intro l hzl hu
    exact hz ((A.mem_basicOpen_eqn_iff_mem_unitLocus l hzl).mp
      (((relCurve C R).mem_basicOpen (A.eqn l) z hzl).mpr hu))
  -- but separation makes the overlap colength trivial, i.e. the overlap ideal is `⊤`
  haveI := hsep i j (by simp [hi, hj])
  have htop : A.ovlIdeal i j = ⊤ := Ideal.Quotient.subsingleton_iff.mp ‹_›
  -- evaluating `1 ∈ ovlIdeal i j` at the germ of `z` contradicts non-unitness
  have hzW : z ∈ A.pieces i ⊓ A.pieces j := ⟨hzi, hzj⟩
  have hone : (1 : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)) ∈ A.ovlIdeal i j := by
    rw [htop]; exact Submodule.mem_top
  rw [Ideal.mem_span_pair] at hone
  obtain ⟨a, b, hab⟩ := hone
  -- push the identity into the local ring at `z`
  have hgerm := congrArg
    (((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hzW).hom) hab
  rw [map_one, map_add, map_mul, map_mul] at hgerm
  -- both germ images lie in the maximal ideal, so their combination cannot be `1`
  have hmi : ((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hzW).hom
      (relResAlgHom C R (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i))
      ∈ IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z) := by
    rw [relResAlgHom_apply, (relCurve C R).presheaf.germ_res_apply]
    exact not_not.mp (fun h => hnu i hzi (IsLocalRing.notMem_maximalIdeal.mp h))
  have hmj : ((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hzW).hom
      (relResAlgHom C R (inf_le_right : A.pieces i ⊓ A.pieces j ≤ A.pieces j) (A.eqn j))
      ∈ IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z) := by
    rw [relResAlgHom_apply, (relCurve C R).presheaf.germ_res_apply]
    exact not_not.mp (fun h => hnu j hzj (IsLocalRing.notMem_maximalIdeal.mp h))
  have hmem : (1 : (relCurve C R).presheaf.stalk z)
      ∈ IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z) := by
    rw [← hgerm]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmi) (Ideal.mul_mem_left _ _ hmj)
  exact (IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z)).ne_top_iff_one.mp
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top hmem

/-- **"At most one piece meets the support" is impossible once the support meets both
pinned charts.** This refutes, at the level of the pieces, the shape the `tube-fibre` leaf
of the certificate lane was aiming at.

A support point `z` of `V₀ ⊓ V₁` lies in a chart-0 piece and a chart-1 piece, and those are
distinct — so two distinct pieces meet the support, no matter how the cover is refined. -/
theorem not_exists_unique_support_piece
    {z : relCurve C R} (hz : z ∈ d.supportLocus)
    (hz₀ : z ∈ (relCover C R (fiberTwoCover pi)).V₀)
    (hz₁ : z ∈ (relCover C R (fiberTwoCover pi)).V₁)
    (j₀ : A.index)
    (hother : ∀ j : A.index, j ≠ j₀ →
      ∀ y : relCurve C R, y ∈ A.pieces j → y ∉ d.supportLocus) : False :=
  A.supportLocus_disjoint_chart_inter_of_separated
    (A.forall_subsingleton_ovlColength_of_unique_support_piece j₀ hother) hz hz₀ hz₁

/-! ## The certificate -/

/-- **The certificate of a support-separated adaptation.** With the off-diagonal overlap
colengths vanishing, the equalizer is the whole product, the Čech difference is zero, and
both flat-cokernel clauses hold automatically.  What is left is exactly the (c1) data —
each chart-local colength finite projective over `R` — plus the constant-rank reading,
which for the product is the sum of the per-piece ranks.

This is the shape the pointwise gate can consume: no kernel-spanning hypothesis, and no
flatness of a Čech cokernel over a possibly nonreduced base. -/
theorem isCertified_of_separated {n : ℕ} [Module.Flat R A.ovlProd]
    (hsep : ∀ i j : A.index, i ≠ j → Subsingleton (A.ovlColength i j))
    (hfin : ∀ j, Module.Finite R (A.colength j))
    (hproj : ∀ j, Module.Projective R (A.colength j))
    (hrank : ∀ p : PrimeSpectrum R,
      ∑ᶠ j : A.index, Module.rankAtStalk (R := R) (A.colength j) p = n) :
    A.IsCertified n := by
  classical
  haveI := hfin
  haveI := hproj
  haveI : ∀ j : A.index, Module.Flat R (A.colength j) := fun _ =>
    Module.Flat.of_projective
  have htop := A.gluedSubmodule_eq_top_of_separated' hsep
  have hequiv : A.Glued ≃ₗ[R] A.chartProd := A.gluedTopEquiv' htop
  haveI hprodProj : Module.Projective R A.chartProd :=
    Module.Projective.of_equiv' (P := A.chartProd)
      (DirectSum.linearEquivFunOnFintype R A.index (fun j => A.colength j))
  refine
    { finite_colength := hfin
      projective_colength := hproj
      finite_glued := Module.Finite.equiv hequiv.symm
      projective_glued := Module.Projective.of_equiv' (P := A.Glued) hequiv.symm
      rankAtStalk_glued := fun p => ?_
      flat_coker_incl := A.flat_coker_incl_of_separated hsep
      flat_coker_diff := A.flat_coker_diff_of_separated hsep }
  rw [Module.rankAtStalk_eq_of_equiv hequiv, Module.rankAtStalk_pi]
  exact hrank p

end DivisorAdaptation

end AlgebraicGeometry
