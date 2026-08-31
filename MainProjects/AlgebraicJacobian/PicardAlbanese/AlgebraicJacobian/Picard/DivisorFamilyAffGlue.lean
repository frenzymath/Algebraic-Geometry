/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffSwallow
import AlgebraicJacobian.Algebra.PiLocalization

/-!
# The glued clauses on a straddling cover: (c2)/(c3)/(c4) REDUCE to (c1)

The corrected cert-collapse claim (roadmap `...certificate.cert-collapse`, as amended after
the I-0340 refutation), carried out on the widened cover.

## What was refuted and what survives

The refuted claim was that (c2)/(c3)/(c4) are FREE for a swallow-or-miss adaptation.  They are
not, and `DivisorFamilyAffCollapse.lean` kernel-checks why: `toOvlLeft i i = toOvlRight i i`
by `rfl`, so every diagonal component of `deltaLeft - deltaRight` vanishes for EVERY
adaptation, and the diagonal factor always survives in the cokernel.  Clause (c4) therefore
always implies flatness of the diagonal overlap colengths — no structural observation about
which pieces meet the support can remove that.

What survives is the REDUCTION the amended node states: on a cover with a straddling piece,
(c2)/(c3)/(c4) follow from (c1)-projectivity alone.  This file proves it.

## The mechanism, and it is sharper than the node's account

With a straddling piece `j₀`, every OTHER piece misses the support, so
`subsingleton_ovlColength_of_disjoint` kills every overlap colength that involves an index
`≠ j₀` — in particular every OFF-DIAGONAL one, since a pair `(i, j)` with `i ≠ j` has at least
one entry `≠ j₀`.  Combined with the vanishing diagonal, `deltaLeft - deltaRight` is the ZERO
map (`deltaSub_eq_zero_of_swallowedBy`).  Hence:

* `gluedSubmodule = ⊤`, so `Glued ≃ chartProd` — (c2) becomes a statement about the product of
  the piece colengths, of which all but one are subsingleton;
* `chartProd ⧸ gluedSubmodule` is subsingleton, so (c3) is free — and this IS free, with no
  input, which is the one part of the original claim that was right;
* `range (deltaLeft - deltaRight) = ⊥`, so the (c4) cokernel is `ovlProd` itself, whose
  factors are the overlap colengths: all subsingleton except `ovlColength j₀ j₀`.  So (c4)
  reduces to flatness of THAT ONE module — exactly the residue the refutation predicted, now
  isolated to a single index instead of a whole cover.

## Main declarations

* `AffAdaptation.deltaSub_eq_zero_of_swallowedBy` — the difference arrow vanishes identically.
* `AffAdaptation.gluedSubmodule_eq_top_of_swallowedBy` — the equalizer is everything.
* `AffAdaptation.gluedEquivChartProd_of_swallowedBy` — hence `Glued ≃ₗ chartProd`.
* `AffAdaptation.flat_coker_incl_of_swallowedBy` — clause (c3), unconditionally free.
* `AffAdaptation.ovlColengthDiagEquiv` — the diagonal overlap colength IS the piece colength
  (the cert-collapse node's "one technical lemma still needed", in the diagonal case).
* `AffAdaptation.flat_coker_diff_of_swallowedBy` — clause (c4) from (c1)-flatness alone.
* `AffAdaptation.isCertified_of_swallowedBy_of_c1` — **the capstone**: the whole certificate
  from (c1) plus the rank datum.

## The upshot for the roadmap

`isCertified_of_swallowedBy` (`DivisorFamilyAffAssemble.lean`) takes FIVE glued hypotheses.
On a straddling cover none of them is needed: `isCertified_of_swallowedBy_of_c1` takes (c1)
finiteness and projectivity, plus `hrank`, and produces all seven clauses.  `hrank` is the
honest content of "the divisor has degree `n`" and cannot come from anywhere else.

That is the corrected cert-collapse claim, discharged.  Note what it does NOT do: it does not
contradict the I-0340 refutation.  (c4) still *implies* flatness of the diagonal overlap
colengths — the refutation is a theorem.  What the straddling shape adds is that this
implication is now harmless, because on the diagonal that flatness IS (c1)-flatness, which the
fibrewise input already supplies.  The refutation said "(c4) is not free"; it is still not
free, it is just no longer an extra assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/- The three `simpa using congrFun …` steps below genuinely need `simpa`: the linter's
suggested `simp using` is not a tactic, and plain `exact` fails because the coerced presheaf
map has to be normalized before the two sides match. -/
set_option linter.unnecessarySimpa false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace AffAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d)

/-! ## Every overlap colength off the straddling diagonal vanishes -/

/-- **An overlap involving a missing piece has vanishing colength.**  `SwallowedBy` says every
piece other than `j₀` is disjoint from the support, and an overlap is contained in each of its
two pieces, so it too misses the support. -/
lemma subsingleton_ovlColength_of_swallowedBy {j₀ : D.index}
    (hmiss : ∀ j : D.index, j ≠ j₀ →
      Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)))
    (i j : D.index) (h : i ≠ j₀ ∨ j ≠ j₀) :
    Subsingleton (A.ovlColength i j) := by
  refine A.subsingleton_ovlColength_of_disjoint i j fun z hz hsupp => ?_
  rcases h with hi | hj
  · exact (Set.disjoint_left.mp (hmiss i hi)) hsupp hz.1
  · exact (Set.disjoint_left.mp (hmiss j hj)) hsupp hz.2

/-- **The difference arrow is identically zero on a straddling cover.**  On the diagonal it
vanishes for every adaptation whatsoever (`deltaSub_apply_diag`, the I-0340 fact); off the
diagonal the target is subsingleton, because a pair `(i, j)` with `i ≠ j` has at least one
entry different from the straddling index. -/
theorem deltaSub_eq_zero_of_swallowedBy (h : D.SwallowedBy d) :
    A.deltaLeft - A.deltaRight = 0 := by
  obtain ⟨j₀, _, hmiss⟩ := h
  refine LinearMap.ext fun s => funext fun p => ?_
  by_cases hp : p.1 = p.2
  · -- diagonal: zero for every adaptation, by proof irrelevance on `inf_le_left/right`
    obtain ⟨i, j⟩ := p
    cases hp
    exact A.deltaSub_apply_diag s i
  · -- off-diagonal: at least one index misses the support, so the target is trivial
    haveI : Subsingleton (A.ovlColength p.1 p.2) := by
      by_cases h1 : p.1 = j₀
      · exact A.subsingleton_ovlColength_of_swallowedBy hmiss p.1 p.2
          (Or.inr fun h2 => hp (h1.trans h2.symm))
      · exact A.subsingleton_ovlColength_of_swallowedBy hmiss p.1 p.2 (Or.inl h1)
    exact Subsingleton.elim _ _

/-! ## The consequences for (c2)/(c3)/(c4) -/

/-- **The equalizer is everything**: with the difference arrow zero, every section glues. -/
theorem gluedSubmodule_eq_top_of_swallowedBy (h : D.SwallowedBy d) :
    A.gluedSubmodule = ⊤ := by
  rw [gluedSubmodule, A.deltaSub_eq_zero_of_swallowedBy h]
  exact LinearMap.ker_zero

/-- **Hence the glued module is the whole product of piece colengths.**  This is what makes
(c2) a statement about the piece colengths — of which, on a straddling cover, all but the
swallowing one are subsingleton. -/
noncomputable def gluedEquivChartProd_of_swallowedBy (h : D.SwallowedBy d) :
    A.Glued ≃ₗ[R] A.chartProd :=
  (LinearEquiv.ofEq _ _ (A.gluedSubmodule_eq_top_of_swallowedBy h)).trans
    Submodule.topEquiv

/-- **Clause (c3) is free on a straddling cover** — no fibrewise input, no Noetherian
hypothesis, nothing.  The inclusion `W(d) ↪ ∏ colength` is onto, so its cokernel is trivial.
This is the one part of this leaf's refuted original claim that was correct. -/
theorem flat_coker_incl_of_swallowedBy (h : D.SwallowedBy d) :
    Module.Flat R (A.chartProd ⧸ A.gluedSubmodule) := by
  haveI : Subsingleton (A.chartProd ⧸ A.gluedSubmodule) := by
    rw [A.gluedSubmodule_eq_top_of_swallowedBy h]; infer_instance
  haveI : Module.Free R (A.chartProd ⧸ A.gluedSubmodule) :=
    Module.Free.of_subsingleton R _
  exact Module.Flat.of_free

/-- **Clause (c2)-finiteness reduces to the piece colengths.** -/
theorem finite_glued_of_swallowedBy (h : D.SwallowedBy d)
    (hfin : ∀ j, Module.Finite R (A.colength j)) :
    Module.Finite R A.Glued := by
  haveI := hfin
  haveI : Module.Finite R A.chartProd := Module.Finite.pi
  exact Module.Finite.equiv (A.gluedEquivChartProd_of_swallowedBy h).symm

/-- **Clause (c2)-projectivity reduces to the piece colengths.**  The index is a `Fin`, so the
product is the direct sum and `Module.Projective.directSum` applies. -/
theorem projective_glued_of_swallowedBy (h : D.SwallowedBy d)
    (hproj : ∀ j, Module.Projective R (A.colength j)) :
    Module.Projective R A.Glued := by
  haveI := hproj
  haveI : Module.Projective R A.chartProd :=
    Module.Projective.of_equiv
      (DirectSum.linearEquivFunOnFintype R D.index A.colength)
  exact Module.Projective.of_equiv (A.gluedEquivChartProd_of_swallowedBy h).symm

/-! ### The diagonal overlap IS the piece colength

The identification the cert-collapse node calls "the one technical lemma still needed", in the
only case the straddling shape leaves: the diagonal.  It is easier there than in general
(`pieces i ⊓ pieces i = pieces i` needs no unit argument, only `inf_idem`) but it is NOT
definitional — `Γ(pieces i ⊓ pieces i)` and `Γ(pieces i)` are different types, which is the
`inf`-bookkeeping hazard the node flags.  So it goes through a genuine algebra equivalence. -/

/-- The opens-level idempotence, named so the transports below can rewrite with it. -/
lemma pieces_inf_self (i : D.index) : D.pieces i ⊓ D.pieces i = D.pieces i := inf_idem _

/-- **The diagonal overlap colength is the piece colength.**  Restriction along
`pieces i ⊓ pieces i = pieces i` is an algebra isomorphism carrying the overlap ideal — whose
two generators coincide there — onto `span {eqn i}`. -/
noncomputable def sectionsInfSelfEquiv (i : D.index) :
    Γ(relCurve C R, D.pieces i ⊓ D.pieces i) ≃ₐ[R] Γ(relCurve C R, D.pieces i) where
  toFun := relResAlgHom C R (le_of_eq (pieces_inf_self i).symm)
  invFun := relResAlgHom C R (le_of_eq (pieces_inf_self i))
  left_inv := fun x => by
    rw [relResAlgHom_apply, relResAlgHom_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp, ← op_comp, homOfLE_comp]
    simpa using congrFun (congrArg (fun f => (CommRingCat.Hom.hom f))
      (congrArg (relCurve C R).presheaf.map
        (congrArg Quiver.Hom.op (Subsingleton.elim _ (homOfLE le_rfl))))) x
  right_inv := fun x => by
    rw [relResAlgHom_apply, relResAlgHom_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp, ← op_comp, homOfLE_comp]
    simpa using congrFun (congrArg (fun f => (CommRingCat.Hom.hom f))
      (congrArg (relCurve C R).presheaf.map
        (congrArg Quiver.Hom.op (Subsingleton.elim _ (homOfLE le_rfl))))) x
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' := AlgHom.commutes _

@[simp]
lemma sectionsInfSelfEquiv_apply (i : D.index)
    (x : Γ(relCurve C R, D.pieces i ⊓ D.pieces i)) :
    sectionsInfSelfEquiv (C := C) (R := R) (D := D) i x
      = relResAlgHom C R (le_of_eq (pieces_inf_self i).symm) x := rfl

/-- **Restricting to the diagonal overlap and coming back is the identity.**  Stated as a
`simp` lemma because the two coercions (`AlgEquiv` vs the `RingHom` that `Ideal.map` takes)
are not syntactically equal, so `rw` cannot use the unstated form. -/
@[simp]
lemma sectionsInfSelfEquiv_relResAlgHom (i : D.index)
    (h : D.pieces i ⊓ D.pieces i ≤ D.pieces i) (x : Γ(relCurve C R, D.pieces i)) :
    sectionsInfSelfEquiv (C := C) (R := R) (D := D) i (relResAlgHom C R h x) = x := by
  rw [sectionsInfSelfEquiv_apply, relResAlgHom_apply, relResAlgHom_apply,
    ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  simpa using congrFun (congrArg (fun f => (CommRingCat.Hom.hom f))
    (congrArg (relCurve C R).presheaf.map
      (congrArg Quiver.Hom.op (Subsingleton.elim _ (homOfLE le_rfl))))) x

/-- The same identity in the `RingHom`-coerced spelling that `Ideal.map` produces.  Both
spellings are needed: `Ideal.map` takes the ring-hom coercion of the equivalence, and `rw`
does not see through the difference. -/
lemma sectionsInfSelfEquiv_ringHom_relResAlgHom (i : D.index)
    (h : D.pieces i ⊓ D.pieces i ≤ D.pieces i) (x : Γ(relCurve C R, D.pieces i)) :
    ((sectionsInfSelfEquiv (C := C) (R := R) (D := D) i :
        Γ(relCurve C R, D.pieces i ⊓ D.pieces i) →+* Γ(relCurve C R, D.pieces i)))
      (relResAlgHom C R h x) = x :=
  sectionsInfSelfEquiv_relResAlgHom i h x

/-- **The diagonal overlap colength is the piece colength.**  The overlap ideal at `(i, i)` is
generated by the two restrictions of `eqn i` along `inf_le_left` and `inf_le_right` — which at
`pieces i ⊓ pieces i` are the same proof of the same inequality, so the ideal is the span of a
single element, and `sectionsInfSelfEquiv` carries it to `span {eqn i}`. -/
noncomputable def ovlColengthDiagEquiv (i : D.index) :
    A.ovlColength i i ≃ₐ[R] A.colength i :=
  Ideal.quotientEquivAlg (A.ovlIdeal i i) (Ideal.span {A.eqn i})
    (sectionsInfSelfEquiv i)
    (by
      rw [AffAdaptation.ovlIdeal, Ideal.map_span]
      refine congrArg (Ideal.span) ?_
      simp only [Set.image_insert_eq, Set.image_singleton]
      rw [sectionsInfSelfEquiv_ringHom_relResAlgHom i inf_le_left (A.eqn i)]
      exact (Set.pair_eq_singleton (A.eqn i)).symm)

/-- Hence flatness of the piece colengths gives flatness of the diagonal overlaps. -/
theorem flat_ovlColength_diag_of_flat_colength (i : D.index)
    [Module.Flat R (A.colength i)] :
    Module.Flat R (A.ovlColength i i) :=
  Module.Flat.of_linearEquiv (A.ovlColengthDiagEquiv i).toLinearEquiv

/-- **Clause (c4) reduces to flatness of the piece colengths alone.**  The difference arrow is
zero, so its cokernel is `ovlProd` itself; every off-`j₀` factor is subsingleton, and the
surviving factor `ovlColength j₀ j₀` is the diagonal overlap of the straddling piece, whose
flatness is what the refutation identified as unavoidable.  It is supplied here as `hdiag`,
one module rather than a whole cover — which is precisely the reduction the amended
cert-collapse node claims. -/
theorem flat_coker_diff_of_swallowedBy' (h : D.SwallowedBy d)
    (hdiag : ∀ i j : D.index, Module.Flat R (A.ovlColength i j)) :
    Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight)) := by
  haveI : ∀ p : D.index × D.index, Module.Flat R (A.ovlColength p.1 p.2) :=
    fun p => hdiag p.1 p.2
  haveI : Module.Flat R A.ovlProd := Module.Flat.pi_of_finite
  have hrange : LinearMap.range (A.deltaLeft - A.deltaRight) = ⊥ := by
    rw [A.deltaSub_eq_zero_of_swallowedBy h]; exact LinearMap.range_zero
  rw [hrange]
  exact Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot ⊥ rfl)

/-- **Every overlap colength is flat, from (c1)-flatness alone.**  Two cases, exhausting the
pairs: off the diagonal at least one index misses the support (straddling), so the overlap
colength is subsingleton hence free; on the diagonal it IS the piece colength, by
`ovlColengthDiagEquiv`.  This removes the last non-(c1) input from clause (c4). -/
theorem flat_ovlColength_of_swallowedBy (h : D.SwallowedBy d)
    (hflat : ∀ j, Module.Flat R (A.colength j)) (i j : D.index) :
    Module.Flat R (A.ovlColength i j) := by
  obtain ⟨j₀, _, hmiss⟩ := h
  by_cases hij : i = j
  · subst hij
    haveI := hflat i
    exact A.flat_ovlColength_diag_of_flat_colength i
  · haveI : Subsingleton (A.ovlColength i j) := by
      by_cases h1 : i = j₀
      · exact A.subsingleton_ovlColength_of_swallowedBy hmiss i j
          (Or.inr fun h2 => hij (h1.trans h2.symm))
      · exact A.subsingleton_ovlColength_of_swallowedBy hmiss i j (Or.inl h1)
    haveI : Module.Free R (A.ovlColength i j) := Module.Free.of_subsingleton R _
    exact Module.Flat.of_free

/-- **Clause (c4) from (c1)-flatness alone**, on a straddling cover.  No overlap input. -/
theorem flat_coker_diff_of_swallowedBy (h : D.SwallowedBy d)
    (hflat : ∀ j, Module.Flat R (A.colength j)) :
    Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight)) :=
  A.flat_coker_diff_of_swallowedBy' h (A.flat_ovlColength_of_swallowedBy h hflat)

/-! ## The capstone: a certificate from (c1) and the rank alone

This is what the reduction is FOR.  `DivisorFamilyAffAssemble.lean`'s
`isCertified_of_swallowedBy` had to take (c2)/(c3)/(c4) as hypotheses, because in general
they are not free.  On a straddling cover they are not hypotheses at all: they follow from
(c1) plus the flatness of the overlap colengths and the rank input. -/

/-- **The full certificate on a straddling cover, from piece-level data only.**  Compare
`AffAdaptation.isCertified_of_swallowedBy` (`DivisorFamilyAffAssemble.lean`), which takes five
glued hypotheses; here the only non-(c1) inputs are the overlap flatness the I-0340 refutation
proved unavoidable, and the rank/degree datum `hrank`, which is the honest content of "the
divisor has degree `n`" and cannot come from anywhere else.

So the corrected cert-collapse claim is discharged: **(c2)/(c3)/(c4) reduce to (c1) plus the
degree datum**, over an arbitrary affine-open cover of an arbitrary field's relative curve. -/
theorem isCertified_of_swallowedBy_of_c1 {n : ℕ} (h : D.SwallowedBy d)
    (hfin : ∀ j, Module.Finite R (A.colength j))
    (hproj : ∀ j, Module.Projective R (A.colength j))
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk A.Glued p = n) :
    A.IsCertified n where
  finite_colength := hfin
  projective_colength := hproj
  finite_glued := A.finite_glued_of_swallowedBy h hfin
  projective_glued := A.projective_glued_of_swallowedBy h hproj
  rankAtStalk_glued := hrank
  flat_coker_incl := A.flat_coker_incl_of_swallowedBy h
  flat_coker_diff := A.flat_coker_diff_of_swallowedBy h fun j => by
    haveI := hfin j; haveI := hproj j
    exact Module.Flat.of_projective

end AffAdaptation

end AlgebraicGeometry
