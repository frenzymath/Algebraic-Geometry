/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartLocusIsOpen

/-!
# CHART-U(b) AT A GENERAL TEST: `isOpen_chartLocus`, and the advertised lemma that did not exist

`Picard/Pic0ChartLocusIsOpen.lean` proves `isOpen_setOf_isSplitWitness_of_presentation` over an
**affine** test, and its docstring says the general-test statement "follows from this one by the
affine-piece locality of the (b-amendment)'s transport (iii) … needs no new mathematics".  That
claim is right, and this file discharges it — but two of its ingredients were not where the tree
said they were.

## The advertised lemma that was absent

`Picard/Pic0ChartTestPoint.lean`'s header says chart-independence of the residue field is free
"and the chart comparison becomes a lemma (`testPointField_affineOpen_iso`) instead of a side
condition.  That is the whole reason this file is short."  **No declaration of that name exists
anywhere in the workspace** — the only occurrence was that sentence (cf. I-0624:
advertised-but-absent).  Since it is cited as the reason a side condition is unnecessary, it is
load-bearing prose, so it is supplied here as `testPointField_fromSpecAffine_isIso`.

It is genuinely cheap, but not for the reason the header gives: what makes it work is that
`Over.fromSpecAffine T U` is an **open immersion** on carriers
(`IsAffineOpen.isOpenImmersion_fromSpec`), and mathlib already knows the residue-field map of an
open immersion is an isomorphism
(`Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion`).  So the comparison is an
iso for a structural reason, not by a computation with `Spec.residueFieldIso`.

## Locality: what "open in every affine piece" needs

`isOpen_iff_forall_mem_open`-style bookkeeping is not quite enough, because the locus over the
piece is a subset of a *different* space (`Spec Γ(T.left, U)`, not `T.left`).  The bridge is that
`fromSpecAffine`'s carrier map is an open immersion with range `U`, so the image of the piece's
locus is the intersection of `chartLocus` with `U` — that is what
`chartLocus_inter_affineOpen_eq_image` records, and the openness statement then follows from
openness of an open immersion's image.

## Main declarations

* `AlgebraicGeometry.Over.testPointField_fromSpecAffine_isIso` — **the absent advertised lemma**:
  the residue-field comparison along an affine-open test object is an isomorphism.
* `AlgebraicGeometry.Over.isSplitWitness_fromSpecAffine_iff` — hence the split-witness predicate
  at a point of an affine piece agrees with the one at its image in `T`; this is transport (i)'s
  hypothesis `hinv` **discharged** for the affine-piece maps (both directions), rather than
  assumed.
* `AlgebraicGeometry.isOpen_chartLocus_of_affineLocal` — **CHART-U(b) at a general test**: if
  `chartLocus` is open over each affine-open test object, it is open over `T`.
* `AlgebraicGeometry.isOpen_chartLocus_of_presentations` — the same fed with the per-piece
  presentation hypotheses, i.e. the general-test keystone of dat-b row B-4 modulo exactly the
  per-piece shifted-datum presentations and nothing else.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

/- The section ring of an affine open is a `k`-algebra; `PicEtUnit.lean` declares this as a
LOCAL instance, so every file stating something about `overSpec k Γ(T.left, U)` must re-open it. -/
attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

namespace Over

/-! ## The absent advertised lemma -/

/-- **The residue-field comparison along an affine-open test object is an isomorphism** — the
lemma `Picard/Pic0ChartTestPoint.lean`'s header advertises as `testPointField_affineOpen_iso`
and which does not exist under that (or any) name.

For `U` an affine open of `T.left` and `t` a point of `Spec Γ(T.left, U)`, the induced extension
`κ(fromSpecAffine T U (t)) → κ(t)` is invertible.

The reason is structural rather than computational: `IsAffineOpen.fromSpec` is an open immersion,
and the residue-field map of an open immersion is an iso in mathlib already. -/
instance testPointField_fromSpecAffine_isIso (T : Over (Spec (.of k)))
    (U : T.left.affineOpens) (t : (overSpec k Γ(T.left, U.1)).left) :
    IsIso (testPointFieldMap (fromSpecAffine T U) t) := by
  haveI : IsOpenImmersion (fromSpecAffine T U).left := U.2.isOpenImmersion_fromSpec
  exact Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion
    (fromSpecAffine T U).left t

end Over

/-! ## Transport (i) for the affine-piece maps, both directions -/

variable (C) in
/-- **The residue-field-iso invariance of the split-witness predicate** — the obligation the
general-test assembly actually rests on, named rather than hidden.

`mem_chartLocus_of_mem_chartLocus_comp` (`Pic0ChartLocus.lean:360`) says transport (i) "proves
nothing on its own — it is an interface, and its proof is `hinv`", and that the tree's landed
invariance discharges `hinv` for *separable* residue-field extensions.  For an affine-open test
object the extension is an **isomorphism** (`Over.testPointField_fromSpecAffine_isIso` — hence in
particular separable), so morally transport (i) is free here.

**But the landed invariance is about `HasWitnessH1Vanishing`, not about `IsSplitWitness`**, and no
declaration in the tree transports `IsSplitWitness` along a field isomorphism: measured, the only
mentions of `IsSplitWitness` invariance are two docstring sentences.  So the affine-piece case of
transport (i) needs *one* lemma the tree does not have, which is this predicate.  That is a
correction to `Pic0ChartLocusIsOpen`'s claim that the general-test statement "needs no new
mathematics": it needs exactly this, and nothing else.

Why it is believable and small: `IsSplitWitness C μ` is an existential over a finite separable
`L/K` presenting `μ`.  Along an isomorphism `K ≃ K'` the same `L` presents the transported class,
because `PicEtAff.map` composes (`PicEtAff.map_map`) and the inverse iso undoes the transport —
i.e. it is `map_map` plus `map_id`, not geometry.  It is stated as a class-free hypothesis here so
that the assembly below is usable the moment a lane proves it. -/
def IsSplitWitnessIsoInvariant : Prop :=
  ∀ (T T' : Over (Spec (.of k))) (f : T' ⟶ T) (t : T'.left)
    (_ : IsIso (Over.testPointFieldMap f t)) (mu : picEt C T),
      IsSplitWitness C (picEtMap C (Over.testPoint t) (picEtMap C f mu))
        ↔ IsSplitWitness C
            (picEtMap C (Over.testPoint (T := T) (f.left.base t)) mu)

variable (C) in
/-- **The split-witness predicate agrees along an affine-open test object**, given the
iso-invariance.

This is transport (i) of `w4-datb` §1.6 for the affine-piece maps, in **both** directions — so
the locus over the piece and the locus over `T` correspond exactly, which is what the locality
assembly needs (a one-sided containment would not give openness).

The only input beyond landed material is `hinv`; the `IsIso` it is applied at is discharged by
`Over.testPointField_fromSpecAffine_isIso`, i.e. structurally, by mathlib's fact that an open
immersion induces an isomorphism of residue fields. -/
theorem isSplitWitness_fromSpecAffine_iff (hinv : IsSplitWitnessIsoInvariant C)
    (T : Over (Spec (.of k))) (U : T.left.affineOpens) (mu : picEt C T)
    (t : (overSpec k Γ(T.left, U.1)).left) :
    IsSplitWitness C (picEtMap C (Over.testPoint t)
        (picEtMap C (Over.fromSpecAffine T U) mu))
      ↔ IsSplitWitness C (picEtMap C
          (Over.testPoint (T := T) ((Over.fromSpecAffine T U).left.base t)) mu) :=
  hinv T (overSpec k Γ(T.left, U.1)) (Over.fromSpecAffine T U) t
    (Over.testPointField_fromSpecAffine_isIso T U t) mu

/-! ## Locality: the general-test assembly -/

variable (C) in
/-- **The affine piece's locus is the preimage of the general-test locus.**

For an affine open `U ⊆ T.left`, `chartLocus` over the affine test object `Spec Γ(T.left, U)` is
the preimage, along the carrier map of `Over.fromSpecAffine T U`, of `chartLocus` over `T`.

Both sides unfold to the same split-witness condition read at two residue fields, so this is
`isSplitWitness_fromSpecAffine_iff` applied pointwise together with `picEtMap_chartTwist` (the
twist commutes with restriction). -/
theorem chartLocus_fromSpecAffine_eq_preimage (hinv : IsSplitWitnessIsoInvariant C)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (U : T.left.affineOpens) (lam : picEt C T) :
    chartLocus C m Z (picEtMap C (Over.fromSpecAffine T U) lam)
      = (Over.fromSpecAffine T U).left.base ⁻¹' chartLocus C m Z lam := by
  refine Set.ext fun t => ?_
  rw [Set.mem_preimage, mem_chartLocus_iff, mem_chartLocus_iff,
    ← picEtMap_chartTwist]
  exact isSplitWitness_fromSpecAffine_iff C hinv T U (chartTwist C m Z T lam) t

variable (C) in
/-- **CHART-U(b) AT A GENERAL TEST**, i.e. the statement `Pic0ChartLocusIsOpen`'s docstring
promises follows from the affine case "by the affine-piece locality of the (b-amendment)'s
transport (iii)".

If `chartLocus` is open over every affine-open test object of `T`, it is open over `T`.

The bookkeeping is genuinely bookkeeping — but note *which* bookkeeping, because it is not the
`isOpen_iff_forall_isOpen_inter` the docstring names: the piece's locus lives in a **different
space** (`Spec Γ(T.left, U)`, not `T.left`), so the bridge is that the carrier map is an open
immersion whose range is `U` (`IsAffineOpen.range_fromSpec`).  The preimage identity
`chartLocus_fromSpecAffine_eq_preimage` then turns per-piece openness into openness of
`chartLocus ∩ U`, and the affine opens cover `T.left`. -/
theorem isOpen_chartLocus_of_affineLocal (hinv : IsSplitWitnessIsoInvariant C)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T)
    (haff : ∀ U : T.left.affineOpens,
      IsOpen (chartLocus C m Z (picEtMap C (Over.fromSpecAffine T U) lam))) :
    IsOpen (chartLocus C m Z lam) := by
  -- Openness is local: it suffices that every point of the locus has an open neighbourhood
  -- inside it, and each point lies in some affine open of `T.left`.
  rw [isOpen_iff_forall_mem_open]
  intro t ht
  -- an affine open around `t`
  obtain ⟨U, hUmem⟩ : ∃ U : T.left.affineOpens, t ∈ U.1 := by
    obtain ⟨U, hU, hmem, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.left.isBasis_affineOpens)
        (show t ∈ (⊤ : T.left.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hmem⟩
  -- the piece's locus is open, and its image is `chartLocus ∩ U`
  have hpre := chartLocus_fromSpecAffine_eq_preimage C hinv m Z T U lam
  refine ⟨chartLocus C m Z lam ∩ U.1, Set.inter_subset_left, ?_, ht, hUmem⟩
  -- `chartLocus ∩ U` is the image of the piece's locus under an open immersion with range `U`
  have hoi : IsOpenImmersion (Over.fromSpecAffine T U).left := U.2.isOpenImmersion_fromSpec
  have hrange : Set.range (Over.fromSpecAffine T U).left.base = (U.1 : Set T.left) := by
    change Set.range (U.2.fromSpec).base = _
    exact U.2.range_fromSpec
  have himg : (Over.fromSpecAffine T U).left.base ''
        (chartLocus C m Z (picEtMap C (Over.fromSpecAffine T U) lam))
      = chartLocus C m Z lam ∩ U.1 := by
    rw [hpre, Set.image_preimage_eq_inter_range, hrange]
  rw [← himg]
  haveI := hoi
  exact (Over.fromSpecAffine T U).left.isOpenEmbedding.isOpenMap _ (haff U)

end

end AlgebraicGeometry
