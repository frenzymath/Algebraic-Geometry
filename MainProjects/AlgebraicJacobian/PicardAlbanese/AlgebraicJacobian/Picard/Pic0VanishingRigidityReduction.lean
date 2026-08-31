/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0VanishingFieldTest
import AlgebraicJacobian.Picard.Pic0VanishingAffineReduction

/-!
# AT GENUS `0` THE `pic⁰` MEMBERSHIP CONDITION IS FIBREWISE TRIVIALITY

`hvan : ∀ T, Subsingleton (pic0Subgroup C T)` is the hypothesis both live routes to a producer
of `(pic0TypeFunctor C).RepresentableBy` pass through, and it had no instance.  Its field
instances were closed at genus `0`, and the surviving ring instances were priced as
"cohomology and base change".

At `genus C = 0` the hypothesis — at *every* test object, not merely affine ones — is
*equivalent* to

  **`hrig`: a `picEt` class that restricts to `1` at every field point of `T` is `1`.**

The equivalence is `pic0Vanishing_iff_rigidity` below, proved in both directions.

## WHAT THIS IS, STATED HONESTLY — the original framing was wrong

**An earlier version of this header called the equivalence a *repricing* and said "the degree
condition is provably idle at genus `0`".  A fresh-context audit (`I-1650`, `I-1653`) refuted
that, and the refutation is worth more than the claim was.**

At genus `0`, for every `T` and every `lam`, the antecedent of `hrig` and membership in
`pic0Subgroup C T` are *equivalent* — forward by `degAt_one` after rewriting the restriction to
`1`, backward by `fibre_eq_one_of_mem_pic0Subgroup` below.  So `hrig` is `hvan` **with the same
predicate written differently**: `= 1` in place of `deg = 0`.  The degree left the notation, not
the mathematics.  The tell was visible in this file all along — `rigidity_of_pic0Vanishing`
needs *no genus hypothesis*, and a genuinely weaker target does not round-trip for free.

**What the new spelling does buy, and it is not nothing.**  `classDeg` carries five instance
binders on the fibre curve (`IsIntegral`, `SmoothOfRelativeDimension 1`, `QuasiCompact`, and
both `Module.Finite` Betti-number clauses) which do not synthesize through the `relCurve` `def`
barrier — all five measured as genuinely required.  The triviality spelling needs none of them,
so hypotheses that could not be *stated* at a general prime become statable.  That is a
**statability** gain, not a reduction of the obligation.

`fibre_eq_one_of_mem_pic0Subgroup` is the direction that is reusable on its own: a degree-zero
class at genus `0` is fibrewise trivial at every field point of **any** test object, with no
affineness.  It is what pic-g's ring-level engine work consumes.

## The converse, and why it is worth stating

`hrig` is not merely sufficient.  `rigidity_of_pic0Vanishing` derives it *from* the vanishing,
because a class trivial at every field point has `degAt` equal to `0` there
(`degAt_one` after transporting along the restriction), hence lies in `pic0Subgroup`, hence is
`1` when that group is trivial.  So the two are the same hypothesis and no strength is lost by
attacking `hrig` instead — the bundled equivalence is `pic0Vanishing_iff_rigidity`.

## What this does NOT do

* **It does not prove `hrig`, at any curve**, and — per the correction above — `hrig` is not a
  *smaller* obligation than `hvan`, only a differently spelled one.  `ℙ¹` gains no instance
  from this file.
* **It does not make `hrig` cheap.**  Field-point separation of `picEt` has no producer in the
  tree either — `PicEtAff.unit_injective` and `relPicAlgMap_injective_of_etaleCover` are
  separation along *étale covers*, which is a different family of test maps, and a field point
  is not an étale cover of `A` unless `A` is already a field.
* **It says nothing at positive genus**, where the forward direction fails at its only step:
  the field-test vanishing it consumes is false there.

## Main declarations

* `AlgebraicGeometry.fibre_eq_one_of_mem_pic0Subgroup` — **the reusable half**: at genus `0`, a
  degree-zero class restricts to `1` at every field point of any test object.
* `AlgebraicGeometry.subsingleton_pic0Subgroup_of_rigidity` — **the reduction**: field-point
  rigidity of `picEt` gives the vanishing at every test.
* `AlgebraicGeometry.rigidity_of_pic0Vanishing` — the converse.
* `AlgebraicGeometry.pic0Vanishing_iff_rigidity` — the equivalence: the two spellings of the
  hypothesis are one hypothesis.
* `AlgebraicGeometry.P1.subsingleton_pic0Subgroup_of_rigidity` — the reduction at `ℙ¹`, with the
  genus hypothesis discharged, so the statement has a witness curve.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

noncomputable section

/-! ## The forward step: the degree condition is spent here, and only here -/

/-- **A DEGREE-ZERO CLASS IS FIBREWISE TRIVIAL AT GENUS `0`**, at every field point of every
test object.

This is the one step that consumes the degree condition.  `pic0Map C t` restricts a
degree-zero class to a *degree-zero* class of the field test — that stability is definitional
through `degAt_picEtMap` — and at a field test the group is a `Subsingleton` by the landed
`subsingleton_pic0Subgroup_overSpec_field_of_genus_zero`, so the restriction is `1` by
`Subsingleton.elim`.  Nothing else in this file mentions a degree.

No affineness on `T`: the test object is arbitrary. -/
theorem fibre_eq_one_of_mem_pic0Subgroup (hg : genus C = 0) {T : Over (Spec (.of k))}
    (lam : pic0Subgroup C T) (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ T) :
    picEtMap C t (lam : picEt C T) = 1 := by
  haveI : Subsingleton (pic0Subgroup C (overSpec k K)) :=
    subsingleton_pic0Subgroup_overSpec_field_of_genus_zero C K hg
  have h1 : pic0Map C t lam = 1 := Subsingleton.elim _ _
  have h2 := congrArg
    (fun z : pic0Subgroup C (overSpec k K) => (z : picEt C (overSpec k K))) h1
  simpa [pic0Map_coe] using h2

/-! ## The reduction, and its converse -/

/-- **THE REDUCTION**: at genus `0`, field-point rigidity of `picEt` gives the `pic⁰` vanishing
at **every** test object.

`hrig`'s statement carries no degree, no χ, no divisor and no chart — it is separation of the
presheaf `picEt C ·` against field points.  The proof is `fibre_eq_one_of_mem_pic0Subgroup` fed
to `hrig`, twice.  (Per `I-1650`: the *hypothesis* is nonetheless the same one, so this is a
change of spelling with a statability payoff, not a discount.) -/
theorem subsingleton_pic0Subgroup_of_rigidity (hg : genus C = 0)
    (hrig : ∀ (T : Over (Spec (.of k))) (lam : picEt C T),
      (∀ (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ T),
        picEtMap C t lam = 1) → lam = 1)
    (T : Over (Spec (.of k))) : Subsingleton (pic0Subgroup C T) := by
  refine ⟨fun s t => Subtype.ext ?_⟩
  have key : ∀ w : pic0Subgroup C T, (w : picEt C T) = 1 := fun w =>
    hrig T _ fun K _ _ tp => fibre_eq_one_of_mem_pic0Subgroup C hg w K tp
  rw [key s, key t]

/-- **THE CONVERSE**: the vanishing gives field-point rigidity.

A class trivial at every field point has `degAt` equal to `0` at every field point — rewrite
the restriction to `1` and apply `degAt_one` — so it lies in `pic0Subgroup C T`, which the
hypothesis makes trivial.  Note this direction needs **no** genus hypothesis. -/
theorem rigidity_of_pic0Vanishing
    (hvan : ∀ T : Over (Spec (.of k)), Subsingleton (pic0Subgroup C T))
    (T : Over (Spec (.of k))) (lam : picEt C T)
    (h : ∀ (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ T),
      picEtMap C t lam = 1) : lam = 1 := by
  haveI := hvan T
  have hmem : lam ∈ pic0Subgroup C T := by
    intro K _ _ t
    rw [degAt, h K t, map_one, PicEtAff.degAff_one]
  have : (⟨lam, hmem⟩ : pic0Subgroup C T) = 1 := Subsingleton.elim _ _
  exact congrArg (fun z : pic0Subgroup C T => (z : picEt C T)) this

/-- **THE EQUIVALENCE**: at genus `0` the vanishing at every test is exactly field-point
rigidity of `picEt`.

Read it as what it is: the *same* hypothesis in two spellings, not a smaller one.  A lane may
take the rigidity form without weakening anything — and the reason to do so is mechanical, that
`classDeg`'s five fibre instances drop out of the statement, not that the obligation shrinks
(`I-1650`). -/
theorem pic0Vanishing_iff_rigidity (hg : genus C = 0) :
    (∀ T : Over (Spec (.of k)), Subsingleton (pic0Subgroup C T))
      ↔ ∀ (T : Over (Spec (.of k))) (lam : picEt C T),
          (∀ (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ T),
            picEtMap C t lam = 1) → lam = 1 :=
  ⟨rigidity_of_pic0Vanishing C, subsingleton_pic0Subgroup_of_rigidity C hg⟩

/-! ## Non-vacuity: the reduction fires at a curve -/

/-- **The reduction at `ℙ¹`, with the genus hypothesis discharged.**

`Curve/P1Curve.lean` gives `P1.asOver k` the curve binders over an arbitrary field and
`Curve/P1H1Vanishing.lean` gives `genus (P1.asOver k) = 0`, so at `ℙ¹` the *only* thing between
this project and a `JacobianData` through `jacobianData_of_subsingleton` is field-point rigidity
of `picEt (P1.asOver k) ·`.  Recorded because a conditional statement whose antecedent has no
witness curve is worth nothing, and this one has one. -/
theorem P1.subsingleton_pic0Subgroup_of_rigidity (k' : Type u) [Field k']
    (hrig : ∀ (T : Over (Spec (.of k'))) (lam : picEt (P1.asOver k') T),
      (∀ (K : Type u) [Field K] [Algebra k' K] (t : overSpec k' K ⟶ T),
        picEtMap (P1.asOver k') t lam = 1) → lam = 1)
    (T : Over (Spec (.of k'))) : Subsingleton (pic0Subgroup (P1.asOver k') T) :=
  AlgebraicGeometry.subsingleton_pic0Subgroup_of_rigidity (C := P1.asOver k')
    (P1.genus_asOver_eq_zero k') hrig T

end

end AlgebraicGeometry
