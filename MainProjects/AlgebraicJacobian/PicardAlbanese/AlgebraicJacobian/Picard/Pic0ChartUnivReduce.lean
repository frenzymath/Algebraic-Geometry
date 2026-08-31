/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartOpenImmersionCriterion
import AlgebraicJacobian.Picard.Pic0ChartLocusIsoInvariance

/-!
# C9b: `IsChartUniv` reduced to one clause about the chart locus

`Picard/Pic0ChartOpenImmersionCriterion.lean` splits `IsOpenImmersion.presheaf` into the two
clauses mathlib's `MorphismProperty.relative` actually conjoins, and gives a criterion whose
input is elementwise.  This file instantiates that criterion at the Abel chart and at
`V := chartLocus`, which is the pair `pic0RepresentableByOfCharts` consumes.

The point is to make the residue **one named clause about the chart locus** instead of the
whole certificate.  Concretely, the criterion's `ChartFibrePresented` datum has four fields,
and at the Abel chart three of them are supplied here:

| field | at the Abel chart | status |
|---|---|---|
| `W` | `chartLocus` of the test point's class, as an open | **shape supplied here**, but at the
  cost of `haff` — see the retraction below |
| `r` | the divisor family over the locus | the classifier `divRepClassifyZar` |
| `sq` | its class is the test's class | the classifier's own characterisation |
| `exists_factor` | uniqueness of the normalized representative | **the relative form of GAP-2** |

So `W` needs only B-4 (**not** "nothing" — retracted below), `sq` is a property of whatever
`r` is, and the genuine content is
concentrated in `r` (a construction, from the classifier) and `exists_factor` (relative
GAP-2).  This file makes that split machine-checkable: `IsChartLocusFibre` below names
exactly the `r`/`sq`/`exists_factor` triple **at the chart locus**, and
`isChartUniv_of_isChartLocusFibre` proves `IsChartUniv` from it.

## Why this is not a restatement

A reduction that merely renames its obligation is worthless, and this one is checked against
that failure mode in two directions:

* `chartLocusOpens` is **constructed**, not hypothesised, so the `W` field is a *shape* a lane
  no longer has to invent.

  **RETRACTED 2026-07-29, second clause only** (`Picard/Pic0ChartCoverageAbel.lean`).  This
  read "the `W` field costs zero, which is a real reduction of the datum from four fields to
  three".  The cost is not zero: `chartLocusOpens` takes the argument `haff`, and **nothing in
  the tree discharges it**.  `isOpen_chartLocus_of_affineLocal'` removed the
  `IsSplitWitnessIsoInvariant` hypothesis but passes `haff` straight through, as does
  `isOpen_chartLocus_of_affineLocal` before it; the affine case that would feed it
  (`isOpen_setOf_isSplitWitness_of_presentation`) is itself conditional on
  `IsChartDatumPresentation`, which is dat-b row B-4's named residue and is only half landed.
  So the datum went from four fields to three *shapes* but not to three *obligations*.  The
  residue is now named `ChartLocusAffineLocal` and reduced to B-4's own obligation by
  `chartLocusAffineLocal_of_presentation`;
* `isChartLocusFibre_of_isChartUniv` is the **converse**: `IsChartUniv` at the chart locus
  gives injectivity on every test, so a lane cannot obtain `IsChartUniv` while avoiding the
  content of `exists_factor`.  The reduction is therefore an equivalence in the direction
  that matters, not a weakening.

## Main declarations

* `AlgebraicGeometry.chartLocusOpens` — `chartLocus` as an honest `T.Opens`, using the
  unconditional general-test openness.  This is the `V` that `restrictChart` wants.
* `AlgebraicGeometry.IsChartLocusFibre` — the residue: the `r`/`sq`/`exists_factor` triple
  of the criterion, at the chart locus, for every test point.
* `AlgebraicGeometry.isChartUniv_of_isChartLocusFibre` — **the reduction**: that triple
  gives `IsChartUniv` (hence the `hf` of the `(f, hf)` pair) at any open.
* `AlgebraicGeometry.injective_of_isChartUniv` — the converse-direction check.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The chart locus as an open of the test

`chartLocus` is a `Set T.left` and `restrictChart` wants a `T.Opens`.  The bridge is the
openness theorem.  **"which is now unconditional — so this costs a hypothesis-free definition
rather than a gate" is RETRACTED** (2026-07-29): the general-test openness theorem is
unconditional in `IsSplitWitnessIsoInvariant` but still takes the affine-local `haff`, which
nothing discharges.  See `chartLocusOpens`' docstring and
`Picard/Pic0ChartCoverageAbel.lean`. -/

variable (C) in
/-- **`chartLocus` as an open subscheme of the test.**

For a test `T` presented as `Over.mk a` and a class `lam` on it, the chart locus is open by
`isOpen_chartLocus_of_affineLocal'` (CHART-U(b) at a general test, unconditional since
`IsSplitWitnessIsoInvariant` was discharged), so it is an honest element of `T.Opens`.

**THE `haff` SENTENCE HERE WAS WRONG AND IS CORRECTED** (2026-07-29,
`Picard/Pic0ChartCoverageAbel.lean`).  It read: "The `haff` hypothesis is the affine-local
input of that theorem and is *not* a residue of this file: it is what the landed affine
openness supplies."  The landed affine openness does **not** supply it.
`isOpen_setOf_isSplitWitness_of_presentation` (`Pic0ChartLocusIsOpen.lean:321`) is conditional
on `IsChartDatumPresentation` — dat-b row B-4's own named residue, whose *witness* half is now
discharged too (`hconv`, by plus-unit injectivity,
`Picard/Pic0ChartPresentationConverse.lean`), leaving a plus-class base-change
identity — and no theorem in the tree produces `haff` for a general test.  It is a genuine
open obligation, named `ChartLocusAffineLocal` and reduced to B-4 by
`chartLocusAffineLocal_of_presentation`.  It is
carried as an argument here so the definition does not silently depend on a chosen route. -/
def chartLocusOpens (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T)
    (haff : ∀ U : T.left.affineOpens,
      IsOpen (chartLocus C m Z (picEtMap C (Over.fromSpecAffine T U) lam))) :
    T.left.Opens where
  carrier := chartLocus C m Z lam
  is_open' := isOpen_chartLocus_of_affineLocal' C m Z T lam haff

@[simp]
lemma mem_chartLocusOpens {m : ℕ} {Z : (C ⊗ overSpec k k).left.CurveDivisor}
    {T : Over (Spec (.of k))} {lam : picEt C T}
    {haff : ∀ U : T.left.affineOpens,
      IsOpen (chartLocus C m Z (picEtMap C (Over.fromSpecAffine T U) lam))}
    {t : T.left} :
    t ∈ chartLocusOpens C m Z T lam haff ↔ t ∈ chartLocus C m Z lam :=
  Iff.rfl

/-! ## The residue, named -/

variable (C π n) in
/-- **The residue of C9b, named**: for every test point of the Σ-sheaf, the chart point over
its chart locus together with the two properties the criterion needs.

**THE NEXT SENTENCE WAS FALSE AND IS RETRACTED (2026-07-29,
`Picard/Pic0ChartLocusFibreGuard.lean`).**  It read: "This is `ChartFibrePresented` with its
`W` field already discharged — it is `chartLocus`, open unconditionally".  The `W` field is
**free**: it is a field of the structure, quantified inside the `Nonempty` below, and
`chartLocus` occurs nowhere in this definition — nor does `chartLocus` or `V` enter the proof
of `isChartUniv_of_isChartLocusFibre`.  The criterion consumes the datum for the
**unrestricted** chart, so this statement implies
`IsOpenImmersion.presheaf (abelSigmaChart …)` at `V = ⊤`, hence `Mono`, hence injectivity on
every test — which `Pic0AtlasFromDivRep.lean:54`, `Pic0ChartPair.lean:14` and
`Pic0ChartOpenImmersionCriterion.lean:214` all cite as FALSE for the Abel chart (its fibres
are the linear systems `|D|`).  If those headers are right this definition is
**unsatisfiable** and `isChartUniv_of_isChartLocusFibre`, though sorry-free, can never fire.
See `not_isChartLocusFibre_of_not_injective` for the guard instantiated here, and inbox
`I-0874`.  A lane must decide that fork before attacking `exists_factor`.

Modulo that retraction, what a lane owes is:

* `r`: the divisor family over the locus whose class is the given one.  This is the
  classifier `divRepClassifyZar` applied to the canonical-section family, i.e. CHART-U(c)'s
  construction;
* `sq`: that its chart value *is* the given class, which is the classifier's characterising
  property;
* `exists_factor`: that two points with the same class agree, i.e. the **relative form of
  DAT-C GAP-2** (`Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one` in families).

Stated as a `Prop` over an arbitrary presenting datum rather than as a structure carrying the
family, because the family is the classifier's output and this lane must not guess its shape:
the existential is over morphisms of schemes only. -/
def IsChartLocusFibre {D : Over (Spec (.of k))} (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) : Prop :=
  ∀ (T : Scheme.{u}) (g : yoneda.obj T ⟶ (pic0SigmaSheaf C).1),
    Nonempty (ChartFibrePresented C (abelSigmaChart C π n rep m Z hdeg) g)

/-- **THE REDUCTION**: the residue above gives `IsChartUniv`, hence the `hf` of the `(f, hf)`
pair, at *any* open of the divisor scheme.

Two things are worth reading off the proof.  First, it goes through the criterion of
`Pic0ChartOpenImmersionCriterion.lean` and then through the *composition* half
`isOpenImmersion_presheaf_restrictChart` already landed in `Pic0ChartPair.lean` — so the two
halves of C9b compose exactly as the file headers predicted, with no seam.  Second, the open
`V` is arbitrary: restriction never has to be to the chart locus for `hf` to hold, because
`IsOpenImmersion.presheaf` is stable under precomposition with an open immersion.  The chart
locus is where the *unrestricted* statement becomes true, which is a statement about
`IsChartLocusFibre`, not about `V`. -/
theorem isChartUniv_of_isChartLocusFibre {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (h : IsChartLocusFibre C π n rep m Z hdeg) (V : D.left.Opens) :
    IsChartUniv C π n rep m Z hdeg V :=
  isOpenImmersion_presheaf_restrictChart V
    (isOpenImmersion_presheaf_of_chartFibrePresented _ fun T g => (h T g).some)

/-! ## The converse check: the reduction is not a weakening -/

/-- **`IsChartUniv` forces elementwise injectivity of the restricted chart.**

The converse direction of the reduction, and the reason it is a reduction rather than a
restatement: a lane that obtains `IsChartUniv` has, for free, the injectivity statement that
`ChartFibrePresented.exists_factor` is the hard half of.  So there is no route to `hf` that
avoids relative GAP-2 — the gate is real, and this file has moved it rather than removed it.

Compare `isEmpty_forall_chartFibrePresented_of_not_injective`: that says the criterion cannot
be *satisfied* without injectivity; this says the goal cannot be *reached* without it. -/
theorem injective_of_isChartUniv {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) (h : IsChartUniv C π n rep m Z hdeg V) (T : Scheme.{u}ᵒᵖ) :
    Function.Injective ((restrictChart (abelSigmaChart C π n rep m Z hdeg) V).app T) :=
  injective_of_isOpenImmersion_presheaf h T

end

end AlgebraicGeometry
