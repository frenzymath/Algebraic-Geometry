/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyDegreeZeroUseSite
import AlgebraicJacobian.Picard.Pic0ChartSeamCollapse

/-!
# THE SEAM PAIR IS INHABITED, AND ITS INHABITANT IS EXACTLY VANISHING `pic⁰`

**Three** roadmap rows defer to one sentence — *"inhabitation of the pair `(huniv V, hcov V)`
is UNMEASURED at every `V` and may be empty everywhere"* — namely `AJCR.w4-rep`,
`…datum.atlas-coupling` and `…datum.chart-restrict`; in Lean the sentence appears verbatim in
exactly one other file, `Pic0ChartSeamCollapse.lean:13`, from which the paragraph you are
reading inherited it.  (**An earlier version of this paragraph said "four rows and three file
headers" and named `Pic0ChartRestrictedFibreSat`, `Pic0ChartVMonotone` and
`Pic0ChartBotRefute` as carrying it.  A normalized-whitespace search finds it in none of the
three** — `Pic0ChartBotRefute.lean:107` says the materially weaker "no measured inhabitant at
any `V`".  Corrected because inflating the count inflates what this file unblocks.)

Every predecessor result is an *endpoint* result — the pair's coverage clause is refuted at
`V = ⊥`, antecedent 1 is free there, and antecedent 1 is maximal at `V = ⊤` — and
`Pic0ChartSeamCollapse` identifies the pair with `IsIso` of the chart map without exhibiting
or refuting one.

**This file decides it.**  At the chart whose `rep` slot is filled by the landed degree-zero
producer, the pair is *equivalent* to a hypothesis that already has a name elsewhere in the
tree:

  `IsOpenImmersion.presheaf f ∧ IsLocallySurjective f  ↔  ∀ S, Subsingleton (pic⁰(S))`

Both directions, with no `V`-restriction, no chart index constraint beyond the free `hdeg` at
parameter `0`, and no hypothesis on the curve beyond its standing package.

## Why this parameter, and why it is not a degenerate dodge

The chart is `abelSigmaChartZero` (`Picard/DivisorFamilyDegreeZeroUseSite.lean`), the Abel
chart at parameter `0`, whose `rep` binder is discharged by `divFunctorZeroRepresentableBy`.
Its source is the representing object's underlying scheme — and at parameter `0` that object
is the *terminal* `Over.mk (𝟙 (Spec k))`, so the source is `Spec k` itself and the chart map
sends a point `v : T ⟶ Spec k` to the Σ-element `⟨v, class⟩`.

That shape is what makes both directions cheap, and in *opposite* ways:

* **Antecedent 1 is free**, because the Σ-component of the chart value **is** the point:
  reading it off recovers `v`, so the map is injective on the nose at every test
  (`injective_abelSigmaChartZero_sigmaComponent`).  This is not the `V = ⊥` degeneracy — the source is
  nonempty and the statement is at the unrestricted chart.
* **Antecedent 2 is exactly the vanishing**, because the Σ-component is *surjective* for free
  and the fibre component then has to be hit, which at a singleton `pic⁰` it is
  (`surjective_app_abelSigmaChartZero_of_subsingleton`).  Conversely a *second* degree-zero
  class at one test defeats surjectivity, so the vanishing is not merely sufficient
  (`subsingleton_pic0Subgroup_of_surjective_app`).

So the pair, at this chart, is one hypothesis wearing two hats — and it is the hypothesis
`Picard/Pic0VanishingRoute.lean` produces `JacobianData` from by a route with *none* of the
atlas's antecedents.  The two routes are not alternatives: they close together.

## What is reused rather than rebuilt

`Pic0ChartSeamCollapse.chartIso_of_seam` takes `IsOpenImmersion.presheaf` and extracts
injectivity from it via `IsOpenImmersion.le_monomorphisms`.  Here injectivity is available
*directly*, which is strictly less than that antecedent, so the collapse is restated on the
weaker input (`chartIso_of_injective`).  That restatement has an independent payoff, recorded
below as `isOpenImmersion_presheaf_of_injective`: **given coverage, antecedent 1 IS plain
elementwise injectivity** — the two-clause `MorphismProperty.relative` reading that
`Pic0ChartOpenImmersionCriterion` prices as a fibre-presentation datum collapses to an
injectivity statement once antecedent 2 is in hand.  A lane holding coverage owes injectivity
and nothing more.

## What this does NOT do

* **It does not represent `pic⁰` for a curve of positive genus.**  Mathematically the
  hypothesis is false there, and `not_seamPair_abelSigmaChartZero_of_two_pic0` converts any two
  distinct degree-zero classes over one test into a refutation of the pair.  **But note what
  is and is not landed**: nothing in this tree proves `0 < genus C → ∃ S, ¬ Subsingleton
  (pic0Subgroup C S)`, so the refutation is a *conditional* one awaiting that input, not a
  theorem about positive-genus curves.  (`Picard/Pic0ChartForkNegativeBranch.lean` refutes
  chart-map injectivity at a degree with two sections; that is a statement about `divFamZar`
  sections at parameter `n`, **not** about two `pic0Subgroup` elements, so it does not supply
  this bullet's input either.)
* **It does not supply the vanishing.**  `genus C = 0 → pic0Subgroup C S = ⊥` is real curve
  theory, is the debt `Albanese/Genus0Terminal.lean` isolates, and nothing here proves it.
* **It says nothing about a `V` strictly between `⊥` and `⊤` at a positive-genus curve.**  The
  interval question those three rows ask is answered *at this parameter only*, and there the
  `Opens` lattice of the chart source has no interior to ask about: it is `{⊥, ⊤}`, inhabited
  at `⊤` under the vanishing and refuted at `⊥`.

## Main declarations

* `AlgebraicGeometry.chartIso_of_injective` — the collapse from **plain injectivity** plus
  coverage, weakening `chartIso_of_seam`'s first input.
* `AlgebraicGeometry.isOpenImmersion_presheaf_of_injective` — **given coverage, antecedent 1
  is elementwise injectivity.**  Chart-free, divisor-free, curve-free.
* `AlgebraicGeometry.sigmaComponent_abelSigmaChartZero` — the Σ-component of the terminal
  chart's value is the point itself.
* `AlgebraicGeometry.injective_abelSigmaChartZero_sigmaComponent` — **antecedent 1's elementwise content,
  unconditionally**, at the unrestricted chart.
* `AlgebraicGeometry.surjective_app_abelSigmaChartZero_of_subsingleton` /
  `subsingleton_pic0Subgroup_of_surjective_app` — surjectivity **is** the vanishing, both ways.
* `AlgebraicGeometry.isIso_abelSigmaChartZero_of_subsingleton` — the chart is an isomorphism
  of presheaves under the vanishing.
* `AlgebraicGeometry.seamPair_abelSigmaChartZero_of_subsingleton` — **THE INHABITANT**: both
  seam antecedents at once.
* `AlgebraicGeometry.seamPair_abelSigmaChartZero_iff` — **the decision**, as an iff.
* `AlgebraicGeometry.not_seamPair_abelSigmaChartZero_of_two_pic0` — the refutation at any
  curve with two distinct degree-zero classes at one test.
* `AlgebraicGeometry.isLocallySurjective_abelSigmaChartZero_iff` — **the sharp form**:
  antecedent 2 *alone* is the equivalence; antecedent 1 rides free on both sides.
* `AlgebraicGeometry.exists_representableBy_pic0TypeFunctor_of_subsingleton` — **the producer
  fires**: `pic0RepresentableByOfCharts` actually runs on this input, across the
  `Sigma.desc` gap that the pair statement alone does not cross.
* `AlgebraicGeometry.isOpenImmersion_presheaf_abelSigmaChart_of_mono_of_cov` — **the repricing
  at arbitrary parameter**, and the most reusable statement here: with `Mono D.hom`, coverage
  implies antecedent 1 for the general Abel chart at any `n`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The collapse on the weaker input

`Pic0ChartSeamCollapse.chartIso_of_seam` derives elementwise injectivity from antecedent 1.
Everything after that step uses only the injectivity, so the same proof runs from it — and
that matters here because the terminal chart has injectivity *without* having antecedent 1
in hand yet. -/

variable [GeometricallyReduced C.hom]

variable (C) in
/-- **The seam collapse from PLAIN INJECTIVITY.**

Verbatim `chartIso_of_seam`'s argument with its first input weakened: instead of
`IsOpenImmersion.presheaf f`, which *implies* elementwise injectivity, take the injectivity
itself.  Nothing else in that proof consumes the stronger form.

Recorded separately because the two inputs are genuinely different in strength — that is the
content of `isOpenImmersion_presheaf_of_injective` below, which recovers the stronger form
from this one *together with coverage*. -/
theorem chartIso_of_injective {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (hinj : ∀ T : Scheme.{u}ᵒᵖ, Function.Injective (f.app T))
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology f) :
    IsIso (chartSheafHom C f) := by
  haveI : Presheaf.IsLocallyInjective Scheme.zariskiTopology (chartSheafHom C f).hom :=
    Presheaf.isLocallyInjective_of_injective _ _ hinj
  haveI : Presheaf.IsLocallySurjective Scheme.zariskiTopology (chartSheafHom C f).hom := hcov
  exact (Sheaf.isLocallyBijective_iff_isIso (chartSheafHom C f)).mp
    ⟨inferInstance, inferInstance⟩

variable (C) in
/-- **GIVEN COVERAGE, ANTECEDENT 1 IS ELEMENTWISE INJECTIVITY.**

`Pic0ChartOpenImmersionCriterion` prices `IsOpenImmersion.presheaf` as a two-clause
`MorphismProperty.relative` statement and supplies a fibre-presentation datum
(`ChartFibrePresented`) to discharge both clauses.  This says that in the presence of
antecedent 2 the whole thing is *one* clause: injectivity on points at every test.

The route is the collapse — injective plus locally surjective makes the chart map an
isomorphism of sheaves, and `MorphismProperty.relative` contains the isomorphisms.  So the
fibre-product representability half of antecedent 1 is not an independent obligation for a
lane that already holds coverage.

Note the direction of use.  This is *not* a cheaper route to the seam: it consumes antecedent
2, which the board prices as the most expensive of the three.  What it does is remove
antecedent 1 from the list of things a coverage lane must separately establish, replacing it
with a statement about points.  Combined with `injective_of_isOpenImmersion_presheaf`
(`Pic0ChartOpenImmersionCriterion`, the converse, which needs no coverage) the two are
equivalent under coverage. -/
theorem isOpenImmersion_presheaf_of_injective {X : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (hinj : ∀ T : Scheme.{u}ᵒᵖ, Function.Injective (f.app T))
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology f) :
    IsOpenImmersion.presheaf f := by
  letI : IsIso f := by
    haveI := chartIso_of_injective C f hinj hcov
    exact (inferInstance : IsIso ((sheafToPresheaf Scheme.zariskiTopology (Type u)).map
      (chartSheafHom C f)))
  exact MorphismProperty.of_isIso (P := IsOpenImmersion.presheaf) f

/-! ## The terminal chart at parameter `0`

`abelSigmaChartZero` (`Picard/DivisorFamilyDegreeZeroUseSite.lean`) is the Abel chart whose
`rep` binder is discharged by `divFunctorZeroRepresentableBy`, i.e. by the degree-zero
producer.  Its representing object is the *terminal* object of the slice, so its source is
`Spec k` and the chart's Σ-component is the identity on points.  That single structural fact
drives both directions below. -/

variable {pi : C.left ⟶ P1 k} [IsAffineHom pi] [IsIntegral (C ⊗ overSpec k k).left]

omit [GeometricallyReduced C.hom] in
variable (C pi) in
/-- **The Σ-component of the terminal chart's value is the point itself.**

`abelSigmaChart` sends `v` to the Σ-element with structure morphism `v ≫ D.hom`
(`toSigmaExtension_app_fst`), and at parameter `0` the representing object is
`Over.mk (𝟙 (Spec k))`, so `D.hom` is the identity.  Hence reading off the Σ-component
recovers `v` on the nose — no transport, no naturality.

Everything in this section is this lemma read in one of two directions. -/
lemma sigmaComponent_abelSigmaChartZero (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - ((0 : ℕ) : ℤ))
    (T : Scheme.{u}) (v : T ⟶ (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left) :
    ((abelSigmaChartZero (C := C) (pi := pi) m Z hdeg).app (op T) v).1 = v := by
  change v ≫ 𝟙 _ = v
  rw [Category.comp_id]

omit [GeometricallyReduced C.hom] in
variable (C pi) in
/-- **ANTECEDENT 1'S ELEMENTWISE CONTENT IS UNCONDITIONAL AT THIS CHART**: the terminal chart
is injective on points at every test, with no hypothesis whatsoever.

**Not new content, and the docstring should say so.**  This is the parameter-`0` instance of a
landed arbitrary-`n` lemma in this file's own import closure:
`injective_abelSigmaChart_of_subsingleton rep m Z hdeg divFunctorObjSubsingleton_zero T`
typechecks as a direct replacement for the proof below.  The direct proof is kept because it
exhibits the *reason* — the Σ-component is the point — which is what the rest of this section
consumes; the credit for the fact belongs upstream.

Two points a lane must not misread.

* This is **not** the `V = ⊥` degeneracy of `isChartUniv_bot`
  (`Pic0ChartRestrictedFibreSat`) — but **an earlier version of this bullet gave the wrong
  reason**, and the wrong reason matters because it would send a lane looking in the wrong
  place.  It said the distinction is that "here the source is `Spec k`, not the empty scheme".
  That is not it: `isOpenImmersion_presheaf_restrictChart_bot` applies to *this* chart too, so
  the bot degeneracy is available at this source as well.  The real distinction is the **value
  of `V`**: the bot lemmas give antecedent 1 at `V = ⊥`, where by `isChartUniv_antitone`
  (`Pic0ChartVMonotone`) it is *easiest*, and coverage is refuted; what is new here is
  antecedent 1 at `V = ⊤`, unconditionally, where antitonicity makes it *hardest*.
  Antitonicity therefore cannot derive this from the bot results — it runs the other way.
* It is also not in tension with `Pic0ChartForkNegativeBranch`'s refutation of chart-map
  injectivity.  That refutation is at a chart of degree `n` with two distinct effective
  divisors in one class, which needs `2 ≤ h⁰`; at parameter `0` the functor value is a
  singleton (`instSubsingletonDivFamZarSectionZero`), so there is no pair to separate.  The
  fork's negative branch and this lemma live at different parameters, and the fork's own
  hypothesis `2 ≤ Sheaf.h0` is what keeps them apart. -/
-- RENAMED by pic-g (0096 r3), not by this file's author, to unbreak the ROOT build.
-- This theorem was declared here as `injective_abelSigmaChartZero`, which
-- `Pic0ChartMonoUnconditional.lean:82` had already taken for the SAME statement nine hours
-- earlier by a different route (via `injective_abelSigmaChart_of_subsingleton`).  Neither file
-- imports the other, so each compiled alone and the clash appeared only in the root's import
-- closure -- `AlgebraicJacobian.lean` failed with "environment already contains".  The suffix
-- names the route used below: the Σ-component of the chart value IS the point.  Nothing else
-- changed, and no external declaration referenced the old name.
theorem injective_abelSigmaChartZero_sigmaComponent (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - ((0 : ℕ) : ℤ))
    (T : Scheme.{u}ᵒᵖ) :
    Function.Injective ((abelSigmaChartZero (C := C) (pi := pi) m Z hdeg).app T) := by
  intro v₁ v₂ h
  have h₁ := sigmaComponent_abelSigmaChartZero C pi m Z hdeg T.unop v₁
  have h₂ := sigmaComponent_abelSigmaChartZero C pi m Z hdeg T.unop v₂
  rw [← h₁, ← h₂, h]

/-! ## Surjectivity IS the vanishing

The Σ-component being the identity on points means the chart's app is surjective exactly when
the fibre components are forced — and there is at most one thing to hit per structure
morphism precisely when `pic⁰` is a singleton there.  Both directions below are that
observation; neither uses the sheaf property, the site, or a cover. -/

omit [GeometricallyReduced C.hom] in
variable (C pi) in
/-- **Surjectivity of the terminal chart's app, from vanishing `pic⁰`.**

Given a Σ-element `⟨a, ξ⟩` over `T`, the point `a : T ⟶ Spec k` is already a point of the
chart source, and its chart value has Σ-component `a` by
`sigmaComponent_abelSigmaChartZero`.  The two fibre components then live in the same
`pic0Subgroup C (Over.mk a)`, where the hypothesis identifies them — so the transport is
`Over.sigmaExtension_ext` with `Subsingleton.allEq`, and no cohomology, cover or naturality
enters. -/
theorem surjective_app_abelSigmaChartZero_of_subsingleton
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - ((0 : ℕ) : ℤ))
    (hvan : ∀ S : Over (Spec (.of k)), Subsingleton (pic0Subgroup C S))
    (T : Scheme.{u}ᵒᵖ) :
    Function.Surjective ((abelSigmaChartZero (C := C) (pi := pi) m Z hdeg).app T) := by
  rintro ⟨a, xi⟩
  refine ⟨a, ?_⟩
  refine Over.sigmaExtension_ext (pic0TypeFunctor C)
    (show a ≫ 𝟙 _ = a from Category.comp_id a) ?_
  exact (hvan _).allEq _ _

omit [GeometricallyReduced C.hom] in
variable (C pi) in
/-- **THE CONVERSE: surjectivity FORCES the vanishing.**

If the chart's app is surjective at the test `S.left`, then every degree-zero class over
`Over.mk S.hom` — i.e. over `S` itself, since `Over.mk S.hom = S` by `rfl` — is the chart
value of some point, and by the previous lemma's Σ-component computation that point is
`S.hom` itself.  So the class is determined, and two classes over `S` coincide.

This is what makes the decision an equivalence rather than a sufficient condition, and it is
the reason this file's headline is not a weakening: a curve with two distinct degree-zero
classes at one test has no hope at this chart, whatever `V` one restricts to
(`not_seamPair_abelSigmaChartZero_of_two_pic0`). -/
theorem subsingleton_pic0Subgroup_of_surjective_app
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - ((0 : ℕ) : ℤ))
    (hsurj : ∀ T : Scheme.{u}ᵒᵖ,
      Function.Surjective ((abelSigmaChartZero (C := C) (pi := pi) m Z hdeg).app T))
    (S : Over (Spec (.of k))) :
    Subsingleton (pic0Subgroup C S) := by
  refine ⟨fun x y => ?_⟩
  -- both classes name a Σ-element over `S.left` with structure morphism `S.hom`
  obtain ⟨vx, hvx⟩ := hsurj (op S.left) ⟨S.hom, x⟩
  obtain ⟨vy, hvy⟩ := hsurj (op S.left) ⟨S.hom, y⟩
  -- the Σ-components pin the two points to `S.hom`, hence to each other
  have hx : vx = S.hom := by
    rw [← sigmaComponent_abelSigmaChartZero C pi m Z hdeg S.left vx, hvx]
  have hy : vy = S.hom := by
    rw [← sigmaComponent_abelSigmaChartZero C pi m Z hdeg S.left vy, hvy]
  have : (⟨S.hom, x⟩ : (pic0SigmaSheaf C).1.obj (op S.left)) = ⟨S.hom, y⟩ := by
    rw [← hvx, ← hvy, hx, hy]
  exact eq_of_heq (Sigma.mk.inj this).2

/-! ## THE INHABITANT, AND THE DECISION

The two sections above meet here.  Injectivity is free, surjectivity is the vanishing, and
`isIso_iff_bijective` at every test turns the pair into `IsIso` — from which both seam
antecedents follow, antecedent 1 because `MorphismProperty.relative` contains the isomorphisms
and antecedent 2 because an iso is locally surjective. -/

omit [GeometricallyReduced C.hom] in
variable (C pi) in
/-- **The terminal chart is an isomorphism of presheaves under the vanishing.**

The bridge lemma of this section: injective (free) plus surjective (the vanishing) at every
test is bijective at every test, and a pointwise-iso natural transformation is an iso. -/
theorem isIso_abelSigmaChartZero_of_subsingleton
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - ((0 : ℕ) : ℤ))
    (hvan : ∀ S : Over (Spec (.of k)), Subsingleton (pic0Subgroup C S)) :
    IsIso (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg) := by
  haveI : ∀ T, IsIso ((abelSigmaChartZero (C := C) (pi := pi) m Z hdeg).app T) := fun T =>
    (isIso_iff_bijective _).mpr
      ⟨injective_abelSigmaChartZero_sigmaComponent C pi m Z hdeg T,
       surjective_app_abelSigmaChartZero_of_subsingleton C pi m Z hdeg hvan T⟩
  exact NatIso.isIso_of_isIso_app _

omit [GeometricallyReduced C.hom] in
variable (C pi) in
/-- **THE INHABITANT OF THE SEAM PAIR.**

Both seam clauses at one chart, at once — the thing three roadmap rows record as unmeasured.
Antecedent 1 is `MorphismProperty.of_isIso`; antecedent 2 is the instance an iso carries.

**Read the clauses' shapes, not their names.**  An earlier version of this docstring said this
gives "both antecedents of `pic0RepresentableByOfCharts` at once", which is false *as an
applicability claim*: that producer takes its coverage antecedent as an instance on
`Sigma.desc f`, not on `f`, and `inferInstance` does not cross the gap.  The producer really
does fire — see `exists_representableBy_pic0TypeFunctor_of_subsingleton` below, which supplies
the `Sigma.ι_desc` factorisation — but this theorem alone does not reach it.

Read against the endpoint literature: `Pic0ChartRestrictedFibreSat` shows the pair's clauses
fail at `V = ⊤` for the *unrestricted divisor scheme* chart and degenerate at `V = ⊥`, and
concludes "any working `V` is a proper intermediate open".  That conclusion is about *that*
chart.  Here the chart source is `Spec k`, and no restriction is used at all — the honest
statement of the interval result is that a working `V` is proper *for a chart whose source is
the divisor scheme of a positive-degree parameter*. -/
theorem seamPair_abelSigmaChartZero_of_subsingleton
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - ((0 : ℕ) : ℤ))
    (hvan : ∀ S : Over (Spec (.of k)), Subsingleton (pic0Subgroup C S)) :
    IsOpenImmersion.presheaf (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg) ∧
      Presheaf.IsLocallySurjective Scheme.zariskiTopology
        (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg) := by
  haveI := isIso_abelSigmaChartZero_of_subsingleton C pi m Z hdeg hvan
  exact ⟨MorphismProperty.of_isIso (P := IsOpenImmersion.presheaf) _, inferInstance⟩

variable (C pi) in
/-- **THE DECISION, as an iff.**  The seam pair at the terminal chart holds *exactly* when
`pic⁰` vanishes at every test.

The forward direction is `subsingleton_pic0Subgroup_of_surjective_app` applied to the
surjectivity that antecedent 2 gives — via the collapse, which turns local surjectivity plus
(free) injectivity into an honest isomorphism, hence honest surjectivity at every test.  The
backward direction is the inhabitant above.

**This is what those rows were asking, answered at this parameter.**  The pair is neither
empty nor unconditionally inhabited: it is inhabited precisely on the curves whose Jacobian is
a point.

Two scope notes, the first a correction.

* **`m` and `Z` are idle; `V` is NOT.**  An earlier version of this docstring said "the answer
  does not depend on `V`, `m`, or `Z`".  The `m`/`Z` half is right — they appear in no
  hypothesis of the iff, matching `chartIndex_iff_isDegree`'s finding that `hdeg` is pure
  arithmetic and `isDegree_zero`'s that it is free at `0`.  The `V` half is **false**: the
  chart source's `Opens` lattice is `{⊥, ⊤}` (`opens_eq_bot_or_top_of_terminalRep`), and at
  `⊥` the coverage clause is refuted outright *even under the vanishing*
  (`not_isLocallySurjective_restrictChart_bot'`, `Pic0ChartBotRefute.lean`, unconditional and
  for an arbitrary chart family).  So the answer is: inhabited at `⊤`, refuted at `⊥`.  What
  is true is that no *restriction* is needed, which is a statement about `V = ⊤` and not about
  `V`-independence.
* **Antecedent 2 alone carries the equivalence**, since antecedent 1 is unconditional forward
  and recovered from antecedent 2 backward — see `isLocallySurjective_abelSigmaChartZero_iff`
  below, which is the sharp form.  So "the *pair* is decided" should not be read as a discount
  on antecedent 1: it is a discount on nothing, and antecedent 2 is the whole content. -/
theorem seamPair_abelSigmaChartZero_iff
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - ((0 : ℕ) : ℤ)) :
    (IsOpenImmersion.presheaf (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg) ∧
        Presheaf.IsLocallySurjective Scheme.zariskiTopology
          (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg))
      ↔ ∀ S : Over (Spec (.of k)), Subsingleton (pic0Subgroup C S) := by
  refine ⟨fun ⟨_, hcov⟩ S => ?_, seamPair_abelSigmaChartZero_of_subsingleton C pi m Z hdeg⟩
  -- coverage plus free injectivity make the chart an iso, hence surjective on the nose
  letI : IsIso (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg) := by
    haveI := chartIso_of_injective C (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg)
      (injective_abelSigmaChartZero_sigmaComponent C pi m Z hdeg) hcov
    exact (inferInstance : IsIso ((sheafToPresheaf Scheme.zariskiTopology (Type u)).map
      (chartSheafHom C (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg))))
  exact subsingleton_pic0Subgroup_of_surjective_app C pi m Z hdeg
    (fun T => (isIso_iff_bijective _).mp inferInstance |>.2) S

omit [GeometricallyReduced C.hom] in
variable (C pi) in
/-- **THE REFUTATION.**  Two distinct degree-zero classes at one test kill the pair, at every
`m` and `Z`.

Contrapositive of the iff, stated separately because it is the direction a lane looking for a
counterexample needs, and because it makes the decision's *content* explicit: this is not a
sufficient condition dressed up as an equivalence.  Any curve for which the tree can exhibit
two degree-zero classes over one test — which is what positive genus means concretely — has no
seam pair at this parameter, and no choice of chart index or restricting open changes that. -/
theorem not_seamPair_abelSigmaChartZero_of_two_pic0
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - ((0 : ℕ) : ℤ))
    {S : Over (Spec (.of k))} {x y : pic0Subgroup C S} (hxy : x ≠ y) :
    ¬ (IsOpenImmersion.presheaf (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg) ∧
        Presheaf.IsLocallySurjective Scheme.zariskiTopology
          (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg)) := by
  intro hpair
  exact hxy (((seamPair_abelSigmaChartZero_iff C pi m Z hdeg).mp hpair S).allEq x y)

omit [GeometricallyReduced C.hom] in
variable (C pi) in
/-- **THE SHARP FORM: antecedent 2 ALONE is equivalent to the vanishing.**

The pair statement above is not wrong, but it is not sharp: antecedent 1 is a free rider on
both sides of it — unconditional in the forward direction
(`injective_abelSigmaChartZero_sigmaComponent`) and recovered from antecedent 2 in the backward one
(`isOpenImmersion_presheaf_of_injective`).  Stated because the board prices antecedent 2 as
the *most expensive* of the three, so "the pair is decided" would read as a larger discount
than the truth: nothing about antecedent 1 is being bought here, and coverage is the whole
content. -/
theorem isLocallySurjective_abelSigmaChartZero_iff
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - ((0 : ℕ) : ℤ)) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
        (abelSigmaChartZero (C := C) (pi := pi) m Z hdeg)
      ↔ ∀ S : Over (Spec (.of k)), Subsingleton (pic0Subgroup C S) :=
  ⟨fun hcov => (seamPair_abelSigmaChartZero_iff C pi m Z hdeg).mp
      ⟨isOpenImmersion_presheaf_of_injective C _
        (injective_abelSigmaChartZero_sigmaComponent C pi m Z hdeg) hcov, hcov⟩,
   fun hvan => (seamPair_abelSigmaChartZero_of_subsingleton C pi m Z hdeg hvan).2⟩

/-! ## The seam fired, and the arbitrary-parameter form of the repricing -/

omit [GeometricallyReduced C.hom] in
variable (C) in
/-- **THE PRODUCER FIRES.**  Under the vanishing, `pic0TypeFunctor C` is representable.

Stated as an `∃`/`Nonempty` because the representing object `pic0RepresentableByOfCharts`
returns is spelled through mathlib's glue data of the very `hf` being supplied, so naming it
in the conclusion would force the reader to reconstruct the term.  What matters is that the
seam machine *runs* on this input: an earlier version of this file claimed
`seamPair_abelSigmaChartZero_of_subsingleton` gave "both antecedents of
`pic0RepresentableByOfCharts` at once", which was **false as an applicability claim** — the
producer's antecedent 2 is an instance on `Sigma.desc f`, not on `f`, and `inferInstance` does
not cross that gap.  The `Sigma.ι_desc` factorisation below is the missing line, and this
theorem exists so that the gap cannot silently reopen. -/
theorem exists_representableBy_pic0TypeFunctor_of_subsingleton
    (pi' : C.left ⟶ P1 k) [IsAffineHom pi']
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - ((0 : ℕ) : ℤ))
    (hvan : ∀ S : Over (Spec (.of k)), Subsingleton (pic0Subgroup C S)) :
    ∃ J : Over (Spec (.of k)), Nonempty ((pic0TypeFunctor C).RepresentableBy J) := by
  set f := fun _ : PUnit.{u+1} => abelSigmaChartZero (C := C) (pi := pi') m Z hdeg with hfdef
  have hpair := seamPair_abelSigmaChartZero_of_subsingleton C pi' m Z hdeg hvan
  haveI : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    haveI := hpair.2
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      (J := Scheme.zariskiTopology)
      (f₁ := Sigma.ι (fun _ : PUnit.{u+1} =>
        yoneda.obj (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left) PUnit.unit)
      (f₂ := Sigma.desc f) (Sigma.ι_desc f PUnit.unit)
  exact ⟨_, ⟨pic0RepresentableByOfCharts C f (fun _ => hpair.1)⟩⟩

variable (C pi) in
/-- **THE REPRICING AT ARBITRARY PARAMETER**, which is what a coverage lane at `n > 0` needs.

`isOpenImmersion_presheaf_of_injective` is stated for an arbitrary presheaf morphism, so it
composes with the *landed* `injective_abelSigmaChart_of_mono` (`Pic0ChartSubsingletonCollapse`)
to give: for the general Abel chart at **any** parameter `n`, with `Mono D.hom` on the
representing object, **coverage implies antecedent 1**.

This is strictly more useful than the parameter-`0` statements above, and it is not about the
terminal chart at all.  A lane holding antecedent 2 at `n > 0` owes `Mono D.hom` and nothing
else on the antecedent-1 side — no `ChartFibrePresented` datum, no relative GAP-2, no
certificate.  `Mono D.hom` is itself a real obligation, and `Pic0ChartForkNegativeBranch`
refutes chart injectivity (hence `Mono`, hence antecedent 1) wherever an effective divisor of
degree `n` has two sections; so this is a reduction of antecedent 1 to a divisor-scheme
property, not a discharge of it. -/
theorem isOpenImmersion_presheaf_abelSigmaChart_of_mono_of_cov {n : ℕ}
    {D : Over (Spec (.of k))} (rep : (divFunctor C pi n).RepresentableBy D) [Mono D.hom]
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (abelSigmaChart C pi n rep m Z hdeg)) :
    IsOpenImmersion.presheaf (abelSigmaChart C pi n rep m Z hdeg) :=
  isOpenImmersion_presheaf_of_injective C _
    (injective_abelSigmaChart_of_mono rep m Z hdeg) hcov

end

end AlgebraicGeometry
