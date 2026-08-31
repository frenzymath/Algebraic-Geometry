/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TwoChartRepresentable
import AlgebraicJacobian.Tangent.TwoChartHonest

/-!
# A CHART-TRIVIAL PICARD CLASS IS TRIVIAL WHEN THE OVERLAP UNITS ARE ALL COBOUNDARIES

For a scheme `X` with two opens `V₀ ⊔ V₁ = ⊤`, the Wave-5 tangent lane built both halves of
the two-chart comparison

```
Γ(X, V₀ ⊓ V₁)ˣ ⧸ (im Γ(V₀)ˣ · im Γ(V₁)ˣ)  ↪  X.CechPic
```

— surjectivity onto the chart-trivial classes (`Scheme.twoChartClassHom_surjOn_of_chartTrivial`,
`Tangent/TwoChartRepresentable.lean:301`) and the exact kernel
(`Scheme.twoChartClassHom_eq_one_iff`, `Tangent/TwoChartCechPic.lean:321`).  Composing them
gives a **criterion** nobody had stated: if every overlap unit is a coboundary, then every class
trivial on both charts is trivial.

That composite is what a computation of `Pic` on a two-chart cover actually wants to consume: it
turns a statement about the *unit groups of three rings* — pure commutative algebra, no
cohomology — into triviality of a Picard class.  Both inputs are general in the scheme, so this
is too: no affineness, no curve, no dual numbers, no field.

## Why it is here rather than in `Tangent/`

The two inputs were built for the Wave-5 `ε`-kernel computation and live there.  This file is
about the *Picard group of a two-chart scheme* rather than about tangent spaces, and its intended
consumer is the ring-case obligation of the representability route
(`Picard/Pic0RingZariskiLocal.lean`), where the relevant `X` is a relative curve over a test ring
and the three rings are the two chart algebras and their overlap.

## The one hypothesis that is not about units

`hsel`, surjectivity of the selector, is what makes the two-chart cover *honest* (both charts are
actually used).  It is not an extra obligation:
`Scheme.AffineTwoCover.surjective_selector_of_not_isAffine`
(`Tangent/TwoChartHonest.lean:108`) derives it from `¬ IsAffine X` alone, and a proper
positive-dimensional scheme over a field is not affine.  Stated with `hsel` explicit because this
file is general in `X` and the non-affineness is the consumer's to supply.

## Main declarations

* `AlgebraicGeometry.Scheme.cechPic_eq_one_of_chartTrivial_of_overlapUnits_coboundary` — the
  criterion.
* `AlgebraicGeometry.Scheme.subsingleton_chartTrivial_of_overlapUnits_coboundary` — the same as a
  statement about the subgroup of chart-trivial classes, for a consumer holding two classes
  rather than one.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}} {V : Bool → X.Opens}

/-- The coboundary subgroup of the overlap units of a two-chart cover: the units of
`Γ(X, V₀ ⊓ V₁)` that are products of restrictions of chart units.  Abbreviation for the
`TruncExpCech` subgroup at the two restriction maps, so that the statements below read. -/
noncomputable abbrev twoChartCoboundaryUnits (V : Bool → X.Opens) :
    Subgroup Γ(X, V false ⊓ V true)ˣ :=
  TruncExpCech.cechCoboundaryUnits
    (X.resHom (inf_le_left : V false ⊓ V true ≤ V false))
    (X.resHom (inf_le_right : V false ⊓ V true ≤ V true))

/-- **THE CRITERION**: on a two-chart cover whose overlap units are *all* coboundaries, a Picard
class trivial on both charts is trivial.

Composite of the two landed halves of the two-chart comparison: surjectivity presents the class
as `twoChartClassHom` of an overlap unit, and the kernel description kills it because that unit
is a coboundary by hypothesis.

Completely general in `X`: no affineness, no curve, no field, no dual numbers.  The content is
that `hcob` is a statement about the unit groups of three rings — so a consumer computes
`Pic` on a two-chart cover by computing units, with no cohomology in sight. -/
theorem cechPic_eq_one_of_chartTrivial_of_overlapUnits_coboundary
    (sel : X → Bool) (hmem : ∀ x, x ∈ V (sel x)) (hsel : Function.Surjective sel)
    (hcob : ∀ u : Γ(X, V false ⊓ V true)ˣ, u ∈ twoChartCoboundaryUnits V)
    (L : X.CechPic) (hL : ∀ s : Bool, Scheme.CechPic.map (V s).ι L = 1) :
    L = 1 := by
  obtain ⟨u, hu⟩ := twoChartClassHom_surjOn_of_chartTrivial sel hmem L hL
  rw [← hu]
  exact (twoChartClassHom_eq_one_iff V sel hmem hsel u).mpr (hcob u)

/-- The criterion for a consumer holding two classes: chart-trivial classes form a subsingleton.

Note this is *not* `Subsingleton X.CechPic` — the chart-triviality hypothesis is on the classes,
not on the scheme, and a class nontrivial on a chart is untouched. -/
theorem subsingleton_chartTrivial_of_overlapUnits_coboundary
    (sel : X → Bool) (hmem : ∀ x, x ∈ V (sel x)) (hsel : Function.Surjective sel)
    (hcob : ∀ u : Γ(X, V false ⊓ V true)ˣ, u ∈ twoChartCoboundaryUnits V)
    {L M : X.CechPic}
    (hL : ∀ s : Bool, Scheme.CechPic.map (V s).ι L = 1)
    (hM : ∀ s : Bool, Scheme.CechPic.map (V s).ι M = 1) :
    L = M := by
  rw [cechPic_eq_one_of_chartTrivial_of_overlapUnits_coboundary sel hmem hsel hcob L hL,
    cechPic_eq_one_of_chartTrivial_of_overlapUnits_coboundary sel hmem hsel hcob M hM]

/-- The criterion with `hsel` discharged from non-affineness, which is how a curve consumer meets
it: a proper positive-dimensional scheme over a field is not affine, and
`surjective_selector_of_not_isAffine` turns that single fact into the selector surjectivity.

Takes the cover as an `AffineTwoCover` because that is the carrier the discharge lemma is stated
against. -/
theorem cechPic_eq_one_of_chartTrivial_of_overlapUnits_coboundary_of_not_isAffine
    {Y : Scheme.{u}} (D : Y.AffineTwoCover) (hY : ¬ IsAffine Y)
    (hcob : ∀ u : Γ(Y, D.boolFamily false ⊓ D.boolFamily true)ˣ,
      u ∈ twoChartCoboundaryUnits D.boolFamily)
    (L : Y.CechPic) (hL : ∀ s : Bool, Scheme.CechPic.map (D.boolFamily s).ι L = 1) :
    L = 1 :=
  cechPic_eq_one_of_chartTrivial_of_overlapUnits_coboundary D.selector D.selector_mem
    (D.surjective_selector_of_not_isAffine hY) hcob L hL

/-! ## The form with a payable hypothesis

The universal hypothesis `hcob` above is **false** at the case the representability route cares
about: for `ℙ¹` over a domain, `t` is an overlap unit and is not a coboundary
(`not_tUnit_mem_laurentCoboundaryUnits`, `Picard/LaurentTwoChartCoboundary.lean`) — which is just
`Pic(ℙ¹_A) = ℤ`.  So a consumer given only the criterion above would set out to prove something
untrue.

The repair is to constrain only the units that *present the class in question*, which is what
surjectivity hands over anyway.  Two things are worth saying about it explicitly, because the
obvious repair is a trap:

* the `↔` version — "`L = 1` iff some presenting unit is a coboundary" — is **vacuous**: its
  forward direction takes the presenting unit to be `1`, and the chart-triviality hypothesis is
  never consulted (measured: the unused-variable linter flags it).  So the useful form is the
  implication with a `∀` over presenting units, below, where both hypotheses are consumed;
* that form is *strictly weaker* than `hcob`, and demonstrably so: `hcob` implies it by ignoring
  the presentation equation (`forall_presenting_of_forall_coboundary`). -/

/-- **THE CRITERION WITH A PAYABLE HYPOTHESIS**: a chart-trivial class is trivial as soon as
*every unit presenting it* is a coboundary.

Both hypotheses are consumed — `hL` produces the presenting unit through surjectivity, and
`hpres` is applied to exactly that unit.  Unlike the universal form this is not refuted by
`ℙ¹`: there the presenting units of a *degree-zero* class are the exponent-zero Laurent units,
which are precisely the coboundaries (`mem_laurentCoboundaryUnits_iff`). -/
theorem cechPic_eq_one_of_forall_presenting_coboundary
    (sel : X → Bool) (hmem : ∀ x, x ∈ V (sel x)) (hsel : Function.Surjective sel)
    (L : X.CechPic) (hL : ∀ s : Bool, Scheme.CechPic.map (V s).ι L = 1)
    (hpres : ∀ u : Γ(X, V false ⊓ V true)ˣ,
      twoChartClassHom V sel hmem u = L → u ∈ twoChartCoboundaryUnits V) :
    L = 1 := by
  obtain ⟨u, hu⟩ := twoChartClassHom_surjOn_of_chartTrivial sel hmem L hL
  rw [← hu]
  exact (twoChartClassHom_eq_one_iff V sel hmem hsel u).mpr (hpres u hu)

/-- The universal hypothesis implies the presenting-unit one, by ignoring the presentation
equation.  Recorded so that "strictly weaker" is a proved relation rather than a reading of the
two statements — the weakening is what makes the hypothesis payable at `ℙ¹`. -/
theorem forall_presenting_of_forall_coboundary
    (sel : X → Bool) (hmem : ∀ x, x ∈ V (sel x))
    (hcob : ∀ u : Γ(X, V false ⊓ V true)ˣ, u ∈ twoChartCoboundaryUnits V)
    (L : X.CechPic) :
    ∀ u : Γ(X, V false ⊓ V true)ˣ,
      twoChartClassHom V sel hmem u = L → u ∈ twoChartCoboundaryUnits V :=
  fun u _ => hcob u

end Scheme

end AlgebraicGeometry
