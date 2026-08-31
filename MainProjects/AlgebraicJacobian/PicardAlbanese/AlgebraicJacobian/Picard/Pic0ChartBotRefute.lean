/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartVMonotone

/-!
# The `V = ⊥` endpoint of the seam, refuted at the INSTANCE level and unconditionally

`Picard/Pic0ChartRestrictedFibreSat.lean` records a loophole in the two-endpoint story
of the `V`-coupled seam.  At `V = ⊥` antecedent 1 is free (`isChartUniv_bot`, no hypothesis),
so the *instance* form of the assembly reduces to the `IsLocallySurjective` binder alone — and
`not_coverageContainment_bot` refutes only the `hcov` *spelling*, never the binder.  Several
board rows and file headers now assert "`⊥` is dead" for the atlas seam on the strength of an
inbox report of that refutation.  **This file is that refutation, as a theorem.**

## The obstruction is not about `pic⁰` at all

An audit of this file's first version found that its proof mentions nothing of its target: the
argument is that `⊥` has no points, and it goes through for an arbitrary presheaf of types on
`Scheme`.  That is `not_isLocallySurjective_restrictChart_bot_of_presheaf`, and everything else
here is an application of it.  Worth stating in that generality rather than only in the `pic⁰`
one, because it settles a question a lane might otherwise ask: no repair to `pic0SigmaSheaf` — a
different sheafification, a different Σ-extension, a finer site — can rescue the `⊥` endpoint,
since the refutation never looks at the presheaf.

## What was actually missing, and it was one mathlib lemma

The step that looked unavailable is the passage from a section of the coproduct presheaf
`⨿ i, yoneda.obj (X i)` to a component: the presheaf is a colimit in the functor category, so
a section at `T'` need not obviously come from one summand.  It does, by
`CategoryTheory.FunctorToTypes.jointly_surjective` — evaluation at `T'` preserves the colimit.
That lemma had **zero citations** in this project before this file.

## The three statements

* `isEmpty_of_hom_bot` — a scheme admitting a morphism to `(⊥ : X.Opens)` is empty.  Split
  out because it is the only geometric input, and it is not about charts.
* `not_isLocallySurjective_restrictChart_bot_of_presheaf` — **the refutation's true generality**,
  found by auditing the proof rather than the statement: it holds for an arbitrary presheaf of
  types on `Scheme`, with no `pic⁰`, no curve, no field and no sheaf condition.  The `pic⁰` version
  below is one application (`restrictChart` is the composite by definition).  This is what
  forecloses "some `pic⁰`-specific repair evades the `⊥` endpoint".
* `not_isLocallySurjective_restrictChart_bot` — **the refutation.**  For an *arbitrary* chart
  family `f`, given any test `T` carrying a point, the `⊥`-restricted atlas is not
  Zariski-locally surjective.  No divisor data, no chart data, no `rep`.
* `not_isLocallySurjective_restrictChart_bot'` — **the same statement with its own antecedents
  discharged.**  This is the form the board should quote.  See below.
* `not_chartsCoverLocally_bot` — the same refutation in the spelling a coverage producer
  actually attempts, since nobody proves the instance directly.
* `false_of_isLocallySurjective_bot` — **the finding.**  `isLocallySurjective_of_bot`
  (`Pic0ChartVMonotone.lean`) is *vacuous*: its hypothesis is precisely what is refuted here.
  Its conclusion — that a `⊥`-based route would give unrestricted coverage — is correct, but it
  does not shut a cheap route; there was never a route to shut.
* `isLocallySurjective_restrictChart_top` — the **control**, and the reason to believe the two
  bullets above are about `⊥` rather than about the seam.  See the paragraph on controls below.

**A binder note, since this file quantifies over more than the theorem it calls vacuous.**  The
declarations here carry four instances on `C` where `Pic0ChartVMonotone.lean` carries three (no
`GeometricallyReduced`, which `pic0SigmaSheaf` needs for the sheaf property).  So on its face this
file speaks about a narrower class of curves.  Measured, not assumed: both
`not_isLocallySurjective_restrictChart_bot` and the vacuity of `isLocallySurjective_of_bot` state
*and prove* inside the three-instance binder set, so the extra hypothesis is inherited from the
carrier and is not doing work in either statement.  (`Smooth.geometricallyReduced` supplies it
anyway.)

## Why the primed form exists, and it is the point of the file

The refutation as stated takes a test `T`, a section `s` on it, and a point `t : T` as
hypotheses.  An implication whose antecedents nobody has exhibited is not a refutation of
anything: it is consistent with `T` never existing.  `Spec k` is a test, it carries a point
(the prime `⊥` of a field), and the *identity* class is a section on it — so the antecedents
are inhabited by objects already in the tree, and the unconditional form follows.  That is
`not_isLocallySurjective_restrictChart_bot'`, whose statement quantifies over nothing but the
chart family.

Read against `isLocallySurjective_of_bot` (`Pic0ChartVMonotone.lean`), the relationship is
sharper than "closed from both sides": that theorem's hypothesis *is* what is refuted here, so
it is vacuous, and the `⊥` loophole was never open in the first place.  Recorded as
`false_of_isLocallySurjective_bot` below rather than only in prose, because "uninhabitable" and
"expensive" price a lane's round differently.

**Why this is a statement about `⊥` and not an accidental refutation of the seam at every `V`.**
An earlier draft of this paragraph offered as evidence that *the same proof script fails with `⊤`
in place of `⊥`*.  That is true and it measures nothing: `isEmpty_of_hom_bot` cannot apply at `⊤`
by its own statement, and would fail identically at every `V`, including any at which the
refutation happens to hold.  A control that could not have come out otherwise is not a control.

The real one is `isLocallySurjective_restrictChart_top` below: at `⊤` the restricted atlas
*inherits* coverage from the unrestricted one, because the inclusion is then an isomorphism.  So a
`⊤` analogue of the refutation would refute DAT-B for every chart family — the endpoint is
protected by the project's own target, not by a tactic breaking.

## A note on citations, so the next pass does not undo it

Cross-file references here name **declarations, not line numbers**, deliberately.  These modules
are edited by several lanes an hour and every docstring insertion above a declaration moves it: the
first version of this file cited three line anchors and all three were stale within the session,
rotted by *this file's own* earlier commit inserting prose above them.  One `grep -n` resolves a
name and nothing invalidates it.  Please do not "refresh" the names back into numbers.

## What is NOT closed here, stated plainly

**Two refutations at two bad values are not an inhabitation.**  `⊥` is dead and `⊤` returns
the unrestricted certificate (`Pic0ChartRestrictedFibreSat.lean`); the pair
(`huniv V`, coverage at `V`) still has **no measured inhabitant at any `V`**, and this file
does not improve that by one line.  What it does is remove the one value at which the seam
would have fired from nothing — which was a live hazard precisely because antecedent 1 is free
there.  No antecedent of `pic0RepresentableByOfCharts` is discharged anywhere below.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

noncomputable section

/-- **A scheme mapping to the empty open is empty.**  The bottom open of `X` has empty carrier,
and the underlying continuous map of a scheme morphism sends points to points.

Split out as the file's only geometric step, and it says nothing about charts: it is the reason
`⊥` kills coverage, and it would kill it for any presheaf whatsoever. -/
theorem isEmpty_of_hom_bot {X : Scheme.{u}} {Y : Scheme.{u}} (g : Y ⟶ (⊥ : X.Opens)) :
    IsEmpty Y :=
  g.base.hom.1.isEmpty

/-- **The refutation, generic in the presheaf** — no `pic⁰`, no curve, no field, no sheaf
condition.

An audit of the `pic⁰`-shaped version below found that its proof uses nothing whatsoever about
its target, so the honest home of the argument is here: *any* presheaf of types on `Scheme`
fails Zariski-local surjectivity along a `⊥`-restricted family, provided some test carries a
point and a section.

Stated separately because it forecloses a route rather than just tidying: a lane hoping that
some `pic⁰`-specific repair — a different sheafification, a different Σ-extension, a finer
site-theoretic massage of `pic0SigmaSheaf` — evades the `⊥` endpoint is hoping against a
statement in which `pic⁰` does not occur.  The obstruction is that `⊥` has no points, and that
survives every change to the presheaf. -/
theorem not_isLocallySurjective_restrictChart_bot_of_presheaf
    {F : Scheme.{u}ᵒᵖ ⥤ Type u} {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ F)
    (T : Scheme.{u}) (s : F.obj (op T)) (t : T) :
    ¬ Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => yoneda.map ((⊥ : (X i).Opens).ι) ≫ f i) := by
  intro hls
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.mp (hls.imageSieve_mem s)
  obtain ⟨j, y, -⟩ := 𝒰.exists_eq t
  obtain ⟨u, -⟩ := hle (𝒰.X j) (𝒰.f j) (Presieve.ofArrows.mk j)
  obtain ⟨i, x, -⟩ := CategoryTheory.FunctorToTypes.jointly_surjective'
    (Discrete.functor fun i => yoneda.obj ((⊥ : (X i).Opens) : Scheme.{u}))
    (op (𝒰.X j)) u
  exact (isEmpty_of_hom_bot (X := X i.as) x).elim y

/-- **The `⊥`-restricted atlas is NOT Zariski-locally surjective** — the instance-level
refutation, for an arbitrary chart family.

Given a test `T` with a point `t` and any section `s`, local surjectivity would make the image
sieve of `s` under `Sigma.desc` covering, hence would supply a Zariski cover of `T`; the cover
member through `t` is nonempty and carries a section of the coproduct presheaf lying in the
image, which `FunctorToTypes.jointly_surjective` resolves into a morphism to some
`(⊥ : (X i).Opens)` — making that member empty, contradicting the point it covers.

Note what does **not** enter: the class equation of the image sieve is discarded, so this is a
refutation of the *typing* at `⊥` and holds for any `f`.  No lane can escape it by changing
charts. -/
theorem not_isLocallySurjective_restrictChart_bot {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : T) :
    ¬ Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => restrictChart (f i) (⊥ : (X i).Opens)) :=
  not_isLocallySurjective_restrictChart_bot_of_presheaf f T s t

/-! ## Discharging the refutation's own antecedents

The theorem above is an implication: it needs a test `T`, a section on it, and a point of `T`.
An implication whose antecedents nobody exhibits refutes nothing — it is consistent with there
being no such `T`.  This section exhibits them, so the `⊥` endpoint is dead outright and not
merely dead-if-something-exists. -/

/-- **`Spec k` carries a point.**  `k` is a field, hence nontrivial, hence its prime spectrum is
nonempty; the carrier of `Spec (.of k)` *is* that spectrum.

Stated because it is the antecedent the refutation needs and no other file in the seam
exhibits it. -/
theorem nonempty_specObj_of_field : Nonempty (Spec (CommRingCat.of k)) :=
  inferInstanceAs (Nonempty (PrimeSpectrum k))

variable (C) in
/-- **A section of `pic0SigmaSheaf` over `Spec k`.**  A `Σ`-section at a test `T` is a pair: a
structure morphism `T ⟶ Spec k` and a degree-zero class on `Over.mk` of it.  Take the identity
morphism and the identity class — the trivial line bundle is always degree zero, so this needs
nothing about the curve.

The point of exhibiting it rather than quantifying over it: `pic0SigmaSheaf` could in principle
have been empty at every test, and then the refutation below would be about nothing. -/
def specSigmaSection : (pic0SigmaSheaf C).1.obj (op (Spec (CommRingCat.of k))) :=
  ⟨𝟙 _, 1⟩

/-- **The `⊥` endpoint is dead, unconditionally** — the form the board should quote.

`not_isLocallySurjective_restrictChart_bot` with all three of its antecedents discharged:
`Spec k` is the test, `specSigmaSection` the section, and `nonempty_specObj_of_field` the point.
Nothing is quantified but the chart family, and nothing about the curve, the divisor index or
`rep` enters at any step.

**What this settles and what it does not.**  Antecedent 1 of `pic0RepresentableByOfCharts` is
free at `⊥` with no hypothesis (`isChartUniv_bot`), so `⊥` was the one parameter value at which
the seam would have fired from nothing.  It cannot.  Combined with `isLocallySurjective_of_bot`
— inhabiting the binder at `⊥` would *give* unrestricted coverage — the endpoint is shut from
both directions.

It does **not** move the seam forward.  The pair (`huniv V`, coverage at `V`) has no measured
inhabitant at any `V`, and refuting two endpoints is not exhibiting an interior point. -/
theorem not_isLocallySurjective_restrictChart_bot' {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) :
    ¬ Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => restrictChart (f i) (⊥ : (X i).Opens)) :=
  not_isLocallySurjective_restrictChart_bot f _ (specSigmaSection C)
    nonempty_specObj_of_field.some

/-! ## The consequence in the coordinates a coverage lane works in

Nobody proves the instance directly: a coverage lane proves `ChartsCoverLocally`
(`Pic0ChartLocalSurjectivity.lean`) and lets `isLocallySurjective_sigmaDesc` convert.  So the
refutation is stated there too, otherwise a lane would have to notice the conversion itself. -/

/-- **`ChartsCoverLocally` is false at `⊥`** — the refutation in the spelling a producer
actually attempts.

`not_isLocallySurjective_restrictChart_bot'` composed with `isLocallySurjective_sigmaDesc`.
Compare `not_coverageContainment_bot` (`Pic0ChartRestrictedFibreSat.lean`), which refutes
the `hcov` conjunct of the *coupled assembly* — a different and weaker statement, since it
leaves the instance binder untouched.  This one closes the binder. -/
theorem not_chartsCoverLocally_bot {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) :
    ¬ ChartsCoverLocally C (fun i => restrictChart (f i) (⊥ : (X i).Opens)) := fun h =>
  not_isLocallySurjective_restrictChart_bot' f (isLocallySurjective_sigmaDesc _ h)

/-- **`isLocallySurjective_of_bot` is VACUOUS, and this is the file's finding for that lane.**

`isLocallySurjective_of_bot` (`Pic0ChartVMonotone.lean`) proves that inhabiting the coverage
instance at `⊥` yields
unrestricted coverage, and reads that as "the `⊥` route is not cheap".  The reading is right;
the mechanism is stronger than advertised.  Its hypothesis is *exactly* the proposition refuted
above, so the theorem is true with an uninhabitable antecedent — it does not shut a cheap route,
there was never a route.

Recorded as a theorem rather than a remark because "this binder cannot be inhabited" and "this
binder is expensive to inhabit" price a lane's round very differently, and only the first is
true.  Nothing here criticises that file's proof, which is correct. -/
theorem false_of_isLocallySurjective_bot {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (h : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => restrictChart (f i) (⊥ : (X i).Opens))) :
    False :=
  not_isLocallySurjective_restrictChart_bot' f h

/-- **The control for the refutation: at `⊤` the restricted atlas INHERITS coverage.**

The converse of `isLocallySurjective_unrestricted` (`Pic0ChartVMonotone.lean`) at `V = ⊤`,
and the reason the refutation above is a fact about `⊥` rather than about the seam.  `⊤`'s
inclusion is an isomorphism, so `sigmaDesc_restrictChart_top` exhibits the `⊤`-restricted atlas as
an iso followed by the unrestricted one, and local surjectivity transfers by instance search.

**Read as the control it is.**  A `⊤` analogue of `not_isLocallySurjective_restrictChart_bot'`
would, through this, refute DAT-B coverage for every chart family — i.e. refute the project's own
target.  So the `⊥` endpoint is protected by something that *could* have come out differently, and
did not.  Note the iso is used here and nowhere in `Pic0ChartVMonotone.lean`, whose header records
that its own `⊤` results never need it; this is the statement that does. -/
theorem isLocallySurjective_restrictChart_top {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (h : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => restrictChart (f i) (⊤ : (X i).Opens)) := by
  rw [sigmaDesc_restrictChart_top (C := C) f]
  infer_instance

end

end AlgebraicGeometry
