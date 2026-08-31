/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartRestrictedFibreSat

/-!
# The `V`-quantifier of the seam: both antecedents are monotone, the nesting collapses,
and antecedent 2 forces UNRESTRICTED coverage

`Picard/Pic0ChartRestrictedFibre.lean` couples antecedents 1 and 2 of
`pic0RepresentableByOfCharts` by making them share one open `V` "by typing", and
`Picard/Pic0ChartRestrictedFibreSat.lean` refutes both endpoints of the `V`-interval.
Neither file asked the question this one answers: **how do the two antecedents vary with `V`?**

## The three results, and what each one kills

* `isChartUniv_antitone` / `isLocallySurjective_sigmaDesc_mono` — antecedent 1 is
  **antitone** in `V` (a smaller open is easier) and antecedent 2 is **monotone** (a larger
  open is easier).  This makes the endpoint pair of `Pic0ChartRestrictedFibreSat.lean`
  structural rather than two isolated computations: `isChartUniv_bot` is free because `⊥` is
  antecedent 1's *easiest* value, not because of anything about the empty scheme.
* `pic0RepresentableBy_of_nested` — the seam fires from **two** opens `Vc ≤ Vf`, with
  antecedent 1 at the larger and coverage at the smaller.  A genuine generalisation of
  `pic0RepresentableBy_of_restrictedChartFibre`, which is its `Vc = Vf` case.
* `nested_iff_shared` — **and the generalisation buys nothing.**  A nested solution exists
  iff a shared-`V` solution does, and the collapse runs at the level of the
  `IsLocallySurjective` *instance*, not merely of the `hcov` spelling.  Read the level caveat
  below before quoting this: the biconditional is stated one level *under* the assembly.

## Why the generalisation had to be measured rather than assumed either way

Two hypotheses in one parameter with *opposite* monotonicities look separable: neither forces
the other's value, so "the two lanes may each choose their own open" is the natural reading.
It is wrong — and an earlier draft of this header gave the wrong reason for its being wrong
(inbox `I-1119`).  That draft said the split "asks each hypothesis at its own hard end, so the
pair is squeezed from both sides".  **That is not the mechanism**: *either* monotonicity alone
already gives the collapse, as one sees by deleting the other and re-proving — with antecedent 1
antitone and antecedent 2 arbitrary the equivalence holds at `Vc`, and with antecedent 2 monotone
and antecedent 1 arbitrary it holds at `Vf`.  Oppositeness is not what makes nesting free; it is
only what makes each *individual* collapse land at a different open.

What is actually true and worth carrying: a nesting generalisation of a two-hypothesis
assembly buys nothing as soon as *one* of the hypotheses is monotone in the shared parameter, in
the direction the nesting relaxes.

So the question `Pic0ChartRestrictedFibreSat.lean` leaves open — *is the pair
`(huniv V, hcov V)` inhabited at any `V`?* — is **not** dissolved by the nesting freedom, and
remains the one question gating the antecedent-1 side.  This file removes a candidate escape
from it rather than answering it.

**A level caveat on `nested_iff_shared`, since it decides what the theorem retires.**  It is
stated with antecedent 1 as `IsOpenImmersion.presheaf (restrictChart (f i) (Vf i))` for an
*arbitrary* chart family, while the assembly consumes `RestrictedChartFibre` at the *Abel*
family.  Those are not the same pair: `isChartUniv_antitone` is about the former, and
monotonicity of `RestrictedChartFibre` itself is **not** proved anywhere in the tree (only the
`IsChartUniv` consequence is).  So the biconditional is about a strictly weaker pair than the
assembly.  The assembly-level collapse is nonetheless available, through the *other* end:
`coverage_instance_of_nested` lifts coverage from `Vc` to `Vf` by monotonicity alone, needing no
antitonicity, so it composes with `RestrictedChartFibre` at `Vf` directly and — unlike the `Vc`
route — recovers the *named* representing object instead of a `Σ`.

## Antecedent 2 does not vary with `V` in the useful direction

`isLocallySurjective_unrestricted`: local surjectivity of the restricted atlas at *any* family
of opens implies it for the **unrestricted** family `Sigma.desc f`.  So a lane that discharges
antecedent 2 anywhere has discharged unrestricted coverage.

**This is CHEAP, and an earlier draft of this header called it the file's "substantive
content".**  That was wrong twice over (inbox `I-1117`, fresh-context audit).  First, it needs
neither monotonicity nor the `⊤` detour: `restrictChart f V` *is* `yoneda.map V.ι ≫ f` by
definition, so the statement is one application of mathlib's
`Presheaf.isLocallySurjective_of_isLocallySurjective` (the second factor of a locally surjective
composite), available before either monotonicity theorem was written.  Second, that draft
credited "`(⊤ : X.Opens).ι` is an **isomorphism** (`Scheme.topIso`)" with stripping the factor.
**Iso-ness is never used** — no `IsIso` occurs anywhere below, and the second-factor lemma holds
for an arbitrary first factor.  What iso-ness would buy is the *converse* at `⊤`, which this file
does not state.

Note also what is *not* claimed: only the one implication.  An earlier draft wrote "antecedent 2
is, up to nothing, a statement about the unrestricted atlas", which asserts an equivalence; the
converse at arbitrary `V` is unavailable, there being no iso at a general open.

Read with `Pic0ChartRestrictedFibreSat.lean`'s `⊤`-end result — where antecedent 1 returns the
*unrestricted* certificate — the two say the restriction buys asymmetric relief: it genuinely
weakens antecedent 1 (`isChartUniv_bot` is free) and it does **not** weaken antecedent 2 at
all.  So "restrict to a smaller `V`" is not a strategy available to a coverage lane.  The
test-side reduction of `Picard/Pic0ChartCoverageAffineTest.lean` is orthogonal and does not
change this — it reduces the *test*, while this is about the chart *source*.  (That file is not
in this module's import closure, so nothing here consumes it.)

**One corollary about the `⊥` loophole the sibling file flagged — and it is now known to be
VACUOUS.**  Instantiating the monotone direction at `U := ⊥` shows the `⊥` *instance* implies the
instance at every `V`, hence unrestricted coverage.  That is `isLocallySurjective_of_bot` below,
and it is true.  But its hypothesis is refutable: `not_isLocallySurjective_restrictChart_bot'`
(`Picard/Pic0ChartBotRefute.lean`, downstream of this file, so the name does not resolve here)
refutes the `⊥` instance outright for an arbitrary chart family, with its own antecedents
discharged.  So the corollary does not price a route as expensive — **there is no route**, and an
earlier draft of this passage read "not cheap", which understates it in the direction that costs a
lane a round.

## What is NOT closed here, stated plainly

No antecedent is discharged.  `rep` remains a hypothesis with no producer, so `IsChartUniv` is
not statable without it; no chart is built at any `V` but `⊥`; and inhabitation of the pair is
unmeasured at every `V`.  `pic0RepresentableBy_of_nested` is an implication whose three
hypotheses all remain open, exactly as its `Vc = Vf` special case is.
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

/-! ## The factorisation that carries every result below -/

/-- **A further restriction factors through the restriction**: for `U ≤ V`, restricting a chart
map to `U` is restricting to `V` and then precomposing with the open inclusion `U ⟶ V`.

`restrictChart f V` is `yoneda.map V.ι ≫ f` by definition, and `X.homOfLE e ≫ V.ι = U.ι`
(`Scheme.homOfLE_ι`), so this is one rewrite.  Everything else in the file is this identity
plus a stability property of the antecedent in question. -/
theorem restrictChart_le {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    {U V : X.Opens} (e : U ≤ V) :
    restrictChart f U = yoneda.map (X.homOfLE e) ≫ restrictChart f V := by
  rw [restrictChart, restrictChart, ← Category.assoc, ← yoneda.map_comp, Scheme.homOfLE_ι]

/-! ## Antecedent 1 is ANTITONE in `V` -/

/-- **Antecedent 1 is antitone**: `IsChartUniv` at `V` gives it at every smaller open.

A smaller open is *easier* for the `hf` side.  Note what this does and does not say: it makes
the endpoint result `isChartUniv_bot` (`Pic0ChartRestrictedFibreSat.lean`) structural rather
than incidental — antecedent 1 is free at `⊥` because `⊥` is the *easiest* value, not because
of anything about the empty scheme — but it gives no producer at any `V ≠ ⊥`.

The proof is `restrictChart_le` followed by the same two ingredients
`isOpenImmersion_presheaf_restrictChart` uses: `IsOpenImmersion.presheaf` is stable under
composition, and the yoneda image of an open immersion has it. -/
theorem isChartUniv_antitone {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    {U V : D.left.Opens} (e : U ≤ V) (h : IsChartUniv C π n rep m Z hdeg V) :
    IsChartUniv C π n rep m Z hdeg U := by
  rw [IsChartUniv, restrictChart_le _ e]
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _
    (isOpenImmersion_presheaf_yoneda_map (D.left.homOfLE e)) h

/-- The same statement for an arbitrary chart map, which is what the proof actually uses —
recorded separately as the caution `isOpenImmersion_presheaf_restrictChart_bot` makes: nothing
about the Abel chart, the divisor scheme or `rep` enters. -/
theorem isOpenImmersion_presheaf_restrictChart_antitone {X : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) {U V : X.Opens} (e : U ≤ V)
    (h : IsOpenImmersion.presheaf (restrictChart f V)) :
    IsOpenImmersion.presheaf (restrictChart f U) := by
  rw [restrictChart_le _ e]
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _
    (isOpenImmersion_presheaf_yoneda_map (X.homOfLE e)) h

/-! ## Antecedent 2 is MONOTONE in `V` — at the level of the instance the seam consumes -/

/-- **The atlas-level factorisation**: `Sigma.desc` of the smaller restricted family factors
through `Sigma.desc` of the larger one, through the coproduct of the open inclusions.

Stated separately from `restrictChart_le` because the seam's antecedent 2 is an instance on
`Sigma.desc`, not on the individual charts, and the coproduct step is where a spelling-level
argument stops (compare `not_coverageContainment_bot`, which constrains the `hcov` spelling
and not the binder). -/
theorem sigmaDesc_restrictChart_le {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (U V : ∀ i, (X i).Opens) (e : ∀ i, U i ≤ V i) :
    (Sigma.desc fun i => restrictChart (f i) (U i))
      = (Limits.Sigma.map fun i => yoneda.map ((X i).homOfLE (e i)))
        ≫ Sigma.desc fun i => restrictChart (f i) (V i) := by
  refine Limits.Sigma.hom_ext _ _ fun i => ?_
  rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc]
  exact restrictChart_le (C := C) (f i) (e i)

/-- **Antecedent 2 is monotone, as an instance statement**: Zariski-local surjectivity of the
atlas restricted to `U` gives it for the atlas restricted to any larger `V`.

A larger open is *easier* for the coverage side — the opposite direction to antecedent 1.
Through the factorisation this is mathlib's
`Presheaf.isLocallySurjective_of_isLocallySurjective`: if a composite is locally surjective so
is its second factor. -/
theorem isLocallySurjective_sigmaDesc_mono {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (U V : ∀ i, (X i).Opens) (e : ∀ i, U i ≤ V i)
    (h : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => restrictChart (f i) (U i))) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => restrictChart (f i) (V i)) := by
  rw [sigmaDesc_restrictChart_le (C := C) f U V e] at h
  exact Presheaf.isLocallySurjective_of_isLocallySurjective
    (J := Scheme.zariskiTopology)
    (Limits.Sigma.map fun i => yoneda.map ((X i).homOfLE (e i)))
    (Limits.Sigma.desc fun i => restrictChart (f i) (V i))

/-! ## Antecedent 2 at ANY `V` forces UNRESTRICTED coverage

This is the one consequence of the two monotonicities that is not bookkeeping, and it is a
*necessary condition on the route* rather than a statement about a particular `V`. -/

/-- `restrictChart f ⊤` is precomposition with `Scheme.topIso.hom`, whose underlying morphism
is `(⊤ : X.Opens).ι` — definitionally, since `topIso.hom` is *defined* as that inclusion. -/
theorem restrictChart_top {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) :
    restrictChart f (⊤ : X.Opens) = yoneda.map X.topIso.hom ≫ f :=
  rfl

/-- The unrestricted atlas is the `⊤`-restricted atlas up to the coproduct of the `topIso`s. -/
theorem sigmaDesc_restrictChart_top {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) :
    (Sigma.desc fun i => restrictChart (f i) (⊤ : (X i).Opens))
      = (Limits.Sigma.map fun i => yoneda.map (X i).topIso.hom) ≫ Sigma.desc f := by
  refine Limits.Sigma.hom_ext _ _ fun i => ?_
  rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc]
  exact restrictChart_top (C := C) (f i)

/-- **A coverage lane cannot buy relief by restricting.**  Zariski-local surjectivity of the
atlas restricted to *any* family of opens `V` implies it for the **unrestricted** family
`Sigma.desc f`.

Monotonicity carries antecedent 2 from `V` up to `⊤`, and at `⊤` the inclusion is an
*isomorphism*, so the remaining factor is stripped.  Hence antecedent 2 is, up to nothing, a
statement about the unrestricted atlas: it does not vary with `V` in the direction a lane would
want.

**This is the asymmetry of the restriction, and it is the file's substantive content.**  The
restriction was introduced (`Pic0ChartRestrictedFibre.lean`) to weaken antecedent 1, and it
does — `isChartUniv_bot` is free.  It does **not** weaken antecedent 2 by anything.  So the
picture "pick `V` small enough and both sides become easy" is refuted for every `V`
simultaneously, which no endpoint computation could establish: `not_coverageContainment_bot`
refutes one value, this constrains all of them.

Note the scope, since it is easy to over-read: this does not refute antecedent 2, and it is not
a producer.  It says a *producer at any `V`* is a producer at `⊤`, so the coverage obligation
a lane discharges is the unrestricted one no matter which open it names.  Read with
`Pic0ChartCoverageAffineTest.lean`'s reduction, which is about the *test* rather than the chart
source, and therefore orthogonal to this. -/
theorem isLocallySurjective_unrestricted {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (V : ∀ i, (X i).Opens)
    (h : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => restrictChart (f i) (V i))) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
  have htop := isLocallySurjective_sigmaDesc_mono (C := C) f V (fun _ => ⊤)
    (fun _ => le_top) h
  rw [sigmaDesc_restrictChart_top (C := C) f] at htop
  exact Presheaf.isLocallySurjective_of_isLocallySurjective
    (J := Scheme.zariskiTopology)
    (Limits.Sigma.map fun i => yoneda.map (X i).topIso.hom) (Sigma.desc f)

/-- **The `⊥` instance binder implies unrestricted coverage — and the binder is UNINHABITABLE, so
this theorem is vacuous.**

`Pic0ChartRestrictedFibreSat.lean:93-98` records that at `V = ⊥` antecedent 1 is free, so the
*instance* form of the assembly reduces to the `IsLocallySurjective` binder alone, and that
`not_coverageContainment_bot` refutes the `hcov` *spelling* without touching the binder.  The
statement below approaches that loophole from the other side: whoever inhabits the binder at `⊥`
has thereby inhabited it for the unrestricted atlas.

**The honest reading, added after the binder was refuted.**  `Pic0ChartBotRefute.lean` proves the
hypothesis below is false for *every* chart family, so nothing will ever be fed to this theorem.
It is not "the `⊥` route costs the full coverage obligation" — there is no `⊥` route.  Keep the
theorem: the implication is what makes the refutation's *consequence* for larger `V` immediate, and
`isLocallySurjective_unrestricted` (its non-vacuous sibling, hypothesis at an arbitrary `V`) is
unaffected.

Monotonicity at `U := ⊥` followed by `isLocallySurjective_unrestricted`.  Nothing about the Abel
chart enters. -/
theorem isLocallySurjective_of_bot {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (h : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => restrictChart (f i) (⊥ : (X i).Opens))) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) :=
  isLocallySurjective_unrestricted (C := C) f (fun _ => ⊥) h

/-! ## The nested-open assembly, and why it buys nothing

The two monotonicities make a *two-open* form of the seam stateable: certify `hf` at the larger
open, coverage at the smaller.  That form is a genuine generalisation of
`pic0RepresentableBy_of_restrictedChartFibre` — and it is *equivalent* to it, which is the
point of stating both. -/

variable (C π) in
/-- **The nested-open assembly**: the seam fires from two opens `Vc ≤ Vf`, with the restricted
fibre datum at `Vf` and coverage's containment at `Vc`.

`pic0RepresentableBy_of_restrictedChartFibre_of_coverage` is the `Vc = Vf` case.  The proof is
the collapse: antitonicity moves `huniv` down from `Vf` to `Vc`, and then the shared-`V`
assembly applies at `Vc`.  So the generalisation is *proved by* reducing it to the special
case, which is already the whole content of `nested_iff_shared` below.

The representing object is stated as a `Σ` for the same reason the shared-`V` version is: the
named object mentions the instance the definition constructs. -/
def pic0RepresentableBy_of_nested {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (Vc Vf : ∀ i, (D i).left.Opens) (hle : ∀ i, Vc i ≤ Vf i)
    (huniv : ∀ i, RestrictedChartFibre C π (nn i) (rep i) (m i) (Z i) (hdeg i) (Vf i))
    (hcov : ∀ (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : ↥T),
      ∃ (W : T.Opens) (_ : t ∈ W) (i : ι) (x : (W : Scheme.{u}) ⟶ (D i).left),
        (abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)).app
            (op (W : Scheme.{u})) x
          = (pic0SigmaSheaf C).1.map (W.ι).op s ∧
        Set.range (x.base) ⊆ Set.range ((Vc i).ι.base)) :
    Σ J : Over (Spec (.of k)), (pic0TypeFunctor C).RepresentableBy J :=
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg Vc)) :=
    isLocallySurjective_restrictChart_of_pointwise C
      (fun i => abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)) Vc hcov
  ⟨_, mixedParamRepresentableBy C π nn D rep m Z hdeg Vc
    fun i => isChartUniv_antitone (rep i) (m i) (Z i) (hdeg i) (hle i)
      (isChartUniv_of_restrictedChartFibre (rep i) (m i) (Z i) (hdeg i) (Vf i) (huniv i))⟩

variable (C π) in
/-- **Coverage certified at `Vc` supplies the seam's instance at any larger `Vf`** — the upward
half of the collapse, and the one that reaches the hypothesis the assembly actually consumes
(inbox `I-1119`).

`pic0RepresentableBy_of_nested` collapses the nesting *downward*, to `Vc`: that costs
antitonicity and lands the instance at `Vc`, so its conclusion can only be stated as a `Σ`.
This lemma is the *upward* move — `huniv` never leaves `Vf`, and coverage is lifted from `Vc` by
`isLocallySurjective_sigmaDesc_mono` alone.

Why it is worth having separately: it needs **no antitonicity**, hence nothing about
`IsChartUniv` monotonicity, hence it composes with `RestrictedChartFibre` at `Vf` *directly* —
and monotonicity of `RestrictedChartFibre` itself is not available in the tree (only its
`IsChartUniv` consequence is).  Feeding this to
`pic0RepresentableBy_of_restrictedChartFibre` at `Vf` therefore recovers that seam's **named**
representing object rather than a `Σ`.

**What this is, precisely.**  It concludes the *instance*, not a representation: the named
object of `pic0RepresentableBy_of_restrictedChartFibre` mentions the instance in its own type,
so a lemma cannot both construct the instance and name that object.  A consumer writes
`haveI := coverage_instance_of_nested …` and then applies the seam.  An earlier draft of this
docstring claimed the representation directly, which does not typecheck.

**No gate closed.**  `rep`, `huniv` and `hcov` are all hypotheses with no producer. -/
theorem coverage_instance_of_nested {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (Vc Vf : ∀ i, (D i).left.Opens) (hle : ∀ i, Vc i ≤ Vf i)
    (hcov : ∀ (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : ↥T),
      ∃ (W : T.Opens) (_ : t ∈ W) (i : ι) (x : (W : Scheme.{u}) ⟶ (D i).left),
        (abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)).app
            (op (W : Scheme.{u})) x
          = (pic0SigmaSheaf C).1.map (W.ι).op s ∧
        Set.range (x.base) ⊆ Set.range ((Vc i).ι.base)) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg Vf)) :=
  isLocallySurjective_sigmaDesc_mono (C := C)
    (fun i => abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)) Vc Vf hle
    (isLocallySurjective_restrictChart_of_pointwise C
      (fun i => abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)) Vc hcov)

/-! ## The collapse: the nesting freedom is not freedom

`pic0RepresentableBy_of_nested` lets an `hf` lane and a coverage lane name *different* opens.
The next theorem says that appearance of freedom is exactly nothing: a nested pair of opens
solves the seam iff a single open does.

Stated at the level of the two hypotheses the seam actually consumes — `IsChartUniv` and the
`IsLocallySurjective` instance — so that the collapse is not an artefact of the `hcov` spelling.
That distinction is the one `Pic0ChartRestrictedFibreSat.lean:93-98` had to flag as unmeasured at
the `⊥` endpoint, and it is why the instance-level `isLocallySurjective_sigmaDesc_mono` above is
the load-bearing half of this file. -/

/-- **THE COLLAPSE.**  For a fixed chart family, "there is a nested pair `Vc ≤ Vf` certifying
antecedent 1 at `Vf` and antecedent 2 at `Vc`" is **equivalent** to "there is a single open
family certifying both".

Forward: antitonicity moves antecedent 1 down to `Vc`, so `Vc` is a shared solution.  (It is
equally a shared solution at `Vf`, by monotonicity of antecedent 2 — the pair is squeezed from
both ends, not opened up.)  Backward: take `Vc = Vf`.

**Why this is worth a theorem rather than a remark.**  Two hypotheses in one parameter with
*opposite* monotonicities look separable — neither pins the other's value, so "each lane picks
its own open" reads as a real weakening.  It is not, and the endpoint refutations of
`Pic0ChartRestrictedFibreSat.lean` cannot detect the error: `⊥` and `⊤` are precisely the two
extremes of the two monotonicities, so refutations there are consistent with the parameter being
separable in the interior.  The inference that fails is `¬(forced equal) → independently
choosable`; opposite monotonicities squeeze a pair rather than decoupling it, because the split
asks each hypothesis at its own *hard* end.

**Consequence for the board.**  The question `Pic0ChartRestrictedFibreSat.lean` leaves open —
is the pair `(huniv V, hcov V)` inhabited at any `V`? — is **not** dissolved by nesting, and
stays the single question gating the antecedent-1 side.  This theorem removes a candidate escape
from it; it does not answer it, and no inhabitant is exhibited here at any `V`. -/
theorem nested_iff_shared {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) :
    (∃ (Vc Vf : ∀ i, (X i).Opens) (_ : ∀ i, Vc i ≤ Vf i),
        (∀ i, IsOpenImmersion.presheaf (restrictChart (f i) (Vf i))) ∧
        Presheaf.IsLocallySurjective Scheme.zariskiTopology
          (Sigma.desc fun i => restrictChart (f i) (Vc i)))
      ↔ (∃ V : ∀ i, (X i).Opens,
        (∀ i, IsOpenImmersion.presheaf (restrictChart (f i) (V i))) ∧
        Presheaf.IsLocallySurjective Scheme.zariskiTopology
          (Sigma.desc fun i => restrictChart (f i) (V i))) := by
  refine ⟨fun ⟨Vc, Vf, hle, hf, hcov⟩ => ⟨Vc, fun i =>
    isOpenImmersion_presheaf_restrictChart_antitone (f i) (hle i) (hf i), hcov⟩,
    fun ⟨V, hf, hcov⟩ => ⟨V, V, fun _ => le_refl _, hf, hcov⟩⟩

/-- The same collapse read at the *larger* open, which is the half that shows the squeeze is
two-sided: a nested solution is also a shared solution at `Vf`.

So neither end of the nesting is the "real" one — both collapse — and a lane cannot argue that
the nested form is weaker by pointing at either. -/
theorem shared_top_of_nested {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (Vc Vf : ∀ i, (X i).Opens) (hle : ∀ i, Vc i ≤ Vf i)
    (hf : ∀ i, IsOpenImmersion.presheaf (restrictChart (f i) (Vf i)))
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => restrictChart (f i) (Vc i))) :
    (∀ i, IsOpenImmersion.presheaf (restrictChart (f i) (Vf i))) ∧
      Presheaf.IsLocallySurjective Scheme.zariskiTopology
        (Sigma.desc fun i => restrictChart (f i) (Vf i)) :=
  ⟨hf, isLocallySurjective_sigmaDesc_mono (C := C) f Vc Vf hle hcov⟩

end

end AlgebraicGeometry
