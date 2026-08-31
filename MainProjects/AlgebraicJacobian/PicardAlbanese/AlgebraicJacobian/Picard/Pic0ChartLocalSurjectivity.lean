/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartUnivReduce

/-!
# DAT-B B-6: the local-surjectivity half of the `(f, hf)` handoff

`pic0RepresentableByOfCharts` (`Picard/Pic0SigmaSheaf.lean:161`) needs two things beyond the
charts: the `hf` certificate (C9b, reduced in `Picard/Pic0ChartUnivReduce.lean`) and the
instance

```
[Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]
```

which is dat-b row B-6.  Three files carry that instance as a `variable`
(`JacobianDataCharts.lean:117`, `JacobianDataAbelSurj.lean:183`,
`JacobianDataAbelImage.lean:131`) and **nothing anywhere produces one**.  This file supplies
the producer, in the form that DAT-B's coverage statement can actually feed.

## What local surjectivity unfolds to, and why that matters here

Mathlib's `Presheaf.IsLocallySurjective J f` has a single field: for every object `T` and
every section `s` of the target at `T`, the *image sieve* of `s` — the sieve of maps
`g : T' ⟶ T` along which `s` pulls back into the image of `f` — is a covering sieve.

For the Zariski topology on schemes that is exactly the geometric statement dat-b row B-5
proves: **every degree-zero class on a test is, locally on that test, a chart value**.  So
B-6 is not a further geometric obligation on top of B-5 — it is B-5 phrased against
mathlib's sieve-theoretic interface, plus the bookkeeping that turns a family of charts into
`Sigma.desc`.

The bookkeeping is what this file provides, and it is not trivial: the section must be hit
by *some* chart of the family, and `Sigma.desc` must be shown to see it.  That is
`ChartsCoverLocally` below.

## The honest scope, stated up front

`ChartsCoverLocally` is the hypothesis, not a theorem.  Its content is B-5 and B-5's residue
is recorded on the dat-b roadmap row (the chart-parameter/threshold reconciliation).  What
this file establishes is that **nothing else** stands between B-5 and the instance the
producer needs — in particular no compatibility across charts, because `Sigma.desc` has
none to check.

## Main declarations

* `AlgebraicGeometry.ChartsCoverLocally` — the coverage hypothesis, stated exactly as the
  image sieve of `Sigma.desc` being covering, but spelled in terms of the individual charts
  so a producer never has to reason about the coproduct.
* `AlgebraicGeometry.isLocallySurjective_sigmaDesc` — **B-6**: that hypothesis gives the
  instance `pic0RepresentableByOfCharts` consumes.
* `AlgebraicGeometry.chartsCoverLocally_of_forall_surjective` — the degenerate sufficient
  condition (a chart that is surjective on points of every test already covers), recorded so
  the hypothesis is visibly *satisfiable* and not a disguised falsehood.
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

variable (C) in
/-- **The coverage hypothesis of DAT-B, stated per chart rather than on the coproduct.**

For every test `T` and every degree-zero class `s` on it, the maps into `T` along which `s`
becomes the value of *some* chart of the family form a Zariski covering sieve.

This is dat-b row B-5 verbatim — "every `pic⁰` point is Zariski-locally a chart point" — with
one deliberate design choice: the sieve is described through the individual `f i`, so a
producer discharges it by exhibiting, for each point of `T`, one open neighbourhood and one
index.  It never has to mention `Sigma.desc` or the coproduct of yoneda presheaves.  Turning
that into the coproduct form is `isLocallySurjective_sigmaDesc` below. -/
def ChartsCoverLocally {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) : Prop :=
  ∀ (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)),
    (⨆ i, Presheaf.imageSieve (f i) s) ∈ Scheme.zariskiTopology T

/-- **B-6**: the coverage hypothesis gives the local-surjectivity instance that
`pic0RepresentableByOfCharts` consumes.

The proof is the bookkeeping the row's name hides: the image sieve of `Sigma.desc f` contains
the image sieve of every individual `f i` — because a `T'`-point of `X i` gives a `T'`-point
of the coproduct through `Sigma.ι` — hence contains their supremum, and a sieve containing a
covering sieve is covering.

Note what is *not* needed: no compatibility between charts, and no injectivity.  `Sigma.desc`
imposes no coherence condition across indices (the observation `Pic0ChartAtlasParamFree.lean`
makes for `hf`, here again for coverage), so a heterogeneous atlas is admissible for B-6 on
exactly the same footing as a homogeneous one. -/
theorem isLocallySurjective_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (h : ChartsCoverLocally C f) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) where
  imageSieve_mem {T} s := by
    refine Scheme.zariskiTopology.superset_covering ?_ (h T s)
    refine iSup_le fun i => ?_
    rintro T' g ⟨t, ht⟩
    -- transport the witness along `Sigma.ι` and use `Sigma.ι_desc`
    refine ⟨(Sigma.ι (fun j => yoneda.obj (X j)) i).app (op T') t, ?_⟩
    rw [← ht, ← NatTrans.comp_app_apply, Sigma.ι_desc f i]

/-- **The hypothesis is satisfiable, checked rather than assumed.**

If one chart of the family is surjective on the points of every test, the coverage hypothesis
holds — its image sieve is already the maximal sieve.  This is the degenerate case (and not
the geometric situation: no single Abel chart is surjective on all tests), but it rules out
the failure mode where a `Prop`-valued hypothesis turns out to be unsatisfiable and the
"reduction" above is therefore vacuous.

Compare the two-sided check in `Pic0ChartUnivReduce.lean`: there the question was whether the
datum was too *weak*; here it is whether it is too *strong*. -/
theorem chartsCoverLocally_of_forall_surjective {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (i : ι)
    (hi : ∀ T : Scheme.{u}ᵒᵖ, Function.Surjective ((f i).app T)) :
    ChartsCoverLocally C f := by
  intro T s
  refine Scheme.zariskiTopology.superset_covering ?_
    (Scheme.zariskiTopology.top_mem T)
  intro T' g _
  exact le_iSup (fun j => Presheaf.imageSieve (f j) s) i g (hi (op T') _)

end

end AlgebraicGeometry
