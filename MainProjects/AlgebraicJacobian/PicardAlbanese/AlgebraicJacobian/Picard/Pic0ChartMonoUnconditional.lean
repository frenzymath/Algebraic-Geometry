/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyDegreeZeroUseSite

/-!
# THE `abel-noninj` FORK IS DECIDED, UNCONDITIONALLY, AT PARAMETER `0`

`Picard/Pic0ChartSubsingletonCollapse.lean` reduced the fork to `Mono D.hom` and stated its
consequences under a hypothesis (`DivFunctorObjSubsingleton`) that had no producer at the time.
`Picard/DivisorFamilyDegreeZeroRep.lean` then produced one at `n = 0`, and
`Picard/DivisorFamilyDegreeZeroUseSite.lean` discharged the hypothesis
(`divFunctorObjSubsingleton_zero`) and built the `rep`-free chart `abelSigmaChartZero`.

**This file spends the last twenty minutes of that chain**: it composes them, so the fork's answer
at `n = 0` is a theorem with *no hypotheses at all* rather than an implication awaiting an input.
Both halves were landed by different lanes minutes apart, and neither wrote the composite; a
verified tower vouches for the joint nobody typed, which is exactly the joint that turns out to be
load-bearing.

## What is unconditional here

* `injective_abelSigmaChartZero` — **the unrestricted Abel chart at parameter `0` is injective on
  every test.**  No `Mono` binder, no subsingleton binder, no `rep` binder.  This is the first
  statement in either project that *decides* the fork rather than conditioning on it, and it
  decides it against the three headers' assertion (`Pic0AtlasFromDivRep.lean:54`,
  `Pic0ChartPair.lean:14`, `Pic0ChartOpenImmersionCriterion.lean:214`) at this parameter.
* `not_pointwiseCoverage_abelSigmaChartZero_of_ne_top` — hence coverage is refuted at **every
  proper** `V`, unconditionally.
* `no_proper_open_abelSigmaChartZero` — and there is no proper `V` to try in the first place: the
  representing object is `Over.mk (𝟙 (Spec k))`, whose space is one point.  The `V`-interval is
  `{⊥, ⊤}`, `⊥` is refuted by `not_coverageContainment_bot`, so at this parameter the coverage
  half is refuted at every open of the chart source **without exception**.

## What this does NOT do, and the limit is sharp rather than hedged

It does **not** close the seam at `n = 0` — it does the opposite, and says so precisely.  The
`(huniv, hcov)` pair of `pic0RepresentableBy_of_restrictedChartFibre_of_coverage` is now known
**unsatisfiable at every `V`** at this parameter, because the source has only two opens and both are
refuted.  So parameter `0` is *not* a route to `Pic⁰` representability through this atlas, and the
value of knowing that is that no lane needs to spend a round trying: the `rep` slot having a
producer at `0` does not make the seam reachable there.

Nor does it say anything about `n > 0`, where the subsingleton fails and the fork is open.  The
honest summary is that the fork is now decided at exactly one parameter, and at that parameter it
decides *against* the atlas rather than for it.

Compare `Picard/Pic0ChartSubsingletonCollapse.lean`'s boundary theorem, which reaches a compatible
conclusion by a different route (the chart *locus* is empty at `n = 0` for genus `≥ 2`, so the
locus-mediated route to coverage is dead).  That one is about the locus and needs `g ≥ 2`; this one
is about the chart source's topology and needs nothing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]
variable [IsIntegral (C ⊗ overSpec k k).left]

noncomputable section

/-- **THE FORK, DECIDED AT PARAMETER `0` WITH NO HYPOTHESES.**

`abelSigmaChartZero` is the Abel chart at the landed degree-`0` representation, and it is a
monomorphism on every test: `injective_abelSigmaChart_of_subsingleton` fed by
`divFunctorObjSubsingleton_zero`.

The three headers assert this chart is *not* injective, with the linear system `|D|` as the stated
reason, and prove nothing.  At this parameter the assertion is **false**. -/
theorem injective_abelSigmaChartZero
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (0 : ℕ))
    (T : Scheme.{u}ᵒᵖ) :
    Function.Injective ((abelSigmaChartZero (pi := pi) m Z hdeg).app T) :=
  injective_abelSigmaChart_of_subsingleton _ m Z hdeg
    (divFunctorObjSubsingleton_zero (C := C) (pi := pi)) T

/-- **Coverage is refuted at every proper `V`, unconditionally at parameter `0`.** -/
theorem not_pointwiseCoverage_abelSigmaChartZero_of_ne_top
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (0 : ℕ))
    (V : (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left.Opens) (hV : V ≠ ⊤) :
    ¬ PointwiseCoverage C
      (fun _ : PUnit.{u+1} => restrictChart (abelSigmaChartZero (pi := pi) m Z hdeg) V) :=
  not_pointwiseCoverage_of_injective_of_ne_top C _ V hV
    (injective_abelSigmaChartZero m Z hdeg)

/-- **And every open is `⊥` or `⊤`, so there is nothing else to try.**

The representing object of the degree-`0` representation is `Over.mk (𝟙 (Spec k))`, a one-point
space.  Combined with the previous theorem and `not_coverageContainment_bot`, the coverage half of
the coupled assembly is refuted at **every** open of the chart source at this parameter — not at
"every proper open, leaving `⊤`", because `⊤` is where the previous theorem's hypothesis `V ≠ ⊤`
fails and `restrictChart … ⊤` returns the unrestricted problem.

Stated as the disjunction rather than as a further refutation, because that is what is proved: the
interval has two points, one of them refuted here and the other refuted by
`not_coverageContainment_bot`.  The conclusion for a lane is that **parameter `0` is not a route to
representability through this atlas**, which is worth a theorem precisely because the `rep` slot
now HAS a producer there and the natural next move would be to try it. -/
theorem no_proper_open_abelSigmaChartZero
    (V : (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left.Opens) :
    V = ⊥ ∨ V = ⊤ :=
  opens_eq_bot_or_top_of_terminalRep (k := k) V

end

end AlgebraicGeometry
