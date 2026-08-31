/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartRestrictedFibreSat

/-!
# Coverage at a PROPER `V` forces non-injectivity — so the `abel-noninj` fork is not a
question about the carve

`Picard/Pic0ChartRestrictedFibreSat.lean` refutes both endpoints of the `V`-interval of
`pic0RepresentableByOfCharts` and leaves one question: *is the pair (`huniv V`, `hcov V`)
inhabited at any `V`?*  Its `⊤`-end refutation
(`not_restrictedChartFibre_top_of_not_injective`) is **conditional** on the Abel chart failing
to be injective — the `abel-noninj` fork, which three file headers assert and no declaration
proves.  That row prices the fork as a question about the *carve*: does `DivScheme g` contain
points where `H¹` fails to vanish?

**The fork is also answered from the other side, by coverage, with no geometry at all.**  This
file proves it.

## The argument, and it has no divisor content

Let `f : yoneda.obj X ⟶ pic0SigmaSheaf C` be *any* map of big-site presheaves and `V ⊆ X` an
open with `V ≠ ⊤`.  Suppose the restricted family `restrictChart f V` satisfies
`PointwiseCoverage` (`Picard/Pic0ChartAtlasCoupling.lean`) — the datum antecedent 2 is
reduced to.  Instantiate coverage at

* the test `X` itself,
* the *tautological* section `f.app (op X) (𝟙 X)`,
* a point `t ∈ X \ V`, which exists because `V ≠ ⊤`.

Coverage returns an open `W ∋ t` and a point `x : ↑W ⟶ ↑V` whose restricted chart value is the
tautological section restricted to `W`.  Unfolding `restrictChart` (which is `rfl`) and the
naturality of `f` at `W.ι`, that equation reads

```
f.app (op ↑W) (x ≫ V.ι) = f.app (op ↑W) (W.ι)
```

and the two arguments are **different**: at the point `t` the left one lands inside `V` and the
right one is `t ∉ V`.  So `f.app (op ↑W)` is not injective.

Two things are worth noting about what that proof does *not* use.  It never looks at the
divisor scheme, the chart index, the twist, `rep`, or `pic⁰` — only that the coverage witness
factors through `V` while the tautological section does not.  And it is the *same* mechanism as
`not_coverageContainment_bot` (`Pic0ChartRestrictedFibreSat.lean`) pushed from `⊥` to an
arbitrary proper open: there the containment was refuted outright because `⊥` has no points;
here it is not refuted, it *costs* non-injectivity.

## What this decides, stated as a dichotomy

For a **one-chart** atlas, exactly one of the following holds:

* the Abel chart is non-injective on some test — the fork's negative branch.  Then `V = ⊤` is
  dead (`not_restrictedChartFibre_top_of_not_injective`) and, by
  `restrictedChartFibre_top_iff`, `IsChartLocusFibre` is dead with it;
* the Abel chart is injective on every test — the fork's positive branch, which the
  `abel-noninj` row's re-pricing (2) argues for at `n = g`.  Then coverage **fails at every
  proper `V`** (`not_pointwiseCoverage_of_injective_of_ne_top`), and coverage also fails at `⊥`
  (`not_coverageContainment_bot`).  **AND `⊤` DIES TOO**, which an earlier version of this
  paragraph got wrong in its own favour by saying "the only `V` at which the seam can close is
  `⊤`": the only thing keeping `⊤` alive is
  `not_restrictedChartFibre_top_of_not_injective`, which *consumes* the negative branch.  So
  under injectivity the seam is unsatisfiable at **every** `V` — a sharper conclusion than the
  dichotomy was claiming (audit `I-1378`).

So the fork and the `V`-interval are one question, not two: a lane cannot pick the restriction
repair and stay agnostic about the fork.

**THE PRECISE LOGICAL FORM, because an earlier version of this paragraph said "*equivalent*" and
that is REFUTED** (audit `I-1379`).  Write `N` for the fork's negative branch and `Q` for
`chart-restrict`'s conclusion "any working `V` is a proper intermediate open".  What holds is
`N → Q`, one direction.  `Q → N` does **not** follow from the three landed facts: `Works ≡ False`
satisfies all of them, satisfies `Q` vacuously, and has `N` false.  It needs the extra premise
`∃ V, Works V` — and `Pic0ChartRestrictedFibreSat.lean`'s own §"CORRECTED FRAMING" says that
premise has never been measured at any `V`.  So the honest claim is: `Q` is *implied by* the
fork's negative branch, and would be equivalent to it given an inhabitant of the seam that
nobody has.  Quoting the equivalence without that premise is the "two refutations are not an
inhabitation" error this seam has already made once.

## The honest limits, stated rather than left for a reviewer

* **Nothing here is discharged.**  `PointwiseCoverage` at a proper `V` is a hypothesis with no
  producer — it is exactly the open question `chart-restrict` names — and so is its negation.
  Every theorem below is an implication between two open propositions.  What is new is that
  they are *linked*.
* **THE ANTECEDENT IS STRONGER THAN DAT-B COVERAGE, and that is the live vacuity risk here**
  (audit `I-1377`).  The hypothesis is coverage by a **single** chart (`ι = PUnit`).  The landed
  converse `pointwise_of_pointwise_restrictChart` (`Pic0ChartAtlasCoupling.lean`) turns it into
  *unrestricted* coverage by that one chart, and thence into the local-surjectivity instance for
  a one-chart atlas — which two of this project's own files say should not hold:
  `Pic0ChartCoveragePointwise.lean` ("nothing forces one index to work at every point") and
  `Pic0ChartCoverageIndexSlack.lean` (the atlas "may be indexed by `m`" precisely so different
  points can use different charts).  So the hypothesis may well be refutable, in which case
  these theorems are true with an antecedent nothing satisfies.  That does **not** damage the
  dichotomy — it is a statement about one-chart atlases either way — but a lane must not read
  "coverage at a proper `V`" here as DAT-B's coverage.  The multi-index version of the argument
  is open; see the next bullet for why it does not go through as written.
* **The argument is per-chart, and a multi-index atlas can evade it.**  Coverage at a general
  family returns *some* index `i`, not the index whose tautological section was tested; if
  `i ≠ i₀` the two chart values live on different sources and no non-injectivity of a single
  map follows.  So the dichotomy above is for a one-chart atlas — which is what
  `Pic0AtlasFromDivRep.lean` builds and what `IsChartUniv`, `RestrictedChartFibre` and
  `restrictedChartFibre_top_iff` are all stated for — and **not** for `mixedParamChart` at
  arbitrary `ι`.  The multi-index case is open and is *not* claimed here.
* **The conclusion is not free**, and the check for that has to satisfy the theorem's *own*
  binders.  `specSecMap_injective` exhibits a map into the Σ-sheaf that is injective on every
  test — the one named by the tautological section `⟨𝟙 (Spec k), 1⟩` — **out of a source that
  has a proper open** (`bot_ne_top_specObj`).  So `(f, V)` with `V ≠ ⊤` exists at which the
  conclusion fails, hence the theorem is a constraint on the pair rather than a fact about the
  sheaf, and composing with `not_pointwiseCoverage_of_injective_of_ne_top` refutes coverage
  there outright.

  **AN EARLIER VERSION OF THIS BULLET NAMED THE WRONG WITNESS, and the correction is the
  lesson** (audit `I-1377`/`I-1380`).  It cited `restrictChart f ⊥`, injective by
  `isOpenImmersion_presheaf_restrictChart_bot`.  That is true and **useless here** on two
  counts: the source `↥(⊥ : X.Opens)` has a subsingleton open lattice, so it admits no
  `V ≠ ⊤` and the theorem cannot be instantiated at it at all; and every map out of
  `yoneda.obj ↥⊥` is injective on every test for free, since that presheaf is
  subsingleton-valued — so the cited route through the open-immersion criterion was doing no
  work either.  A non-vacuity witness must live where the theorem quantifies.

## Main declarations

* `AlgebraicGeometry.chart_map_ι_apply` — naturality of a chart map at an opens inclusion,
  elementwise, named because three proofs below use it.
* `AlgebraicGeometry.not_injective_of_pointwiseCoverage_of_ne_top` — **the step**: coverage for
  the family restricted to a proper `V` gives a test on which the *unrestricted* map fails to
  be injective.  Arbitrary presheaf map; no divisor content.
* `AlgebraicGeometry.not_pointwiseCoverage_of_injective_of_ne_top` — the contrapositive, which
  is the form the fork's positive branch reads: injectivity confines coverage to `V = ⊤`.
* `AlgebraicGeometry.not_restrictedChartFibre_top_of_pointwiseCoverage_of_ne_top` and
  `AlgebraicGeometry.not_isChartLocusFibre_of_pointwiseCoverage_of_ne_top` — the compositions
  at the Abel chart: coverage at a proper `V` kills the `⊤` end and the old route with it.
* `AlgebraicGeometry.exists_injective_into_pic0Sigma` — the non-vacuity check.
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

/-! ## The naturality step, named -/

/-- **A chart map read at an opens inclusion.**

`f.app` at the open `W` applied to `W.ι ≫ u` is the restriction along `W.ι` of `f.app` at the
whole scheme applied to `u`.  This is `NatTrans.naturality_apply` at `(W.ι).op`, with the
`yoneda`-side map being precomposition.

Named rather than inlined because the `yoneda`-side unfolding is the only thing that has to be
got right: an attempt to use the Σ-sheaf's own restriction on the wrong side does not typecheck.
(An earlier version said "all three refutations below consume it".  **One** does — the others
reach it only transitively through the main theorem.) -/
theorem chart_map_ι_apply {X : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) (W : X.Opens) (u : X ⟶ X) :
    (pic0SigmaSheaf C).1.map (W.ι).op (f.app (op X) u)
      = f.app (op (W : Scheme.{u})) (W.ι ≫ u) :=
  (NatTrans.naturality_apply f (W.ι).op u).symm

/-! ## The step -/

variable (C) in
/-- **COVERAGE AT A PROPER `V` FORCES NON-INJECTIVITY OF THE UNRESTRICTED MAP.**

For an arbitrary map of big-site presheaves `f : yoneda.obj X ⟶ pic0SigmaSheaf C` and an open
`V ≠ ⊤`: if the one-chart family `restrictChart f V` satisfies `PointwiseCoverage`, then `f`
fails to be injective on some test.

The proof is the tautological section at the test `X`, read at a point outside `V`; see the
module docstring.  No divisor, no chart index, no `rep`, no `pic⁰` fact is used — only that a
coverage witness factors through `V` and the identity does not.

Note the hypothesis is coverage for the family *restricted to `V`*, which is what the seam
consumes at a restricted atlas (`Pic0ChartAtlasCoupling.liftPointwiseToOpens`), not
unrestricted coverage. -/
theorem not_injective_of_pointwiseCoverage_of_ne_top
    {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) (V : X.Opens)
    (hV : V ≠ ⊤)
    (hcov : PointwiseCoverage C (fun _ : PUnit.{u+1} => restrictChart f V)) :
    ∃ T : Scheme.{u}ᵒᵖ, ¬ Function.Injective (f.app T) := by
  -- `V ≠ ⊤` gives a point of `X` outside `V`
  obtain ⟨t, htV⟩ : ∃ t : X, t ∉ V := by
    by_contra h
    exact hV (top_le_iff.mp fun t _ => not_not.mp fun ht => h ⟨t, ht⟩)
  obtain ⟨W, htW, iu, x, hx⟩ := hcov X (f.app (op X) (𝟙 X)) t
  refine ⟨op (W : Scheme.{u}), fun hinj => ?_⟩
  -- the coverage witness and the identity have the same chart value over `W`
  have hxv : f.app (op (W : Scheme.{u})) (x ≫ V.ι)
      = f.app (op (W : Scheme.{u})) (W.ι ≫ 𝟙 X) := by
    rw [← chart_map_ι_apply f W (𝟙 X)]
    exact hx
  have heq := hinj hxv
  -- but they disagree at `t`: the witness lands in `V` and `t` does not
  have hpt : ((x ≫ V.ι).base ⟨t, htW⟩ : X) = ((W.ι ≫ 𝟙 X).base ⟨t, htW⟩ : X) := by
    rw [heq]
  have hmem : ((x ≫ V.ι).base ⟨t, htW⟩ : X) ∈ V := (x.base ⟨t, htW⟩).2
  rw [hpt] at hmem
  exact htV (by simpa using hmem)

variable (C) in
/-- **The contrapositive: injectivity confines coverage to `V = ⊤`.**

If a chart map is injective on every test, then no proper open supports coverage for its
restriction.  Read with `not_coverageContainment_bot` — which refutes the containment at `⊥` —
this says an injective chart leaves exactly one candidate value of `V`, namely `⊤`.

This is the form the fork's *positive* branch reads, and the reason this file's finding is not
one-sided: the branch that the `abel-noninj` row argues for (uniqueness of the degree-`g`
representative, hence injectivity) is the branch that kills the restriction apparatus. -/
theorem not_pointwiseCoverage_of_injective_of_ne_top
    {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) (V : X.Opens)
    (hV : V ≠ ⊤) (hinj : ∀ T : Scheme.{u}ᵒᵖ, Function.Injective (f.app T)) :
    ¬ PointwiseCoverage C (fun _ : PUnit.{u+1} => restrictChart f V) := by
  intro hcov
  obtain ⟨T, hT⟩ := not_injective_of_pointwiseCoverage_of_ne_top C f V hV hcov
  exact hT (hinj T)

/-! ## The compositions at the Abel chart

The two theorems above are about an arbitrary presheaf map.  Instantiated at `abelSigmaChart`
they close the `⊤` end of the `V`-interval *unconditionally on the fork*, which is what makes
the fork and the interval one question. -/

variable (C π n) in
/-- **Coverage at a proper `V` kills the `⊤` end.**

`not_restrictedChartFibre_top_of_not_injective` (`Pic0ChartRestrictedFibreSat.lean`) needs
a test on which the Abel chart is not injective, and says so conditionally — the `abel-noninj`
fork.  Coverage at any proper `V` *supplies* that test, by
`not_injective_of_pointwiseCoverage_of_ne_top`.

So a lane holding coverage at a proper `V` does not have to decide the fork to know that
`V = ⊤` is dead: coverage decides it. -/
theorem not_restrictedChartFibre_top_of_pointwiseCoverage_of_ne_top
    {D : Over (Spec (.of k))} (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) (hV : V ≠ ⊤)
    (hcov : PointwiseCoverage C
      (fun _ : PUnit.{u+1} => restrictChart (abelSigmaChart C π n rep m Z hdeg) V)) :
    ¬ RestrictedChartFibre C π n rep m Z hdeg ⊤ := by
  obtain ⟨T, hT⟩ := not_injective_of_pointwiseCoverage_of_ne_top C
    (abelSigmaChart C π n rep m Z hdeg) V hV hcov
  exact not_restrictedChartFibre_top_of_not_injective rep m Z hdeg T hT

variable (C π n) in
/-- **Coverage at a proper `V` kills `IsChartLocusFibre`** — the old route to antecedent 1.

Composite of the previous theorem with `restrictedChartFibre_top_iff`
(`Pic0ChartRestrictedFibreSat.lean`), which identifies `IsChartLocusFibre` with the `⊤`
instance of the restricted class.

This is the sharp statement of the finding: the guard
`not_isChartLocusFibre_of_not_injective` was waiting on two divisors in one linear system, and
coverage at a proper open produces the same conclusion with no divisor at all. -/
theorem not_isChartLocusFibre_of_pointwiseCoverage_of_ne_top
    {D : Over (Spec (.of k))} (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) (hV : V ≠ ⊤)
    (hcov : PointwiseCoverage C
      (fun _ : PUnit.{u+1} => restrictChart (abelSigmaChart C π n rep m Z hdeg) V)) :
    ¬ IsChartLocusFibre C π n rep m Z hdeg := fun h =>
  not_restrictedChartFibre_top_of_pointwiseCoverage_of_ne_top C π n rep m Z hdeg V hV hcov
    ((restrictedChartFibre_top_iff C π n rep m Z hdeg).mpr h)

/-! ## Non-vacuity: the conclusion is not free, at a pair the theorem quantifies over

`not_injective_of_pointwiseCoverage_of_ne_top` concludes "some test where `f` is not injective".
If that held for *every* `(f, V)` with `V ≠ ⊤`, the theorem would carry no information.

The witness has to satisfy **both** binders: `f` injective on every test, *and* a source with a
proper open.  The obvious candidate — `restrictChart f ⊥`, injective by the open-immersion
criterion — satisfies the first and **fails the second**, since `↥(⊥ : X.Opens)` has a
subsingleton open lattice and so admits no `V ≠ ⊤`.  (It is also injective for free, `yoneda.obj
↥⊥` being subsingleton-valued, so the criterion adds nothing there.)  The witness below is
`Spec k` with the tautological section, which has both. -/

variable (C) in
/-- **The tautological Σ-section over `Spec k`**: the identity structure morphism paired with the
identity class.  Degree-zero needs nothing about the curve.

Same construction as `Pic0ChartBotRefute.specSigmaSection`, which is not in this file's import
closure; recorded here rather than importing that file, since only the section is wanted and not
its `⊥` refutation. -/
def specSigmaSectionTaut :
    (pic0SigmaSheaf C).1.obj (op (Spec (CommRingCat.of k))) :=
  ⟨𝟙 _, 1⟩

/-- **`Spec k` has a proper open** — the binder the `⊥` witness could not supply.

`k` is a field, so `Spec k` has a point, so `⊥ ≠ ⊤` there. -/
theorem bot_ne_top_specObj : (⊥ : (Spec (CommRingCat.of k)).Opens) ≠ ⊤ := by
  intro h
  have hne : Nonempty (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  have hm : hne.some ∈ (⊥ : (Spec (CommRingCat.of k)).Opens) := by rw [h]; trivial
  exact hm

variable (C) in
/-- **THE NON-VACUITY WITNESS**: the map named by the tautological section is injective on every
test, and its source has a proper open.

Injectivity is one step: the Σ-component of the section's restriction along `u` is `u ≫ 𝟙 = u`
(`Over.sigmaExtension_map_fst`), so the map's first component recovers its own argument.

Composed with `not_pointwiseCoverage_of_injective_of_ne_top` and `bot_ne_top_specObj` this
*refutes* coverage at `⊥ ≠ ⊤` on this source — so the theorem's conclusion genuinely fails for
some pair it quantifies over, which is what non-vacuity here means. -/
theorem specSecMap_injective :
    ∀ T : Scheme.{u}ᵒᵖ,
      Function.Injective
        ((yonedaEquiv.symm (specSigmaSectionTaut C)).app T) := by
  intro T u v h
  have h1 : ((yonedaEquiv.symm (specSigmaSectionTaut C)).app T u).1
      = ((yonedaEquiv.symm (specSigmaSectionTaut C)).app T v).1 := by rw [h]
  have key : ∀ w : (yoneda.obj (Spec (CommRingCat.of k))).obj T,
      ((yonedaEquiv.symm (specSigmaSectionTaut C)).app T w).1 = w := by
    intro w
    show ((Over.sigmaExtension (Spec (CommRingCat.of k)) (pic0TypeFunctor C)).map
      (Quiver.Hom.op w) (specSigmaSectionTaut C)).1 = w
    rw [Over.sigmaExtension_map_fst]
    simp [specSigmaSectionTaut]
  rw [key u, key v] at h1
  exact h1

variable (C) in
/-- **Coverage is refuted outright at this witness** — the non-vacuity check in the form that
uses the theorem rather than merely accompanying it. -/
theorem not_pointwiseCoverage_specSecMap :
    ¬ PointwiseCoverage C (fun _ : PUnit.{u+1} =>
        restrictChart (yonedaEquiv.symm (specSigmaSectionTaut C))
          (⊥ : (Spec (CommRingCat.of k)).Opens)) :=
  not_pointwiseCoverage_of_injective_of_ne_top C _ _ bot_ne_top_specObj
    (specSecMap_injective C)

/-! ## The old, mis-aimed witness, kept with its defect named

Retained rather than deleted because a lane reading the audit trail should be able to see what
was wrong with it: it is true, and it is about a pair the theorem cannot be instantiated at. -/

variable (C) in
/-- **True but off-target**: `restrictChart f ⊥` is injective on every test.

This was this file's original non-vacuity check and it does not serve that purpose — see the
section header above and `I-1380`.  Kept because it is the shape a reader will reach for. -/
theorem injective_restrictChart_bot {X : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) :
    ∀ T : Scheme.{u}ᵒᵖ,
      Function.Injective ((restrictChart f (⊥ : X.Opens)).app T) :=
  fun T => injective_of_isOpenImmersion_presheaf
    (isOpenImmersion_presheaf_restrictChart_bot C f) T

end

end AlgebraicGeometry
