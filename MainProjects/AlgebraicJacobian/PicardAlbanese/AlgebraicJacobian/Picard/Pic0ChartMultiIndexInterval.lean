/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverForcesNonInj

/-!
# The `V`-interval at a MULTI-INDEX atlas: the hypothesis the one-chart no-go was hiding

`Picard/Pic0ChartCoverForcesNonInj.lean` proves that coverage at a proper open `V ≠ ⊤` forces
the chart map to be non-injective on some test, and `Picard/Pic0ChartRestrictedFibreSat.lean`
refutes both endpoints of the `V`-interval.  **Every one of those statements is about a
one-chart atlas** (`ι := PUnit`), and the first file says so twice in its own limits section:

> the dichotomy above is for a one-chart atlas … and **not** for `mixedParamChart` at
> arbitrary `ι`.  The multi-index case is open and is *not* claimed here.

The reason it gives is correct: coverage returns *some* index `i`, not the index `i₀` whose
tautological section was tested, and if `i ≠ i₀` the two chart values live on different sources,
so no non-injectivity of a single map follows.

But the seam consumes `mixedParamChart` at arbitrary `ι`
(`pic0RepresentableBy_of_restrictedChartFibre`, `Pic0ChartRestrictedFibre.lean:259`).  So as the
tree stands, every "this `V` is dead" fact is about an atlas the assembly does not use, and
nothing says whether the interval is constrained at all for the real one.  **This file settles
that**, and the answer is that the no-go does *not* propagate — with the obstruction isolated as
a named hypothesis rather than left as a caveat.

## What the multi-index argument actually proves

Run the one-chart proof at a general family.  Coverage at the test `X i₀`, the tautological
section of `f i₀`, and a point `t ∉ V i₀` returns `W ∋ t`, an index `i`, and
`x : ↥W ⟶ ↥(V i)` with

```
(f i).app (op ↥W) (x ≫ (V i).ι)  =  (f i₀).app (op ↥W) (W.ι)
```

Two *different* points of the disjoint union of the chart sources therefore carry the same
value.  That is `¬ JointlyInjective f`, and it is all the argument gives: joint injectivity is
the conjunction of index separation and per-chart injectivity
(`jointlyInjective_iff`), and only the second half is what the one-chart theorem concluded.

## The premise that would restore the no-go, and the trap in stating it

Recovering the one-chart conclusion needs a premise ruling out the crossing case.  The obvious
one is "distinct indices never share a value", and **stating it over all tests makes it
vacuous**: `IndexSeparatedAll` is equivalent to `Subsingleton ι` for *every* family
(`indexSeparatedAll_iff_subsingleton`), because the Σ-sheaf is a subsingleton at an empty test
(`pic0Sigma_obj_subsingleton_of_isEmpty`) and each `X i` supplies one via its `⊥` open.  A
refutation of that condition is a fact about `ι`, not about the charts — which is why it is
landed here as a theorem, so nobody re-states it.

`IndexSeparated` is the repair: the same condition **at tests that have a point**.  That is the
form the coverage argument consumes anyway (the test it produces contains the point it started
from), and it is a genuine hypothesis about `f`: `not_indexSeparated_duplicated` refutes it at a
two-chart family whose every member *is* injective (`injective_duplicated`), on the test
`Spec k`, which has a point.  So per-chart injectivity — all the one-chart no-go concludes —
does not deliver it, and a glueing atlas, whose charts overlap by construction, is the shape
that evades the no-go.

The positive form is `not_injective_of_pointwiseCoverage_of_indexSeparated_of_ne_top`: coverage
at a proper `V i₀` *plus* index separation refutes injectivity of that chart.  Whether that
premise holds for the Abel atlas at `|ι| ≥ 2` is **not measured here**, so the theorems
conditioned on it are implications and not results about the seam; the second half of this file
is the route that does not need it.

## The honest limits

* **Nothing here discharges an antecedent.**  `PointwiseCoverage` at a proper `V` has no
  producer, and neither does its negation; every theorem below is an implication between open
  propositions, or a statement about a concrete witness family.  What changes is that the
  `V`-interval no-go is now known **not** to transmit to `mixedParamChart` through any premise
  stated here except a point-independent witness index, so a lane may aim antecedent 1 at a
  genuinely large `ι` without the landed refutations standing in its way.
* **This is not a claim that the multi-index seam is satisfiable.**  Refuting a refutation is
  not an inhabitation.  `(huniv V, hcov V)` remains unmeasured at every `V`, at every `ι`.
* **Everything is stated for an arbitrary family of big-site presheaf maps.**  No divisor
  scheme, chart index, twist, `rep` or `pic⁰` fact enters any statement or proof, exactly as in
  the one-chart file — so nothing here depends on which atlas a producer eventually builds.
* **`IndexSeparated` and `JointlyInjective` are restricted to NONEMPTY tests, and that is
  load-bearing rather than cosmetic.**  An earlier version of this file quantified them over all
  tests; a fresh-context audit found that version equivalent to `Subsingleton ι`, so its
  refutation was a fact about the index type and the headline read backwards.  The unrestricted
  form is retained as `IndexSeparatedAll` with `indexSeparatedAll_iff_subsingleton` as its
  epitaph.  Any further predicate on this Σ-sheaf should be probed at the empty test before its
  refutation is called a finding.
* **`IndexSeparated` IS satisfiable at two distinct indices** (`indexSeparated_satFam`,
  `not_subsingleton_ulift_bool`), so the repair is not a slower vacuity.  But the witness uses an
  **empty** chart source, which no producer would build, so satisfiability *at the Abel atlas*
  remains open and the theorems conditioned on index separation are implications rather than
  measurements of the seam.  `jointlyInjective_singleSpecFamily` inhabits `JointlyInjective` only
  at `PUnit`.

## Main declarations

* `AlgebraicGeometry.JointlyInjective` — the multi-index strengthening of per-test injectivity
  at nonempty tests: the chart sources inject *jointly* into the Σ-sheaf.
* `AlgebraicGeometry.IndexSeparated` — distinct indices never share a value on a test with a
  point.
* `AlgebraicGeometry.jointlyInjective_iff` — joint injectivity **is** index separation plus
  per-chart injectivity.  This is the decomposition that shows what the one-chart conclusion was.
* `AlgebraicGeometry.not_jointlyInjective_of_pointwiseCoverage_of_ne_top` — **the multi-index
  step**: coverage at a proper `V i₀` refutes joint injectivity, at arbitrary `ι`.
* `AlgebraicGeometry.not_injective_of_pointwiseCoverage_of_indexSeparated_of_ne_top` — the
  one-chart conclusion recovered at arbitrary `ι`, with the missing hypothesis explicit.
* `AlgebraicGeometry.indexSeparated_of_subsingleton` — why the one-chart theorem needed none.
* `AlgebraicGeometry.not_indexSeparated_duplicated` and
  `AlgebraicGeometry.injective_duplicated` — the negative answer: an all-injective family that
  is not index separated, so the added hypothesis is not free and the no-go does not propagate.
* `AlgebraicGeometry.exists_crossing_or_not_injective_of_pointwiseCoverage_of_ne_top` — the
  dichotomy in the form a coverage lane consumes: the witness crossed to another chart, or the
  tested chart is non-injective on the produced open.
* `AlgebraicGeometry.exists_crossing_or_not_injective_mixedParamChart` and
  `AlgebraicGeometry.not_pointwiseCoverage_mixedParamChart_of_jointlyInjective` — both
  instantiated at `mixedParamChart`, i.e. at the atlas
  `pic0RepresentableBy_of_restrictedChartFibre` actually takes, so the measurement is about the
  real assembly and not about a one-chart stand-in.
* `AlgebraicGeometry.jointlyInjective_singleSpecFamily` — the non-vacuity check: joint
  injectivity is inhabited, so the refutation above is about the *index* and not about the
  Σ-sheaf admitting no injective family at all.
* `AlgebraicGeometry.IndexSeparatedAll` and
  `AlgebraicGeometry.indexSeparatedAll_iff_subsingleton` — the naive index-separation condition
  and **its vacuity**: over all tests it *is* `Subsingleton ι`, for every family.  Landed so the
  trap is a theorem instead of a warning.
* `AlgebraicGeometry.indexSeparated_satFam` with `AlgebraicGeometry.not_subsingleton_ulift_bool` —
  the nonempty-test form **is** satisfiable at two distinct indices, so the repair above is not a
  slower vacuity.  Its witness uses an empty chart source, which bounds what it establishes.
* `AlgebraicGeometry.UniformCoverage` and
  `AlgebraicGeometry.not_injective_of_uniformCoverage_of_ne_top` — the half needing no unmeasured
  premise: the no-go propagates when the coverage witness index does not depend on the point.
  This is the landed one-chart theorem with `Subsingleton ι` replaced by a hypothesis naming the
  index; the multi-index escape is available exactly to atlases whose coverage genuinely varies
  its chart with the point.
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

/-! ## The two multi-index injectivity notions -/

variable (C) in
/-- **The naive index-separation condition, kept only to be refuted**: distinct indices never
share a value, quantified over *every* test including the empty one.

This is the shape a lane reaches for first, and it is **vacuous**:
`indexSeparatedAll_iff_subsingleton` proves it equivalent to `Subsingleton ι` for every family
whatsoever.  It mentions `f` and does not constrain it — the empty test alone decides it, because
the Σ-sheaf is a subsingleton there (`pic0Sigma_obj_subsingleton_of_isEmpty`) and each `X i`
supplies an empty test via its `⊥` open.

It is defined here rather than avoided so the refutation is a theorem in Lean and not a warning
in prose. -/
def IndexSeparatedAll {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) : Prop :=
  ∀ (S : Scheme.{u}ᵒᵖ) (i j : ι) (x : (yoneda.obj (X i)).obj S)
    (y : (yoneda.obj (X j)).obj S), (f i).app S x = (f j).app S y → i = j

variable (C) in
/-- **THE NAIVE CONDITION IS VACUOUS**: `IndexSeparatedAll f` is `Subsingleton ι`, for an
arbitrary family of maps into the Σ-sheaf.

Forward: instantiate at the empty test `↥(⊥ : (X i).Opens)`, where the unique maps out of the
initial object have equal value because the Σ-sheaf's value there is a subsingleton
(`pic0Sigma_obj_subsingleton_of_isEmpty`, `Pic0ChartRestrictedFibreSat.lean:160`).  Backward is
`Subsingleton.elim`.

So a "distinct indices never share a value" hypothesis quantified over all tests says nothing
about the chart maps at all, and refuting it at some family is not a fact about that family.
`IndexSeparated` below is the repair: the same condition at tests that have a point. -/
theorem indexSeparatedAll_iff_subsingleton {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) :
    IndexSeparatedAll C f ↔ Subsingleton ι := by
  constructor
  · intro h
    refine ⟨fun i j => ?_⟩
    refine h (op ((⊥ : (X i).Opens) : Scheme.{u})) i j
      (isInitialOfIsEmpty.to _) (isInitialOfIsEmpty.to _) ?_
    exact (pic0Sigma_obj_subsingleton_of_isEmpty (C := C)
      ((⊥ : (X i).Opens) : Scheme.{u})).elim _ _
  · intro _ _ i j _ _ _
    exact Subsingleton.elim i j

variable (C) in
/-- **Index separation, at tests that have a point**: two charts with different indices never
take the same value on a *nonempty* test.

The nonemptiness restriction is what makes this a hypothesis about `f` rather than about `ι`:
without it the condition collapses to `Subsingleton ι`
(`indexSeparatedAll_iff_subsingleton`), and with it an overlapping family genuinely refutes it
(`not_indexSeparated_duplicated`).  It is also exactly the form the coverage argument consumes,
since the test the argument produces contains the point it started from.

This is the half of joint injectivity that has no one-chart counterpart, and the content of the
gap between the one-chart no-go and the multi-index case. -/
def IndexSeparated {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) : Prop :=
  ∀ (S : Scheme.{u}) (_ : Nonempty S) (i j : ι) (x : (yoneda.obj (X i)).obj (op S))
    (y : (yoneda.obj (X j)).obj (op S)),
    (f i).app (op S) x = (f j).app (op S) y → i = j

variable (C) in
/-- **Joint injectivity of a chart family**: over every nonempty test, the disjoint union of the
chart sources injects into the Σ-sheaf.

For a one-element family this is per-test injectivity of the single chart map; for a general
family it is strictly stronger (`jointlyInjective_iff`, `not_indexSeparated_duplicated`), and it
is exactly the statement the multi-index coverage argument refutes.

Restricted to nonempty tests for the same reason as `IndexSeparated`: at an empty test the
Σ-sheaf is a subsingleton, so the unrestricted version would carry `Subsingleton ι` as a free
consequence and say nothing about `f`. -/
def JointlyInjective {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) : Prop :=
  ∀ (S : Scheme.{u}) (_ : Nonempty S) (i j : ι) (x : (yoneda.obj (X i)).obj (op S))
    (y : (yoneda.obj (X j)).obj (op S)),
    (f i).app (op S) x = (f j).app (op S) y →
      (⟨i, x⟩ : Σ i, (yoneda.obj (X i)).obj (op S)) = ⟨j, y⟩

/-- **Joint injectivity decomposes**: it is index separation together with per-chart
injectivity on every test.

Read left to right this says what the multi-index coverage argument's conclusion contains; read
right to left it says the one-chart theorem's conclusion (per-chart injectivity) is only *half*
of what would be needed to run the refutation at a general `ι`. -/
theorem jointlyInjective_iff {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) :
    JointlyInjective C f ↔
      IndexSeparated C f ∧ ∀ (i : ι) (S : Scheme.{u}) (_ : Nonempty S),
        Function.Injective ((f i).app (op S)) := by
  constructor
  · intro h
    refine ⟨fun S hS i j x y hxy => ?_, fun i S hS x y hxy => ?_⟩
    · exact congrArg Sigma.fst (h S hS i j x y hxy)
    · exact eq_of_heq (Sigma.mk.injEq .. ▸ h S hS i i x y hxy).2
  · rintro ⟨hsep, hinj⟩ S hS i j x y hxy
    obtain rfl : i = j := hsep S hS i j x y hxy
    exact congrArg (fun z => (⟨i, z⟩ : Σ i, (yoneda.obj (X i)).obj (op S))) (hinj i S hS hxy)

/-- Joint injectivity implies per-chart injectivity at nonempty tests — the direction a lane
will reach for. -/
theorem injective_of_jointlyInjective {ι : Type u} {X : ι → Scheme.{u}}
    {f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1} (h : JointlyInjective C f)
    (i : ι) (S : Scheme.{u}) (hS : Nonempty S) : Function.Injective ((f i).app (op S)) :=
  ((jointlyInjective_iff f).mp h).2 i S hS

/-- **Index separation is free for a one-chart atlas** — the reason
`not_injective_of_pointwiseCoverage_of_ne_top` needed no such hypothesis, and the reason its
proof cannot be read as covering the general case.

Note this is the *only* route to `IndexSeparated` that costs nothing: unlike the naive
`IndexSeparatedAll`, which is `Subsingleton ι` outright, the nonempty-test form is not implied
by a subsingleton-free hypothesis anywhere in this file. -/
theorem indexSeparated_of_subsingleton {ι : Type u} [Subsingleton ι] {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) :
    IndexSeparated C f :=
  fun _ _ _ _ _ _ _ => Subsingleton.elim _ _

/-! ## The multi-index step -/

variable (C) in
/-- **COVERAGE AT A PROPER `V i₀` REFUTES JOINT INJECTIVITY, AT ARBITRARY `ι`.**

The one-chart argument of `not_injective_of_pointwiseCoverage_of_ne_top`, run at a general
family: the tautological section of `f i₀`, tested at `X i₀` and read at a point outside
`V i₀`, is matched by a coverage witness that factors through `V i` for *some* index `i`.  Those
are two different points of the disjoint union of the chart sources with the same value.

The conclusion is about the family, not about `f i₀`: that is exactly the loss the one-chart
file predicted, made precise.  Nothing beyond the equation is used — no divisor, chart index,
twist, `rep`, or `pic⁰` fact. -/
theorem not_jointlyInjective_of_pointwiseCoverage_of_ne_top {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (V : ∀ i, (X i).Opens)
    (i₀ : ι) (hV : V i₀ ≠ ⊤)
    (hcov : PointwiseCoverage C (fun i => restrictChart (f i) (V i))) :
    ¬ JointlyInjective C f := by
  intro h
  obtain ⟨hsep, hinj⟩ := (jointlyInjective_iff f).mp h
  -- `V i₀ ≠ ⊤` gives a point of `X i₀` outside `V i₀`
  obtain ⟨t, htV⟩ : ∃ t : X i₀, t ∉ V i₀ := by
    by_contra hc
    exact hV (top_le_iff.mp fun t _ => not_not.mp fun ht => hc ⟨t, ht⟩)
  obtain ⟨W, htW, i, x, hx⟩ := hcov (X i₀) ((f i₀).app (op (X i₀)) (𝟙 (X i₀))) t
  -- the coverage witness at index `i` and the identity at index `i₀` agree over `W`
  have hxv : (f i).app (op (W : Scheme.{u})) (x ≫ (V i).ι)
      = (f i₀).app (op (W : Scheme.{u})) (W.ι ≫ 𝟙 (X i₀)) := by
    rw [← chart_map_ι_apply (f i₀) W (𝟙 (X i₀))]
    exact hx
  -- the produced test contains `t`, so it is nonempty: the hypotheses apply at it
  have hWne : Nonempty (W : Scheme.{u}) := ⟨⟨t, htW⟩⟩
  -- index separation collapses the two indices, and then per-chart injectivity the two points
  obtain rfl : i = i₀ := hsep _ hWne i i₀ _ _ hxv
  have heq := hinj i _ hWne hxv
  -- but they disagree at `t`: the witness lands in `V i` and `t` does not
  have hpt : ((x ≫ (V i).ι).base ⟨t, htW⟩ : X i)
      = ((W.ι ≫ 𝟙 (X i)).base ⟨t, htW⟩ : X i) := by rw [heq]
  have hmem : ((x ≫ (V i).ι).base ⟨t, htW⟩ : X i) ∈ V i := (x.base ⟨t, htW⟩).2
  rw [hpt] at hmem
  exact htV (by simpa using hmem)

variable (C) in
/-- **The one-chart conclusion, recovered at arbitrary `ι` with the missing hypothesis
explicit**: coverage at a proper `V i₀` together with index separation refutes injectivity of
the tested chart on some test.

At `ι := PUnit` the index-separation hypothesis is free (`indexSeparated_of_subsingleton`), so
this contains `not_injective_of_pointwiseCoverage_of_ne_top`; at a general `ι` it is a genuine
extra premise, and `not_indexSeparated_duplicated` shows it is not one an overlapping atlas
supplies. -/
theorem not_injective_of_pointwiseCoverage_of_indexSeparated_of_ne_top
    {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (V : ∀ i, (X i).Opens)
    (i₀ : ι) (hV : V i₀ ≠ ⊤) (hsep : IndexSeparated C f)
    (hcov : PointwiseCoverage C (fun i => restrictChart (f i) (V i))) :
    ∃ (i : ι) (S : Scheme.{u}) (_ : Nonempty S),
      ¬ Function.Injective ((f i).app (op S)) := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  exact not_jointlyInjective_of_pointwiseCoverage_of_ne_top C f V i₀ hV hcov
    ((jointlyInjective_iff f).mpr ⟨hsep, fun i S hS => hall i S hS⟩)

variable (C) in
/-- **THE DICHOTOMY, WITH ITS WITNESS EXHIBITED** — the form a coverage lane consumes.

Coverage at a proper `V i₀` produces an open `W` of `X i₀` and an index `i` such that a
`W`-point of `X i` and the inclusion `W.ι` carry the same class, and then **either** `i ≠ i₀`
(the coverage witness crossed to another chart) **or** `f i₀` is non-injective on `W`.

This is the actionable content of the multi-index measurement.  The one-chart theorem is the
case where the first alternative is unavailable, so it reads off the second; at a general `ι`
a lane supplying coverage must say which alternative its witness realises, and
`not_indexSeparated_duplicated` shows nothing in the shape of an overlapping atlas forces the
second.  Both alternatives are about the *family*, so neither can be dismissed by a fact about
one chart. -/
theorem exists_crossing_or_not_injective_of_pointwiseCoverage_of_ne_top
    {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (V : ∀ i, (X i).Opens)
    (i₀ : ι) (hV : V i₀ ≠ ⊤)
    (hcov : PointwiseCoverage C (fun i => restrictChart (f i) (V i))) :
    ∃ (W : (X i₀).Opens) (i : ι) (x : (W : Scheme.{u}) ⟶ X i),
      (f i).app (op (W : Scheme.{u})) x
          = (f i₀).app (op (W : Scheme.{u})) (W.ι) ∧
        (i ≠ i₀ ∨ ¬ Function.Injective ((f i₀).app (op (W : Scheme.{u})))) := by
  classical
  obtain ⟨t, htV⟩ : ∃ t : X i₀, t ∉ V i₀ := by
    by_contra hc
    exact hV (top_le_iff.mp fun t _ => not_not.mp fun ht => hc ⟨t, ht⟩)
  obtain ⟨W, htW, i, x, hx⟩ := hcov (X i₀) ((f i₀).app (op (X i₀)) (𝟙 (X i₀))) t
  have hxv : (f i).app (op (W : Scheme.{u})) (x ≫ (V i).ι)
      = (f i₀).app (op (W : Scheme.{u})) (W.ι) := by
    rw [show (W.ι : (W : Scheme.{u}) ⟶ X i₀) = W.ι ≫ 𝟙 (X i₀) from (Category.comp_id _).symm,
      ← chart_map_ι_apply (f i₀) W (𝟙 (X i₀))]
    exact hx
  refine ⟨W, i, x ≫ (V i).ι, hxv, ?_⟩
  by_cases hi : i = i₀
  · subst hi
    -- same index: the two points differ at `t`, so the chart is not injective there
    refine Or.inr fun hinj => ?_
    have heq := hinj hxv
    have hmem : ((x ≫ (V i).ι).base ⟨t, htW⟩ : X i) ∈ V i := (x.base ⟨t, htW⟩).2
    rw [show ((x ≫ (V i).ι).base ⟨t, htW⟩ : X i) = (W.ι.base ⟨t, htW⟩ : X i) from by rw [heq]]
      at hmem
    exact htV (by simpa using hmem)
  · exact Or.inl hi

/-- **The contrapositive, in the form the fork's positive branch reads**: an index-separated
family all of whose charts are injective admits coverage at no proper `V`. -/
theorem not_pointwiseCoverage_of_jointlyInjective_of_ne_top {ι : Type u} {X : ι → Scheme.{u}}
    {f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1} (V : ∀ i, (X i).Opens)
    (i₀ : ι) (hV : V i₀ ≠ ⊤) (hinj : JointlyInjective C f) :
    ¬ PointwiseCoverage C (fun i => restrictChart (f i) (V i)) :=
  fun hcov => not_jointlyInjective_of_pointwiseCoverage_of_ne_top C f V i₀ hV hcov hinj

/-! ## The composition at the atlas the seam actually consumes

Everything above is about an arbitrary family.  This section instantiates it at
`mixedParamChart`, which is the family `pic0RepresentableBy_of_restrictedChartFibre`
(`Pic0ChartRestrictedFibre.lean:259`) takes — so the statements are about the atlas the
assembly uses rather than about a one-chart stand-in. -/

variable {π : C.left ⟶ P1 k} [IsAffineHom π]

variable (C π) in
/-- **The dichotomy at `mixedParamChart`**, i.e. at the real atlas.

`mixedParamChart` is `restrictChart` of `abelSigmaChart` applied pointwise, so the coverage
hypothesis here is literally the `PointwiseCoverage` of the family the seam consumes.  The
conclusion is the dichotomy of
`exists_crossing_or_not_injective_of_pointwiseCoverage_of_ne_top`, read at the Abel charts.

This is what makes the multi-index measurement bear on the campaign rather than on an
abstraction: the tree's `V`-interval refutations are all at `ι := PUnit`, and this says what
survives at the `ι` the assembly quantifies over — a disjunction, with the crossing alternative
live by `not_indexSeparated_duplicated`. -/
theorem exists_crossing_or_not_injective_mixedParamChart {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens) (i₀ : ι) (hV : V i₀ ≠ ⊤)
    (hcov : PointwiseCoverage C (mixedParamChart C π nn D rep m Z hdeg V)) :
    ∃ (W : (D i₀).left.Opens) (i : ι) (x : (W : Scheme.{u}) ⟶ (D i).left),
      (abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)).app
            (op (W : Scheme.{u})) x
          = (abelSigmaChart C π (nn i₀) (rep i₀) (m i₀) (Z i₀) (hdeg i₀)).app
            (op (W : Scheme.{u})) (W.ι) ∧
        (i ≠ i₀ ∨ ¬ Function.Injective
          ((abelSigmaChart C π (nn i₀) (rep i₀) (m i₀) (Z i₀) (hdeg i₀)).app
            (op (W : Scheme.{u})))) :=
  exists_crossing_or_not_injective_of_pointwiseCoverage_of_ne_top C
    (fun i => abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)) V i₀ hV hcov

variable (C π) in
/-- **The positive branch at the real atlas**: an index-separated Abel atlas all of whose charts
are injective supports coverage at no proper `V i₀`.

At `ι := PUnit` this is `not_pointwiseCoverage_of_injective_of_ne_top`
(`Pic0ChartCoverForcesNonInj.lean`), whose index-separation premise is free there.  At the real
`ι` the premise is an extra obligation on the atlas, and the point of this file is that no
landed fact supplies it. -/
theorem not_pointwiseCoverage_mixedParamChart_of_jointlyInjective {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens) (i₀ : ι) (hV : V i₀ ≠ ⊤)
    (hinj : JointlyInjective C
      (fun i => abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i))) :
    ¬ PointwiseCoverage C (mixedParamChart C π nn D rep m Z hdeg V) :=
  not_pointwiseCoverage_of_jointlyInjective_of_ne_top V i₀ hV hinj

/-! ## The second way to close the crossing alternative: a uniform index

Index separation is one way to rule out the crossing alternative, and
`not_indexSeparated_duplicated` shows an overlapping atlas does not supply it.  There is a
second, and it is the one a coverage lane can actually produce: coverage that always returns
*the same* index.  That is what a chart whose locus is the whole test gives, so this section is
the joint with the coverage side rather than with the injectivity side. -/

variable (C) in
/-- **Coverage at a fixed index**: the pointwise coverage datum, strengthened to return one
prescribed index `i₀` at every test and point.

This is the shape a *uniform* chart supplies — a single index whose chart locus is everything —
as opposed to the plain `PointwiseCoverage`, which is free to choose an index per point. -/
def UniformCoverage {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (i₀ : ι) : Prop :=
  ∀ (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : ↥T),
    ∃ (W : T.Opens) (_ : t ∈ W) (x : (W : Scheme.{u}) ⟶ X i₀),
      (f i₀).app (op (W : Scheme.{u})) x = (pic0SigmaSheaf C).1.map (W.ι).op s

/-- A uniform coverage datum is in particular a pointwise one. -/
theorem pointwiseCoverage_of_uniformCoverage {ι : Type u} {X : ι → Scheme.{u}}
    {f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1} {i₀ : ι}
    (h : UniformCoverage C f i₀) : PointwiseCoverage C f := by
  intro T s t
  obtain ⟨W, htW, x, hx⟩ := h T s t
  exact ⟨W, htW, i₀, x, hx⟩

variable (C) in
/-- **THE CROSSING ALTERNATIVE IS CLOSED BY A UNIFORM INDEX**, so the one-chart no-go *does*
propagate to a multi-index atlas whose coverage is uniform: at a proper `V i₀`, uniform coverage
for the restricted family refutes injectivity of `f i₀` on some test.

The proof is the one-chart argument with the index supplied by hypothesis rather than by
`Subsingleton ι`, which is the honest replacement for the premise
`not_indexSeparated_duplicated` rules out.

**This is the half of the file that needs no unmeasured premise.**  It says which coverage
results reinstate the no-go: not the ones that merely cover, but the ones that cover *at one
named chart*, i.e. whose witness index does not depend on the point.

**Two things this does NOT say**, both of which an earlier draft of this docstring got wrong.
First, `hV : V i₀ ≠ ⊤` is a hypothesis about the open of the chart **source** at which the
`hf` certificate is taken, and a chart "whose locus is the whole test" is a statement about a
subset of a **test** — different carriers, bridged only by `chartLocusOpens` at the cost of
`haff` (`Pic0ChartAtlasCoupling.lean:50-55` is explicit that they are not interchangeable).  So
this theorem does not compose with a full-locus coverage result without that bridge.  Second,
`UniformCoverage C f i₀` is definitionally the one-chart `PointwiseCoverage` of the single map
`f i₀` — the other charts are not mentioned — so this is the landed one-chart theorem with its
`Subsingleton ι` premise replaced by a hypothesis that names the index, not new mathematics. -/
theorem not_injective_of_uniformCoverage_of_ne_top {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (V : ∀ i, (X i).Opens)
    (i₀ : ι) (hV : V i₀ ≠ ⊤)
    (hcov : UniformCoverage C (fun i => restrictChart (f i) (V i)) i₀) :
    ∃ S : Scheme.{u}ᵒᵖ, ¬ Function.Injective ((f i₀).app S) := by
  obtain ⟨t, htV⟩ : ∃ t : X i₀, t ∉ V i₀ := by
    by_contra hc
    exact hV (top_le_iff.mp fun t _ => not_not.mp fun ht => hc ⟨t, ht⟩)
  obtain ⟨W, htW, x, hx⟩ := hcov (X i₀) ((f i₀).app (op (X i₀)) (𝟙 (X i₀))) t
  refine ⟨op (W : Scheme.{u}), fun hinj => ?_⟩
  have hxv : (f i₀).app (op (W : Scheme.{u})) (x ≫ (V i₀).ι)
      = (f i₀).app (op (W : Scheme.{u})) (W.ι ≫ 𝟙 (X i₀)) := by
    rw [← chart_map_ι_apply (f i₀) W (𝟙 (X i₀))]
    exact hx
  have heq := hinj hxv
  have hmem : ((x ≫ (V i₀).ι).base ⟨t, htW⟩ : X i₀) ∈ V i₀ := (x.base ⟨t, htW⟩).2
  rw [show ((x ≫ (V i₀).ι).base ⟨t, htW⟩ : X i₀)
      = ((W.ι ≫ 𝟙 (X i₀)).base ⟨t, htW⟩ : X i₀) from by rw [heq]] at hmem
  exact htV (by simpa using hmem)

variable (C) in
/-- **The contrapositive at a uniform index**: an injective chart admits uniform coverage at no
proper `V`, whatever the ambient index type. -/
theorem not_uniformCoverage_of_injective_of_ne_top {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1) (V : ∀ i, (X i).Opens)
    (i₀ : ι) (hV : V i₀ ≠ ⊤)
    (hinj : ∀ S : Scheme.{u}ᵒᵖ, Function.Injective ((f i₀).app S)) :
    ¬ UniformCoverage C (fun i => restrictChart (f i) (V i)) i₀ := by
  intro hcov
  obtain ⟨S, hS⟩ := not_injective_of_uniformCoverage_of_ne_top C f V i₀ hV hcov
  exact hS (hinj S)

/-! ## The negative answer: index separation is not free, so the no-go does not propagate -/

variable (C) in
/-- The two-element duplicated family: two copies of the map named by the tautological section
of `Spec k`, indexed by `ULift Bool`.

This is the witness that separates the two notions.  Its sources and its maps are the ones
`Pic0ChartCoverForcesNonInj.specSecMap_injective` already certifies, so no new geometry is
introduced — only a second index. -/
def duplicatedSpecFamily (_ : ULift.{u} Bool) :
    yoneda.obj (Spec (CommRingCat.of k)) ⟶ (pic0SigmaSheaf C).1 :=
  yonedaEquiv.symm (specSigmaSectionTaut C)

variable (C) in
/-- Every member of the duplicated family is injective on every test — `specSecMap_injective`
verbatim. -/
theorem injective_duplicated (i : ULift.{u} Bool) (S : Scheme.{u}ᵒᵖ) :
    Function.Injective ((duplicatedSpecFamily C i).app S) :=
  specSecMap_injective C S

variable (C) in
/-- **INDEX SEPARATION IS NOT FREE, AND NOT IMPLIED BY PER-CHART INJECTIVITY.**

The duplicated family has both charts injective on every test (`injective_duplicated`) and is
*not* index separated: the identity point of `Spec k` has the same value in both components.

This is the negative answer to the multi-index question.  The one-chart refutation of the
`V`-interval concludes per-chart injectivity, and per-chart injectivity does not give the
index-separation premise that
`not_injective_of_pointwiseCoverage_of_indexSeparated_of_ne_top` needs — so the no-go has no
multi-index analogue, and a glueing atlas, whose charts overlap by construction, is precisely
the shape that evades it. -/
theorem not_indexSeparated_duplicated :
    ¬ IndexSeparated C (duplicatedSpecFamily C) := by
  intro hsep
  have hne : (⟨false⟩ : ULift.{u} Bool) ≠ ⟨true⟩ := by simp
  -- the test is `Spec k`, which HAS a point: this is the nonempty-test form, so the refutation
  -- is a fact about the family and not the `Subsingleton ι` collapse of `IndexSeparatedAll`
  exact hne (hsep (Spec (CommRingCat.of k))
    (inferInstanceAs (Nonempty (PrimeSpectrum k))) ⟨false⟩ ⟨true⟩
    (𝟙 (Spec (CommRingCat.of k))) (𝟙 (Spec (CommRingCat.of k))) rfl)

/-! ### `IndexSeparated` is satisfiable at two indices — the repair is not a second vacuity

Restricting to nonempty tests removes the `Subsingleton ι` collapse; it would be an empty
victory if the restricted condition were *unsatisfiable* whenever `ι` has two elements.  It is
not, and this section proves it, so `IndexSeparated` is a genuine hypothesis with a genuine
witness at `|ι| = 2` rather than a condition that merely fails more slowly. -/

/-- A two-element source family whose second member is the **empty** open of the first.  The
sources are what carries the witness; the maps are the tautological one and its restriction. -/
def satSrc (k : Type u) [Field k] : ULift.{u} Bool → Scheme.{u}
  | ⟨true⟩ => Spec (CommRingCat.of k)
  | ⟨false⟩ => ((⊥ : (Spec (CommRingCat.of k)).Opens) : Scheme.{u})

variable (C) in
/-- The two-index family on `satSrc`: the tautological section at `true`, its `⊥`-restriction at
`false`. -/
def satFam : ∀ i, yoneda.obj (satSrc k i) ⟶ (pic0SigmaSheaf C).1
  | ⟨true⟩ => yonedaEquiv.symm (specSigmaSectionTaut C)
  | ⟨false⟩ => restrictChart (yonedaEquiv.symm (specSigmaSectionTaut C))
                 (⊥ : (Spec (CommRingCat.of k)).Opens)

variable (C) in
/-- **`IndexSeparated` IS SATISFIABLE WITH TWO DISTINCT INDICES.**

So the nonempty-test restriction is a real repair and not a slower vacuity: unlike
`IndexSeparatedAll`, which forces `Subsingleton ι` outright
(`indexSeparatedAll_iff_subsingleton`), the restricted condition holds here at
`ι = ULift Bool`.

The witness is deliberately cheap and its cheapness is the point.  Index `false` has an *empty*
source, so a test admitting a map to it is empty and the `Nonempty` binder is contradicted —
every cross-index pair is vacuous, and the diagonal pairs are `rfl`.  It shows the shape of a
satisfying family: index separation is a condition on where the chart sources have points, which
is exactly the sort of thing an atlas can arrange and `IndexSeparatedAll` could never express.

What it does **not** show, and this bound is why it is stated separately from the theorems that
consume the hypothesis: nothing here says the *Abel* atlas can be arranged this way.  A witness
using an empty chart source is not a chart family a producer would build. -/
theorem indexSeparated_satFam : IndexSeparated C (satFam C) := by
  rintro S hS ⟨i⟩ ⟨j⟩ x y _
  have hemp : ∀ (_ : (yoneda.obj (satSrc k (⟨false⟩ : ULift.{u} Bool))).obj (op S)),
      False := by
    intro z
    have : IsEmpty S := (show S ⟶ ((⊥ : (Spec (CommRingCat.of k)).Opens) : Scheme.{u})
      from z).base.hom.1.isEmpty
    exact this.elim hS.some
  cases i <;> cases j
  · rfl
  · exact (hemp x).elim
  · exact (hemp y).elim
  · rfl

/-- The index type of the witness genuinely has two elements, so
`indexSeparated_satFam` is not `indexSeparated_of_subsingleton` in disguise. -/
theorem not_subsingleton_ulift_bool : ¬ Subsingleton (ULift.{u} Bool) := fun h =>
  absurd (h.elim (⟨false⟩ : ULift.{u} Bool) ⟨true⟩) (by simp)

variable (C) in
/-- The same fact at the level the coverage step consumes: the duplicated family is not jointly
injective, although each of its charts is injective. -/
theorem not_jointlyInjective_duplicated :
    ¬ JointlyInjective C (duplicatedSpecFamily C) :=
  fun h => not_indexSeparated_duplicated C ((jointlyInjective_iff _).mp h).1

/-- **Joint injectivity is inhabited** — so the hypothesis of
`not_pointwiseCoverage_of_jointlyInjective_of_ne_top` is not vacuous, and the refutation above
is about the *index*, not about the Σ-sheaf admitting no injective family at all.

The one-element family at the tautological section of `Spec k` is jointly injective: index
separation is free by `indexSeparated_of_subsingleton` and per-chart injectivity is
`specSecMap_injective`. -/
theorem jointlyInjective_singleSpecFamily :
    JointlyInjective C (fun _ : PUnit.{u+1} => yonedaEquiv.symm (specSigmaSectionTaut C)) :=
  (jointlyInjective_iff _).mpr
    ⟨indexSeparated_of_subsingleton _, fun _ S _ => specSecMap_injective C (op S)⟩

end

end AlgebraicGeometry
