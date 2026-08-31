/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartRestrictedFibre

/-!
# `RestrictedChartFibre` is inhabited, and where the content of antecedent 1 actually sits

`Picard/Pic0ChartRestrictedFibre.lean` repairs the route to `IsChartUniv` — antecedent 1 of
`pic0RepresentableByOfCharts` — by demanding the fibre datum at the **restricted** chart.  Its
own "honest limits" section then recorded the thing it could not settle:

> an inhabitant at `V = ⊥` was **attempted and not obtained** in this session … the `sq` field
> … needs `Subsingleton (pic0Subgroup C (Over.mk a₁))` over an empty base.  That is the
> triviality of `picEt` over the empty scheme: true, a genuinely separate lemma, and absent
> from the tree.

**That pricing was wrong, and the error was in the reduction rather than in the census.**  The
`sq` goal is an equality of two elements of `(pic0SigmaSheaf C).1.obj (op S)` at an *empty* test
`S`, and `pic0SigmaSheaf` is a **sheaf**.  A sheaf's value at an object covered by the empty
sieve is terminal, so the goal is closed with no fact about `picEt` at all:

* `Scheme.bot_mem_grothendieckTopology` (mathlib, `Sites/Pretopology.lean`) — stated exactly for
  `[IsEmpty X]`;
* `Sheaf.isTerminalOfBotCover` (mathlib, `Sites/Sheaf.lean`).

The `congr 1` that peeled the Σ-component and named `pic0Subgroup` as the residue is what made
a free goal look like a missing lemma.  Recorded because the prose pricing outlived the check.

## What this file establishes

* `pic0Sigma_obj_subsingleton_of_isEmpty` — the sheaf value at an empty test is a subsingleton.
  Three lines, no `picEt` input, no geometry.
* `restrictedChartFibre_bot` — **`RestrictedChartFibre` at `V = ⊥` is inhabited,
  unconditionally**: for every `rep`, `m`, `Z`, `hdeg`.  So the class is non-empty and the
  unmeasured-inhabitation risk `Pic0ChartRestrictedFibre.lean` flagged against itself (and that
  `ChartTyping` and `IsChartLocusFibre` carried) is discharged for this class.
* `isChartUniv_bot` — hence `IsChartUniv C π n rep m Z hdeg ⊥` holds with **no hypothesis**.
* `isOpenImmersion_presheaf_restrictChart_bot` — the same construction for an **arbitrary** chart
  map, which is what the `⊥` witness really rests on: a lane that gets `hf` at `⊥` has learned
  nothing about its own chart.
* `range_subset_range_top_ι`,
  `isOpenImmersion_presheaf_abelSigmaChart_of_restrictedChartFibre_top` and
  `not_restrictedChartFibre_top_of_not_injective` — the opposite end of the interval.
* `restrictedChartFibre_top_iff` — at `V = ⊤` the class is **equivalent** to
  `IsChartLocusFibre`, which retires the latter as an independent obligation and supplies the
  converse `Pic0ChartUnivReduce.lean:55` claims exists under a name nothing defines.

## The consequence, and it is a statement about the seam rather than about this file

`isChartUniv_bot` says antecedent 1 **carries no content at `V = ⊥`**.  That is not a defect of
the repair, and it is *not* a vacuity of the coupled assembly — because the coverage side is
refuted at the same value:

* `not_coverageContainment_bot` — the `hcov` hypothesis of
  `pic0RepresentableBy_of_restrictedChartFibre_of_coverage` at `V = ⊥` is **false** as soon as
  some test has a point.  Its witness `x` would have range inside `Set.range ((⊥).ι.base) = ∅`
  while `t ∈ W` exhibits a point of the source.

## Both ends of the `V`-interval, and why the coupling has an interior

The two endpoints are priced in **opposite** directions, and that is the file's main content:

* at `V = ⊥`: `hf` is **free** (`restrictedChartFibre_bot`), and coverage's containment is
  **impossible** (`not_coverageContainment_bot`);
* at `V = ⊤`: coverage's containment is **free** (`range_subset_range_top_ι`), and `hf` is the
  **unrestricted certificate** (`isOpenImmersion_presheaf_abelSigmaChart_of_…_top`).

At `⊤` the restricted datum returns exactly the certificate the restriction was introduced to
avoid — the one `Pic0AtlasFromDivRep.lean:54`, `Pic0ChartPair.lean:14` and
`Pic0ChartOpenImmersionCriterion.lean:214` assert to be false for the Abel chart.  So the
restriction is not a formality that a lane could undo by taking `V` large.

Hence **no endpoint discharges the assembly**, and any `V` that works must be a proper
intermediate open (`not_restrictedChartFibre_top_of_not_injective` makes the `⊤` end an outright
refutation, conditional on the `abel-noninj` fork).  That is what the chart locus is for, and it
is why CHART-U(b)'s openness is a real obligation rather than bookkeeping: neither an `hf` lane
nor a coverage lane can retreat to a convenient `V`.

**What this is NOT, and an earlier draft of this header claimed otherwise** (`I-1012`, filed by a
fresh-context review of this file).  The two endpoints are **not** a non-vacuity check for the
coupled assembly.  Non-vacuity of a pair `(huniv V, hcov V)` needs a `V` where both hold — or a
refutation at every `V` — and two *bad* values of `V` supply neither.  The pair still has **no
measured inhabitant at any `V`**, and nothing here excludes it being unsatisfiable everywhere.
What *is* discharged is inhabitation of `RestrictedChartFibre` alone, at `⊥`, which is strictly
weaker.  The sentence above ("any `V` that works must be a proper intermediate open") is a
conditional and must not be read as an existence claim.  So `necessity_of_restrictedChartFibre`
was not the assembly's non-vacuity check (`I-0937`), and neither is this file; the assembly's
non-vacuity is **open**.

A further limit the endpoints below do not reach: at `V = ⊥` the *instance* form
`pic0RepresentableBy_of_restrictedChartFibre` goes through with `huniv` supplied free by
`restrictedChartFibre_bot`, leaving the `IsLocallySurjective` instance binder as the sole
remaining antecedent.  `not_coverageContainment_bot` constrains the `hcov` *spelling* of coverage,
not that instance binder — so it does not by itself rule out a `⊥`-based route through the
instance version.

**That loophole is now shut, and it turns out never to have been open.**  Both declarations
named below live in modules *downstream* of this one, so neither name resolves in this file's
import closure — `#check` them from `Picard/Pic0ChartBotRefute.lean`, not from here.  (Recorded
because a bare name in a docstring that grep confirms and `#check` refutes has cost this project
several rounds.)

* `Picard/Pic0ChartBotRefute.lean`'s `not_isLocallySurjective_restrictChart_bot'` refutes the
  instance binder at `⊥` **outright**, for an arbitrary chart family and with its own antecedents
  discharged (`Spec k` is the test, the identity class the section, and a field's spectrum
  supplies the point).  So the loophole was never open.  The producer-side spelling is
  `not_chartsCoverLocally_bot` in the same file.
* `Picard/Pic0ChartVMonotone.lean`'s `isLocallySurjective_of_bot` reaches the same endpoint by
  monotonicity — inhabiting the binder at `⊥` would yield it at every `V`, hence for the
  **unrestricted** atlas — and reads that as "the `⊥` route is not cheap".  Given the refutation
  above, that theorem is **vacuous**: its hypothesis is precisely what is refuted, so it is not
  pricing a route, and `false_of_isLocallySurjective_bot` records that.  Its companion result is
  unaffected and remains the useful one: coverage at *any* `V` implies unrestricted coverage, so
  the restriction relieves this side by nothing at all.

So both endpoints are now refuted at *instance* level rather than at the level of one
formulation, and the conditional below ("any `V` that works must be a proper intermediate open")
no longer rests on the `hcov` spelling.  It remains a conditional: no `V` is exhibited.

**What is still NOT closed, stated plainly.**  `rep` remains a hypothesis with no producer, so
`IsChartUniv` is not even statable without it; `hcov` at a useful `V` has no producer; and
nothing here produces a chart at a `V` other than `⊥`.  No antecedent of
`pic0RepresentableByOfCharts` is discharged by this file.  What is discharged is the
*satisfiability question* about the class, plus the sharp localisation of the remaining
obligation.
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

/-! ## The empty test, from the sheaf axiom -/

/-- **The Σ-sheaf is trivial on an empty test** — by the sheaf axiom, not by any property of
`picEt`.

The empty sieve covers an empty scheme (`Scheme.bot_mem_grothendieckTopology`), and a sheaf's
value at an object with a `⊥` cover is terminal (`Sheaf.isTerminalOfBotCover`); a terminal
object of `Type u` is a subsingleton.

This is the declaration `Pic0ChartRestrictedFibre.lean` priced as "the triviality of `picEt`
over the empty scheme: true, a genuinely separate lemma, and absent from the tree".  Note what
does *not* appear: no `picEt`, no `pic0Subgroup`, no `relPic`, no curve geometry.  The residue
was named after a `congr 1` had already thrown away the structure that makes it free. -/
theorem pic0Sigma_obj_subsingleton_of_isEmpty (S : Scheme.{u}) [IsEmpty S] :
    Subsingleton ((pic0SigmaSheaf C).1.obj (op S)) :=
  (Equiv.subsingleton_congr
    ((Types.isTerminalEquivIsoPUnit _
      (Sheaf.isTerminalOfBotCover (pic0SigmaSheaf C) S
        (Scheme.bot_mem_grothendieckTopology S))).toEquiv)).mpr inferInstance

/-- The carrier of the bottom open of a scheme is empty.  Stated as an instance because the
`isInitialOfIsEmpty` applications below need it by synthesis. -/
instance isEmpty_coe_bot_opens (T : Scheme.{u}) : IsEmpty ((⊥ : T.Opens) : Scheme.{u}) :=
  ⟨fun x => x.2⟩

/-! ## Inhabitation of the restricted datum -/

/-- **`RestrictedChartFibre` at `V = ⊥` is inhabited, with no hypotheses beyond the data the
statement mentions.**

Take `W := ⊥` as well.  Then:

* `r` is the unique map out of an empty scheme (`isInitialOfIsEmpty`);
* `sq` is an equality of natural transformations out of `yoneda.obj ↑⊥`; after `ext S x` the
  morphism `x : S.unop ⟶ ↑⊥` forces `S.unop` empty, and
  `pic0Sigma_obj_subsingleton_of_isEmpty` closes it;
* `exists_factor` is free: `v : S ⟶ ↑⊥` forces `S` empty, hence initial, so the factoring map
  and both compatibilities are unique.

**Why this is worth landing rather than just knowing.**  `Pic0ChartRestrictedFibre.lean` said a
lane picking up that row "should produce that witness first … it decides whether the repair is
real".  It does, and the answer is yes: the class is not empty, so the repaired route to
`IsChartUniv` is not a route to an uninhabitable hypothesis. -/
theorem restrictedChartFibre_bot {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) :
    RestrictedChartFibre C π n rep m Z hdeg ⊥ := by
  intro T g
  refine ⟨⟨⊥, isInitialOfIsEmpty.to _, ?_, ?_⟩⟩
  · ext S x
    have : IsEmpty (S.unop : Scheme.{u}) := x.base.hom.1.isEmpty
    exact (pic0Sigma_obj_subsingleton_of_isEmpty (C := C) S.unop).elim _ _
  · intro S v w _
    have : IsEmpty S := v.base.hom.1.isEmpty
    exact ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _,
      isInitialOfIsEmpty.hom_ext _ _⟩

variable (C) in
/-- **The `⊥` construction never mentions the Abel chart** — it works for an arbitrary morphism of
presheaves into the Σ-sheaf.

Stated separately because it says what `restrictedChartFibre_bot` really rests on: nothing about
divisors, the chart index, the twist, or `rep`.  Any chart family whatsoever is an open immersion
of presheaves after restriction to `⊥`.  Read as a caution — a lane that obtains `hf` at `⊥` has
learned nothing about its own chart. -/
theorem isOpenImmersion_presheaf_restrictChart_bot {X : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) :
    IsOpenImmersion.presheaf (restrictChart f (⊥ : X.Opens)) := by
  refine isOpenImmersion_presheaf_of_chartFibrePresented _ fun T g => ?_
  refine ⟨⊥, isInitialOfIsEmpty.to _, ?_, ?_⟩
  · ext S x
    have : IsEmpty (S.unop : Scheme.{u}) := x.base.hom.1.isEmpty
    exact (pic0Sigma_obj_subsingleton_of_isEmpty (C := C) S.unop).elim _ _
  · intro S v w _
    have : IsEmpty S := v.base.hom.1.isEmpty
    exact ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _,
      isInitialOfIsEmpty.hom_ext _ _⟩

/-- **Antecedent 1 is free at `V = ⊥`**: `IsChartUniv` holds there with no hypothesis.

One application of `isChartUniv_of_restrictedChartFibre` to the witness above.  Read together
with `not_coverageContainment_bot` below: `⊥` is exactly the value at which `hf` costs nothing
and coverage is impossible. -/
theorem isChartUniv_bot {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) :
    IsChartUniv C π n rep m Z hdeg ⊥ :=
  isChartUniv_of_restrictedChartFibre rep m Z hdeg ⊥ (restrictedChartFibre_bot rep m Z hdeg)

/-! ## The coverage side is refuted at the same value — so the assembly is not vacuous -/

variable (C π) in
/-- **The coverage hypothesis of the coupled assembly is FALSE at `V = ⊥`.**

This is the statement that stops `isChartUniv_bot` from making
`pic0RepresentableBy_of_restrictedChartFibre_of_coverage` vacuous.  Given any test `T` with a
point `t` and a section `s`, the `hcov` clause would supply an open `W ∋ t` and a chart point
`x : ↑W ⟶ (D i).left` whose base range is contained in `Set.range ((⊥).ι.base)`, which is
empty — while `t ∈ W` exhibits an element of `↑W`, hence of the range.

So the pair (`huniv`, `hcov`) is **not** jointly satisfiable at the value where `huniv` is
free.  Both hypotheses mention the same `V` by typing, and this says the typing is doing real
work: an `hf` lane and a coverage lane cannot each retreat to a convenient `V`.

Only the containment conjunct is used; the class equation is discarded.  So the refutation is
of the *containment at `⊥`*, and it does not depend on anything about the Abel chart. -/
theorem not_coverageContainment_bot {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : ↥T) :
    ¬ (∀ (T' : Scheme.{u}) (s' : (pic0SigmaSheaf C).1.obj (op T')) (t' : ↥T'),
      ∃ (W : T'.Opens) (_ : t' ∈ W) (i : ι) (x : (W : Scheme.{u}) ⟶ (D i).left),
        (abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)).app
            (op (W : Scheme.{u})) x
          = (pic0SigmaSheaf C).1.map (W.ι).op s' ∧
        Set.range (x.base) ⊆ Set.range ((⊥ : (D i).left.Opens).ι.base)) := by
  intro hcov
  obtain ⟨W, htW, i, x, -, hrange⟩ := hcov T s t
  obtain ⟨y, -⟩ := hrange (Set.mem_range_self (⟨t, htW⟩ : ↥W))
  exact y.2

/-! ## The other end: at `V = ⊤` the prices are exactly swapped

`⊥` is where `hf` is free and coverage is impossible.  This section shows `⊤` is where coverage's
containment is free and `hf` is *maximally* expensive — it returns the very certificate the
restriction was introduced to avoid.  Together the two ends say the `V`-coupling has a genuine
interior: there is no endpoint at which both sides are cheap, so the seam cannot be closed by
either lane choosing a convenient `V`. -/

/-- **At `V = ⊤` the coverage containment is free.**  Hence the `hcov` hypothesis of
`pic0RepresentableBy_of_restrictedChartFibre_of_coverage` collapses at `⊤` to plain
`PointwiseCoverage` — the unrestricted coverage datum, with no extra content.

Contrast `not_coverageContainment_bot`, where the same conjunct is unsatisfiable. -/
theorem range_subset_range_top_ι {Y : Scheme.{u}} {X : Scheme.{u}} (f : Y ⟶ X) :
    Set.range (f.base) ⊆ Set.range ((⊤ : X.Opens).ι.base) := by
  intro y _
  exact ⟨⟨_, trivial⟩, rfl⟩

variable (C π n) in
/-- **At `V = ⊤` the restricted datum gives back the UNRESTRICTED certificate** — the statement
`Pic0AtlasFromDivRep.lean:54`, `Pic0ChartPair.lean:14` and
`Pic0ChartOpenImmersionCriterion.lean:214` all assert to be false for the Abel chart, the linear
system `|D|` being its fibres.

So the restriction to `V` is not a formality that could be undone by taking `V` large: at the
largest `V` the repaired hypothesis is exactly as strong as the one it replaced.  Read with
`Pic0ChartPair.lean:184` — "the hypothesis of that lemma is false for the Abel chart at
`V = ⊤`" — this is the converse of `isChartUniv_of_unrestricted` at `⊤`, and it makes that
sentence a statement about `RestrictedChartFibre` too.

**Consequence for the seam, and this is the point of the file.**  Combining with
`restrictedChartFibre_bot` and `not_coverageContainment_bot`: the pair (`huniv`, `hcov`) is
free-and-impossible at `⊥`, and possible-and-maximal at `⊤`.  Neither endpoint discharges the
assembly, so any `V` that works is a proper intermediate open — which is what the chart locus is
for, and why CHART-U(b)'s openness is not optional bookkeeping.

**SHARPENED 2026-07-30 (`Picard/Pic0ChartCoverForcesNonInj.lean`), and it makes that
"proper intermediate open" conclusion *equivalent* to the `abel-noninj` fork rather than
independent of it.**  The theorem below is conditional on the Abel chart failing to be injective,
which this file's docstring correctly calls unproved.  But coverage at *any* proper `V` supplies
that failure outright, with no divisor and no carve input:
`not_injective_of_pointwiseCoverage_of_ne_top` reads the *tautological* section at a point
outside `V`, and the coverage witness — which factors through `V` — disagrees with it there.  So
for a one-chart atlas:

* if the chart is non-injective, `⊤` is dead by the theorem below;
* if it is injective, coverage holds at **no** proper `V`
  (`not_pointwiseCoverage_of_injective_of_ne_top`), and with `⊥` refuted here only `⊤` survives.

Hence a lane cannot adopt the restriction repair and stay agnostic about the fork.  **The
implication runs one way only**: "any working `V` is proper" is *implied by* the fork's negative
branch, and an earlier version of this paragraph said the two are equivalent, which is REFUTED —
the converse needs `∃ V, both clauses hold`, and the CORRECTED FRAMING section above says that
has never been measured at any `V` (audit `I-1379`).  Two further limits: the argument is for
**one chart** (at a general index coverage may return an index other than the one tested), and
its coverage antecedent is correspondingly *stronger* than DAT-B coverage, since
`pointwise_of_pointwise_restrictChart` converts it to unrestricted coverage by a single chart —
which `Pic0ChartCoveragePointwise.lean` says is not expected to hold.

The proof re-applies the criterion at the unrestricted chart, using the `⊤`-datum's own `W` and
composing its `r` with `(⊤).ι`; `exists_factor` transfers because every `v : S ⟶ X` lifts through
`(⊤).ι` by `range_subset_range_top_ι`. -/
theorem isOpenImmersion_presheaf_abelSigmaChart_of_restrictedChartFibre_top
    {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (h : RestrictedChartFibre C π n rep m Z hdeg ⊤) :
    IsOpenImmersion.presheaf (abelSigmaChart C π n rep m Z hdeg) := by
  refine isOpenImmersion_presheaf_of_chartFibrePresented _ fun T g => ?_
  refine ⟨(h T g).some.W, (h T g).some.r ≫ (⊤ : D.left.Opens).ι, ?_, ?_⟩
  · rw [yoneda.map_comp, Category.assoc]
    exact (h T g).some.sq
  · intro S v w hvw
    obtain ⟨u, hu1, hu2⟩ := (h T g).some.exists_factor S
      (IsOpenImmersion.lift (⊤ : D.left.Opens).ι v (range_subset_range_top_ι v)) w
      (by rw [restrictChart_app_apply, IsOpenImmersion.lift_fac]; exact hvw)
    refine ⟨u, ?_, hu2⟩
    rw [← Category.assoc, hu1, IsOpenImmersion.lift_fac]

variable (C π n) in
/-- **At `V = ⊤` the restricted class is EQUIVALENT to `IsChartLocusFibre`** — not merely stronger
than the certificate.

Backward is `restrictedChartFibre_of_isChartLocusFibre` with its containment `hr` supplied free by
`range_subset_range_top_ι`.  Forward is direct — keep the datum's `W` and postcompose `r` with
`(⊤).ι`, the same two-line transport as
`isOpenImmersion_presheaf_abelSigmaChart_of_restrictedChartFibre_top`; no relative-representability
round trip is needed, and in particular the pullback-vs-open-of-`T` mismatch that
`pointwise_of_chartsCoverLocally` documents does not arise here.

**What this buys.**  It retires `IsChartLocusFibre` as an independent obligation: it is exactly the
`V = ⊤` instance of the restricted class, so a lane holding either holds the other, and the
`⊤`-refutation `not_restrictedChartFibre_top_of_not_injective` transfers to it verbatim.  The two
classes were being tracked apart.

**It also supplies a declaration the tree claims already exists and does not.**
`Pic0ChartUnivReduce.lean:55` advertises "`isChartLocusFibre_of_isChartUniv` is the **converse**",
and that name occurs nowhere in either project — the docstring line is its only occurrence.
This theorem is the converse it describes, in the sharp form: not `IsChartUniv V →
IsChartLocusFibre` for arbitrary `V` (which is false in the direction that matters, since
`isChartUniv_bot` is free), but an equivalence at `V = ⊤`. -/
theorem restrictedChartFibre_top_iff {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) :
    RestrictedChartFibre C π n rep m Z hdeg ⊤
      ↔ IsChartLocusFibre C π n rep m Z hdeg := by
  refine ⟨fun h T g => ?_, fun h =>
    restrictedChartFibre_of_isChartLocusFibre rep m Z hdeg ⊤ h
      fun _ _ => range_subset_range_top_ι _⟩
  refine ⟨⟨(h T g).some.W, (h T g).some.r ≫ (⊤ : D.left.Opens).ι, ?_, ?_⟩⟩
  · rw [yoneda.map_comp, Category.assoc]
    exact (h T g).some.sq
  · intro S v w hvw
    obtain ⟨u, hu1, hu2⟩ := (h T g).some.exists_factor S
      (IsOpenImmersion.lift (⊤ : D.left.Opens).ι v (range_subset_range_top_ι v)) w
      (by rw [restrictChart_app_apply, IsOpenImmersion.lift_fac]; exact hvw)
    refine ⟨u, ?_, hu2⟩
    rw [← Category.assoc, hu1, IsOpenImmersion.lift_fac]

/-- The sharp form of the two ends, as one statement a board row can cite: at `⊤` the restricted
datum is unsatisfiable **as soon as** the Abel chart fails to be injective on some test.

This is `isEmpty_forall_chartFibrePresented_of_not_injective`'s guard, transported to the
restricted class at `V = ⊤`.  Note it is conditional: the non-injectivity is asserted in three
headers and proved nowhere (the `abel-noninj` fork), so this says "if the headers are right, `⊤`
is dead", not "`⊤` is dead". -/
theorem not_restrictedChartFibre_top_of_not_injective {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (T : Scheme.{u}ᵒᵖ)
    (hT : ¬ Function.Injective ((abelSigmaChart C π n rep m Z hdeg).app T)) :
    ¬ RestrictedChartFibre C π n rep m Z hdeg ⊤ := fun h =>
  hT (injective_of_isOpenImmersion_presheaf
    (isOpenImmersion_presheaf_abelSigmaChart_of_restrictedChartFibre_top
      C π n rep m Z hdeg h) T)

end

end AlgebraicGeometry
