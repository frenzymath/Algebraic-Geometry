/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartVMonotone
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The two seam antecedents COLLAPSE at a one-chart atlas: the pair forces an ISOMORPHISM

Four rows and three file headers in this project defer to one question, in these words:
**"inhabitation of the pair `(huniv V, hcov V)` is unmeasured at every `V` and may be empty
everywhere"** (`AJCR.w4-rep.datum.chart-restrict`, repeated verbatim on
`…datum.atlas-coupling`, whose own summary adds that its round "removed a candidate escape from
that question, it did not answer it").  Five files of endpoint refutations and monotonicity
results (`Pic0ChartRestrictedFibreSat`, `Pic0ChartVMonotone`, `Pic0ChartBotRefute`,
`Pic0ChartAtlasCoupling`, `Pic0ChartCoverForcesNonInj`) all stop there.

**This file answers what the pair IS.**  For a one-chart atlas the two antecedents are not two
independent conditions to be met at some lucky `V` — together they say the chart map is an
**isomorphism of sheaves onto `pic0SigmaSheaf C`**, and conversely any such isomorphism
satisfies both.  So the question "is the pair inhabited at some `V`?" is *equivalent* to
"is `pic0SigmaFunctor C` representable by an open of the divisor scheme?", which is the
project's own headline restricted to a one-chart atlas.

## Why this is a collapse and not a restatement

The two clauses are `MorphismProperty.relative`-shaped and sieve-shaped respectively, and
nothing in the tree related them.  The bridge is that each is *half of a bijectivity*:

* antecedent 1 (`IsChartUniv`, i.e. `IsOpenImmersion.presheaf`) **implies** elementwise
  injectivity on every test — that is `injective_of_isOpenImmersion_presheaf`
  (`Pic0ChartOpenImmersionCriterion.lean`), which routes through
  `IsOpenImmersion.le_monomorphisms`.  Injectivity on the nose is *stronger* than
  `Presheaf.IsLocallyInjective`, so it gives it (`isLocallyInjective_of_injective`);
* antecedent 2 is `Presheaf.IsLocallySurjective` verbatim;
* and mathlib's `Sheaf.isLocallyBijective_iff_isIso` turns locally-injective-plus-locally-
  surjective into `IsIso` — **provided both sides are sheaves**.  The target is one by
  construction (`pic0SigmaFunctor_isSheaf`); the source is one because the big Zariski topology
  is **subcanonical** (`AlgebraicGeometry.subcanonical_zariskiTopology`, mathlib), so `yoneda.obj X`
  is a sheaf for it with no hypothesis on `X` at all.

That last point is the step that had never been taken here: the chart source is representable,
and on a subcanonical site a representable presheaf is a sheaf, so the seam's two antecedents
live in a category where mathlib's bijectivity criterion applies.  Nothing about `pic⁰`,
divisors, charts or the curve enters any proof below.

## What this buys, stated as three consequences and one non-consequence

* **`chartIso_of_seam`** — the collapse. Both antecedents at a one-chart atlas give
  `IsIso` of the sheaf morphism.
* **`representableBy_of_seam`** — hence `pic0SigmaFunctor C` is represented by the chart
  source *on the nose*, without going through mathlib's 01JJ gluing engine at all.  For a
  one-chart atlas the whole `Scheme.LocalRepresentability` apparatus of
  `pic0RepresentableByOfCharts` is bypassed: the glued scheme is the chart.
* **`exists_retraction_of_seam`** — the sharp constraint on `V`.  If the pair holds at `V` then
  the open inclusion `V.ι : ↥V ⟶ D.left` is a **split mono in `Scheme`**: the chart map
  composed with the inverse retracts it.  So a working `V` is not merely a proper intermediate
  open (which is all the endpoint results gave); it is a **retract of the divisor scheme**.
  That is a much stronger structural demand, and it is the form in which the inhabitation
  question should be attacked next.
* **The non-consequence, and it is why this file does not claim to have answered the question.**
  `IsIso` is an *equivalent reformulation*, not a refutation and not a witness.  Nothing below
  exhibits a `V` at which the pair holds, and nothing below refutes one.  What changes is that
  the target is now a single familiar statement about one morphism instead of a conjunction of
  two conditions of different shapes — and that the retraction constraint is available to
  whoever attacks it.

## Scope: one chart, and that is a real restriction

Every statement here is for a **`PUnit`-indexed** atlas.  That is not a convenience: for a
general `ι` the two antecedents are about *different* morphisms (`f i` versus `Sigma.desc f`),
and `Sigma.desc f` is not a map out of a representable, so `chartSheafHom` cannot even be
*formed* on it: the collapse needs the **source** to be a sheaf, and a coproduct of
representables is not one in general — subcanonicity gives the sheaf property of
`yoneda.obj X`, not of `∐ i, yoneda.obj (X i)`.  (Measured rather than asserted: an `exact?`
on `Presheaf.IsSheaf Scheme.zariskiTopology (∐ fun i => yoneda.obj (X i))` finds nothing, which
is weak evidence of absence on a composite goal but is the right *reason* — the coproduct
presheaf is a sheaf only after sheafification, and that is a different object from the one the
seam's antecedent 2 is stated about.)

The one-chart case is not a caricature either — `Pic0AtlasFromDivRep.lean` builds a
one-chart atlas, and `IsChartUniv`, `RestrictedChartFibre` and `restrictedChartFibre_top_iff`
are all stated for one.  But a lane must not read `chartIso_of_seam` as a statement about
`mixedParamChart` at arbitrary `ι`.  `isLocallySurjective_oneChart` below is the bridge that
makes the one-chart hypothesis usable in the coproduct spelling the seam consumes, so the
restriction is to the *index*, not to the *spelling*.

## Main declarations

* `AlgebraicGeometry.chartSourceSheaf` — the chart source as a sheaf, by subcanonicity.
* `AlgebraicGeometry.isLocallySurjective_oneChart` — antecedent 2 in the coproduct spelling
  gives local surjectivity of the single chart.
* `AlgebraicGeometry.chartIso_of_seam` — **the collapse**.
* `AlgebraicGeometry.seam_of_chartIso` — **the converse**, so this is an equivalence and not a
  weakening.
* `AlgebraicGeometry.representableBy_of_seam` — the representation, engine-free.
* `AlgebraicGeometry.exists_retraction_of_seam` — `V.ι` is a split mono.
* `AlgebraicGeometry.eq_top_of_retraction_of_isDominant` and
  `AlgebraicGeometry.eq_top_of_seam_of_isDominant` — a **dense** working `V` is `⊤`.
* `AlgebraicGeometry.isDominant_opens_ι_of_irreducibleSpace` and
  `AlgebraicGeometry.eq_top_of_seam_of_irreducible` — **the constraint's final form**: on an
  irreducible reduced separated chart source every *nonempty* working `V` is `⊤`, so a working
  `V` in the interior of the interval requires a **reducible** chart source.
* `AlgebraicGeometry.injective_abelSigmaChart_of_seam_of_irreducible` — **the sharpest form**:
  the seam at any *nonempty* `V` over an irreducible reduced separated divisor scheme forces the
  UNRESTRICTED Abel chart to be injective, i.e. reduces the whole `V`-interval question to the
  `abel-noninj` fork.
* `AlgebraicGeometry.chartIso_of_isChartUniv` and
  `AlgebraicGeometry.exists_retraction_of_isChartUniv` — the applicability check at the Abel
  chart, fed by `IsChartUniv` itself.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

noncomputable section

/-! ## The chart source is a sheaf -/

/-- **A representable presheaf is a big-Zariski sheaf**, because the big Zariski topology is
subcanonical (`subcanonical_zariskiTopology`, mathlib).

Recorded as a named lemma because it is the step the whole file rests on and the step nobody
had taken: the chart source of the atlas is `yoneda.obj (V : Scheme)`, hence a sheaf, hence the
chart map is a morphism *of sheaves* — which is what lets mathlib's bijectivity criterion see
it.  No hypothesis on the scheme. -/
theorem isSheaf_yoneda_obj (X : Scheme.{u}) :
    Presheaf.IsSheaf Scheme.zariskiTopology (yoneda.obj X) :=
  (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X))

/-- The chart source bundled as a sheaf on the big Zariski site. -/
def chartSourceSheaf (X : Scheme.{u}) : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
  ⟨yoneda.obj X, isSheaf_yoneda_obj X⟩

variable (C) in
/-- A chart map read as a morphism of sheaves. -/
def chartSheafHom {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) :
    chartSourceSheaf X ⟶ pic0SigmaSheaf C :=
  ⟨f⟩

/-! ## Antecedent 2 at a one-chart atlas -/

variable (C) in
/-- **Antecedent 2, de-coproducted at one chart**: local surjectivity of `Sigma.desc` for a
`PUnit`-indexed family gives local surjectivity of the chart itself.

The image sieve of `Sigma.desc` is contained in that of the single chart, because a section of
the coproduct presheaf resolves into a section of the one summand
(`FunctorToTypes.jointly_surjective'`, the lemma `Pic0ChartBotRefute.lean` first brought into
this project) and `Sigma.ι_desc` identifies the two readings.

This is what makes the one-chart restriction a restriction on the *index* only: a lane holding
the instance the seam consumes holds this. -/
theorem isLocallySurjective_oneChart {X : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (h : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun _ : PUnit.{u+1} => f))) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology f := by
  haveI := h
  constructor
  intro T s
  refine Scheme.zariskiTopology.superset_covering ?_
    (Presheaf.imageSieve_mem (J := Scheme.zariskiTopology)
      (Sigma.desc (fun _ : PUnit.{u+1} => f)) s)
  intro Y g hg
  obtain ⟨t, ht⟩ := hg
  obtain ⟨i, y, rfl⟩ := CategoryTheory.FunctorToTypes.jointly_surjective'
    (Discrete.functor fun _ : PUnit.{u+1} => yoneda.obj X) (op Y) t
  refine ⟨y, ?_⟩
  rw [← ht, ← NatTrans.comp_app_apply]
  simpa using
    (NatTrans.congr_app (Sigma.ι_desc (fun _ : PUnit.{u+1} => f) i.as) (op Y)).symm ▸ rfl

/-! ## The collapse -/

variable (C) in
/-- **THE COLLAPSE**: at a one-chart atlas the two seam antecedents together say the chart map
is an isomorphism onto the Σ-sheaf.

Antecedent 1 gives injectivity on every test, hence local injectivity; antecedent 2 is local
surjectivity; and on a site where both sides are sheaves mathlib's
`Sheaf.isLocallyBijective_iff_isIso` closes it.  The source is a sheaf by subcanonicity
(`isSheaf_yoneda_obj`) — the observation this file exists to spend.

Read against the five files of `V`-interval results: those establish that a working `V` must be
a proper intermediate open.  This says what a working `V` *is*. -/
theorem chartIso_of_seam {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (hf : IsOpenImmersion.presheaf f)
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology f) :
    IsIso (chartSheafHom C f) := by
  haveI : Presheaf.IsLocallyInjective Scheme.zariskiTopology (chartSheafHom C f).hom :=
    Presheaf.isLocallyInjective_of_injective _ _
      (fun T => injective_of_isOpenImmersion_presheaf hf T)
  haveI : Presheaf.IsLocallySurjective Scheme.zariskiTopology (chartSheafHom C f).hom := hcov
  exact (Sheaf.isLocallyBijective_iff_isIso (chartSheafHom C f)).mp
    ⟨inferInstance, inferInstance⟩

variable (C) in
/-- **THE CONVERSE**, so the collapse is an equivalence and not a weakening (the `I-0896`
criterion).  An isomorphism satisfies both antecedents:

* antecedent 1 because `IsOpenImmersion.presheaf` is `MorphismProperty.relative`, which
  contains the isomorphisms (`MorphismProperty.of_isIso`, available since `relative` is
  multiplicative and respects isos);
* antecedent 2 because a locally surjective map is what an iso trivially is
  (`Presheaf.isLocallySurjective_of_iso`).

Together with `chartIso_of_seam` this says: **the pair is inhabited at `V` if and only if the
restricted chart is an isomorphism of sheaves.**  So the unmeasured inhabitation question has
not been weakened into something easier — it has been identified. -/
theorem seam_of_chartIso {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (h : IsIso f) :
    IsOpenImmersion.presheaf f
      ∧ Presheaf.IsLocallySurjective Scheme.zariskiTopology f := by
  haveI := h
  exact ⟨MorphismProperty.of_isIso (P := IsOpenImmersion.presheaf) f, inferInstance⟩

/-! ## The representation, without the gluing engine -/

variable (C) in
/-- **The seam's conclusion at a one-chart atlas, engine-free**: the two antecedents represent
`pic0SigmaFunctor C` by the chart source itself.

`pic0RepresentableByOfCharts` obtains its representing object from mathlib's 01JJ
`Scheme.LocalRepresentability` gluing engine, as
`(Scheme.LocalRepresentability.glueData hf).glued`.  At one chart that is unnecessary: the
underlying presheaf map of the iso is already an equivalence at every test, and naturality is
the chart map's own naturality.  So a lane that closes the pair at one `V` does not owe the
glue-data bookkeeping — it gets the representation directly, over the chart.

This is stated for `pic0SigmaFunctor` rather than `pic0TypeFunctor`: the Σ-descent to the
slice is `Functor.RepresentableBy.overSlice`, exactly as in `pic0RepresentableByOfCharts`, and
is not re-proved here. -/
def representableBy_of_seam {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (hf : IsOpenImmersion.presheaf f)
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology f) :
    (pic0SigmaFunctor C).RepresentableBy X :=
  letI : IsIso f := by
    haveI := chartIso_of_seam C f hf hcov
    exact (inferInstance : IsIso ((sheafToPresheaf Scheme.zariskiTopology (Type u)).map
      (chartSheafHom C f)))
  { homEquiv := fun {T} => Iso.toEquiv ((asIso f).app (op T))
    homEquiv_comp := fun {_T _T'} g x => NatTrans.naturality_apply f g.op x }

/-! ## The sharp constraint on `V` -/

variable (C) in
/-- **A WORKING `V` IS A RETRACT OF THE CHART SOURCE.**

If the two antecedents hold for `restrictChart f V` then `V.ι : ↥V ⟶ X` is a **split mono in
`Scheme`**: its retraction is `yoneda.preimage (f ≫ inv (restrictChart f V))`, i.e. "read the
class, then invert the restricted chart".  Yoneda is full, so this is an honest morphism of
schemes and not merely a presheaf-level section.

This strictly strengthens what the endpoint literature gives.  `Pic0ChartRestrictedFibreSat`
and `Pic0ChartVMonotone` establish that a working `V` must be a *proper intermediate open*;
this says it must be a *retract*, which for an open subscheme is a strong structural demand
(e.g. it forces `V.ι` to be a topological embedding admitting a continuous left inverse on all
of `X`, so `V` meets every connected component and its closure is `X` whenever `X` is
irreducible and `V` nonempty).

Deliberately not pushed to a refutation.  Whether the divisor scheme admits a proper open
retract is a question about `DivScheme`'s geometry that this file does not touch, and asserting
it cannot is exactly the kind of unverified claim the `unverified-counterexample-in-docstring`
lesson is about.  What is established is the obligation's *shape*. -/
theorem exists_retraction_of_seam {X : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) (V : X.Opens)
    (hf : IsOpenImmersion.presheaf (restrictChart f V))
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology (restrictChart f V)) :
    ∃ r : X ⟶ (V : Scheme.{u}), V.ι ≫ r = 𝟙 _ := by
  letI : IsIso (restrictChart f V) := by
    haveI := chartIso_of_seam C (restrictChart f V) hf hcov
    exact (inferInstance : IsIso ((sheafToPresheaf Scheme.zariskiTopology (Type u)).map
      (chartSheafHom C (restrictChart f V))))
  refine ⟨yoneda.preimage (f ≫ inv (restrictChart f V)), ?_⟩
  apply yoneda.map_injective
  have h1 : yoneda.map (V.ι ≫ yoneda.preimage (f ≫ inv (restrictChart f V)))
      = yoneda.map V.ι ≫ (f ≫ inv (restrictChart f V)) := by
    rw [Functor.map_comp, yoneda.map_preimage]
  have h2 : yoneda.map V.ι ≫ (f ≫ inv (restrictChart f V))
      = 𝟙 (yoneda.obj (V : Scheme.{u})) := by
    rw [← Category.assoc]; exact IsIso.hom_inv_id (restrictChart f V)
  rw [h1, h2, ← yoneda.map_id]

/-! ## The retraction collapses the interval on a DENSE open

The retraction above is a statement about an arbitrary open.  On a *dense* one it forces
`V = ⊤`, which sends the seam back to the endpoint literature's `⊤` case — and that case is
refuted the moment the Abel chart fails to be injective.  So on the geometrically natural
candidates for `V` the interval has no interior at all. -/

/-- **A dense working `V` in a reduced separated ambient scheme is `⊤`.**

The retraction `r` is a *left* inverse of `V.ι`; to promote it to a two-sided one we need
`r ≫ V.ι = 𝟙 X`, and that follows from mathlib's agreement principle
`ext_of_isDominant`: the two morphisms `r ≫ V.ι` and `𝟙 X` agree after precomposition with
the dominant `V.ι`, and `X` is reduced and separated.  An iso open inclusion is surjective on
points, hence `V = ⊤`.

`IsDominant V.ι` is exactly density of `V` (mathlib's `IsDominant` is denseness of the range).
**An earlier version of this docstring hedged that "for an irreducible ambient every nonempty
open is dense — so this is not an exotic side condition", i.e. it asserted the bridge in prose
instead of proving it.  That was understated in the file's own disfavour: the bridge is two
lines** (`isDominant_opens_ι_of_irreducibleSpace` below), so the hypothesis is not density at
all — it is **irreducibility plus nonemptiness**, which is a property of the chart source rather
than of the candidate open.  `eq_top_of_seam_of_irreducible` states it that way.

The hypotheses `[IsReduced X]`, `[X.IsSeparated]`, `[IsDominant V.ι]` are all load-bearing and
none is about `pic⁰`: this is a general fact about split-mono open immersions. -/
theorem eq_top_of_retraction_of_isDominant {X : Scheme.{u}} [IsReduced X] [X.IsSeparated]
    (V : X.Opens) [IsDominant (V.ι)]
    (r : X ⟶ (V : Scheme.{u})) (hr : V.ι ≫ r = 𝟙 _) :
    V = ⊤ := by
  haveI : IsIso (V.ι) := by
    refine ⟨r, hr, ?_⟩
    refine ext_of_isDominant (X := X) (Y := X) (W := (V : Scheme.{u})) (V.ι) ?_
    rw [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  have hsurj : Function.Surjective (V.ι).base :=
    (TopCat.homeoOfIso (asIso (Scheme.forgetToTop.map (V.ι)))).surjective
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨y, rfl⟩ := hsurj x
  exact y.2

variable (C) in
/-- **THE INTERVAL HAS NO INTERIOR ON DENSE OPENS**: the two antecedents at a dense `V` force
`V = ⊤`.

Composite of `exists_retraction_of_seam` with `eq_top_of_retraction_of_isDominant`.  This is
the statement to read against the four rows that call the inhabitation question open: they are
right that it is open, and this says **where** it can be open.  Every candidate `V` that is
dense in the chart source — which, on an irreducible chart source, means every nonempty
candidate — is `⊤`.  And `⊤` is refuted by
`not_restrictedChartFibre_top_of_not_injective` (`Pic0ChartRestrictedFibreSat.lean`, downstream
of this file so the name does not resolve here) as soon as the Abel chart fails to be injective
on one test — the `abel-noninj` fork.

**What this does NOT prove, stated because the temptation is exactly the error this project has
made before** (`two-refutations-are-not-inhabitation`).  It does not refute the pair.  Two
things stand between this and a refutation, and neither is supplied here: the chart source must
be shown irreducible (or the candidate `V` shown dense), and the `abel-noninj` fork must be
decided in the negative — which three file headers assert and no declaration proves.  What is
established is that a lane hunting for a working `V` in the interior of the interval must
either exhibit a **non-dense** one or first settle the fork. That is a genuine narrowing of the
search, not a closure of it. -/
theorem eq_top_of_seam_of_isDominant {X : Scheme.{u}} [IsReduced X] [X.IsSeparated]
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) (V : X.Opens) [IsDominant (V.ι)]
    (hf : IsOpenImmersion.presheaf (restrictChart f V))
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology (restrictChart f V)) :
    V = ⊤ := by
  obtain ⟨r, hr⟩ := exists_retraction_of_seam C f V hf hcov
  exact eq_top_of_retraction_of_isDominant V r hr

/-! ## The applicability check

A sorry-free axiom-clean theorem can have **no site where it can be applied**, and satisfying
its binders in the abstract is a *different* measurement from applying it at the object the
route uses (the lesson of inbox `I-1463`, established the same day on a sibling artifact).
Every check this workspace routinely runs — build, sorry census, axiom probe, binder deletion —
passes on a theorem with no site.

So the two statements below apply the collapse and the retraction **at the Abel chart**, the
family `Pic0AtlasFromDivRep` builds and the one `IsChartUniv` is stated for, with `IsChartUniv`
in the hypothesis position rather than a bare `IsOpenImmersion.presheaf`.  They take no
hypothesis the seam does not already carry.  That is the evidence that this file's results have
a site; it is deliberately *not* evidence that the site is inhabited. -/

/-! ## Density is irreducibility: the hypothesis restated where it belongs -/

/-- **On an irreducible scheme every nonempty open is dominant.**

Two lines: `isDominant_iff` unfolds to `DenseRange`, `Scheme.Opens.range_ι` identifies the range
with the open, and `IsOpen.dense` is the topological fact.  Landed as a named lemma because the
docstring above previously *asserted* it as a reason not to worry about the `IsDominant` binder,
which is the "prose standing in for a theorem" failure mode.

The sibling project has the density form of this (`isDominant_opens_ι`,
`AlgebraicJacobian/Albanese/AlbaneseFromData.lean:280` in Algebraic-Jacobian-Challenge, outside
this project's import closure); the irreducibility form is what a consumer here wants, because
irreducibility is a property of the *chart source* and can be discharged once, whereas density
is a property of each candidate `V`. -/
theorem isDominant_opens_ι_of_irreducibleSpace {X : Scheme.{u}} [IrreducibleSpace X]
    (V : X.Opens) (hne : (V : Set X).Nonempty) :
    IsDominant (V.ι) := by
  rw [isDominant_iff]
  simpa [DenseRange, Scheme.Opens.range_ι] using V.2.dense hne

variable (C) in
/-- **THE CONSTRAINT IN ITS FINAL FORM**: on an irreducible reduced separated chart source,
**every nonempty working `V` is `⊤`**.

This is `eq_top_of_seam_of_isDominant` with the density hypothesis traded for irreducibility of
the ambient — the form in which the constraint is checkable once per carrier rather than once
per candidate open.

So the shape of the remaining question is now completely explicit.  A working `V` in the
*interior* of the interval requires the chart source to be **reducible** (or the candidate to be
empty, which `not_isLocallySurjective_restrictChart_bot'` in `Pic0ChartBotRefute.lean` refutes).
Otherwise the only candidate is `⊤`, which dies with the `abel-noninj` fork.

**Neither disjunct is settled here**, and that is the whole honest content: I do not prove the
divisor scheme irreducible, and I do not decide the fork.  What is established is that those two
are now the *only* two places a working `V` can come from. -/
theorem eq_top_of_seam_of_irreducible {X : Scheme.{u}} [IsReduced X] [X.IsSeparated]
    [IrreducibleSpace X] (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) (V : X.Opens)
    (hne : (V : Set X).Nonempty)
    (hf : IsOpenImmersion.presheaf (restrictChart f V))
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology (restrictChart f V)) :
    V = ⊤ :=
  letI := isDominant_opens_ι_of_irreducibleSpace V hne
  eq_top_of_seam_of_isDominant C f V hf hcov

variable (C π n) in
/-- **The collapse at the Abel chart**, so `IsChartUniv` — the seam's own antecedent 1, not a
paraphrase — feeds it directly.

`IsChartUniv C π n rep m Z hdeg V` is by definition
`IsOpenImmersion.presheaf (restrictChart (abelSigmaChart …) V)`, so this is `chartIso_of_seam`
with no bridging lemma.  Recorded because "applies at the route's own object" is a claim that
has to be typechecked rather than asserted. -/
theorem chartIso_of_isChartUniv {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) (huniv : IsChartUniv C π n rep m Z hdeg V)
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (restrictChart (abelSigmaChart C π n rep m Z hdeg) V)) :
    IsIso (chartSheafHom C (restrictChart (abelSigmaChart C π n rep m Z hdeg) V)) :=
  chartIso_of_seam C _ huniv hcov

-- `GeometricallyReduced C.hom` is genuinely idle in the theorem below (linter-flagged and
-- omitted rather than left in the binder list): the conclusion is about the chart map's
-- injectivity, and the sheaf property of `pic0SigmaSheaf` — the only thing that instance feeds —
-- is consumed inside `eq_top_of_seam_of_irreducible`, whose own statement carries it.
omit [GeometricallyReduced C.hom] in
variable (C π n) in
/-- **THE SEAM AT ANY NONEMPTY `V` FORCES THE UNRESTRICTED ABEL CHART TO BE INJECTIVE.**

This is the sharpest form of everything above, and it turns the `V`-interval question into the
`abel-noninj` fork outright.

The chain: on an irreducible reduced separated divisor scheme the two antecedents at a nonempty
`V` force `V = ⊤` (`eq_top_of_seam_of_irreducible`); at `⊤` the restricted chart is
precomposition with `D.left.topIso.hom`, an **isomorphism** (`restrictChart_top`,
`Pic0ChartVMonotone.lean`), and `IsOpenImmersion.presheaf` cancels isomorphisms on the left
(`MorphismProperty.cancel_left_of_respectsIso`); so antecedent 1 at `⊤` *is* the unrestricted
certificate, which implies injectivity on every test.

**What this means for the board.**  Three file headers assert the Abel chart is *not* injective
(its fibres are the linear systems `|D|`) and no declaration proves it — the `abel-noninj` fork.
If those headers are right, this theorem says the seam is **unsatisfiable at every nonempty
`V`** on an irreducible chart source, and the `⊥` case is refuted separately
(`not_isLocallySurjective_restrictChart_bot'`, `Pic0ChartBotRefute.lean`).  So the interval
question is not merely narrowed — it is *reduced to the fork*, plus irreducibility of the
divisor scheme.

**And what it does not mean.**  It is still an implication, not a refutation.  I do not prove
the divisor scheme irreducible (no `IrreducibleSpace`/`IsReduced` instance on `divSchemeOver`
was found by grep in `Picard/`, but the synthesis probe that would settle it was blocked by
unrelated `P1 k` instances, so that is **unmeasured**, not an absence claim), and I do not
decide the fork.  Note also the caution of the memory `generic-degree-intuition-fails-at-the-
pinned-degree`: at the pinned degree `n = g` with fibrewise `H¹`-vanishing the rank anchor
forces `h⁰ = 1`, so the `|D|` argument the three headers give for non-injectivity is *not*
available at the degree the atlas actually reads.  The fork may well go the other way, in which
case this theorem is satisfied rather than contradicted — and then `V = ⊤` is the only candidate
and `representableBy_of_seam` hands over the representation directly. -/
theorem injective_abelSigmaChart_of_seam_of_irreducible {D : Over (Spec (.of k))}
    [IsReduced D.left] [D.left.IsSeparated] [IrreducibleSpace D.left]
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) (hne : (V : Set D.left).Nonempty)
    (huniv : IsChartUniv C π n rep m Z hdeg V)
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (restrictChart (abelSigmaChart C π n rep m Z hdeg) V))
    (T : Scheme.{u}ᵒᵖ) :
    Function.Injective ((abelSigmaChart C π n rep m Z hdeg).app T) := by
  obtain rfl : V = ⊤ :=
    eq_top_of_seam_of_irreducible C (abelSigmaChart C π n rep m Z hdeg) V hne huniv hcov
  have hr : restrictChart (abelSigmaChart C π n rep m Z hdeg) (⊤ : D.left.Opens)
      = yoneda.map D.left.topIso.hom ≫ abelSigmaChart C π n rep m Z hdeg :=
    restrictChart_top (C := C) _
  have h2 : IsOpenImmersion.presheaf
      (yoneda.map D.left.topIso.hom ≫ abelSigmaChart C π n rep m Z hdeg) := hr ▸ huniv
  exact injective_of_isOpenImmersion_presheaf
    ((MorphismProperty.cancel_left_of_respectsIso (P := IsOpenImmersion.presheaf)
      (yoneda.map D.left.topIso.hom) (abelSigmaChart C π n rep m Z hdeg)).mp h2) T

variable (C π n) in
/-- **The retraction at the Abel chart**: the seam's two antecedents at `V` make `V` a retract
of the *divisor scheme* `D.left`.

This is the form in which the constraint should be read against the `divrep` lane: whatever
representing object `rep` supplies, a working `V` is a retract of it. -/
theorem exists_retraction_of_isChartUniv {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) (huniv : IsChartUniv C π n rep m Z hdeg V)
    (hcov : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (restrictChart (abelSigmaChart C π n rep m Z hdeg) V)) :
    ∃ r : D.left ⟶ (V : Scheme.{u}), V.ι ≫ r = 𝟙 _ :=
  exists_retraction_of_seam C _ V huniv hcov

end

end AlgebraicGeometry
