/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartAtlasParamFree
import AlgebraicJacobian.Picard.JacobianDataCharts
import AlgebraicJacobian.Picard.DivSchemeQProj

/-!
# THE FOURTH ANTECEDENT: the chart-finiteness certificate of the real atlas

## Why this file exists

The board, and every lane working the Picard seam, prices the distance to representability as
the three undischarged antecedents of `pic0RepresentableByOfCharts`
(`Picard/Pic0SigmaSheaf.lean`): `IsChartUniv`, Zariski-local surjectivity of `Sigma.desc f`,
and a representation `rep` of the divisor functor.

**That is the antecedent list of the implication, not of the goal.**  `JacobianData`
(`Picard/JacobianData.lean`) has **four** fields — `J`, `rep`, `locallyOfFiniteType`,
`quasiCompact` — and its every producer from an atlas takes a fourth input on top of `hf` and the
local-surjectivity instance:

  `hlft : ∀ i, LocallyOfFiniteType (chartHom C f i)`

`JacobianData.ofCharts` and `JacobianData.ofChartsOfCompactSpace` both carry it, as do the two
Abel-image producers in `Picard/JacobianDataAbelImage.lean` and
`Picard/JacobianDataAbelSurj.lean` (named there, not cited here: neither module is in this file's
import closure, and a name outside the closure is not a name).  So a session that discharged all
three tracked antecedents would still not have produced a `JacobianData C`, and nothing in the
tree produces `hlft` **at a chart of an atlas** — `locallyOfFiniteType_gluedHom`
(`JacobianDataCharts.lean`) is the only route to the glued object's certificate and it *takes*
`hlft` as a hypothesis.  The DAT-glue route does not escape this either: `PicRepDatum.lft` is a
structure *field* and `PicRepDatum.toJacobianData` only carries it across, so the certificate was
an assumption there too.

Two things this file does **not** claim, both of which an earlier draft of this header got wrong
and which are corrected here rather than annotated:

* it does not claim `Challenge.lean` routes through `JacobianData`.  The frozen `Jacobian` is a
  `sorry` and does not import this layer; `Jacobian C := (jacobianData C).J` is the *planned*
  discharge route recorded in `JacobianData.lean`/`JacobianDataCharts.lean`, and no `jacobianData`
  producer exists in either project;
* it does not claim the certificate is untracked on the board.  The `dat-glue` row has named "the
  locally-of-finite-type certificate" in its title since 2026-07-16.  What was missing is a proof,
  not a mention.

## What is actually owed, and it is much less than the gap suggests

`Picard/Pic0ChartPair.lean` states, in prose, that the certificate is "inherited by every
restriction: being locally of finite type is local on the source, and an open immersion is
locally of finite type".  That sentence is correct and had never been proved — the shape this
workspace has repeatedly found to be the least-audited kind of claim.  Discharged here, and the
two ingredients are cheap:

* `chartHom_restrictChart` (`Pic0ChartPair.lean`) and `chartHom_abelSigmaChart`
  (`Pic0AtlasFromDivRep.lean`) identify the structure morphism of a *restricted Abel chart* as
  `V.ι ≫ D.hom`;
* mathlib's composition instance for `LocallyOfFiniteType` closes the rest, with an open
  immersion on the left — `inferInstance` alone, no lemma.

So the fourth antecedent, at the **real** atlas (heterogeneous parameters, restricted charts —
`mixedParamChart`, `Picard/Pic0ChartAtlasParamFree.lean`), reduces to
`LocallyOfFiniteType (D i).hom`: a property of the divisor scheme with no Picard content, no
chart parameter, and no dependence on the open `V i`.

**And that reduction is not a relocation, for a reason stronger than a carrier match.**
`LocallyOfFiniteType (D i).hom` is a property of the *functor* `divFunctor C π n`, not of the
representing object chosen for it: any two representing objects are isomorphic over the base
(`Functor.RepresentableBy.uniqueUpToIso`), and `LocallyOfFiniteType` transports across an
isomorphism in the slice.  So **no producer of `rep` can pick a `D` that fails `hD`**, at any
parameter — `locallyOfFiniteType_of_representableBy` below.

That matters because the contingent argument is weaker in exactly the place it would be tested.
At the carrier today's producers return — `DivOver`, a local notation for `divSchemeOver …` in
`DivRepGlobalClassify.lean` / `DivRepChartRange.lean` / `DivRepAffPullClause.lean` — the property
is a *global instance* (`locallyOfFiniteType_divSchemeOverHom`, `DivSchemeQProj.lean`) and so free
by `inferInstance`.  But `Pic0ChartAtlasParamFree.lean`'s own header records that representations
at parameters other than `g` are not available, so a carrier-specific argument would cover only
the charts whose representing object happens to be that one.  The transport covers all of them,
including parameters whose representing object nobody has built yet.

One incidental measurement, recorded because it is the reason the freeness was not already
visible: `DivRepGlobalClassify.lean` — the file that *defines* `DivOver` — does not import
`DivSchemeQProj.lean`, so inside it neither finiteness instance can be found. Nothing is wrong
with either file; the instances simply never met the carrier.

## Main declarations

* `AlgebraicGeometry.chartHom_mixedParamChart` — the structure morphism of the `i`-th chart of
  the mixed-parameter atlas is `(V i).ι ≫ (D i).hom`.
* `AlgebraicGeometry.locallyOfFiniteType_chartHom_mixedParamChart` — **the fourth antecedent
  discharged** for the real atlas, from `LocallyOfFiniteType (D i).hom` alone.
* `AlgebraicGeometry.locallyOfFiniteType_gluedHom_mixedParamChart` — hence the glued object is
  locally of finite type over the base field, which is the `JacobianData` field itself.
* `AlgebraicGeometry.locallyOfFiniteType_of_representableBy` — **the fourth antecedent is
  representation-independent**: the certificate depends on the functor, not on the representing
  object, so no producer of `rep` can pick a `D` that fails it.
* `AlgebraicGeometry.jacobianDataOfMixedParamCharts` — **the assembly**: the mixed-parameter
  atlas plus `hf`, local surjectivity, per-index `LocallyOfFiniteType (D i).hom` and
  quasi-compactness of the glued object produce `JacobianData C`.  Landed so that the obligations
  that remain are visible in **one signature** rather than spread over four files.  Of its inputs,
  `hD` is discharged; `hf`, the local-surjectivity instance, `rep` **and `hcpt`** remain open —
  four, not three, and `hcpt` is an explicit hypothesis of the signature.

## What this does NOT do, stated plainly

It closes no gate of the seam.  `IsChartUniv` (`hf`), Zariski-local surjectivity and `rep` are
untouched and remain unproduced, and each is another lane's target.  The `quasiCompact` field is
*not* discharged here either, and it is now the exposed one: for the class-indexed atlas it is
genuinely a-posteriori — `JacobianDataCharts.lean` records that `CompactSpace` of the *glued*
object is a theorem about the Jacobian rather than a consequence of the atlas, and the producer
that supplies it from a surjective Abel map lives in `Picard/JacobianDataAbelImage.lean`, outside
this file's import closure.  Note the distinction, since the two are easy to conflate: *per-chart*
compactness is free at the divisor scheme (below), while the *glued* form is not implied by it for
an infinite atlas.

**CORRECTED 2026-07-30 (`Picard/Pic0AtlasCompactNoetherian.lean`): "per-chart compactness is free
at the divisor scheme" is about the wrong object.**  The charts of the atlas are not the
representing objects — `mixedParamChart` is `restrictChart … (V i)`, whose source is
`yoneda.obj ((V i : Scheme))`, an **open subscheme** of `(D i).left`.  Compactness does not pass
to open subspaces, and `CompactSpace (V : Scheme)` for `V` an open of `divSchemeOver` is **not**
an instance (measured: `infer_instance` fails).  The `Discharged` example below is true of
`divSchemeOver` and is not the hypothesis `Scheme.OpenCover.compactSpace` consumes.  What makes
the per-chart half genuinely free is *local noetherianity* — the structure morphism is locally of
finite type over `Spec k`, so the inclusion of an open is quasi-compact
(`compactSpace_isOpen_divSchemeOver`).  The conclusion of that paragraph survives; its reason did
not.  And the property belongs to the *functor*, not to this carrier:
`compactSpace_of_representableBy` there is the companion of
`locallyOfFiniteType_of_representableBy` below.

What is removed is a fourth undischarged antecedent — proved nowhere, though the `dat-glue` row
did name it — so that discharging the three tracked antecedents now genuinely reaches the datum
the north star's planned route consumes.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The structure morphism of a chart of the real atlas -/

variable (C π) in
/-- **The structure morphism of the `i`-th chart of the mixed-parameter atlas** is the
inclusion of `V i` followed by the structure morphism of the `i`-th representing object.

Both ingredients were already in the tree and had never been composed: `chartHom_restrictChart`
moves `chartHom` across a restriction, and `chartHom_abelSigmaChart` identifies the unrestricted
Abel chart's structure morphism as `D.hom`.  Note that the chart *parameter* `nn i`, the twist
exponent `m i` and the chart index `Z i` do not occur on the right-hand side: the finiteness of a
chart is independent of the heterogeneity this atlas exists to permit. -/
lemma chartHom_mixedParamChart {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens) (i : ι) :
    chartHom C (mixedParamChart C π nn D rep m Z hdeg V) i = (V i).ι ≫ (D i).hom :=
  (chartHom_restrictChart _ (V i) i).trans (by rw [chartHom_abelSigmaChart])

/-! ## The fourth antecedent -/

variable (C π) in
/-- **THE FOURTH ANTECEDENT OF THE NORTH STAR, DISCHARGED AT THE REAL ATLAS**: each chart of the
mixed-parameter atlas is locally of finite type over the base field as soon as its representing
object is.

This is the `hlft` hypothesis that `JacobianData.ofCharts` and all three of its variants carry
and that the board's three-antecedent picture omits.  `Pic0ChartPair.lean` asserts the inheritance
in prose; this is the proof, and it consumes nothing but `chartHom_mixedParamChart` and mathlib's
composition instance — an open immersion is locally of finite type and the property is stable
under composition.

The hypothesis is a statement about the divisor scheme alone.  In particular it does not mention
`pic⁰`, the chart parameter, the twist, or the open `V i` — so it is discharged for *every*
restriction of a chart at once, and a lane that produces `rep` at a parameter automatically
supplies it whenever the representing object is of finite type over `k`. -/
theorem locallyOfFiniteType_chartHom_mixedParamChart {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (hD : ∀ i, LocallyOfFiniteType (D i).hom) (i : ι) :
    LocallyOfFiniteType (chartHom C (mixedParamChart C π nn D rep m Z hdeg V) i) := by
  rw [chartHom_mixedParamChart]
  haveI := hD i
  infer_instance

/-! ## The glued object, and the assembly to the north star's datum -/

variable (C π) in
/-- **The glued object of the real atlas is locally of finite type over the base field** — the
`JacobianData.locallyOfFiniteType` field itself, from a property of the divisor schemes.

`locallyOfFiniteType_gluedHom` descends the certificate from the charts (the property is local on
the source and the glue maps cover), and the previous theorem supplies the charts.  Note that no
finiteness of the index type is used anywhere on this route: the certificate descends to an
infinite atlas exactly as it does to a finite one, which matters because the classical atlas is
indexed by divisor classes. -/
theorem locallyOfFiniteType_gluedHom_mixedParamChart {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (mixedParamChart C π nn D rep m Z hdeg V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg V))]
    (hD : ∀ i, LocallyOfFiniteType (D i).hom) :
    LocallyOfFiniteType (gluedHom C (mixedParamChart C π nn D rep m Z hdeg V) hf) :=
  locallyOfFiniteType_gluedHom C _ hf
    (locallyOfFiniteType_chartHom_mixedParamChart C π nn D rep m Z hdeg V hD)

variable (C π) in
/-- **THE ASSEMBLY: the real atlas produces the north star's datum.**

Every obligation of `JacobianData C` at the mixed-parameter restricted atlas, in one signature.
Read it as the corrected antecedent list of the *goal*:

* `rep` — a representation of the divisor functor at each parameter.  **Open** (another lane's
  target; `Pic0AtlasFromDivRep.lean` takes it as a hypothesis and constructs no representation);
* `hf` — the per-index chart certificate, i.e. `IsChartUniv`.  **Open**;
* the `Presheaf.IsLocallySurjective` instance — DAT-B coverage.  **Open**;
* `hD` — `LocallyOfFiniteType (D i).hom`.  **Discharged**, and at the carrier the producers of
  `rep` return it is free by `inferInstance` (the `Discharged` section above).  So a lane that
  produces `rep` supplies this input in the same breath;
* `hcpt` — `CompactSpace` of the glued object.  **Open**, and it is the input this file leaves
  exposed.  `JacobianDataCharts.lean` calls it a-posteriori for the class-indexed atlas — a
  theorem about the Jacobian, supplied there from a surjective Abel map (`JacobianDataAbelImage`,
  outside this closure).

  **CORRECTED 2026-07-30 (`Picard/Pic0AtlasCompactFromClass.lean`, inbox `I-1132`): `hcpt` is
  not atlas-specific and there is a THIRD route.**  Two things measured there:
  `compactSpace_glued_iff_quasiCompact` shows `hcpt` is *interderivable* with
  `QuasiCompact (gluedHom …)` over the affine base — i.e. it **is** the `JacobianData.quasiCompact`
  field, not an extra input, so the `dat-glue` and `dat-j` rows were holding one obligation
  between them; and `compactSpace_glued_of_pic0_class` supplies it from the `dat-j.qcfield`
  hypothesis `hcl` applied to *this atlas's own* representation, needing no Abel morphism and no
  index finiteness.

  **Two qualifications on that correction** (`review-ajcr`, `I-1162`), because the first sentence
  reads as though a reduction had been discovered this round.  (a) The `mpr` half — the direction
  that turns `hcpt` into the field — is not new and was never merely available: it is the existing
  producer's *implementation*.  `JacobianData.ofChartsOfCompactSpace` (`JacobianDataCharts.lean:216`)
  builds the `quasiCompact` field as literally `HasAffineProperty.iff_of_isAffine.mpr hcpt`, and has
  done since `9d99b0451d` (2026-07-27).  What is genuinely new is the `mp` direction — HEAD's only
  use of `iff_of_isAffine.mp` on this seam — which is what upgrades "the two rows name the same
  obligation" from an observation about the producer to a theorem that no route can pay one side and
  still owe the other.  (b) The two propositions are about *different objects*: `hcpt` is
  `CompactSpace` of the glued **chart** object, while `JacobianData.quasiCompact` is
  `QuasiCompact J.hom` for the **representing** object `J`.  They coincide here only because
  `ofChartsOfCompactSpace_J` (`:219`) makes `J = gluedOfCharts C f hf` by `rfl`; the `iff` itself is
  stated for `gluedHom`.  A lane that swaps the representing carrier breaks that identification
  without touching the `iff`.  So "the two routes the tree already names are still the honest ones" below
  is an incomplete enumeration.  What that file does **not** change: `hcl` has no producer, so
  nothing is discharged.  But that is the board's pricing quoted, **not** a measurement made here,
  and it is a genuine obligation rather than a repackaging of coverage.  That was worth checking,
  since `review-ajcr` observed that at `ι = PEmpty` every explicit input including `hcpt` is free
  and read it as evidence that `hcpt` is a *consequence* of the local-surjectivity instance.
  Measured: with `hf` and that instance in scope and nothing else, `CompactSpace` of the glued
  object does not follow, and the single missing ingredient on the route that does prove it
  (`GlueData.openCover.compactSpace`) is `Finite …openCover.I₀` — not chart compactness, not
  coverage.  The `PEmpty` observation is explained by `PEmpty` being *finite*, so it attributes to
  coverage what index finiteness supplies.  Since a failing synthesis measures the instance graph
  and not the mathematics, the claim is the careful one: nothing in scope derives `hcpt` from
  coverage, and the gap is finiteness — which the class-indexed atlas does not have.  So the two
  routes the tree already names are still the honest ones: a finite atlas, or the Abel image.
  **That last sentence is corrected above**: a third route (the `dat-j.qcfield` class hypothesis
  at this atlas's own representation) needs neither, and `hcpt` is the `quasiCompact` field
  rather than a separate input — `Picard/Pic0AtlasCompactFromClass.lean`.

So this declaration is an *implication*, not a witness: it produces no `JacobianData` at any curve
until the four open inputs above are produced.  Its value is that the fourth antecedent is no
longer among them, and that the list is now checkable in one place instead of being distributed
over `JacobianDataCharts`, `Pic0ChartPair`, `Pic0AtlasFromDivRep` and
`Pic0ChartAtlasParamFree`. -/
def jacobianDataOfMixedParamCharts {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (mixedParamChart C π nn D rep m Z hdeg V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg V))]
    (hD : ∀ i, LocallyOfFiniteType (D i).hom)
    (hcpt : CompactSpace (Scheme.LocalRepresentability.glueData hf).glued) :
    JacobianData C :=
  JacobianData.ofChartsOfCompactSpace C _ hf
    (locallyOfFiniteType_chartHom_mixedParamChart C π nn D rep m Z hdeg V hD) hcpt

/-! ## `hD` is a RIDER on antecedent 3, not an independent obligation -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
variable (C π) in
/-- **The chart-finiteness certificate is representation-independent.**

If `divFunctor C π n` is represented by `D` and also by `D'`, and `D'.hom` is locally of finite
type, then so is `D.hom`.  Representing objects are isomorphic over the base
(`Functor.RepresentableBy.uniqueUpToIso`), the isomorphism's underlying morphism commutes with the
structure morphisms (`Over.w`), and `LocallyOfFiniteType` is preserved by precomposition with an
isomorphism.

**This is what makes the fourth antecedent a rider on the third rather than a peer of it.**  A
producer of `rep` does not get to choose a representing object that fails `hD`: the property
belongs to the functor.  In particular the discharge does not depend on today's representing
object being `divSchemeOver`, and it covers the parameters `n ≠ g` at which
`Pic0ChartAtlasParamFree.lean` records that no representation has been built — a carrier-specific
argument would not.

Stated with `D'` explicit rather than as an instance so that the direction of use is visible: one
exhibits *some* representing object of finite type, and every other one inherits it.

A measurement rather than a claim, and it is independent evidence for the reading above: the proof
uses none of the curve's geometry — not smoothness, not properness, not geometric irreducibility
(hence the `omit`).  A statement about the divisor scheme's finiteness would need the curve; this
one needs only that the functor is represented twice. -/
theorem locallyOfFiniteType_of_representableBy {n : ℕ} {D D' : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (rep' : (divFunctor C π n).RepresentableBy D')
    (h : LocallyOfFiniteType D'.hom) :
    LocallyOfFiniteType D.hom := by
  have e := rep.uniqueUpToIso rep'
  haveI := h
  rw [← Over.w e.hom]
  infer_instance

/-! ## `hD` is not merely reduced to — it is DISCHARGED at the carrier the producer returns

The theorems above take `hD : ∀ i, LocallyOfFiniteType (D i).hom` as a hypothesis, which by
itself would only *relocate* the fourth antecedent.  It does not: the divisor-representability
lane's producers all return `RepresentableBy DivOver` with `DivOver` a local notation for
`divSchemeOver …` (`DivRepGlobalClassify.lean`, `DivRepChartRange.lean`,
`DivRepAffPullClause.lean`), and at *that* carrier both finiteness inputs are global instances
(`locallyOfFiniteType_divSchemeOverHom`, `compactSpace_divScheme`, `DivSchemeQProj.lean`).

Worth recording precisely, because the two are easy to confuse and the difference is the whole
value of this section: the instances hold *at the carrier*, and they were nevertheless not in
scope where the carrier is defined — `DivRepGlobalClassify.lean` does not import
`DivSchemeQProj.lean`, so inside that file neither is findable.  Importing `DivSchemeQProj` here
is what makes them available to a consumer of this module, and it is why the examples below are
`inferInstance` rather than named applications. -/

section Discharged

open Scheme

variable (k) in
/-- **The fourth antecedent is free at the divisor-representability lane's own carrier**: for a
`divSchemeOver`, `LocallyOfFiniteType` of the structure morphism needs no hypothesis.

So a lane that produces `rep` supplies `hD` at the same moment, at no cost, and the fourth
antecedent is *discharged* rather than relocated. -/
example {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
    (A B : X.CurveDivisor) (n r₁ r₂ : ℕ)
    (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
    (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤)) :
    LocallyOfFiniteType (divSchemeOver k A B n r₁ r₂ b₁ b₂).hom :=
  inferInstance

variable (k) in
/-- **And so is the compactness input** of `JacobianData.ofCharts`'s finite route, at the same
carrier — `DivScheme` is a closed subscheme of the compact Grassmannian pair.

This does **not** discharge `hcpt` of the assembly below, and the distinction matters: `hcpt` is
`CompactSpace` of the **glued** object, which for a class-indexed atlas is not the compactness of
any one chart.

**AND IT IS ALSO NOT "exactly the hypothesis of the finite-index route", which is what an earlier
version of this docstring said.**  `JacobianData.ofCharts` / `Scheme.OpenCover.compactSpace` want
`CompactSpace (X i)` for the *chart* objects, and the charts of `mixedParamChart` are
`(V i : Scheme)` — **opens** of the representing object, not the object.  Compactness is not
inherited by open subspaces, and `infer_instance` fails on `CompactSpace (V : Scheme)` for `V` an
open of `divSchemeOver` (measured).  So this example is a true statement about the wrong object.
The per-chart half *is* free, by noetherianity rather than by this instance:
`compactSpace_isOpen_divSchemeOver` (`Picard/Pic0AtlasCompactNoetherian.lean`), which is outside
this file's import closure because that module imports this one. -/
example {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
    (A B : X.CurveDivisor) (n r₁ r₂ : ℕ)
    (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
    (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤)) :
    CompactSpace (divSchemeOver k A B n r₁ r₂ b₁ b₂).left :=
  inferInstance

end Discharged

@[simp]
lemma jacobianDataOfMixedParamCharts_J {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (mixedParamChart C π nn D rep m Z hdeg V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg V))]
    (hD : ∀ i, LocallyOfFiniteType (D i).hom)
    (hcpt : CompactSpace (Scheme.LocalRepresentability.glueData hf).glued) :
    (jacobianDataOfMixedParamCharts C π nn D rep m Z hdeg V hf hD hcpt).J
      = gluedOfCharts C (mixedParamChart C π nn D rep m Z hdeg V) hf :=
  rfl

end

end AlgebraicGeometry
