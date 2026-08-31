/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianData
import AlgebraicJacobian.Picard.Pic0SigmaSheaf

/-!
# Producing the Jacobian representability datum from a Zariski chart family

The pinned datum `JacobianData C` of the curve `C` bundles a representing object for the
degree-zero Picard functor together with the two finiteness certificates of that object.
This file constructs it: first from a bare representation (`JacobianData.ofRepresentableBy`),
and then — the substance — from a Zariski chart family of the Σ-extension sheaf, whose glued
scheme is the representing object and whose charts carry the finiteness.

## Main declarations

* `AlgebraicGeometry.JacobianData.ofRepresentableBy` — a representation of `pic0TypeFunctor C`
  by `J`, plus `LocallyOfFiniteType J.hom` and `QuasiCompact J.hom`, is a `JacobianData C`.
* `AlgebraicGeometry.gluedHom` / `AlgebraicGeometry.gluedOfCharts` — the glued scheme of a chart
  family, placed over the base field by the Σ-component of the universal element of the
  representation it induces.
* `AlgebraicGeometry.chartHom` — the structure morphism `X i ⟶ Spec k` of the `i`-th chart:
  the Σ-component of the element of `pic0SigmaFunctor C` classified by `f i`.
* `AlgebraicGeometry.toGlued_comp_gluedHom` — **the compatibility of the two**: the glue map
  `X i ⟶ gluedOfCharts` composed with the structure morphism of the glued object is exactly
  `chartHom i`.  So the charts are charts *over the base field*, and the glued object is
  covered by them as a `k`-scheme.
* `AlgebraicGeometry.locallyOfFiniteType_gluedHom` — being locally of finite type is local
  on the source, so it descends from the charts to the glued object.
* `AlgebraicGeometry.quasiCompact_gluedHom` — over the affine base `Spec k`, quasi-compactness
  of the glued object is compactness of its space, which a finite family of compact charts
  supplies.
* `AlgebraicGeometry.JacobianData.ofCharts` — **the first producer of the Jacobian datum**:
  a finite Zariski chart family of relatively representable open immersions into
  `pic0SigmaSheaf C`, jointly locally surjective, with quasi-compact charts that are locally of
  finite type over `k`, yields `JacobianData C`.

## The hypothesis bundle

Every declaration here carries exactly the three hypotheses of the frozen `Jacobian` of
`Challenge.lean` — `IsProper`, `SmoothOfRelativeDimension 1`, `GeometricallyIrreducible`.  The
`GeometricallyReduced C.hom` hypothesis of `Pic0SigmaSheaf.lean` is *not* an extra assumption:
a morphism smooth of relative dimension `1` is smooth (`Smooth.of_smoothOfRelativeDimension_one`)
and a smooth morphism is geometrically reduced (`Smooth.geometricallyReduced`), both global
instances of `AlgebraicJacobian.Curve.GeometricallyReduced`, so instance resolution supplies it
from the frozen bundle.  The `example` at the end of this file is the machine-checked record.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

/-! ## Packaging a representation as the datum -/

/-- **Package a representation of the degree-zero Picard functor**, with its two finiteness
certificates, as the pinned Jacobian datum.  The representation is stated in the
`pic0TypeFunctor` spelling; that abbreviation unfolds to the `forget₂ ⋙ forget` massage that
`JacobianData.rep` is typed against. -/
noncomputable def JacobianData.ofRepresentableBy (J : Over (Spec (.of k)))
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hlft : LocallyOfFiniteType J.hom) (hqc : QuasiCompact J.hom) :
    JacobianData C where
  J := J
  rep := rep
  locallyOfFiniteType := hlft
  quasiCompact := hqc

@[simp]
lemma JacobianData.ofRepresentableBy_J (J : Over (Spec (.of k)))
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hlft : LocallyOfFiniteType J.hom) (hqc : QuasiCompact J.hom) :
    (JacobianData.ofRepresentableBy C J rep hlft hqc).J = J :=
  rfl

@[simp]
lemma JacobianData.ofRepresentableBy_rep (J : Over (Spec (.of k)))
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hlft : LocallyOfFiniteType J.hom) (hqc : QuasiCompact J.hom) :
    (JacobianData.ofRepresentableBy C J rep hlft hqc).rep = rep :=
  rfl

/-- The universal property of a packaged datum is the packaged representation. -/
@[simp]
lemma JacobianData.homEquiv_ofRepresentableBy (J : Over (Spec (.of k)))
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (hlft : LocallyOfFiniteType J.hom) (hqc : QuasiCompact J.hom)
    {T : Over (Spec (.of k))} (g : T ⟶ J) :
    (JacobianData.ofRepresentableBy C J rep hlft hqc).homEquiv g = rep.homEquiv g :=
  rfl

/-! ## The chart family and its glued object -/

section Charts

variable {ι : Type u} {X : ι → Scheme.{u}}
  (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)

/-- **The structure morphism of the `i`-th chart** over the base field: the Σ-component of the
element of `pic0SigmaFunctor C` classified by `f i`.  A chart of the degree-zero Picard sheaf
is by construction a scheme *together with* a map to `Spec k`, namely the base over which the
line bundle it classifies lives; this is that map. -/
noncomputable def chartHom (i : ι) : X i ⟶ Spec (.of k) := (yonedaEquiv (f i)).1

variable (hf : ∀ i, IsOpenImmersion.presheaf (f i))
variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]

/-- **The structure morphism of the glued object of a chart family**: mathlib's 01JJ engine
glues the charts into a scheme representing the Σ-extension sheaf, and the Σ-component of the
universal element of that representation is the map of that scheme to `Spec k`. -/
noncomputable abbrev gluedHom :
    (Scheme.LocalRepresentability.glueData hf).glued ⟶ Spec (.of k) :=
  ((Scheme.LocalRepresentability.representableBy hf).homEquiv
    (𝟙 (Scheme.LocalRepresentability.glueData hf).glued)).1

/-- **The glued object of a chart family**, as a scheme over the base field.  This is the
object represented by `pic0RepresentableByOfCharts`. -/
noncomputable abbrev gluedOfCharts : Over (Spec (.of k)) := Over.mk (gluedHom C f hf)

/-- The universal element of the glued representation restricts along the `i`-th glue map to
the element classified by `f i`. -/
lemma representableBy_homEquiv_toGlued (i : ι) :
    (Scheme.LocalRepresentability.representableBy hf).homEquiv
      (Scheme.LocalRepresentability.toGlued hf i) = yonedaEquiv (f i) :=
  Scheme.LocalRepresentability.yonedaGluedToSheaf_app_toGlued hf

/-- **The charts are charts over the base field**: the `i`-th glue map into the glued object,
followed by the structure morphism of the glued object, is the structure morphism of the `i`-th
chart.  Both sides are Σ-components of the same restriction of the universal element. -/
lemma toGlued_comp_gluedHom (i : ι) :
    Scheme.LocalRepresentability.toGlued hf i ≫ gluedHom C f hf = chartHom C f i := by
  have h := congrArg Sigma.fst
    ((Scheme.LocalRepresentability.representableBy hf).homEquiv_eq
      (Scheme.LocalRepresentability.toGlued hf i))
  rw [representableBy_homEquiv_toGlued] at h
  exact h.symm

/-! ## The two finiteness certificates from the charts -/

/-- **Locally of finite type descends from the charts**: the property is local on the source
and the glue maps of the glue data cover the glued object, so if each chart is locally of finite
type over the base field then so is the glued object. -/
theorem locallyOfFiniteType_gluedHom (hlft : ∀ i, LocallyOfFiniteType (chartHom C f i)) :
    LocallyOfFiniteType (gluedHom C f hf) := by
  refine IsZariskiLocalAtSource.of_openCover
    (P := @LocallyOfFiniteType) (Scheme.LocalRepresentability.glueData hf).openCover fun i => ?_
  have h := hlft i
  rwa [← toGlued_comp_gluedHom C f hf i] at h

/-- **Quasi-compactness descends from a finite family of quasi-compact charts**: the base
`Spec k` is affine, so quasi-compactness of the structure morphism is compactness of the space
of the glued object, and that space is the union of the finitely many compact chart images. -/
theorem quasiCompact_gluedHom [Finite ι] (hcpt : ∀ i, CompactSpace (X i)) :
    QuasiCompact (gluedHom C f hf) := by
  haveI : Finite (Scheme.LocalRepresentability.glueData hf).openCover.I₀ := ‹Finite ι›
  haveI : ∀ i, CompactSpace ((Scheme.LocalRepresentability.glueData hf).openCover.X i) := hcpt
  haveI : CompactSpace (Scheme.LocalRepresentability.glueData hf).glued :=
    (Scheme.LocalRepresentability.glueData hf).openCover.compactSpace
  exact HasAffineProperty.iff_of_isAffine.mpr ‹_›

/-! ## The producer -/

/-- **The first producer of the Jacobian datum**: a Zariski chart family of relatively
representable open immersions into the Σ-extension sheaf of the degree-zero Picard functor,
jointly locally surjective, indexed by a finite type, with quasi-compact charts that are locally
of finite type over the base field, produces the pinned representability datum of the curve.

The representing object is the glued scheme of the family, placed over `Spec k` by the
Σ-component of the universal element; the two certificates are `locallyOfFiniteType_gluedHom`
and `quasiCompact_gluedHom`. -/
noncomputable def JacobianData.ofCharts [Finite ι]
    (hlft : ∀ i, LocallyOfFiniteType (chartHom C f i))
    (hcpt : ∀ i, CompactSpace (X i)) :
    JacobianData C :=
  JacobianData.ofRepresentableBy C (gluedOfCharts C f hf)
    (pic0RepresentableByOfCharts C f hf)
    (locallyOfFiniteType_gluedHom C f hf hlft)
    (quasiCompact_gluedHom C f hf hcpt)

@[simp]
lemma JacobianData.ofCharts_J [Finite ι]
    (hlft : ∀ i, LocallyOfFiniteType (chartHom C f i))
    (hcpt : ∀ i, CompactSpace (X i)) :
    (JacobianData.ofCharts C f hf hlft hcpt).J = gluedOfCharts C f hf :=
  rfl

/-- **The producer for an infinite atlas**: same as `JacobianData.ofCharts`, but the index type
is arbitrary and quasi-compactness of the glued object is supplied directly instead of being
derived from finitely many compact charts.

This is the form the classical construction needs.  The charts of the degree-zero Picard functor
are indexed by divisor *classes* — one chart per class whose twisted fibre class has an effective
witness — and that index set is not finite; compactness of the glued object is then a genuine
theorem about the Jacobian (it is the union of the images of a *quasi-compact* divisor scheme
under the Abel map), not a consequence of finiteness of the atlas.  Note that the
locally-of-finite-type certificate still descends from the charts with no finiteness hypothesis
whatsoever: `locallyOfFiniteType_gluedHom` never uses `Finite ι`. -/
noncomputable def JacobianData.ofChartsOfCompactSpace
    (hlft : ∀ i, LocallyOfFiniteType (chartHom C f i))
    (hcpt : CompactSpace (Scheme.LocalRepresentability.glueData hf).glued) :
    JacobianData C :=
  JacobianData.ofRepresentableBy C (gluedOfCharts C f hf)
    (pic0RepresentableByOfCharts C f hf)
    (locallyOfFiniteType_gluedHom C f hf hlft)
    (HasAffineProperty.iff_of_isAffine.mpr hcpt)

@[simp]
lemma JacobianData.ofChartsOfCompactSpace_J
    (hlft : ∀ i, LocallyOfFiniteType (chartHom C f i))
    (hcpt : CompactSpace (Scheme.LocalRepresentability.glueData hf).glued) :
    (JacobianData.ofChartsOfCompactSpace C f hf hlft hcpt).J = gluedOfCharts C f hf :=
  rfl

end Charts

/-! ## The hypothesis bundle of the frozen `Jacobian` suffices

`Pic0SigmaSheaf.lean` introduces `[GeometricallyReduced C.hom]` before its sheaf and
representability statements, while the frozen `Jacobian` of `Challenge.lean` carries only
`IsProper`, `SmoothOfRelativeDimension 1` and `GeometricallyIrreducible`.  There is no gap:
geometric reducedness is *derived* from smoothness of relative dimension one by the global
instances of `AlgebraicJacobian.Curve.GeometricallyReduced`, which is in the import closure of
`Pic0SigmaSheaf.lean`.  Hence every declaration above elaborates under the frozen bundle alone,
and the example below records it. -/

example : GeometricallyReduced C.hom := inferInstance

/-! ## What remains

`JacobianData.ofCharts` reduces the frozen `Jacobian` of `Challenge.lean` — that is, the
production of `jacobianData C : JacobianData C`, from which `Jacobian C := (jacobianData C).J` —
to a single geometric statement about the degree-zero Picard sheaf of the curve, namely the
existence of a finite Zariski atlas:

> there exist a finite index type `ι`, schemes `X : ι → Scheme`, and morphisms of presheaves
> `f i : yoneda.obj (X i) ⟶ pic0SigmaFunctor C` such that
>
> 1. **(relative representability)** each `f i` is a relatively representable open immersion,
>    `IsOpenImmersion.presheaf (f i)`;
> 2. **(coverage)** the family is jointly locally surjective for the big Zariski topology,
>    `Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)`;
> 3. **(chart finiteness)** each chart is locally of finite type over the base field with
>    respect to its own structure morphism, `LocallyOfFiniteType (chartHom C f i)`, and each
>    chart space is quasi-compact, `CompactSpace (X i)`.

Nothing else about the Picard functor is needed: the sheaf condition is already discharged
(`pic0SigmaFunctor_isSheaf`), the gluing is mathlib's (`Scheme.LocalRepresentability`), the
Σ-descent to the slice is already discharged (`Functor.RepresentableBy.overSlice`), and the two
certificates of the glued object are discharged here from (3).

Conditions (1) and (2) are the geometric input — they are what the divisor-scheme/Abel-map
machinery of the `DivScheme…` and `DivRep…` files exists to produce, one chart being carved out
of a symmetric power of the curve by an effectivity locus.  Condition (3) is a property of those
charts alone and does not interact with the Picard functor at all.

If the atlas that machinery produces is *not* finitely indexed — and the classical one is not,
its charts being indexed by divisor classes — then `JacobianData.ofChartsOfCompactSpace` is the
form to use: `ι` is then arbitrary, condition (3) weakens to `LocallyOfFiniteType (chartHom C f i)`
alone, and the second certificate becomes the single statement `CompactSpace` of the glued
object.  That statement is not a bookkeeping hypothesis but a theorem about the Jacobian — the
underlying space is the image of a quasi-compact divisor scheme under the Abel map — and it is
where the quasi-compactness content of the construction actually lives. -/

end AlgebraicGeometry
