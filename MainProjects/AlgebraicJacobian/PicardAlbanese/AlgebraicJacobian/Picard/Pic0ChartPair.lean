/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartLocusIsOpen
import AlgebraicJacobian.Picard.Pic0AtlasFromDivRep

/-!
# C9b: the restricted chart map and the `(f, hf)` pair

`Picard/Pic0AtlasFromDivRep.lean` builds the Abel chart map `abelSigmaChart` out of a
representation of the divisor functor, and its header states — correctly — that
`IsOpenImmersion.presheaf (abelSigmaChart …)` is **false as stated for the whole divisor
scheme**: the Abel map has projective spaces `|D|` as fibres, so it is not even a
monomorphism.  It becomes an open immersion only after restriction to the locus where the
fibre is a single point.

This file supplies the restriction, which is the half of C9b that needs no new mathematics
once `chartLocus` exists — and it makes precise which half does.

## What C9b consists of, and which part is here

`pic0RepresentableByOfCharts` (`Picard/Pic0SigmaSheaf.lean:161`) consumes a pair
`(f, hf)`.  Producing it from `abelSigmaChart` factors into exactly two steps:

1. **restrict the source along an open immersion** — `restrictChart` below.  Given any open
   `V ⊆ D.left`, precomposing `abelSigmaChart` with `yoneda.map V.ι` gives a chart map out of
   `V`, and this is a *composition* of presheaf morphisms.  Landed here, sorry-free.
2. **certify the restricted map an open immersion of presheaves** — the honest content.
   `IsOpenImmersion.presheaf` (mathlib `MorphismProperty.relative`) has two clauses:
   relative representability, and the open-immersion property of every represented pullback.
   Step 1 supplies the *left* factor of both clauses for free
   (`isOpenImmersion_presheaf_yoneda_map_of_isOpenImmersion` +
   `MorphismProperty.relative_isStableUnderComposition`), so what remains is exactly the
   corresponding statement for `abelSigmaChart` restricted to `V = chartLocus`, i.e.
   CHART-U(c): on the chart locus the Abel map is a bijection onto its image because the
   normalized effective representative is unique there (DAT-C GAP-2).

So: the *composition* half of the `hf` certificate is discharged here, unconditionally; the
*chart-locus* half is CHART-U(c) and is stated but not proved (it needs GAP-2 plus the
classifier, and the openness of the locus itself, `Pic0ChartLocusIsOpen`).

## CORRECTION 2026-07-29: step 2 above is itself TWO clauses, not one

The description of step 2 as "*the* honest content" is right that it is not bookkeeping and
wrong that it is a single obligation.  `IsOpenImmersion.presheaf` conjoins **relative
representability** (the fibre product is a scheme at all) with **the property clause** (each
represented pullback is an open immersion).  The GAP-2/classifier story is the input to the
second only.  The first needs just an open of the test, and `chartLocus` is one
unconditionally — so it is not CERT-Σ-gated at all.

That split is landed: `Picard/Pic0ChartOpenImmersionCriterion.lean` (the criterion, from
elementwise data) and `Picard/Pic0ChartUnivReduce.lean` (instantiated at the Abel chart,
reducing the datum from four fields to three).  `IsChartUniv` below is unchanged as a
*statement* — it is still the right pin — but it is no longer the right unit of *pricing*.
Read `isChartUniv_of_isChartLocusFibre` for what a lane now actually owes.

## Main declarations

* `AlgebraicGeometry.isOpenImmersion_presheaf_yoneda_map` — an open immersion of schemes is
  an open immersion of presheaves under yoneda.  This is mathlib's `relative_map` at
  `P := IsOpenImmersion`, recorded once with the instances it needs discharged.
* `AlgebraicGeometry.restrictChart` — the chart map restricted to an open of the source.
* `AlgebraicGeometry.isOpenImmersion_presheaf_restrictChart` — **the composition half of
  `hf`**: if the unrestricted chart map is an open immersion of presheaves, so is any
  restriction of it along an open immersion.  Unconditional in the restriction.
* `AlgebraicGeometry.chartHom_restrictChart` — the structure morphism of a restricted chart
  is the restriction of the structure morphism, so the `LocallyOfFiniteType` hypothesis of
  `JacobianData.ofCharts` is inherited (being locally of finite type is local on the
  source).
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

/-! ## An open immersion of schemes is one of presheaves -/

/-- **Open immersions transfer through yoneda**: for an open immersion of schemes
`g : X ⟶ Y`, the induced map of yoneda presheaves satisfies `IsOpenImmersion.presheaf`.

This is mathlib's `MorphismProperty.relative_map` specialised to `F := yoneda` and
`P := @IsOpenImmersion`; the two side conditions it needs — that open immersions are stable
under base change, and that yoneda preserves the relevant pullbacks (it is fully faithful and
`Scheme` has pullbacks) — are discharged by instances.

Recorded as a named lemma because it is the *only* source of `IsOpenImmersion.presheaf`
facts anywhere in this tree that does not go through a chart certificate: every restriction
of a chart map is built from it. -/
theorem isOpenImmersion_presheaf_yoneda_map {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] :
    IsOpenImmersion.presheaf (yoneda.map g) :=
  MorphismProperty.relative_map (P := @IsOpenImmersion) (F := yoneda) ‹IsOpenImmersion g›

/-! ## The restricted chart map -/

/-- **The chart map restricted to an open of its source.**

`f` is the unrestricted chart map (in practice `abelSigmaChart`, whose source is the divisor
scheme) and `V` an open subscheme of the source; the restriction is the composition with the
yoneda image of the open inclusion.

The point of restricting is that the unrestricted Abel map is *not* an open immersion of
presheaves — see the `Pic0AtlasFromDivRep` header — while its restriction to the locus where
the fibre is a single point is.  This definition is neutral about which open `V` is; the
chart-locus choice enters only in the certificate. -/
def restrictChart {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (V : X.Opens) : yoneda.obj (V : Scheme.{u}) ⟶ (pic0SigmaSheaf C).1 :=
  yoneda.map V.ι ≫ f

/-- **The composition half of the `hf` certificate**: a restriction of an open immersion of
presheaves along an open immersion is again one.

`IsOpenImmersion.presheaf` is `MorphismProperty.relative` at `yoneda`, which is stable under
composition (`MorphismProperty.relative_isStableUnderComposition`, needing `yoneda` full and
faithful and `IsOpenImmersion` stable under composition — all instances).  Together with
`isOpenImmersion_presheaf_yoneda_map` this discharges, for free and in full generality, the
part of C9b that is bookkeeping.

What it does NOT discharge, and what is therefore the whole remaining content of C9b: the
hypothesis `hfV`.  For `f := abelSigmaChart` that hypothesis is FALSE for `V = ⊤` and is
expected to be true for `V = chartLocus` — it is CHART-U(c), whose proof needs the
uniqueness of the normalized effective representative (DAT-C GAP-2) and the classifier.  A
lane must not read this lemma as reducing C9b to plumbing; it isolates the plumbing so the
mathematics is visible. -/
theorem isOpenImmersion_presheaf_restrictChart {X : Scheme.{u}}
    {f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1} (V : X.Opens)
    (hfV : IsOpenImmersion.presheaf f) :
    IsOpenImmersion.presheaf (restrictChart f V) :=
  MorphismProperty.IsStableUnderComposition.comp_mem _ _
    (isOpenImmersion_presheaf_yoneda_map V.ι) hfV

/-! ## CHART-U(c): the remaining obligation, pinned

With the composition half discharged, `hf` for a restricted Abel chart reduces to a single
statement.  It is pinned here as a definition so that the gate has a name in Lean and not
only in a worksheet — the pattern `Pic0ChartLocusIsOpen.IsChartDatumPresentation` uses.

**Its field-level input is available.**  DAT-C GAP-2 (Σ-UNIQ-fld) is *landed*:
`Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one`
(`RiemannRoch/EffectiveUniqueness.lean:144`) — for effective `D`, `D'` with equal Čech class
and `h⁰(𝒪(D)) = 1`, `D' = D`.  (The `w4-datc` §0.3 GAP-2 row claimed no such lemma existed;
that claim was stale and is corrected there as of 2026-07-28.)  What CHART-U(c) still needs
beyond it is the *relative* statement — uniqueness in families over the locus — plus the
classifier `divRepClassifyZar`. -/

variable (C π n) in
/-- **CHART-U(c), pinned**: the chart map is an open immersion of presheaves after restriction
to the locus where the fibre class has a unique effective representative.

This is the whole remaining content of C9b's `hf`.  Stated as a `Prop`-valued definition
rather than proved, because its proof needs the *relative* form of GAP-2 over `chartLocus`
together with `divRepClassifyZar`; a lane that discharges it gets `hf` by feeding it to
`isOpenImmersion_presheaf_restrictChart`.

Deliberately stated about `abelSigmaChart` and a *given* open `V`, rather than about
`chartLocus` directly: the openness of `chartLocus` is a separate obligation
(`Pic0ChartLocusIsOpen`), and keeping the two apart means neither has to wait for the
other. -/
def IsChartUniv {D : Over (Spec (.of k))} (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) : Prop :=
  IsOpenImmersion.presheaf (restrictChart (abelSigmaChart C π n rep m Z hdeg) V)

/-- The pinned obligation is exactly what `isOpenImmersion_presheaf_restrictChart` would
give from an unrestricted certificate — recorded so that no lane proves the same thing
twice, and so that the *reason* the unrestricted route is unavailable stays visible: the
hypothesis of that lemma is false for the Abel chart at `V = ⊤`. -/
lemma isChartUniv_of_unrestricted {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens)
    (h : IsOpenImmersion.presheaf (abelSigmaChart C π n rep m Z hdeg)) :
    IsChartUniv C π n rep m Z hdeg V :=
  isOpenImmersion_presheaf_restrictChart V h

/-! ## The structure morphism of a restricted chart -/

/-- **The structure morphism of a restricted chart is the restriction of the structure
morphism.**  Hence the `LocallyOfFiniteType (chartHom …)` hypothesis of
`JacobianData.ofCharts` is inherited by every restriction: being locally of finite type is
local on the source, and an open immersion is locally of finite type.

Concretely, for the Abel chart of a representation `rep` by `D` the unrestricted structure
morphism is `D.hom` (`chartHom_abelSigmaChart`, `Pic0AtlasFromDivRep.lean:212`), so a
restricted Abel chart over `V ⊆ D.left` has structure morphism `V.ι ≫ D.hom`. -/
lemma chartHom_restrictChart {X : Scheme.{u}} (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (V : X.Opens) {ι : Type u} (i : ι) :
    chartHom C (fun _ : ι => restrictChart f V) i
      = V.ι ≫ chartHom C (fun _ : ι => f) i := by
  change (yonedaEquiv (yoneda.map V.ι ≫ f)).1 = V.ι ≫ (yonedaEquiv f).1
  -- Both sides are the Σ-component of the universal element restricted along `V.ι`:
  -- the `Over.sigmaExtension` transition map precomposes the structure morphism, and
  -- `f`'s naturality moves the restriction across `f`.
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  have hnat := congrArg Sigma.fst
    (ConcreteCategory.congr_hom (f.naturality (V.ι).op) (𝟙 X))
  refine hnat.trans ?_
  exact Over.sigmaExtension_map_fst (V.ι) _

end

end AlgebraicGeometry
