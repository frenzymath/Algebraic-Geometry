/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffStalkEval
import AlgebraicJacobian.Picard.DivisorFamilyAffGlueZarKit
import AlgebraicJacobian.Picard.DivisorFamilyAffFace
import AlgebraicJacobian.Picard.DivisorFamilyAffAbel
import AlgebraicJacobian.Picard.DivisorFamilyAffCompare
import AlgebraicJacobian.Picard.DivisorFamilyFieldSurj
import AlgebraicJacobian.Curve.RelativeCurveBridge

/-!
# `hdegAff` DISCHARGED: the widened class-degree law and the widened Abel ledger

`Picard/DivisorFamilyAffAbel.lean` builds the Abel layer on the R2 carrier `DivFamZarAff`
(human decision `I-0492`) but leaves one statement as an explicit hypothesis: `hdegAff`, the
*widened degree ledger* — the widened Abel value of a degree-`n` widened class has degree `n`
at every field point.  Its own docstring (`:296-300`) names what stands between the file and
that hypothesis:

> the chart-typed ledger routes through `DivFamZar.classDeg_picClass`, i.e. from the
> presentation divisor's degree to the Picard class of the widened section, and that transport
> has no widened analogue yet.

**This file supplies that transport and discharges `hdegAff`.**  So
`chartValueAff_mem_pic0Subgroup` (`DivisorFamilyAffAbel.lean:304`) now holds with no
hypothesis beyond the chart-index degree constraint `hdeg`, exactly as its chart-typed twin
`chartValue_mem_pic0Subgroup` does.

## The route, and why it is short

Three observations, in the order that matters:

1. **The degree of the presentation divisor is a `DivEq` invariant.**
   `Scheme.presentationDivisor_eq_of_divEq` rewrites the *divisor* along a `DivEq`, so a
   certificate carried by any system divisor-equal to `d` computes `d`'s presentation degree.
   Composed with `ajcr-p3`'s cover-free identity
   `AffAdaptation.IsCertified.deg_presentationDivisor`
   (`Picard/DivisorFamilyAffStalkEval.lean:660`) this is `deg_presentationDivisor_of_divEq`
   below — two lines, and it needs neither `IsProper C.hom` nor a separation hypothesis.
2. **Over a field the widened pin collapses**, exactly as the chart-typed one does
   (`DivFam.exists_toZar_eq`, `Picard/DivSchemeAbel.lean:77`): a span-`⊤` family over a field
   has a nonzero member, which is a unit, so its away localization *is* `K`, and the local
   certified family transports back along that isomorphism.  The argument is entirely on the
   BASE — no piece, cover, chart or partition occurs — which is why R2, which widened only
   where the pieces live on the curve, does not touch it.
3. **The naturality lemma two hand-offs priced as this row's cost is one line** —
   `CertifiedDivisorFamilyAff.toZarAff_mapAlg` below, `mk_eq_mk_iff.mpr (divEq_refl _)`, the
   widened twin of `DivFam.toZar_mapAlgHom` (`Picard/DivisorFamilyZarVehicle.lean:169`).
   `ajcr-p3`'s hand-off (`I-1187`, conversation `I-1190`) and `review-ajcr`'s `I-1196` both
   named it as what a lane still owed.

   **AN EARLIER VERSION OF THIS ITEM CLAIMED MORE AND WAS WRONG.** It read: "stating (2) in
   `DivEq` form *avoids* a lemma that does not exist … the quotient level is never re-entered,
   so the missing naturality lemma is never called.  The obligation was over-priced by one
   lemma, and the lemma is avoidable rather than cheap."  Refuted by a fresh-context audit
   (`I-1229`) and reproduced: `DivFamZarAff.mk_eq_mk_iff` crosses between the `DivEq` level and
   the quotient level **for free in both directions**, so the two forms are *equivalent* and no
   naturality lemma was needed for either.  There was no avoidance to discover.  The honest
   residue of the finding is only the first sentence: the step was over-priced, and it is cheap.
   The `DivEq` form is still stated first because it is what (1) consumes.

## Main declarations

* `AlgebraicGeometry.AffAdaptation.deg_presentationDivisor_of_divEq` — a widened certificate
  on any divisor-equal system computes the presentation degree.
* `AlgebraicGeometry.exists_certifiedAff_divEq` — **the widened field collapse**: over a field
  every widened locally certified system is divisor-equal to a globally certified widened
  family.
* `AlgebraicGeometry.DivFamZarAff.classDeg_picClass` — **the widened class-degree law**, the
  transport `DivisorFamilyAffAbel.lean:296-300` named as absent.
* `AlgebraicGeometry.degAt_abelDivAff'` — **`hdegAff`, DISCHARGED** at an arbitrary test for an
  arbitrary widened section.
* `AlgebraicGeometry.chartValueAff_mem_pic0Subgroup'` — hence the widened chart value lands in
  `pic⁰` with `hdegAff` removed from the signature.

## What this does NOT do

`rep` — a representation of the divisor functor — is untouched, and so are the two antecedents
of `pic0RepresentableByOfCharts` (`IsChartUniv` and Zariski-local surjectivity of `Sigma.desc`).
**No antecedent of the representability seam is discharged here.**  What is discharged is the
last obligation standing between the R2 carrier and a widened `chartValueTrans`: the widened
chart value is now known to be a degree-zero class unconditionally, which is what a widened
Σ-chart needs of it.

An earlier version of this paragraph added that "building that natural transformation, and the
widened `abelSigmaChart` above it, remains open".  **That is no longer true and the sentence is
withdrawn**: with `hdegAff` discharged both are the chart-typed definitions verbatim, and they
are landed in `Picard/Pic0AtlasFromDivRepAff.lean` (`chartValueAffTrans`, `abelSigmaChartAff`).
The remaining gap on that route is a *producer* of `(divFunctorAff C n).RepresentableBy`, which
nothing supplies — the same hypothesis `abelSigmaChart` carries on the chart-typed side.
-/

set_option autoImplicit false
/- Statements mix `relCurve C K` with the product spelling `(C ⊗ overSpec k K).left`; see
`AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis depth
must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

open scoped RelativeCurve

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K] {n : ℕ}

noncomputable section

/-! ## The certificate transports along divisor equality -/

namespace AffAdaptation

variable [IsIntegral (relCurve C K)]
variable [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
variable [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **A widened certificate on a divisor-equal system computes the presentation degree.**

`Scheme.presentationDivisor_eq_of_divEq` moves the divisor itself along the `DivEq`, so
`ajcr-p3`'s cover-free identity applies at `G`'s own system and the conclusion lands on `d`.

Note what is *not* needed: no `IsProper C.hom` (the base change of the family never happens —
only the divisor is rewritten) and no separation hypothesis (that was the route
`I-1186` retired). -/
theorem deg_presentationDivisor_of_divEq {D : AffCoverData C K}
    {dG d : (relCurve C K).LocalEquations} (A : AffAdaptation D dG)
    (hc : A.IsCertified n) (h : Scheme.LocalEquations.DivEq dG d) :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K d.presentation) = (n : ℤ) := by
  rw [← Scheme.presentationDivisor_eq_of_divEq K h]
  exact AffAdaptation.IsCertified.deg_presentationDivisor A hc

end AffAdaptation

/-! ## The widened field collapse -/

variable [IsProper C.hom]

set_option maxHeartbeats 1600000 in
/- The `AlgHom`-induced algebra structures on `Localization.Away (g i)` and `K` make the
`divEq_mapAlg_pullback` unifier work through two towers; within the DivSchemeAbel precedent. -/
/-- **Over a field, every widened locally certified system is divisor-equal to a globally
certified widened family** — the widened `DivFam.exists_toZar_eq`
(`Picard/DivSchemeAbel.lean:77`), stated at the level of systems rather than of classes.

A span-`⊤` family over a field has a nonzero member, which is a unit, so
`Localization.Away (g i)` is `K` itself (`IsLocalization.atUnits`); the local certified family
base-changes back along that isomorphism, and the composite pullback collapses by
`relCurveMap_id`.  Every step is about the base, so the widening is invisible here.

**The `DivEq` conclusion is deliberate and is what makes this cheap.**  The class-level form
`∃ G, G.toZarAff = F₀` would need `toZarAff (F.mapAlg R' n hinf) = DivFamZarAff.mapAlg R' n
F.toZarAff`, which does not exist in the tree; the consumer
(`AffAdaptation.deg_presentationDivisor_of_divEq`) wants a `DivEq` anyway, so the quotient
level is never re-entered. -/
theorem exists_certifiedAff_divEq (d : (relCurve C K).LocalEquations)
    (hd : IsLocallyCertifiedAff n d) :
    ∃ G : CertifiedDivisorFamilyAff C K n, Scheme.LocalEquations.DivEq G.eqns d := by
  obtain ⟨m, g, hspan, hG⟩ := id hd
  -- some member of the span-⊤ family is nonzero
  have hex : ∃ i, g i ≠ 0 := by
    by_contra hall
    have hall' : ∀ i, g i = 0 := fun i => by
      by_contra hi
      exact hall ⟨i, hi⟩
    have hle : Ideal.span (Set.range g) ≤ ⊥ := Ideal.span_le.mpr (by
      rintro x ⟨i, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_bot]
      exact hall' i)
    rw [hspan, top_le_iff] at hle
    exact one_ne_zero (Ideal.mem_bot.mp (hle ▸ Submodule.mem_top (x := (1 : K))))
  obtain ⟨i, hgi⟩ := hex
  haveI : IsOpenImmersion (relCurveMap C K (Localization.Away (g i))) :=
    isOpenImmersion_relCurveMap_away C K (Localization.Away (g i)) (g i)
  obtain ⟨Gᵢ, hGdiv⟩ := hG i
  -- the away localization at a unit is `K` itself
  have hunits : Submonoid.powers (g i) ≤ IsUnit.submonoid K := by
    rintro x ⟨e, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hgi).pow e
  haveI : IsLocalization (Submonoid.powers (g i)) K :=
    IsLocalization.of_le_isUnit hunits
  let e₀ : K ≃ₐ[K] Localization.Away (g i) :=
    IsLocalization.atUnits K (Submonoid.powers (g i)) hunits
  let e : Localization.Away (g i) ≃ₐ[k] K := e₀.symm.restrictScalars k
  letI : Algebra (Localization.Away (g i)) K := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower k (Localization.Away (g i)) K :=
    .of_algebraMap_eq fun a => (e.commutes a).symm
  have hKA : ∀ a : K, e (algebraMap K (Localization.Away (g i)) a) = a := by
    intro a
    change e₀.symm (algebraMap K (Localization.Away (g i)) a) = a
    rw [← e₀.commutes a]
    exact e₀.symm_apply_apply _
  haveI : IsScalarTower K (Localization.Away (g i)) K :=
    .of_algebraMap_eq fun a => (hKA a).symm
  -- base change the local family back to `K` and collapse the composite pullback
  refine ⟨Gᵢ.mapAlg K n Gᵢ.cover.hasAffineOverlaps_of_isProper, ?_⟩
  refine (CertifiedDivisorFamilyAff.divEq_mapAlg_pullback n K Gᵢ
    Gᵢ.cover.hasAffineOverlaps_of_isProper
    (hd.germ_pullbackEqn_mem_nonZeroDivisors K n) hGdiv).trans ?_
  exact Scheme.LocalEquations.divEq_pullback_id relCurveMap_id d _

/-! ## The widened class-degree law -/

set_option maxHeartbeats 1600000 in
/- The `Quotient.inductionOn` unfolds `DivFamZarAff.picClass` through the setoid; within the
DivSchemeAbel precedent for the chart-typed twin. -/
/-- **The widened class-degree law** (the transport `DivisorFamilyAffAbel.lean:296-300` names as
absent): the Čech Picard class of a *widened* locally certified class of degree `n` over a field
has `classDeg = n`.

Verbatim the chart-typed `DivFamZar.classDeg_picClass` (`Picard/DivSchemeAbel.lean:136`) with
the widened field collapse in place of `DivFam.exists_toZar_eq` and the widened cover-free
degree identity in place of `deg_divFamDivisor`.  The three middle steps
(`presentation_picClass`, `picClass_presentationDivisor`, `classDeg_picClass`) are carrier-free:
they take a system or a divisor and never saw a cover, which is why only the two ends had to be
widened. -/
theorem DivFamZarAff.classDeg_picClass
    [IsIntegral (relCurve C K)]
    [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]
    (F₀ : DivFamZarAff C K n) :
    classDeg K F₀.picClass = (n : ℤ) := by
  induction F₀ using Quotient.inductionOn with
  | h dp =>
    obtain ⟨G, hG⟩ := exists_certifiedAff_divEq dp.1 dp.2
    calc classDeg K (DivFamZarAff.picClass (DivFamZarAff.mk dp.1 dp.2))
        = classDeg K dp.1.presentation.picClass := by
          rw [DivFamZarAff.picClass_mk, Scheme.LocalEquations.presentation_picClass]
      _ = classDeg K (Scheme.CurveDivisor.picClass K
            (Scheme.presentationDivisor K dp.1.presentation)) := by
          rw [Scheme.CurveDivisor.picClass_presentationDivisor]
      _ = Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K dp.1.presentation) :=
          _root_.AlgebraicGeometry.classDeg_picClass K _
      _ = (n : ℤ) :=
          G.adaptation.deg_presentationDivisor_of_divEq G.certified hG

/-! ## The collapse at the quotient level, and the naturality it needs -/

/-- **`toZarAff` commutes with base change**: the class of a base-changed widened certified
family is the base change of its class.

The widened twin of `DivFam.toZar_mapAlg` (`Picard/DivisorFamilyZarMapAlg.lean:204`), whose
absence `I-1187` and conversation `I-1190` both priced as this row's remaining cost.  It is one
line: both sides are `mk` of the pulled system — `CertifiedDivisorFamilyAff.mapAlg`'s `eqns`
field *is* `pulledEquations`, which *is* the pullback along the comparison, with the regularity
proof irrelevant — so `mk_eq_mk_iff` reduces the goal to `divEq_refl`. -/
theorem CertifiedDivisorFamilyAff.toZarAff_mapAlg {R : Type u} [CommRing R] [Algebra k R]
    (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
    (F : CertifiedDivisorFamilyAff C R n) (hinf : F.cover.HasAffineOverlaps) :
    (F.mapAlg R' n hinf).toZarAff = DivFamZarAff.mapAlg R' n F.toZarAff :=
  DivFamZarAff.mk_eq_mk_iff.mpr (Scheme.LocalEquations.divEq_refl _)

/-- **The widened field collapse at the quotient level** — the exact analogue of
`DivFam.exists_toZar_eq` (`Picard/DivSchemeAbel.lean:77`): over a field every widened class is
the class of a *globally* certified widened family.

**This is EQUIVALENT to `exists_certifiedAff_divEq`, not stronger, and an earlier version of
this docstring and of the module header both claimed otherwise.**  Refuted by a fresh-context
audit (`I-1229`), reproduced here as the proof: `DivFamZarAff.mk_eq_mk_iff` crosses between the
`DivEq` level and the quotient level for free in *both* directions, so this is a three-line
corollary of the `DivEq` form rather than a separate result.  It previously duplicated fifty
lines of that proof verbatim; the duplicate is deleted.

The `DivEq` form is still the one stated first, because it is what
`AffAdaptation.deg_presentationDivisor_of_divEq` consumes — but "the quotient level is never
re-entered" was never a route discovery. -/
theorem DivFamZarAff.exists_toZarAff_eq (F₀ : DivFamZarAff C K n) :
    ∃ G : CertifiedDivisorFamilyAff C K n, G.toZarAff = F₀ := by
  induction F₀ using Quotient.inductionOn with
  | h dp =>
    obtain ⟨G, hG⟩ := exists_certifiedAff_divEq dp.1 dp.2
    exact ⟨G, DivFamZarAff.mk_eq_mk_iff.mpr hG⟩

/-! ## Non-vacuity of the law, at an arbitrary degree -/

/-- **The class-degree law is not vacuous, at every `n`**: over a field, every effective Weil
divisor of degree `n` yields a widened class whose `classDeg` the law computes.

This is the check trap (c) of the axiom-probe catalogue (`I-0442`) asks for, and it is stated
because prior reviews found the widened certificate tail witnessed **only** at `n = 0` with empty
support (`I-1109`).  Here `n` is arbitrary and the support is not: the witness is
`exists_divFam_divFamDivisor_eq` (`Picard/DivisorFamilyFieldSurj.lean`) followed by
`DivFamZar.toAff`.

**What it does NOT witness, and the distinction is the whole point of R2.**  The witness factors
through the *chart-typed* carrier, so it inhabits `DivFamZarAff` only at classes that already had
a chart-typed preimage.  The classes the widening exists to admit — those certified on a
straddling affine open and provably *not* chart-typed
(`isCertified_affine_and_not_isCertified_chart`, `Picard/DivisorFamilyAffStrict.lean`) — are
**not** exhibited here, and that file's own scope note explains why: the separating divisor needs
`Symᵍ C`, which this tree does not construct.  So the law is non-vacuous, and its non-vacuity is
not yet witnessed on the part of the carrier that motivated widening it. -/
theorem exists_divFamZarAff_classDeg_eq {π : C.left ⟶ P1 k} [IsAffineHom π]
    [IsIntegral (relCurve C K)]
    [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]
    (D : (relCurve C K).CurveDivisor) (hD : 0 ≤ D)
    (hdeg : Scheme.CurveDivisor.deg K D = (n : ℤ)) :
    ∃ G : DivFamZarAff C K n, classDeg K G.picClass = (n : ℤ) := by
  obtain ⟨F, _⟩ := exists_divFam_divFamDivisor_eq (π := π) (n := n) D hD hdeg
  exact ⟨(F.toZar).toAff, DivFamZarAff.classDeg_picClass _⟩

/-! ## `hdegAff`, discharged -/

section HDeg

/- `picEtMap` and the twist factors carry these beyond `[IsProper C.hom]`; all are standing
DD-R hypotheses, and `[SmoothOfRelativeDimension 1 C.hom]` is additionally needed here because
`PicEtAff.degAff_unit` and `relPicDeg_relPicMk` consume it. -/
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
  [SmoothOfRelativeDimension 1 C.hom]

omit [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
  [SmoothOfRelativeDimension 1 C.hom] in
/-- **The widened affine collapse of the Abel value** — the R2 twin of
`picEtAffineEquiv_abelDiv` (`Picard/DivSchemeAbel.lean:236`): on an affine test the vehicle-level
widened Abel value is the affine one, through the comparison equivalences.

`abelDivAffPlus_mapAlgHom` at the top affine open, one line — and the `omit` records what
extraction revealed: the collapse needs **none** of the three geometric instances the section
carries (`GeometricallyIrreducible`, `GeometricallyReduced`, `SmoothOfRelativeDimension 1`).
Those enter only at `degAff_unit`/`relPicDeg_relPicMk` further down.  Inline, that was invisible.

**Named on ajcr-p3's finding `I-1225`, which is about this file.**  It was an anonymous `have`
inside `degAt_abelDivAff'` below, and an inlined `have` is invisible to every search this
workspace runs — `horizon search`, loogle, `local_search` and the declaration index all
enumerate *declarations*, and a proof-local binder is not one.  So p3 priced this exact term as
a missing port step while it sat proved four lines away.  Extracted rather than left inline
precisely so the next lane finds it by name. -/
theorem picEtAffineEquiv_abelDivAff' (A : Type u) [CommRing A] [Algebra k A]
    (s : divFamZarAff C n (overSpec k A)) :
    picEtAffineEquiv C A (abelDivAff' C n (overSpec k A) s)
      = abelDivAffPlus C A (divFamZarAffAffineEquiv C n A s) :=
  abelDivAffPlus_mapAlgHom (Over.overSpecΓTopAlgEquiv k A).toAlgHom
    (s.1 (overSpecTopAffine A))

set_option maxHeartbeats 1600000 in
/- The five base-change instances plus the `picEtAffineEquiv` collapse; within the
`degAt_abelDiv` precedent for the chart-typed twin. -/
omit [GeometricallyReduced C.hom] in
/-- **`hdegAff`, DISCHARGED** (`Picard/DivisorFamilyAffAbel.lean:309`): the widened Abel value
of a degree-`n` widened class has degree `n` at every field point of every test.

Verbatim `degAt_abelDiv` (`Picard/DivSchemeAbel.lean:277`): naturality
(`picEtMap_abelDivAff'`) reduces to the affine collapse at the field
(`picEtAffineEquiv_abelDivAff'`, above), `degAff_unit` and `relPicDeg_relPicMk` read the class
degree, and the widened class-degree law finishes.

**Unconditional in the section, i.e. at an arbitrary test and an arbitrary widened section** —
not only on the image of a chart-typed class, which is what `degAt_abelDivAff'_toAff`
(`DivisorFamilyAffAbel.lean:327`) already gave.  That distinction is the whole point: the
classes R2 exists to admit are exactly those with no chart-typed preimage, and its own
docstring names them as the open case. -/
theorem degAt_abelDivAff' {T : Over (Spec (.of k))} (s : divFamZarAff C n T)
    {K : Type u} [Field K] [Algebra k K] (t : overSpec k K ⟶ T) :
    degAt (abelDivAff' C n T s) t = (n : ℤ) := by
  change PicEtAff.degAff K (picEtAffineEquiv C K
      (picEtMap C t (abelDivAff' C n T s))) = (n : ℤ)
  rw [picEtMap_abelDivAff', picEtAffineEquiv_abelDivAff', abelDivAffPlus,
    PicEtAff.degAff_unit, relPicDeg_relPicMk]
  exact DivFamZarAff.classDeg_picClass _

omit [GeometricallyReduced C.hom] in
/-- **The widened chart value lands in `pic⁰`, with `hdegAff` REMOVED from the signature** —
`chartValueAff_mem_pic0Subgroup` (`Picard/DivisorFamilyAffAbel.lean:304`) with its only
hypothesis discharged, so the statement now matches its chart-typed twin
`chartValue_mem_pic0Subgroup` exactly.

This is what the R2 carrier owed before a widened `chartValueTrans` could exist: the widened
chart value is a degree-zero class unconditionally.  That transformation and the widened
`abelSigmaChart` above it are landed in `Picard/Pic0AtlasFromDivRepAff.lean`; what neither has
is a producer of `(divFunctorAff C n).RepresentableBy`. -/
theorem chartValueAff_mem_pic0Subgroup' (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (T : Over (Spec (.of k))) (s : divFamZarAff C n T) :
    chartValueAff C n m Z T s ∈ pic0Subgroup C T :=
  chartValueAff_mem_pic0Subgroup C n m Z hdeg T s fun t => degAt_abelDivAff' s t

end HDeg

end

end AlgebraicGeometry
