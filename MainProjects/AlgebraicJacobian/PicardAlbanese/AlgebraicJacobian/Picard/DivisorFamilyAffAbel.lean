/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFunctorCompare
import AlgebraicJacobian.Picard.DivSchemeAbel
-- The two declarations this file's docstrings reason ABOUT rather than use:
-- `isCertified_affine_and_not_isCertified_chart` (the R2 strictness payoff, which is WHY the
-- widened carrier has to reach the Picard side at all) and `abelSigmaChart` (the consumer that
-- takes a CHART-TYPED representation, which is what it cannot currently reach). Imported so
-- every cited name is in this file's import closure and `#check`s here rather than merely
-- being greppable elsewhere -- measured on the first version of this header, which cited both
-- out of scope (the recurring failure recorded at I-1073).
import AlgebraicJacobian.Picard.DivisorFamilyAffStrict
import AlgebraicJacobian.Picard.Pic0AtlasFromDivRep

/-!
# THE ABEL HOOK ON THE R2 CARRIER: `DivFamZarAff` acquires a Picard class in `picEt`

Protection `I-0492` mandates the **widened** carrier — `DivFamZarAff`, certificates over
arbitrary affine-open covers — and `isCertified_affine_and_not_isCertified_chart`
(`Picard/DivisorFamilyAffStrict.lean`) proves the widening is *strict*: a straddling connected
divisor is certified on the widened side and on **no** chart-typed adaptation, in any degree.

Measured at HEAD before writing this file (declaration index, plus a case-insensitive grep so
that producers in suffix position are not missed — memory `I-1005`): the widened carrier had a
class map (`DivFamZarAff.picClass`) and its two naturalities, a functor (`divFunctorAff`) and a
comparison (`divFunctorToAff`) — and **zero** declarations carrying it to `PicEtAff`, `picEt`,
`relPic` or `pic0`.  The whole Abel layer (`abelDivPlus`, `abelDivAff`, `abelDiv`,
`abelDivTrans`, `chartValue`, `DivFamZar.classDeg_picClass`) is stated at `DivFamZar` alone
(`Picard/DivSchemeAbel.lean`); of the 25 files mentioning `DivFamZarAff`, none composed it with
the unit of the plus construction.

That gap is why the two halves of the DD-R lane cannot meet.  `abelSigmaChart`
(`Picard/Pic0AtlasFromDivRep.lean:205`) takes `rep : (divFunctor C π n).RepresentableBy D` — the
**chart-typed** functor — and composes it through `chartValueTrans`/`chartValue`/`abelDiv`.  So
the only Σ-atlas the tree can build is built from a representation of `divFunctor`, while the
carrier the human's decision mandates is `divFunctorAff`.  A widened representability datum,
had anyone one, could not have reached the atlas at all.

## What this file lands, and what it does NOT

It lands the Abel hook on the widened carrier: the composite
`PicEtAff.unit ∘ relPicMk ∘ DivFamZarAff.picClass`, its naturality in the test algebra, its
lift to an arbitrary test object through the widened vehicle, and naturality there.  Every step
is the chart-typed proof with `DivFamZarAff` in place of `DivFamZar`; nothing is new
mathematics, and that cheapness is the finding — the gap was a missing transcription, not a
missing theorem.

**No certificate is produced and no gate is cleared.**  In particular this does *not* prove the
widened functor representable, does not discharge `rep`, and does not weaken the straddling
no-go.

Two corrections to how a first version of this header described its own position, both
measured.  (i) `rep` is **not** an antecedent of `pic0RepresentableByOfCharts`: that declaration
takes `f`, `hf` and the `IsLocallySurjective` instance, and `rep` occurs nowhere in it.  `rep` is
an argument of `abelSigmaChart` (`Picard/Pic0AtlasFromDivRep.lean:205`) and of
`mixedParamRepresentableBy` (`Picard/Pic0ChartAtlasParamFree.lean:127`) — the atlas *producers*,
which is upstream of the assembly rather than inside it.  (ii) `π` is a section variable
**nowhere** in this file; it appears as a local binder in exactly the two comparison lemmas that
mention the chart-typed carrier, and the other eight declarations are `π`-free.  That is the
point of I-0492 rather than a caveat against it, and the earlier wording understated it.

And the distance still to go, stated so nobody reads the file as further along than it is: what
`abelSigmaChart` consumes is a natural transformation `divFunctorAff ⟶ pic0TypeFunctor` — the
widened `chartValueTrans` — and building it needs `chartValueAff_mem_pic0Subgroup` **without**
`hdegAff`.  So `hdegAff` is not a footnote; it is the whole remaining gap between this file and
a widened Σ-chart.

## The compatibility that makes this consistent with the chart-typed layer

`abelDivAffPlus_toAff` records that the widened hook applied to the image of a chart-typed
class is the chart-typed hook: the two Abel values agree, because `DivFamZarAff.picClass_toAff`
says the widening does not move the Picard class.  So this is an *extension* of the existing
Abel layer along `divFunctorToAff`, not a second incompatible one.

## Main declarations

* `AlgebraicGeometry.abelDivAffPlus` — the widened Abel transformation at an affine test.
* `AlgebraicGeometry.abelDivAffPlus_mapAlgHom` — its naturality in the test algebra.
* `AlgebraicGeometry.abelDivAffPlus_toAff` — agreement with the chart-typed hook.
* `AlgebraicGeometry.abelDivAff'` — the widened Abel transformation at an arbitrary test.
* `AlgebraicGeometry.picEtMap_abelDivAff'` — its naturality in the test object.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling; see
`AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis depth
must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom] {n : ℕ}

noncomputable section

/-! ## The widened Abel transformation at an affine test -/

section AbelAff

variable (C) in
/-- **The Abel transformation of a widened locally certified class at an affine test**: the
étale-unit image of the relative Picard class of `𝒪(F₀)`.

Verbatim `abelDivPlus` (`Picard/DivSchemeAbel.lean`) with `DivFamZarAff` in place of
`DivFamZar` — the class map `DivFamZarAff.picClass` is all that is consumed, and it never saw
the cover, so no chart typing enters. -/
def abelDivAffPlus (A : Type u) [CommRing A] [Algebra k A] (F₀ : DivFamZarAff C A n) :
    PicEtAff C A :=
  PicEtAff.unit C A (relPicMk C (overSpec k A) F₀.picClass)

/-- **Naturality of the widened affine Abel transformation in the test algebra**
(`DivFamZarAff.picClass_mapAlg` + `PicEtAff.mapAlg_unit`): base change of the widened Abel
value is the Abel value of the base-changed class. -/
theorem abelDivAffPlus_mapAlgHom {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (φ : A →ₐ[k] B) (F₀ : DivFamZarAff C A n) :
    PicEtAff.mapAlg C φ (abelDivAffPlus C A F₀)
      = abelDivAffPlus C B (DivFamZarAff.mapAlgHom φ F₀) := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A B := .of_algebraMap_eq fun a => (φ.commutes a).symm
  have hclass : (DivFamZarAff.mapAlgHom φ F₀).picClass
      = Scheme.CechPic.map (C ◁ Over.overSpecMap φ).left F₀.picClass := by
    have hcurve : relCurveMap C A B = (C ◁ Over.overSpecMap φ).left := by
      refine congrArg (fun ψ : overSpec k B ⟶ overSpec k A => (C ◁ ψ).left) ?_
      exact Over.OverMorphism.ext rfl
    rw [← hcurve]
    exact DivFamZarAff.picClass_mapAlg B n F₀
  calc PicEtAff.mapAlg C φ (abelDivAffPlus C A F₀)
      = PicEtAff.unit C B (relPicAlgMap C φ
          (relPicMk C (overSpec k A) F₀.picClass)) := PicEtAff.mapAlg_unit C φ _
    _ = PicEtAff.unit C B (relPicMk C (overSpec k B)
          (Scheme.CechPic.map (C ◁ Over.overSpecMap φ).left F₀.picClass)) :=
        congrArg (PicEtAff.unit C B)
          (relPicMap_mk C (Over.overSpecMap φ) F₀.picClass)
    _ = abelDivAffPlus C B (DivFamZarAff.mapAlgHom φ F₀) := by
        rw [abelDivAffPlus, hclass]

omit [IsProper C.hom] in
/-- **The widened hook extends the chart-typed one along `DivFamZar.toAff`**: the widened Abel
value of the image of a chart-typed class is the chart-typed Abel value.

This is what makes the file an *extension* of `Picard/DivSchemeAbel.lean` rather than a second,
incompatible Abel layer: `DivFamZarAff.picClass_toAff` says the widening does not move the
Picard class, and both hooks are `unit ∘ relPicMk` of that class. -/
theorem abelDivAffPlus_toAff {A : Type u} [CommRing A] [Algebra k A]
    {π : C.left ⟶ P1 k} [IsAffineHom π] (F₀ : DivFamZar C A π n) :
    abelDivAffPlus C A F₀.toAff = abelDivPlus C π A F₀ := by
  rw [abelDivAffPlus, abelDivPlus, DivFamZarAff.picClass_toAff]

end AbelAff

/-! ## The widened Abel transformation at an arbitrary test -/

section AbelVehicle

/- `picEtMap` (`Picard/PicEtMap.lean:206-207`) carries these two beyond `[IsProper C.hom]`; they
are hypotheses of the whole DD-R lane, so this costs no generality, but they are stated rather
than inherited silently. -/
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

variable (C n) in
/-- **The Abel transformation of a widened class at an arbitrary test object**: componentwise
over the affine opens of the test, compatible by `abelDivAffPlus_mapAlgHom`.

Verbatim `abelDiv` (`Picard/DivSchemeAbel.lean`) on the widened vehicle. -/
def abelDivAff' (T : Over (Spec (.of k))) (s : divFamZarAff C n T) : picEt C T :=
  ⟨fun U => abelDivAffPlus C Γ(T.left, U.1) (s.1 U), fun U V h => by
    rw [abelDivAffPlus_mapAlgHom (Over.resAlgHom T h) (s.1 V), s.compat U V h]⟩

omit [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom] in
@[simp]
lemma abelDivAff'_val (T : Over (Spec (.of k))) (s : divFamZarAff C n T)
    (U : T.left.affineOpens) :
    (abelDivAff' C n T s).1 U = abelDivAffPlus C Γ(T.left, U.1) (s.1 U) :=
  rfl

/-- **Naturality of the widened Abel transformation in the test object**: restriction of the
widened Abel value along an arbitrary test morphism is the widened Abel value of the restricted
family.

The chart-typed proof (`picEtMap_abelDiv`) transported: both glued restrictions are pinned by
their `∃!`-characterizations, and the widened one is `divFamZarAff.mapVal_spec`. -/
theorem picEtMap_abelDivAff' {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (s : divFamZarAff C n T) :
    picEtMap C f (abelDivAff' C n T s) = abelDivAff' C n T' (divFamZarAff.map C n f s) := by
  refine picEt.ext fun W => ?_
  rw [picEtMap_val]
  refine picEtMapVal_eq_of C f (abelDivAff' C n T s) ?_
  intro W₀ hW₀ V hV
  rw [abelDivAff'_val, abelDivAff'_val, divFamZarAff.map_val,
    abelDivAffPlus_mapAlgHom (Over.resAlgHom T' hW₀) (divFamZarAff.mapVal C n f s W),
    abelDivAffPlus_mapAlgHom (Over.appLEAlgHom f V.1 W₀.1 hV) (s.1 V),
    divFamZarAff.mapVal_spec C n f s W W₀ hW₀ V hV]

end AbelVehicle

/-! ## The widened chart value, and the ONE statement still owed

`chartValue` (`Picard/DivSchemeAbel.lean`) twists the Abel value into degree zero, and its
`pic0Subgroup` membership is `degAt_chartValue` plus the chart-index degree constraint.  The
widened analogue of the twist is free — it is the same product in `picEt C T`, whose factors
`sigmaFamily`/`thetaFamily` never saw a divisor cover at all.  What is **not yet proved** is the
degree ledger: `degAt_abelDiv` rests on `DivFamZar.classDeg_picClass`, whose proof runs through
the field collapse `DivFam.exists_toZar_eq` and the CRT identity `deg_divFamDivisor`, whose
degree half is `DivisorAdaptation.deg_presentationDivisor_eq_finrank_glued`.

**MEASURED CLOSED, 2026-07-30 (review-ajcr, issue I-1197; working proof handed to the owning
lane at I-1196).**  `hdegAff` below is no longer owed: it closes on landed material, sorry-free
and axiom-clean against a control firing `sorryAx`.  Read the sentence above carefully, because
it is the one that named the defect and then failed to act on it — it lists **two** inputs of
`classDeg_picClass`, the field collapse *and* the CRT identity, while every pricing downstream
of it (and `Picard/DivisorFamilyAffFieldDegree.lean`, `…AffStalkEval.lean`, and the board row)
tracked only the CRT half.  The collapse was the input with no widened analogue at all
(`DivFamAff`: zero tokens project-wide), so the half that looked absent was the half nobody
costed.  It is cheap: the chart-typed proof (`DivSchemeAbel.lean:79-130`) transports verbatim,
both of its widening touch-points already existed (`CertifiedDivisorFamilyAff.mapAlg`, whose
`hinf` is free under `[IsProper C.hom]`; the explicit face `DivFamZarAff.mapAlgHom_*`,
`Picard/DivisorFamilyAffFace.lean:84-127`), and the two steps that had no name — the widened
`toZar_mapAlg` and the widened affine collapse — are one line each.

The rule worth keeping from this: to price a **port**, read the *proof term* of what is being
ported, not its statement.  A statement lists what a lemma wants from its reader; the proof
lists what it wants from the library, and a port pays the second.  Anything a proof obtains by
`obtain … := <lemma>` in its opening lines is a port obligation no signature-level reading
shows you.  Nothing here touches `rep`, `IsChartUniv`, or Zariski-local surjectivity of
`Sigma.desc f`.

**RETRACTED, and the correction is the useful part.**  A first version of this paragraph priced
that step as *obstructed*, on the grounds that its proof cites `relCover_sup` together with
`cover₀`/`cover₁` — the pinned pair R2 deletes.  The citation is real
(`Picard/DivisorFamilyFieldDegree.lean:354-360`) and the inference from it was wrong.  Read what
those lines *output* rather than which names they mention: the whole three-line block produces
`∃ j, p.1 ∈ A.pieces j`, "every point lies in some piece".  On the widened side that is not a
theorem to be re-earned but the structure **field** `AffCoverData.cover`, already extracted as
`AffCoverData.exists_mem_pieces` (`Picard/DivisorFamilyAffCover.lean:166`), whose own docstring
says so.  At the step named, the widening is *cheaper*: the pinned pair was the chart-typed
**cost** of a fact `AffCoverData` assumes.

**THE PORT IS NOW DONE, and this paragraph records what it actually cost.**  It priced the
residue as a four-lemma port over an abstract index — real work, not blocked — on the grounds
that each chart-typed original quantifies **only** over `A.index`, `A.pieces`, `A.eqn`,
`A.colength`, `A.ovlColength`, `A.Glued`, all carried verbatim by `AffAdaptation`, and none
mentions `m₀`, `m₁`, `h₀`, `h₁`, `partition₀`/`partition₁` or a chart.  That reasoning held.
The count did not: it is **five** lemmas, the omitted one being `coeffAt_eq_toAdd_ordZ_eqn`, the
coefficient dictionary that both `finrank_colength_eq_sum` and `coeffAt_eq_zero_of_isUnit_germ`
call.  All five are proved in `Picard/DivisorFamilyAffFieldDegree.lean`, together with the
assembly `AffAdaptation.deg_presentationDivisor_eq_finrank_glued`, the field half
`AffAdaptation.IsCertified.finrank_glued`, and `deg = n`
(`AffAdaptation.deg_presentationDivisor_eq_of_isCertified`) — sorry-free, and not one proof step
of any of the five differs from its chart-typed original.  The "recover the pinned pair" front
stays closed: exactly two steps needed the chart typing, and both are structure fields on the
widened side (`AffCoverData.isAffineOpen_pieces` for the colength keystone, whose consumer takes
`IsAffineOpen V` as an argument, and `exists_mem_pieces` for the covering).

So the degree ledger is stated below as an explicit hypothesis `hdegAff` on the widened Abel
transformation, at exactly the shape `degAt_abelDiv` has.  It is **not** discharged here, and it
is **not** hidden inside a class whose statement omits the objects: it mentions the curve, the
widened section, the field point and the degree.  A `sorry` would have been dishonest in the
other direction — this way the obligation appears in every consumer's signature. -/

section ChartValueAff

/- Beyond the vehicle's instances, the TWIST factors need the curve's geometry: `sigmaFamily`
and `thetaFamily` (`Picard/DivSchemeAbel.lean` §Sigma, `Picard/ThetaShift.lean`) carry
`[SmoothOfRelativeDimension 1 C.hom]` and `[GeometricallyIrreducible C.hom]`.  All are standing
DD-R hypotheses; they are named here rather than inherited. -/
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
  [SmoothOfRelativeDimension 1 C.hom]

variable (C n) in
/-- **The widened chart value**: the widened Abel value shifted by the Σ-family and `m` inverse
powers of the pinned θ-family — verbatim `chartValue` with `abelDivAff'` in place of `abelDiv`.

The twist itself is cover-free: `sigmaFamily` and `thetaFamily` are built from Čech classes on
the base-changed curve and know nothing of a divisor cover, so the widening does not touch
them. -/
def chartValueAff (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (s : divFamZarAff C n T) : picEt C T :=
  abelDivAff' C n T s * sigmaFamily C Z T
    * (thetaFamily C (thetaCechClass C) T ^ m)⁻¹

variable (C n) in
/-- Naturality of the widened chart value in the test object — `picEtMap_abelDivAff'` together
with the two naturalities of the twist factors. -/
theorem picEtMap_chartValueAff (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (s : divFamZarAff C n T) :
    picEtMap C f (chartValueAff C n m Z T s)
      = chartValueAff C n m Z T' (divFamZarAff.map C n f s) := by
  rw [chartValueAff, chartValueAff, map_mul, map_mul, map_inv, map_pow, picEtMap_abelDivAff',
    sigmaFamily_natural, thetaFamily_natural]

omit [GeometricallyReduced C.hom] in
variable (C n) in
/-- **The widened chart value lands in `pic0`, GIVEN the widened degree ledger.**

`hdegAff` is the widened form of `degAt_abelDiv` and it is the single statement this file does
not prove: *the widened Abel value of a degree-`n` widened class has degree `n` at every field
point*.

Read the dependency honestly, and note that an earlier version of this docstring read it wrongly:
it said the degree half "consumes the pinned-pair covering (`relCover_sup`, `cover₀`/`cover₁`)
that R2 deletes".  It does not — that block outputs only "every point lies in some piece", which
is a field of `AffCoverData`, and the whole colength↔degree identity is now proved over arbitrary
affine pieces in `Picard/DivisorFamilyAffFieldDegree.lean`.  So the pinned pair is not what stands
between here and `hdegAff`.

What genuinely remains is the step *above* the degree identity: the chart-typed ledger routes
through `DivFamZar.classDeg_picClass`, i.e. from the presentation divisor's degree to the Picard
class of the widened section, and that transport has no widened analogue yet.  `hdegAff` is
therefore still a real obligation — but a strictly smaller and differently-located one than this
docstring previously claimed.

**SUPERSEDED 2026-07-30 (review-ajcr, I-1197 / I-1196): `hdegAff` CLOSES, so this hypothesis is
dischargeable and the paragraph above over-states the distance.**  "That transport has no widened
analogue yet" was true as a statement about names and misleading as a price.  The transport needs
the widened *field collapse* (`DivFamZarAff.exists_toZarAff_eq`, the analogue of
`DivFam.exists_toZar_eq`), which nothing had built, plus three one-to-six-line steps; all of it
transports from the chart-typed originals with the two substitutions R2 already paid for.  With
those, this theorem's `hdegAff` argument is provable outright — verified sorry-free and
axiom-clean against a same-file `sorryAx` control.

Whoever discharges it should **drop the `hdegAff` binder from this statement** rather than
supplying it at call sites; that changes every consumer's signature, and it is a deliberate
consumer repair, not a rename.  See the header for the generalisable rule about pricing ports
from proof terms rather than statements.

Everything else in the degree-zero-ness argument transports unchanged: the three degrees still
sum to zero under the chart-index constraint, because the twist factors are cover-free. -/
theorem chartValueAff_mem_pic0Subgroup (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (T : Over (Spec (.of k))) (s : divFamZarAff C n T)
    (hdegAff : ∀ {K : Type u} [Field K] [Algebra k K] (t : overSpec k K ⟶ T),
      degAt (abelDivAff' C n T s) t = (n : ℤ)) :
    chartValueAff C n m Z T s ∈ pic0Subgroup C T := by
  rw [mem_pic0Subgroup_iff]
  intro K _ _ t
  rw [chartValueAff, degAt_mul, degAt_mul, degAt_inv, degAt_thetaFamily_pow,
    degAt_sigmaFamily, hdegAff t, hdeg]
  ring

omit [GeometricallyReduced C.hom] in
/-- The widened Abel transformation agrees with the chart-typed transformation on the image of
the old-to-widened vehicle comparison. -/
theorem abelDivAff'_toAff {π : C.left ⟶ P1 k} [IsAffineHom π]
    {T : Over (Spec (.of k))} (s : divFamZar C π n T) :
    abelDivAff' C n T (divFamZarToAffVehicle C n π s) = abelDiv C π n T s := by
  refine picEt.ext fun U => ?_
  rw [abelDivAff'_val, abelDiv_val, divFamZarToAffVehicle_val, abelDivAffPlus_toAff]

omit [GeometricallyReduced C.hom] in
/-- The widened chart value extends the chart-typed chart value along the injective vehicle
comparison. -/
theorem chartValueAff_toAff {π : C.left ⟶ P1 k} [IsAffineHom π]
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T : Over (Spec (.of k))} (s : divFamZar C π n T) :
    chartValueAff C n m Z T (divFamZarToAffVehicle C n π s) =
      chartValue C π n m Z T s := by
  rw [chartValueAff, chartValue, abelDivAff'_toAff]

omit [GeometricallyReduced C.hom] in
/-- **The widened ledger holds on the image of a chart-typed class** — so the hypothesis of
`chartValueAff_mem_pic0Subgroup` is not vacuous: it is inhabited at every widened section that
comes from a chart-typed one, by `degAt_abelDiv` transported along `abelDivAff'_toAff`.

This is deliberately *not* offered as evidence that the general ledger holds.  It says the
obligation has witnesses, which is what distinguishes a real hypothesis from an unsatisfiable
one; the open question is whether it holds for a widened class with no chart-typed preimage,
which is exactly the class the R2 widening exists to admit. -/
theorem degAt_abelDivAff'_toAff {π : C.left ⟶ P1 k} [IsAffineHom π]
    {T : Over (Spec (.of k))} (s : divFamZar C π n T) {K : Type u} [Field K] [Algebra k K]
    (t : overSpec k K ⟶ T) :
    degAt (abelDivAff' C n T (divFamZarToAffVehicle C n π s)) t = (n : ℤ) := by
  rw [abelDivAff'_toAff, degAt_abelDiv]

end ChartValueAff

end

end AlgebraicGeometry
