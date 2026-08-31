/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AtlasFromDivRepAff
import AlgebraicJacobian.Picard.Pic0ChartPlusFibreProducer
import AlgebraicJacobian.Picard.Pic0ChartUnivReduce

/-!
# CHART-U(b) ON THE R2 CARRIER: the widened Abel value is plus-honest

## The gap this closes

`Picard/Pic0AtlasFromDivRepAff.lean` gives `abelSigmaChartAff` exactly the type
`pic0RepresentableByOfCharts` consumes for its `f i`, so the carrier that human decision
`I-0492` mandates now reaches the representability seam's *input*.  It does not reach the
seam's **openness** antecedent, and that is what this file repairs.

CHART-U(b) at a general test is `isOpen_chartLocus_of_isPlusHonest`
(`Picard/Pic0ChartPlusFibreProducer.lean:316`), whose single non-instance hypothesis is
`IsPlusHonest C T lam` (`:200`).  Measured at HEAD before writing this file, case-insensitively
so that producers in suffix position are not missed (the mechanism recorded at `I-1005`, and the
census error the reviewer made on this very predicate): `IsPlusHonest` has four producers —
`thetaFamily_isPlusHonest`, `sigmaFamily_isPlusHonest`, `abelDiv_isPlusHonest`,
`chartTwist_isPlusHonest` — and **all four are stated at the chart-typed carrier**.  Zero
declarations related `IsPlusHonest` to `abelDivAff'`, `chartValueAff` or `divFamZarAff`.

So the widened Σ-chart could be built and its locus could not be shown open: the same
carrier-target defect as the Abel hook itself (memory `census-the-carrier-target-pair`), one
level up, and re-opened by the commit that closed the level below.

## What is landed here, and what is NOT

Landed: honesty of the widened Abel value at an arbitrary test and an arbitrary widened
section, and hence openness of `chartLocus` at a widened chart value — the widened twin of
`isOpen_chartLocus_of_isPlusHonest`, with no hypothesis on the section.

**NOT landed, and none of it is weakened by the above.**  `IsChartUniv` for the widened family
is not stated here; Zariski-local surjectivity of `Sigma.desc` is untouched; and
`(divFunctorAff C n).RepresentableBy` still has no producer anywhere in the tree, so this file
supplies openness *of a locus of a chart shape*, not a chart.  In particular no antecedent of
`pic0RepresentableByOfCharts` is discharged.

**Honesty at an ARBITRARY `picEt` class remains open and is NOT approached here.**  That is the
étale-sheafification question.  Its *absolute* form is reportedly refuted elsewhere in this tree
by `PicEtAff.unit_surjective_of_section` (`Picard/EffectivityClose.lean:141`), which is said to
make honesty vacuously true over a field test admitting a curve point — flagged as a citation
rather than asserted, because `EffectivityClose` is **outside this file's import closure**, so
that name does not `#check` here and nothing below depends on it.  (A first version of this
header stated the refutation flatly on the strength of a grep; the distinction is the recurring
failure recorded at `I-1073`.)  What this file proves is the same *specific-class* statement the
chart-typed side already had, transported to the carrier the human decision mandates.

## Why it was cheap, and the correction a fresh-context audit forced

`abelDiv_isPlusHonest` is four lines: exhibit `relPicMk` of the restricted family's class, then
rewrite by naturality and the affine collapse.  Every widened ingredient existed, and the one I
took to be missing — the widened affine collapse — was **not** missing in either of the two
senses a first version of this header claimed.

That first version said the collapse existed only as an anonymous `have hcollapse` inside the
proof of `degAt_abelDivAff'`, and stated it here under a new name.  Both halves were wrong, and
the second is the expensive one: `picEtAffineEquiv_abelDivAff'`
(`Picard/DivisorFamilyAffClassDegree.lean:340`) is that lemma, named and landed by another lane
in the *same round*, in the very file this header cited by line number — and byte-identical in
statement and proof term to the duplicate this file briefly carried.  Verified interchangeable
before the duplicate was deleted.  So the honest finding is narrower than "an inlined `have` is
invisible to search" (true in general, and still worth the memory item it got): here the term
had already been named one commit earlier, and the miss was mine for pricing against a stale
read of a file that was moving under me.  What remains of the original observation is that the
port is a transcription — `picEtMap_abelDivAff'` for `picEtMap_abelDiv`, p1's collapse for
`picEtAffineEquiv_abelDiv`, and nothing else changes.

## Main declarations

* `AlgebraicGeometry.abelDivAff'_isPlusHonest` — **the widened Abel value is honest at every
  test**, the widened twin of `abelDiv_isPlusHonest`.
* `AlgebraicGeometry.chartValueAff_isPlusHonest` — hence so is the widened chart value.
* `AlgebraicGeometry.isOpen_chartLocus_chartValueAff` — **CHART-U(b) on the R2 carrier**:
  the chart locus of a widened chart value is open, unconditionally in the section.
* `AlgebraicGeometry.chartLocusAffineLocal_chartValueAff` — the `haff` residue **discharged**
  for the widened chart value, and `chartLocusOpensChartValueAff` the resulting `T.left.Opens`.
  Added after the audit pointed out that this file's first version *understated* itself: three
  sites still price `haff` as owed at a general test, and for this carrier it is not.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling; see
`AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis depth
must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
variable {n : ℕ}

noncomputable section

/-! ## Honesty of the widened Abel value

The affine collapse this section consumes is `picEtAffineEquiv_abelDivAff'`
(`Picard/DivisorFamilyAffClassDegree.lean:340`), landed by another lane in the same round.  A
first version of this file carried a byte-identical duplicate of it under a different name; the
duplicate is deleted and the original consumed. -/

omit [SmoothOfRelativeDimension 1 C.hom] in
variable (C n) in
/-- **THE WIDENED ABEL VALUE IS PLUS-HONEST AT EVERY TEST** — the widened twin of
`abelDiv_isPlusHonest` (`Picard/Pic0ChartPlusFibreProducer.lean:275`), and the declaration whose
absence kept CHART-U(b) from reaching the R2 carrier.

Unconditional in the section: no chart-typed preimage is assumed, which matters because the
classes the widening exists to admit are exactly those that have none.

The witness on the affine piece `U` is the relative Picard class of the *restricted* widened
family, and the proof is the chart-typed one with `picEtMap_abelDivAff'` in place of
`picEtMap_abelDiv`: honesty compares `relPicToPicEt` with `abelDivAffPlus`, both of which are
`PicEtAff.unit` of a `relPic` class, so after the collapse the two sides are the same term.

`[SmoothOfRelativeDimension 1 C.hom]` is `omit`ted, and a first version of this file wrongly
claimed it could not be: it asserted that `IsPlusHonest` is declared under that instance, so the
statement consumes it and omitting leaves an unsolved goal — and suppressed the linter on that
basis.  `#check @IsPlusHonest` shows the predicate carries only `IsProper`,
`GeometricallyIrreducible` and `GeometricallyReduced`.  The unsolved goal I measured came from a
local collapse helper that did not itself omit the section instances, i.e. from the helper I had
rather than the statement I wrote; with p1's collapse consumed instead, `omit` compiles.  The
linter was right both times. -/
theorem abelDivAff'_isPlusHonest (T : Over (Spec (.of k))) (s : divFamZarAff C n T) :
    IsPlusHonest C T (abelDivAff' C n T s) := by
  intro U
  refine ⟨relPicMk C (overSpec k Γ(T.left, U.1))
    ((divFamZarAffAffineEquiv C n Γ(T.left, U.1)
      (divFamZarAff.map C n (Over.fromSpecAffine T U) s)).picClass), ?_⟩
  rw [picEtMap_abelDivAff']
  refine (picEtAffineEquiv C Γ(T.left, U.1)).injective ?_
  rw [picEtAffineEquiv_relPicToPicEt, picEtAffineEquiv_abelDivAff', abelDivAffPlus]

variable (C n) in
/-- **The widened chart value is plus-honest** — the widened twin of `chartTwist_isPlusHonest`
composed with the Abel witness.

`chartValueAff = abelDivAff' · Σ · (θᵐ)⁻¹` (`Picard/DivisorFamilyAffAbel.lean:266`) and honesty
is a subgroup condition (`IsPlusHonest.mul`/`.inv`/`.pow`), while `sigmaFamily` and `thetaFamily`
are honest at every test with no hypothesis on the curve.  So honesty of the widened chart value
reduces to honesty of its Abel factor, which is the theorem above. -/
theorem chartValueAff_isPlusHonest (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (s : divFamZarAff C n T) :
    IsPlusHonest C T (chartValueAff C n m Z T s) :=
  ((abelDivAff'_isPlusHonest C n T s).mul C (sigmaFamily_isPlusHonest C Z T)).mul C
    ((thetaFamily_isPlusHonest C (thetaCechClass C) T).pow C m).inv

/-! ## CHART-U(b) on the R2 carrier -/

variable (C π n) in
/-- **CHART-U(b) ON THE R2 CARRIER**: the chart locus of a *widened* chart value is open, with no
hypothesis on the widened section.

This is `isOpen_chartLocus_of_isPlusHonest` (`Picard/Pic0ChartPlusFibreProducer.lean:316`) with
its residue discharged at the carrier human decision `I-0492` mandates.  Nothing about the
openness chain changes — engine, RE-5, iso-invariance, `haff`, the presentation and the
plus-fibre producer are all reused verbatim; what was missing was a producer of `IsPlusHonest`
for a widened class, and the four existing producers were chart-typed.

**This closes no antecedent of `pic0RepresentableByOfCharts`.**  `IsChartUniv` and Zariski-local
surjectivity are untouched, and `(divFunctorAff C n).RepresentableBy` still has no producer, so
`s` is available only where a widened representation is. -/
theorem isOpen_chartLocus_chartValueAff (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (s : divFamZarAff C n T) :
    IsOpen (chartLocus C m Z (chartValueAff C n m Z T s)) :=
  isOpen_chartLocus_of_isPlusHonest C π hπ m Z T _ (chartValueAff_isPlusHonest C n m Z T s)

/-! ## The `haff` residue, discharged for this carrier -/

variable (C π n) in
/-- **`ChartLocusAffineLocal` DISCHARGED for the widened chart value** — the `haff` argument that
`chartLocusOpens` (`Picard/Pic0ChartUnivReduce.lean:115`) takes, produced rather than passed
through.

`Pic0ChartUnivReduce.lean:104-114` says "nothing in the tree produces `haff` for a general test",
and `Pic0ChartAtlasCoupling.lean:53`/`:142` twice price the `chartLocusOpens` bridge at the cost
of `haff`.  For the widened chart value that is no longer so, and the step is two lines:
`picEtMap_chartValueAff` (`Picard/DivisorFamilyAffAbel.lean:295`) says a *restricted* widened
chart value is again a widened chart value — of the restricted family — so the openness theorem
above applies to each restriction directly.

This section exists because a fresh-context audit found the first version of this file
*understating* itself: it declared that it discharged no consumer's obligation, having checked
only the seam's three antecedents and not the `haff` sites.  Understated prose costs a lane a
round exactly as overstated prose does. -/
theorem chartLocusAffineLocal_chartValueAff (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (s : divFamZarAff C n T) :
    ∀ U : T.left.affineOpens,
      IsOpen (chartLocus C m Z (picEtMap C (Over.fromSpecAffine T U)
        (chartValueAff C n m Z T s))) := by
  intro U
  rw [picEtMap_chartValueAff]
  exact isOpen_chartLocus_chartValueAff C π n hπ m Z _ _

variable (C π n) in
/-- **The chart locus of a widened chart value as an OPEN OF THE TEST**, with no argument left
over — the shape the `W` field of a chart datum consumes (`chartLocusOpens`).

`chartLocusOpens` is where the openness obligation is actually spent, so this, rather than the
bare `IsOpen`, is what a consumer of the widened carrier can use. -/
def chartLocusOpensChartValueAff (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (s : divFamZarAff C n T) : T.left.Opens :=
  chartLocusOpens C m Z T (chartValueAff C n m Z T s)
    (chartLocusAffineLocal_chartValueAff C π n hπ m Z T s)

/-! ## The universal widened source open

The preceding definition produces an open for every widened family.  A representation of
`divFunctorAff C n` carries a distinguished universal family, so it also determines a
distinguished open of the representing object.  This section makes that open, and the exact
range-containment condition used by `liftPointwiseToOpens`, available as named data.

There are two deliberately separate steps.

* `DivFamZarAff.HasFiniteSeparableH1Witness` is a class-intrinsic field predicate.  It asks for
  precisely the finite separable witness appearing in `IsSplitWitness`, but names the class as
  the base change of a widened divisor family rather than as an anonymous Cech class.
* `universalChartSourceAff` specializes `chartLocusOpensChartValueAff` to the universal family
  `rep.homEquiv (𝟙 D)`.  Its range law turns the set-theoretic containment required by the
  restricted-atlas coupling into the pointwise predicate above.

This does not produce `rep`, `IsChartUniv`, or coverage.  It produces the source open `V` that
those constructions use once widened divisor representability is available, and identifies
membership in `V` without an extra hypothesis or a chart-typed representative.
-/

/-- A widened divisor class over a field has a finite-separable `H¹` witness if, after some
finite separable field extension, its base-changed Cech class is represented by a divisor with
vanishing first cohomology.

This is the class-intrinsic content of `IsSplitWitness`: the anonymous presenting class in that
predicate is pinned here to the widened family's Picard class. -/
def DivFamZarAff.HasFiniteSeparableH1Witness {K : Type u} [Field K] [Algebra k K]
    (F : DivFamZarAff C K n) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra K L)
      (_ : IsScalarTower k K L) (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L)
      (W : ((C ⊗ overSpec k L).left).CurveDivisor),
    Scheme.CurveDivisor.picClass L W =
        Scheme.CechPic.map (relCurveMap C K L) F.picClass
      ∧ Subsingleton (Sheaf.HModule
          ((C ⊗ overSpec k L).left.divisorSheaf L W) 1)

omit [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [GeometricallyReduced C.hom] in
/-- The affine Abel value of a widened family is the plus-unit of its Picard class after every
field extension.  This pins the presenting class used by `IsSplitWitness`. -/
theorem abelDivAff'_fibreClass
    {K L : Type u} [Field K] [Algebra k K] [Field L] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L]
    (s : divFamZarAff C n (overSpec k K)) :
    PicEtAff.map C L (picEtAffineEquiv C K (abelDivAff' C n (overSpec k K) s))
      = PicEtAff.unit C L (relPicMk C (overSpec k L)
          (Scheme.CechPic.map (relCurveMap C K L)
            (divFamZarAffAffineEquiv C n K s).picClass)) := by
  rw [picEtAffineEquiv_abelDivAff', abelDivAffPlus, PicEtAff.map_unit, relPicAlgMap_mk]
  refine congrArg (PicEtAff.unit C L) ?_
  refine congrArg (relPicMk C (overSpec k L)) ?_
  have hcurve : relCurveMap C K L =
      (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K L)).left := by
    refine congrArg (fun q : overSpec k L ⟶ overSpec k K => (C ◁ q).left) ?_
    exact Over.OverMorphism.ext rfl
  rw [hcurve]
  rfl

/-- The widened finite-separable `H¹` predicate is exactly `IsSplitWitness` for the widened
Abel value.

The reverse implication uses injectivity of the plus unit and of `relPicMk` to identify the
anonymous Cech class supplied by `IsSplitWitness` with the base-changed widened class. -/
theorem DivFamZarAff.hasFiniteSeparableH1Witness_iff
    (K : Type u) [Field K] [Algebra k K]
    (s : divFamZarAff C n (overSpec k K)) :
    (divFamZarAffAffineEquiv C n K s).HasFiniteSeparableH1Witness
      ↔ IsSplitWitness C (abelDivAff' C n (overSpec k K) s) := by
  constructor
  · rintro ⟨L, hLf, hLk, hLK, htow, hfin, hsep, W, hW, hW1⟩
    letI : Field L := hLf
    letI : Algebra k L := hLk
    letI : Algebra K L := hLK
    letI : IsScalarTower k K L := htow
    letI : Module.Finite K L := hfin
    letI : Algebra.IsSeparable K L := hsep
    exact isSplitWitness_of_presenting_witness C _ _ (abelDivAff'_fibreClass s) W hW hW1
  · rintro ⟨L, hLf, hLk, hLK, htow, hfin, hsep, M, hM, W, hW, hW1⟩
    letI : Field L := hLf
    letI : Algebra k L := hLk
    letI : Algebra K L := hLK
    letI : IsScalarTower k K L := htow
    letI : Module.Finite K L := hfin
    letI : Algebra.IsSeparable K L := hsep
    have hid : PicEtAff.unit C L (relPicMk C (overSpec k L) M)
        = PicEtAff.unit C L (relPicMk C (overSpec k L)
            (Scheme.CechPic.map (relCurveMap C K L)
              (divFamZarAffAffineEquiv C n K s).picClass)) :=
      hM.symm.trans (abelDivAff'_fibreClass s)
    have hMcl : M = Scheme.CechPic.map (relCurveMap C K L)
        (divFamZarAffAffineEquiv C n K s).picClass :=
      relPicMk_injective_of_subsingleton C (overSpec k L)
        (PicEtAff.unit_injective C L hid)
    refine Exists.intro L ?_
    refine Exists.intro hLf ?_
    refine Exists.intro hLk ?_
    refine Exists.intro hLK ?_
    refine Exists.intro htow ?_
    refine Exists.intro hfin ?_
    refine Exists.intro hsep ?_
    refine Exists.intro W ?_
    exact ⟨hW.trans hMcl, hW1⟩

/-- The finite-separable `H¹` predicate at a point of a general test, evaluated on the widened
family pulled to that point's residue field. -/
def divFamZarAff.HasFiniteSeparableH1WitnessAt {T : Over (Spec (.of k))}
    (s : divFamZarAff C n T) (t : T.left) : Prop :=
  (divFamZarAffAffineEquiv C n (Over.testPointField t)
    (divFamZarAff.map C n (Over.testPoint t) s)).HasFiniteSeparableH1Witness

omit [GeometricallyReduced C.hom] in
/-- `chartTwist` cancels the twist in the widened chart value, just as it does for the
chart-typed value. -/
theorem chartTwist_chartValueAff (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor) (T : Over (Spec (.of k)))
    (s : divFamZarAff C n T) :
    chartTwist C m Z T (chartValueAff C n m Z T s) = abelDivAff' C n T s := by
  rw [chartTwist, chartValueAff]
  group

/-- Membership in the chart locus of a widened chart value is exactly the widened family's
finite-separable `H¹` predicate at that point.  In particular the result is independent of the
chosen twist parameters, although those parameters remain part of the chart map. -/
theorem DivFamZarAff.hasFiniteSeparableH1WitnessAt_iff_mem_chartLocus
    {T : Over (Spec (.of k))} (s : divFamZarAff C n T) (t : T.left)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) :
    s.HasFiniteSeparableH1WitnessAt t
      ↔ t ∈ chartLocus C m Z (chartValueAff C n m Z T s) := by
  rw [mem_chartLocus_iff, chartTwist_chartValueAff, picEtMap_abelDivAff']
  exact DivFamZarAff.hasFiniteSeparableH1Witness_iff (C := C) (n := n)
    (Over.testPointField t) _

/-- The universal widened divisor family selected by a representation of `divFunctorAff`. -/
def universalDivFamAff {D : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D) : divFamZarAff C n D :=
  rep.homEquiv (𝟙 D)

omit [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [GeometricallyReduced C.hom] in
/-- Pulling back the universal widened family along `q` gives the family classified by `q`. -/
theorem universalDivFamAff_map {D T : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D) (q : T ⟶ D) :
    divFamZarAff.map C n q (universalDivFamAff rep) = rep.homEquiv q := by
  have h := rep.homEquiv_comp q (𝟙 D)
  rw [Category.comp_id] at h
  exact h.symm

/-- The actual source open `V` on a representing object: the chart locus of its universal
widened divisor family.  Openness is supplied by `chartLocusOpensChartValueAff`. -/
def universalChartSourceAff {D : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) : D.left.Opens :=
  chartLocusOpensChartValueAff C π n hπ m Z D (universalDivFamAff rep)

/-- A point lies in the universal source open exactly when the universal widened family has a
finite-separable `H¹` witness there. -/
theorem mem_universalChartSourceAff_iff {D : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) (y : D.left) :
    y ∈ universalChartSourceAff (C := C) (π := π) rep hπ m Z
      ↔ (universalDivFamAff rep).HasFiniteSeparableH1WitnessAt y := by
  exact (DivFamZarAff.hasFiniteSeparableH1WitnessAt_iff_mem_chartLocus
    (universalDivFamAff rep) y m Z).symm

/-- The range condition consumed by `liftPointwiseToOpens`, specialized to the universal
widened source open, is equivalent to a pointwise finite-separable `H¹` witness for the
universal family at every image point.

This is an iff: it neither strengthens the range condition nor hides a coverage obligation. -/
theorem range_subset_universalChartSourceAff_iff {D T : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) (q : T ⟶ D) :
    Set.range q.left.base ⊆
        Set.range ((universalChartSourceAff (C := C) (π := π) rep hπ m Z).ι.base)
      ↔ ∀ t : T.left,
        (universalDivFamAff rep).HasFiniteSeparableH1WitnessAt (q.left.base t) := by
  constructor
  · intro h t
    apply (mem_universalChartSourceAff_iff (C := C) (π := π) rep hπ m Z _).mp
    have hr := h ⟨t, rfl⟩
    rwa [Scheme.Opens.range_ι] at hr
  · intro h y hy
    obtain ⟨t, rfl⟩ := hy
    rw [Scheme.Opens.range_ι]
    exact (mem_universalChartSourceAff_iff (C := C) (π := π) rep hπ m Z _).mpr (h t)

/-- The chart value of the universal widened family restricts to the chart value of the family
classified by a test morphism. -/
theorem picEtMap_chartValueAff_universal {D T : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) (q : T ⟶ D) :
    picEtMap C q (chartValueAff C n m Z D (universalDivFamAff rep))
      = chartValueAff C n m Z T (rep.homEquiv q) := by
  rw [picEtMap_chartValueAff, universalDivFamAff_map]

end

end AlgebraicGeometry
