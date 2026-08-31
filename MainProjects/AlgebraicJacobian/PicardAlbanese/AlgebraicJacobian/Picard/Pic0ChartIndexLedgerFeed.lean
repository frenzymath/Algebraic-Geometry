/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartIndexAdmissible
import AlgebraicJacobian.Picard.Pic0ChartCoverageThreshold

/-!
# The fixed-ledger-parameter reduction reaches the coverage consumer

## Current status (2026-07-30): this is no longer the route endpoint

Every theorem below remains true, but the advertised `IsDivisorDegree C g` residue was created
by fixing the chart parameter to the minimal ledger bound `M·δ + g`.  Coverage only needs a
parameter *at least* that bound.  `Pic0ChartCoverageThreshold.admissibleCoverageParameter`
chooses a larger positive-theta-degree multiple, and
`exists_uniform_admissibleCoverageChart_eq_univ` proves unconditionally that one resulting
legal chart locus is all of every `pic⁰` test.  Read the reductions below as the exact cost of
the fixed-parameter branch, not as an open hypothesis of DAT-B.

`Picard/Pic0ChartIndexAdmissible.lean` reduces the chart layer's `hdeg` binder to
`IsDivisorDegree C c` ("`c` is the degree of some divisor on `C_k`").  That is a statement about
a group homomorphism's image, with no chart in it.  A reduction that no consumer can consume is
worth nothing, though (`I-1345`'s own lesson: price the *consumer's* carrier), so this file
plugs it in at the one place the tree actually needs it.

`exists_chartIndex_mem_chartLocus_of_ledgerIndex` (`Pic0ChartCoverageThreshold.lean:349`) takes
the constraint `deg_k Z = m·d₁ − (M·δ + g)` as a hypothesis, and its docstring says so
explicitly: *"`Z` of prescribed degree is a divisor-side existence statement this file does not
prove and does not claim."*  `mem_chartLocus_of_ledgerIndex_of_isDegree` below discharges
exactly that clause from `IsDivisorDegree`, with the twist exponent chosen for us (`m = 0`).

## What this buys, stated exactly

Coverage's locus membership at the fixed ledger parameter rests on **one arithmetic hypothesis**
about the base field — `IsDivisorDegree C (M·δ + g)` — in place of an unexhibited pair `(m, Z)`.
The splitting/degree-zero inputs are unchanged, and the following are **untouched**: antecedent 1
(`IsChartUniv`), the pointwise-to-neighbourhood spreading-out that `Pic0ChartCoverageSlice.lean`
records as absent, and `rep` at any parameter.  **No antecedent of `pic0RepresentableByOfCharts`
is discharged here.**

## And what the remaining hypothesis costs, honestly

`IsDivisorDegree C (M·δ + g)` is **not** known to hold.  Over an arbitrary base field `deg_k` is
weighted by residue degrees, so its image is a proper subgroup of `ℤ` in general; the multiples
of `d₁` are admissible unconditionally (`isDegree_mul_thetaDeg`) and `M·δ + g` is not visibly
one of them.

But the residue is **smaller than that paragraph suggests**, and `isDegree_mul_thetaDeg_add_iff`
is why: if `M·δ` is a multiple of `d₁`, then `IsDivisorDegree C (M·δ + g)` is *equivalent* to
`IsDivisorDegree C g` — the ledger constants drop out entirely and what remains is whether the
**genus** is a divisor degree.  So the open question is one hypothesis about `π` versus
`thetaP1 C` (are their fibre degrees commensurable?) plus one about the curve at `g`.

**And the "if" costs nothing** (`isDegree_ledger_add_iff`): read on `C.left`, `δ = windowδ π` *is*
the degree of a divisor — the fibre divisor of the ledger's own `π` — so `M` copies of it shift
the target by `M·δ` in both directions, with no hypothesis.

So the residue of the fixed-ledger-parameter branch is exactly one question:

> **is the genus `g` the degree of a divisor on `C.left`?**

No ledger constant, no θ-class, no chart, no second map.  It is still open — `deg_k` is
residue-degree weighted, so nothing forces `g` into its image over an arbitrary base field, and
the tree's only residue-degree-one point needs `[IsSepClosed k]`
(`Over.dense_baseChange_rationalPoints`, `Curve/SepPointsDense.lean:278`), which the
arbitrary-field statement forbids assuming.

**Two earlier versions of this paragraph priced that residue higher, and both were refuted** —
first "two maps on two different curves, unrelated in the tree", then "a commensurability question
between `π` and `thetaP1 C`".  Each was measured, each was wrong in the expensive direction, and
each is recorded at the theorem that refuted it (`isDivisorDegree_iff_left`,
`isDegree_ledger_add_iff`).  The `rfl` fact `windowδ (thetaP1 C) = classDeg k (thetaCechClass C)`
survives from the first round and is what `isDegree_mul_thetaDeg_add_iff` rests on.

## The chart index this route produces is UNIFORM in the point — read against `I-1389`

`I-1389` warns that a coverage statement at a *fixed* chart index is strictly stronger than
DAT-B's antecedent 2, because the heterogeneous-atlas apparatus (`mixedParamChart`, the
index-by-`m` atlas of `Pic0ChartCoverageIndexSlack`) exists precisely so different points may use
different charts.  The warning applies to this file, so the position is stated rather than left
for a reader to work out:

* the `(m, Z)` comes from `hadm`, which **does not mention the point** `t`, so the chart index
  really is uniform in `t`.  **But that is a fact about the proof, not about the statement** —
  `mem_chartLocus_of_ledgerIndex_of_isDegree` puts its `∃ m Z` *inside* the per-point binders, so
  read literally it is the non-uniform claim.  A first draft asserted the uniformity only in this
  paragraph; since `I-1389`'s whole point is that a chart-index claim must say which of the two it
  is, the uniform form is now a theorem —
  `exists_uniform_chartIndex_forall_mem_chartLocus_of_isDegree`, with `∃ m Z` hoisted outside
  every binder.  (Found by a fresh-context audit of this file.)
* it is nonetheless **not** one-chart coverage in `I-1389`'s sense and does not imply it: even in
  the hoisted form the splitting data `L`, `M₀`, `hM₀` stays quantified per point *inside* the
  conclusion.  What is uniform is the chart index alone.

For this historical branch, the non-uniformity is in the **splitting data**, not in the chart
parameter.  The newer admissible-parameter endpoint eliminates that splitting input internally
and hoists the chart index across every test and class.  Neither result produces the remaining
neighbourhood morphism into the chart.

## Main declarations

* `AlgebraicGeometry.mem_chartLocus_of_ledgerIndex_of_isDegree` — locus membership at the ledger
  parameter from `IsDivisorDegree`, replacing the unexhibited `(m, Z)`.  This is *already* the
  `∃`-form DAT-B B-6 packages; the last section records why a second declaration a first draft
  added was the same proposition and was removed.
* `AlgebraicGeometry.exists_uniform_chartIndex_forall_mem_chartLocus_of_isDegree` — the same, with
  the chart index hoisted out of every per-point binder, so the uniformity is in the statement.
* `AlgebraicGeometry.isDivisorDegree_iff_left` — the predicate transports to `C.left`; the
  base-changed curve is not a second curve.
* `AlgebraicGeometry.isDegree_ledger_add_iff` — the ledger constants drop out unconditionally.
* `AlgebraicGeometry.mem_chartLocus_of_ledgerIndex_of_isDegree_genus` — the fixed-parameter
  endpoint: locus membership at the ledger parameter from `IsDivisorDegree C g`; superseded as
  the live route by `exists_uniform_admissibleCoverageChart_eq_univ`.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- The standing `C.left`-over-`k` structure keyed on `C.hom`, matching
`Pic0ChartCoverageThreshold.lean`'s. -/
noncomputable local instance instOverCleftLedgerFeed :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

noncomputable section

/-! ## The predicate is about `C.left`, not the base-changed curve

A first draft of this file, and of `Pic0ChartIndexAdmissible`, named the residue as arithmetic on
the base-changed curve **plus** an unbridgeable comparison between two curves: "their fibre
degrees are unrelated by anything in the tree.  Naming that precisely is the point of this
paragraph."  **That sentence was false**, found by a fresh-context audit and reproduced here
before being replaced: base change along the identity extension `k → k` is an *isomorphism*, and
the transport of degrees across it is landed.  `RelThetaTransport.lean:49` already names
`relCurveSelfIso` for this collapse and `RelCurveCollapse.lean:492` already pulls a fibre divisor
across it.

So `IsDivisorDegree C c` is a statement about `C.left` — the curve where the residue-degree and
rational-point machinery lives — and the two-*curves* half of the residue costs nothing.  What
remains open is the two-*maps* half: `π : C.left ⟶ P1 k` versus `thetaP1 C`, a commensurability
question on **one** curve, materially cheaper than what the withdrawn sentence named. -/
theorem isDivisorDegree_iff_left {c : ℤ} :
    IsDivisorDegree C c ↔ ∃ W : C.left.CurveDivisor, Scheme.CurveDivisor.deg k W = c := by
  haveI := isIso_fst_left_overSpec_self C
  haveI := instSmoothOfRelativeDimensionBaseChange (C := C) (K := k)
  haveI := instQuasiCompactBaseChange (C := C) (K := k)
  haveI := instModuleFiniteHModuleZeroBaseChange (C := C) (K := k)
  haveI := instModuleFiniteHModuleOneBaseChange (C := C) (K := k)
  constructor
  · rintro ⟨W, hW⟩
    -- transport `W`'s class along the inverse iso, then re-present it by a divisor on `C.left`
    obtain ⟨W', hW'⟩ := Scheme.CurveDivisor.exists_picClass_eq (K := k)
      (X := C.left) (Scheme.CechPic.map (CategoryTheory.inv (fst C (overSpec k k)).left)
        (Scheme.CurveDivisor.picClass k W))
    refine ⟨W', ?_⟩
    rw [← classDeg_picClass k W', hW']
    rw [classDeg_cechPicMap_of_isIso k (CategoryTheory.inv (fst C (overSpec k k)).left) ?_,
      classDeg_picClass k W, hW]
    · rw [CategoryTheory.IsIso.inv_comp_eq]
      exact (fst_left_self_over C).symm
  · rintro ⟨W, hW⟩
    obtain ⟨W', hW'⟩ := Scheme.CurveDivisor.exists_picClass_eq (K := k)
      (X := (C ⊗ overSpec k k).left)
      (Scheme.CechPic.map (fst C (overSpec k k)).left (Scheme.CurveDivisor.picClass k W))
    refine ⟨W', ?_⟩
    rw [← classDeg_picClass k W', hW',
      classDeg_cechPicMap_of_isIso k (fst C (overSpec k k)).left (fst_left_self_over C),
      classDeg_picClass k W, hW]

/-- **THE LEDGER CONSTANTS DROP OUT UNCONDITIONALLY**: the ledger target `M·δ + g` is a divisor
degree if and only if `g` is — with **no** commensurability hypothesis.

This is the third and last correction to this file's own residue pricing, and it removes the
hypothesis the previous two rounds of prose treated as the open question.  The argument, once the
predicate is read on `C.left` (`isDivisorDegree_iff_left`), is one line: `δ = windowδ π` **is**
the degree of a divisor on `C.left`, namely the fibre divisor of `π` itself
(`deg_fiberWeilDivisor_windowδ`).  So `M` copies of it shift the target by exactly `M·δ`, in both
directions.

What the two withdrawn versions said, recorded because each was measured and each was wrong in
the same direction — too expensive:

1. "the ledger constants are unrelated to `d₁`, two maps on two different curves" — refuted by
   `isDivisorDegree_iff_left`: the curves are isomorphic;
2. "so the residue is a commensurability question between `π` and `thetaP1 C` on one curve" —
   refuted here: no comparison between the two maps is needed at all, because the *ledger's own*
   `π` supplies the shift.  `isDegree_mul_thetaDeg_add_iff` does the same job through `d₁` and is
   the θ-side statement; this is the `π`-side one, and it is the one the ledger consumer needs.

**So the entire residue of the coverage route at the ledger parameter is: is the GENUS a divisor
degree on `C.left`?**  That is one question about one curve, with no ledger constant, no θ-class
and no chart in it.  It is still open — `deg_k` is residue-degree weighted, so nothing forces `g`
into its image over an arbitrary base field, and the tree's only residue-degree-one point needs
`[IsSepClosed k]` (`Over.dense_baseChange_rationalPoints`, `Curve/SepPointsDense.lean:278`),
which the arbitrary-field statement forbids assuming. -/
theorem isDegree_ledger_add_iff {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (M : ℕ) (c : ℤ) :
    IsDivisorDegree C ((M : ℤ) * windowδ π + c) ↔ IsDivisorDegree C c := by
  rw [isDivisorDegree_iff_left, isDivisorDegree_iff_left]
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨W - M • fiberWeilDivisor π, ?_⟩
    rw [Scheme.CurveDivisor.deg_sub' k, hW, Scheme.CurveDivisor.deg_nsmul' k,
      deg_fiberWeilDivisor_windowδ]
    ring
  · rintro ⟨W, hW⟩
    refine ⟨W + M • fiberWeilDivisor π, ?_⟩
    rw [Scheme.CurveDivisor.deg_add, hW, Scheme.CurveDivisor.deg_nsmul' k,
      deg_fiberWeilDivisor_windowδ]
    ring

/-- **Coverage's locus membership at the ledger parameter, with the chart index replaced by an
arithmetic hypothesis on the base field.**

`mem_chartLocus_of_ledgerIndex` needs a pair `(m, Z)` with `deg_k Z = m·d₁ − (M·δ + g)`, which
nothing in the tree produces.  `chartIndex_of_isDegree` produces it from
`IsDivisorDegree C (M·δ + g)` alone, taking `m = 0` — so the twist exponent is not a choice the
consumer has to make.

The chart index is `Z = −W` for `W` the divisor of degree `M·δ + g`, and the resulting locus is
`chartLocus C 0 (−W)`; the exponent is `0` because `hdeg` never constrained it. -/
theorem mem_chartLocus_of_ledgerIndex_of_isDegree
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hadm : IsDivisorDegree C ((windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ)))
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (hlam : degAt lam (Over.testPoint t) = 0)
    {L : Type u} [Field L] [Algebra k L] [Algebra (Over.testPointField t) L]
    [IsScalarTower k (Over.testPointField t) L]
    [Module.Finite (Over.testPointField t) L]
    [Algebra.IsSeparable (Over.testPointField t) L]
    (M₀ : (C ⊗ overSpec k L).left.CechPic)
    (hM₀ : PicEtAff.map C L
        (picEtAffineEquiv C (Over.testPointField t) (picEtMap C (Over.testPoint t) lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)] :
    ∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor), t ∈ chartLocus C m Z lam := by
  obtain ⟨m, Z, hZ⟩ := chartIndex_of_isDegree C hadm
  exact ⟨m, Z, mem_chartLocus_of_ledgerIndex hπ g hχ lam t hlam m Z hZ M₀ hM₀⟩

/-- **THE ENDPOINT: coverage at the ledger parameter from the GENUS alone.**

`mem_chartLocus_of_ledgerIndex_of_isDegree` asks for `IsDivisorDegree C (M·δ + g)`, a condition
mentioning two ledger constants.  `isDegree_ledger_add_iff` says that is the same condition as
`IsDivisorDegree C g`, so the ledger constants can be dropped from the interface entirely.

This is the honest headline of the whole `param-admissible` line of work: **coverage's locus
membership at the ledger parameter follows from one arithmetic fact about the curve — that its
genus is a divisor degree — plus the splitting data coverage already has.**  Nothing about charts,
certificates, θ-classes or representability remains in the hypothesis.

It does **not** discharge antecedent 2, and none of the three seam antecedents moves: this is
locus membership at a point, and `Pic0ChartCoverageSlice.lean` records that the pointwise datum
coverage needs also wants a chart *point over a neighbourhood* — a spreading-out absent for this
carrier.  Nor is `IsDivisorDegree C g` known to hold; see the module docstring. -/
theorem mem_chartLocus_of_ledgerIndex_of_isDegree_genus
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hg : IsDivisorDegree C (g : ℤ))
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (hlam : degAt lam (Over.testPoint t) = 0)
    {L : Type u} [Field L] [Algebra k L] [Algebra (Over.testPointField t) L]
    [IsScalarTower k (Over.testPointField t) L]
    [Module.Finite (Over.testPointField t) L]
    [Algebra.IsSeparable (Over.testPointField t) L]
    (M₀ : (C ⊗ overSpec k L).left.CechPic)
    (hM₀ : PicEtAff.map C L
        (picEtAffineEquiv C (Over.testPointField t) (picEtMap C (Over.testPoint t) lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)] :
    ∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor), t ∈ chartLocus C m Z lam :=
  mem_chartLocus_of_ledgerIndex_of_isDegree hπ g hχ
    ((isDegree_ledger_add_iff (windowM_choice π hπ g) (g : ℤ)).mpr hg) lam t hlam M₀ hM₀

/-- **The chart index is UNIFORM in the point — hoisted out of every per-point binder.**

`mem_chartLocus_of_ledgerIndex_of_isDegree` concludes `∃ m Z, t ∈ chartLocus C m Z lam` *inside*
the per-point binders, so as a statement it is the NON-uniform one: read literally, each `t` may
get its own `(m, Z)`.  The uniformity is a fact about the proof, and `I-1389` is precisely the
warning that a chart-index claim must say which of the two it is.  So it is said here, in Lean.

The single `(m, Z)` serves **every** point of every test, at every splitting field: it comes from
`hadm`, which does not mention `t`.  Per `I-1389` this is still **not** one-chart coverage — the
splitting data `L`, `M₀`, `hM₀` remains quantified per point inside the conclusion, and that is
where the route's non-uniformity actually lives. -/
theorem exists_uniform_chartIndex_forall_mem_chartLocus_of_isDegree
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hadm : IsDivisorDegree C ((windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ))) :
    ∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor),
      ∀ {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left),
        degAt lam (Over.testPoint t) = 0 →
        ∀ {L : Type u} [Field L] [Algebra k L] [Algebra (Over.testPointField t) L],
          ∀ [IsScalarTower k (Over.testPointField t) L]
            [Module.Finite (Over.testPointField t) L]
            [Algebra.IsSeparable (Over.testPointField t) L]
            (M₀ : (C ⊗ overSpec k L).left.CechPic),
            PicEtAff.map C L
                (picEtAffineEquiv C (Over.testPointField t)
                  (picEtMap C (Over.testPoint t) lam))
              = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀) →
            ∀ [IsIntegral (relCurve C L)]
              [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
              [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
              [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
              [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)],
              t ∈ chartLocus C m Z lam := by
  obtain ⟨m, Z, hZ⟩ := chartIndex_of_isDegree C hadm
  refine ⟨m, Z, ?_⟩
  intro T lam t hlam L _ _ _ _ _ _ M₀ hM₀ _ _ _ _ _
  exact mem_chartLocus_of_ledgerIndex hπ g hχ lam t hlam m Z hZ M₀ hM₀

/-! ## The B-6 packaging form is the SAME proposition, not a second lemma

`Pic0ChartCoverageThreshold.lean` states its ledger result twice — `mem_chartLocus_of_ledgerIndex`
(bare membership at a given `(m, Z)`) and `exists_chartIndex_mem_chartLocus_of_ledgerIndex` (the
`∃`-form B-6 packages).  There the split is genuine: the two conclusions differ.

**Here it is not, and a first draft of this file shipped both anyway.**  Once the `(m, Z, hZ)`
triple is replaced by `hadm`, the witnesses move inside the existential and the "bare" form *is*
the `∃`-form: `mem_chartLocus_of_ledgerIndex_of_isDegree` already concludes
`∃ m Z, t ∈ chartLocus C m Z lam`.  A second declaration differed from it only by renaming the
bound `m`/`Z` to `m'`/`Z'`, and `@f = @g := rfl` typechecked between them (control: the same
equation between two genuinely different lemmas of this file errors).  It was removed.

Recorded rather than silently deleted because the mechanism is reusable: the two-lemma shape was
transcribed from the file being reduced, and the reduction is exactly what collapsed the
distinction.  **A duplicate can be created by the very step that makes it a duplicate**, and no
`sorry` census, axiom probe or build sees it.  Found by a fresh-context audit of this file, and
reproduced with the `rfl` test above before removal.
-/

end

end AlgebraicGeometry
