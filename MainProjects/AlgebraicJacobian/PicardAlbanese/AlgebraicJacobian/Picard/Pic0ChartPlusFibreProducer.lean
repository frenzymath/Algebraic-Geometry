/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartLocusPlusFibre

/-!
# THE PRODUCER: `IsChartDatumPlusFibre` for a class in the image of the sheafification unit

## What this file closes

`Picard/Pic0ChartLocusPlusFibre.lean` proves CHART-U(b) at a general test from a per-affine-piece
`IsChartDatumPlusFibre`, and its header says plainly what it does not do:

> The hypothesis is a *per-affine-piece existence of a datum with the plus-class property*, and
> nothing here produces such a datum.

**This file produces one**, and the ingredient that was missing is smaller than four successive
sessions on this leaf priced it: on an **affine** test the canonical field point `Over.testPoint t`
**is** the base-change morphism `overSpecMap A κ(t)`.  Both sides are `Spec` of the same ring map —
`Over.instAlgebraTestPointFieldAffine` is *defined* as `Spec.preimage` of `fromSpecResidueField`,
so `Spec.map_preimage` closes it — but nothing in the tree said so, and every plus-class identity
on this lane is an identity between a class pulled along `Over.testPoint` and one pulled along
`relCurveMap`.  Without the comparison the two sides are not even syntactically comparable; with
it they are the same class.

## The shape of the producer, and its one genuine restriction

`IsChartDatumPlusFibre C π μ D` compares `μ`'s fibre at `κ(t)`, read as a plus class, with the
plus-*unit* of `D`'s fibre class.  So the natural hypothesis on `μ` is that it is *already* a
plus unit — i.e. in the image of the sheafification unit `relPicToPicEt` — and then `D` comes
from `exists_cechPicClass_eq` applied to any Čech representative.

That restriction is real and is named `IsPlusHonest` below.  It is **not** vacuous and **not**
automatic:

* not automatic — a general plus class over `Spec A` is `PicEtAff.mk E x` for an étale cover `E`,
  and `Picard/Pic0ChartHonest.lean` is precisely the record that it becomes honest only over
  `E.Carrier`, not over `A`.  So `IsPlusHonest` is a genuine hypothesis, not a restatement;
* not vacuous, and this is the payoff — the range of `relPicToPicEt` is a **subgroup**, and every
  class the chart layer twists by is in it: the θ-family (`thetaFamily_isPlusHonest`), the
  Σ-family, and the Abel value itself (`abelDiv_isPlusHonest`).  So `chartTwist` preserves
  honesty, and CHART-U(b) becomes **unconditional** on exactly the classes DAT-C's Σ-chart reads.

  **A CORRECTION TO THIS PARAGRAPH, from a fresh-context review of the commit that first wrote
  it, and it is the same failure this leaf recorded one round earlier.**  When first committed the
  sentence above cited `abelDiv_isPlusHonest` **and that declaration did not exist** — a
  workspace-wide grep returned exactly one hit, the sentence itself.  That is precisely the
  failure mode r7 diagnosed (`docstring-declaration-lists-unchecked`) and filed a lesson about,
  reproduced by the very session that filed it, inside its own *non-vacuity* argument.
  A kernel check, a `sorry` census and an axiom probe are all silent about it.

  It also mattered mathematically, which is why it was worth writing rather than deleting: the
  θ- and Σ-witnesses are the **twist factors**, which `chartTwist_isPlusHonest` discharges anyway,
  so they say nothing about the class being *charted*.  Since `chartValue = abelDiv · Σ · (θᵐ)⁻¹`,
  honesty of a chart value reduces to honesty of `abelDiv` alone — so `abelDiv_isPlusHonest` was
  carrying the whole of the final clause.  It is now proved (below), so the paragraph stands as
  written; had it not been, the honest statement would have been "no residue beyond
  `IsPlusHonest lam`", with the Σ-chart clause unproved.

## Main declarations

* `AlgebraicGeometry.testPoint_eq_overSpecMap` — **the comparison**: on an affine test the
  canonical field point is the base-change morphism.
* `AlgebraicGeometry.isChartDatumPlusFibre_of_relPicToPicEt` — the producer, with the datum given.
* `AlgebraicGeometry.exists_isChartDatumPlusFibre_of_mem_range` — **the producer proper**: for a
  class in the image of the unit, a datum with the plus-class property EXISTS.
* `AlgebraicGeometry.IsPlusHonest` — the per-affine-piece form, closed under the group operations.
* `AlgebraicGeometry.isOpen_chartLocus_of_isPlusHonest` — **CHART-U(b) with no residue** for an
  honest class, and `chartLocusOpensOfIsPlusHonest` the same open as DATA.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

noncomputable section

/-! ## The comparison: on an affine test the field point IS the base change -/

/-- **On an affine test, the canonical field point is the base-change morphism.**

`Over.testPoint t : overSpec k κ(t) ⟶ overSpec k A` is built from mathlib's
`Scheme.fromSpecResidueField`, while `overSpecMap A κ(t)` is `Spec` of `algebraMap A κ(t)`.  They
are equal because the `A`-algebra structure on `κ(t)` (`instAlgebraTestPointFieldAffine`) is
*defined* to be `Spec.preimage` of that very morphism, so `Spec.map_preimage` is the whole proof.

**Why this was the gate.**  Every plus-class identity on this lane compares a class pulled along
`Over.testPoint` (the `chartLocus` side, indexed by points of a test) with one pulled along
`relCurveMap C A κ(t)` (the datum side, indexed by base change).  Absent this lemma the two are
not syntactically comparable and no producer can be written; with it they are the same morphism
and the producer below is three rewrites.  The lemma is *cheap*, which is the point: four
sessions on this leaf priced the missing producer as the identification of a fibre class, i.e.
as geometry, when what was missing was a comparison of two spellings of one morphism. -/
theorem testPoint_eq_overSpecMap {A : Type u} [CommRing A] [Algebra k A]
    (t : (overSpec k A).left) :
    Over.testPoint t
      = overSpecMap (k := k) A (Over.testPointField (T := overSpec k A) t) := by
  apply Over.OverMorphism.ext
  simp only [Over.testPoint_left, overSpecMap_left]
  rw [Over.algebraMap_testPointFieldAffine]
  exact (Spec.map_preimage _).symm

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  [GeometricallyReduced C.hom] in
/-- The whiskered form: the relative-curve comparison at the field point of an affine test is
`relCurveMap`.  This is the shape `IsChartDatumPlusFibre` reads on its right-hand side. -/
theorem relCurveMap_testPoint {A : Type u} [CommRing A] [Algebra k A]
    (t : (overSpec k A).left) :
    (C ◁ Over.testPoint t).left
      = relCurveMap C A (Over.testPointField (T := overSpec k A) t) := by
  rw [testPoint_eq_overSpecMap]
  rfl

/-! ## The producer -/

omit [GeometricallyReduced C.hom] in
variable (C π) in
/-- **THE PRODUCER, with the datum supplied**: if `μ` is the unit image of a relative Picard
class presented by the Čech class `L₀`, then any datum whose class is `L₀` satisfies
`IsChartDatumPlusFibre`.

The proof is four rewrites and no geometry.  `picEtMap_relPicToPicEt` moves the restriction to
`κ(t)` inside the unit; `picEtAffineEquiv_relPicToPicEt` collapses the affine comparison to
`PicEtAff.unit`; `PicEtAff.map_id` deletes the identity restriction `κ(t) → κ(t)` that
`IsChartDatumPlusFibre`'s left-hand side carries; and `relCurveMap_testPoint` identifies
the two spellings of the base change.

Note which hypotheses are absent: no witness, no `H¹`, no divisor, no degree, no separability,
and no certificate.  The plus-class identity was never geometry — it is the statement that the
two ways of restricting a *unit* to a residue field agree.

**A measurement, not a claim, and it is independent evidence for that reading**: this theorem does
not use `GeometricallyReduced C.hom` either — the linter says so, hence the `omit`.  A statement
about a fibre class would need the curve's geometry; this one needs the curve only to have the
functor defined. -/
theorem isChartDatumPlusFibre_of_relPicToPicEt {A : Type u} [CommRing A] [Algebra k A]
    (L₀ : (C ⊗ overSpec k A).left.CechPic) (D : BasicOpenCocycleDatum C A π)
    (hD : D.cechPicClass = L₀) :
    IsChartDatumPlusFibre C π
      (relPicToPicEt C (overSpec k A) (relPicMk C (overSpec k A) L₀)) D := by
  intro t
  rw [picEtMap_relPicToPicEt, picEtAffineEquiv_relPicToPicEt, PicEtAff.map_id, hD,
    relPicMap_mk, relCurveMap_testPoint]
  rfl

omit [GeometricallyReduced C.hom] in
variable (C π) in
/-- **THE PRODUCER PROPER**: for a class in the image of the sheafification unit, a datum with
the plus-class property EXISTS.

The datum comes from `BasicOpenCocycleDatum.exists_cechPicClass_eq` (the extraction keystone,
`Cohomology/GluedSheafExtraction.lean:301`) applied to any Čech representative of the class, and
`relPicMk_surjective` supplies the representative.  So the existential
`isOpen_chartLocus_of_plusFibre` asks for is met outright, with no choice left to the caller.

This is the statement `Picard/Pic0ChartLocusPlusFibre.lean`'s header names as not claimed, and it
too is `GeometricallyReduced`-free. -/
theorem exists_isChartDatumPlusFibre_of_mem_range {A : Type u} [CommRing A] [Algebra k A]
    (μ : picEt C (overSpec k A))
    (hμ : ∃ z : relPic C (overSpec k A), relPicToPicEt C (overSpec k A) z = μ) :
    ∃ D : BasicOpenCocycleDatum C A π, IsChartDatumPlusFibre C π μ D := by
  obtain ⟨z, rfl⟩ := hμ
  obtain ⟨L₀, rfl⟩ := relPicMk_surjective C (overSpec k A) z
  obtain ⟨D, hD⟩ := BasicOpenCocycleDatum.exists_cechPicClass_eq
    (C := C) (B := A) (π := π) L₀
  exact ⟨D, isChartDatumPlusFibre_of_relPicToPicEt C π L₀ D hD⟩

/-! ## The honesty hypothesis, and why it is not vacuous -/

variable (C) in
/-- **The honesty hypothesis: `μ` is a plus unit on every affine piece of the test.**

This is the one thing the producer needs of `μ`, and it is a genuine hypothesis rather than a
restatement: a plus class over `Spec A` is `PicEtAff.mk E x` for an étale cover `E`, and
`Picard/Pic0ChartHonest.lean` is the record that it becomes honest over `E.Carrier` and not over
`A`.  So `IsPlusHonest` is exactly the gap between an arbitrary class and one the producer reaches.

It is stated per affine piece because that is the shape `isOpen_chartLocus_of_plusFibre` consumes;
over an affine test it is the single condition that `μ` is in the range of `relPicToPicEt`. -/
def IsPlusHonest (T : Over (Spec (.of k))) (μ : picEt C T) : Prop :=
  ∀ U : T.left.affineOpens, ∃ z : relPic C (overSpec k Γ(T.left, U.1)),
    relPicToPicEt C (overSpec k Γ(T.left, U.1)) z
      = picEtMap C (Over.fromSpecAffine T U) μ

omit [SmoothOfRelativeDimension 1 C.hom] in
variable (C) in
/-- Honesty is closed under multiplication — the range of `relPicToPicEt` is a subgroup, and
`picEtMap` is a homomorphism. -/
theorem IsPlusHonest.mul {T : Over (Spec (.of k))} {μ ν : picEt C T}
    (hμ : IsPlusHonest C T μ) (hν : IsPlusHonest C T ν) :
    IsPlusHonest C T (μ * ν) := by
  intro U
  obtain ⟨z, hz⟩ := hμ U
  obtain ⟨w, hw⟩ := hν U
  exact ⟨z * w, by rw [map_mul, hz, hw, map_mul]⟩

omit [SmoothOfRelativeDimension 1 C.hom] in
variable (C) in
/-- Honesty is closed under inversion. -/
theorem IsPlusHonest.inv {T : Over (Spec (.of k))} {μ : picEt C T}
    (hμ : IsPlusHonest C T μ) :
    IsPlusHonest C T μ⁻¹ := by
  intro U
  obtain ⟨z, hz⟩ := hμ U
  exact ⟨z⁻¹, by rw [map_inv, hz, map_inv]⟩

omit [SmoothOfRelativeDimension 1 C.hom] in
variable (C) in
/-- Honesty is closed under powers. -/
theorem IsPlusHonest.pow {T : Over (Spec (.of k))} {μ : picEt C T}
    (hμ : IsPlusHonest C T μ) (m : ℕ) :
    IsPlusHonest C T (μ ^ m) := by
  intro U
  obtain ⟨z, hz⟩ := hμ U
  exact ⟨z ^ m, by rw [map_pow, hz, map_pow]⟩

variable (C) in
/-- **A θ-family is honest at every test** — the first half of the non-vacuity check.

`thetaFamily_natural` restricts a θ-family to a θ-family, and `thetaFamily_overSpec_affineEquiv`
says its affine collapse is the plus unit of the base-changed base class.  So a θ-family is in the
range of the unit on every affine piece, with no hypothesis on the curve.

This is why `chartTwist` preserves honesty: two of its three factors are θ-families. -/
theorem thetaFamily_isPlusHonest (L₀ : (C ⊗ overSpec k k).left.CechPic)
    (T : Over (Spec (.of k))) :
    IsPlusHonest C T (thetaFamily C L₀ T) := by
  intro U
  refine ⟨relPicAlgMap C (Algebra.ofId k Γ(T.left, U.1)) (relPicMk C (overSpec k k) L₀), ?_⟩
  rw [thetaFamily_natural]
  exact (picEtAffineEquiv C Γ(T.left, U.1)).injective (by
    rw [picEtAffineEquiv_relPicToPicEt, thetaFamily_overSpec_affineEquiv])

variable (C) in
/-- A Σ-family is honest: it *is* a θ-family (`sigmaFamily` is defined as one). -/
theorem sigmaFamily_isPlusHonest (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) :
    IsPlusHonest C T (sigmaFamily C Z T) :=
  thetaFamily_isPlusHonest C _ T

variable (C π) in
/-- **THE ABEL VALUE IS HONEST AT EVERY TEST** — the witness that carries weight, and the one this
file's header cited by name before it existed (see the header's own retraction).

The θ- and Σ-family witnesses above are the *twist factors*, which `chartTwist_isPlusHonest`
discharges anyway; they say nothing about the class being charted.  Since
`chartValue = abelDiv · Σ · (θᵐ)⁻¹` and honesty is a subgroup condition, honesty of a **chart
value** reduces to honesty of `abelDiv` — so this is the row that makes CHART-U(b) unconditional
on the classes DAT-C's Σ-chart actually reads.

It is cheap for a structural reason: `abelDiv`'s components are `abelDivPlus`, i.e. `PicEtAff.unit`
of `relPicMk` of the family's class, and `relPicToPicEt`'s components are `PicEtAff.unit` of
`relPicMap` — so the witness on the piece `U` is the class of the *restricted* family, and
`abelDiv_val` plus `picEtMap_abelDiv` line the two up. -/
theorem abelDiv_isPlusHonest {n : ℕ} (T : Over (Spec (.of k)))
    (s : divFamZar C π n T) :
    IsPlusHonest C T (abelDiv C π n T s) := by
  intro U
  refine ⟨relPicMk C (overSpec k Γ(T.left, U.1))
    ((divFamZarAffineEquiv C π n Γ(T.left, U.1)
      (divFamZar.map C π n (Over.fromSpecAffine T U) s)).picClass), ?_⟩
  rw [picEtMap_abelDiv, abelDiv_overSpec]
  rfl

variable (C) in
/-- **`chartTwist` PRESERVES honesty** — the reason the producer reaches the Σ-chart.

`chartTwist λ = λ · θᵐ · Σ⁻¹`, and both twist factors are θ-families, hence honest at every test
with no hypothesis.  Since honesty is a subgroup condition, the twisted class is honest exactly
when `λ` is.

So the residue of CHART-U(b) is **the λ-factor alone**: no twist bookkeeping enters, which is the
mis-pricing the §3.3 correction 5 records. -/
theorem chartTwist_isPlusHonest (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) {lam : picEt C T} (hlam : IsPlusHonest C T lam) :
    IsPlusHonest C T (chartTwist C m Z T lam) := by
  rw [chartTwist]
  exact (hlam.mul C ((thetaFamily_isPlusHonest C (thetaCechClass C) T).pow C m)).mul C
    ((sigmaFamily_isPlusHonest C Z T).inv C)

/-! ## CHART-U(b) with the residue discharged -/

set_option linter.overlappingInstances false in
variable (C π) in
/-- **CHART-U(b) AT A GENERAL TEST, WITH NO RESIDUE**, for a class that is honest on the affine
pieces of the test.

`isOpen_chartLocus_of_plusFibre` needs a per-piece datum with the plus-class property;
`exists_isChartDatumPlusFibre_of_mem_range` produces one from honesty, and
`chartTwist_isPlusHonest` says the twist does not disturb honesty.  So the whole chain — the
engine, RE-5, the dictionary, the fibre-field invariance, `haff`, the presentation, `hconv`,
`hplus`, and now the producer — closes on the single hypothesis `IsPlusHonest`.

`IsAffineHom π` follows from `IsFinite π`, whence the disabled overlapping-instance linter — the
same configuration `chartLocusAffineLocal_of_plusFibre` carries and for the same reason. -/
theorem isOpen_chartLocus_of_isPlusHonest
    (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T) (hlam : IsPlusHonest C T lam) :
    IsOpen (chartLocus C m Z lam) :=
  isOpen_chartLocus_of_plusFibre C π hπ m Z T lam fun U =>
    exists_isChartDatumPlusFibre_of_mem_range C π _
      (by
        obtain ⟨z, hz⟩ := chartTwist_isPlusHonest C m Z T hlam U
        exact ⟨z, hz.trans (picEtMap_chartTwist m Z (Over.fromSpecAffine T U) lam)⟩)

set_option linter.overlappingInstances false in
variable (C π) in
/-- **The chart locus as an OPEN OF THE TEST, from honesty alone** — the shape the `W` field of a
chart datum consumes (`chartLocusOpens`, `Picard/Pic0ChartUnivReduce.lean:115`), with its `haff`
argument discharged rather than passed through.

This is c9b's clause (i) paid in full for an honest class: not "reduced to", but produced. -/
def chartLocusOpensOfIsPlusHonest
    (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T) (hlam : IsPlusHonest C T lam) :
    T.left.Opens where
  carrier := chartLocus C m Z lam
  is_open' := isOpen_chartLocus_of_isPlusHonest C π hπ m Z T lam hlam

@[simp]
lemma mem_chartLocusOpensOfIsPlusHonest
    {hπ : π ≫ P1.structureMap k = C.hom}
    {m : ℕ} {Z : (C ⊗ overSpec k k).left.CurveDivisor}
    {T : Over (Spec (.of k))} {lam : picEt C T} {hlam : IsPlusHonest C T lam}
    {t : T.left} :
    t ∈ chartLocusOpensOfIsPlusHonest C π hπ m Z T lam hlam ↔ t ∈ chartLocus C m Z lam :=
  Iff.rfl

end

end AlgebraicGeometry
