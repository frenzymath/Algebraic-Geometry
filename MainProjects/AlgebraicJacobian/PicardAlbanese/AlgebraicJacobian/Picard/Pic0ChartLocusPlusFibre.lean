/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageAbel
import AlgebraicJacobian.Picard.Pic0ChartPlusFibreTower
import AlgebraicJacobian.Picard.Pic0ChartLocusIsoInvariance

/-!
# CHART-U(b) at a general test, from the plus-class identity alone

## What this file is

The endpoint of the CHART-U(b) chain, assembled.  Reading the chain from the bottom up, the
general-test openness `isOpen_chartLocus` rested on:

| input | supplied by |
|---|---|
| iso-invariance of the split predicate | `isSplitWitnessIsoInvariant_holds` (landed, r5) |
| `haff` — affine-local openness | `ChartLocusAffineLocal`, **named** at r6 |
| `haff` from a per-piece presentation | `chartLocusAffineLocal_of_presentation` (r6) |
| `IsChartDatumPresentation` from `hfib` + `hplus` | `isChartDatumPresentation_of_plusFibre` (r6) |
| **`hplus` from `hfib`** | **`isChartDatumPlusFibreAt_of_isScalarTower` (r7)** |

Only the last row was missing, and it was missing while being cited by name — see
`Picard/Pic0ChartPlusFibreTower.lean`'s header for that correction.  With it the chain composes,
and this file states the composite so that no consumer has to rebuild it.

## What the resulting hypothesis is, precisely

`isOpen_chartLocus_of_plusFibre` below asks, for each affine open `U` of the test, for a
`BasicOpenCocycleDatum` over `Γ(T.left, U)` satisfying `IsChartDatumPlusFibre` — one equation of
plus classes per point of `U`.  That hypothesis is:

* **witness-free, `H¹`-free and divisor-free.**  No effective divisor, no vanishing cohomology, no
  degree.  This matters because those three are exactly what the certificate lane produces, and
  their absence is why this leg was always developable ahead of CERT-Σ.
* **certificate-free and divRep-free** — and the instrument matters here, because the obvious one
  gives the wrong answer.  This module's **import closure is not certificate-free**: it reaches
  `DivSchemeCertificate`, `DivSchemeClassify*` and `Pic0AtlasFromDivRep` along
  `Pic0ChartLocusFibreField → DivisorFamilyH1Locus → DivRepClassifyZarKit → …`, purely incidentally
  (the fibre-field file wants an `H¹` locus, which lives in a module that also serves the
  classifier).  So "no certificate module in the imports" is false, and a lane checking
  certificate-freedom by grepping imports would wrongly conclude this leg is gated.
  What is true is the statement about the **theorems**: walking the transitive *constant*
  dependencies of `isOpen_chartLocus_of_plusFibre` (7445 constants) and
  `chartLocusAffineLocal_of_plusFibre` (7448) yields **zero** constants whose name contains
  `Cert`, `DivFamZar`, `FinCover`, `Classify`, `DivRep` or `divRep`.  Availability is cone-relative
  and so is gatedness: measure the declaration's own closure, not the module's imports.
* **not vacuous.**  `IsChartDatumPlusFibre` is a genuine equation between plus classes — `rfl` and
  `simp` both fail on it at arbitrary `μ`, `D` (measured; recorded on
  `isChartDatumPlusFibreAt_self` and re-run for the transport).
* **inhabited.**  `exists_splitting_of_picEt` produces, unconditionally on the curve and at any
  reading field, a presenting class with exactly this shape — so the hypothesis is satisfiable,
  not a reduction to a false premise.  (Both halves of the probe, per the rule this project's
  lanes converged on: run the direction matching which arguments the consumer chooses.)

## What is still NOT closed, stated so the file is not over-read

The hypothesis is a *per-affine-piece existence of a datum with the plus-class property*, and
nothing here produces such a datum.  Producing one is a different obligation from anything above:
it is the identification of the datum's fibre class with `μ`'s fibre, i.e. the content the c9b row
calls the presentation, and for the specific `μ` of the Σ-chart it is where the twist bookkeeping
of `w4-datb` §1.2 enters.  So this file closes CHART-U(b) *modulo a producer*, which is strictly
what the chain above it needed, and does not claim the producer.

In particular this is **not** a claim about `c9b`'s clause (ii).  That clause is the property half
of `IsChartUniv` and remains CERT-Σ/divRep-gated through `IsChartLocusFibre`'s `exists_factor`;
nothing in this file touches it.  What this file removes is clause (i)'s cost — the `W` field, i.e.
the chart-locus open — which the c9b row priced at zero, then correctly re-priced at "B-4 through
`haff`", and which is now genuinely discharged from a witness-free hypothesis.

## Main declarations

* `AlgebraicGeometry.chartLocusAffineLocal_of_plusFibre` — `haff` from a per-piece
  `IsChartDatumPlusFibre`.
* `AlgebraicGeometry.isOpen_chartLocus_of_plusFibre` — **CHART-U(b) at a general test** from that
  hypothesis alone.
* `AlgebraicGeometry.chartLocusOpensOfPlusFibre` — the open of the test as data, which is the
  shape the `W` field of a chart datum consumes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

noncomputable section

/-! ## `haff` from the plus-class identity -/

set_option linter.overlappingInstances false in
variable (C π) in
/-- **The `haff` residue from a per-affine-piece PLUS-CLASS identity.**

`chartLocusAffineLocal_of_presentation` reduces `haff` to a per-piece
`IsChartDatumPresentation`; the transport of `Pic0ChartPlusFibreTower` reduces that to a per-piece
`IsChartDatumPlusFibre`.  This composes the two, so the affine-local residue is discharged from a
hypothesis mentioning no witness, no `H¹` and no divisor.

`IsAffineHom π` follows from `IsFinite π`, whence the disabled overlapping-instance linter — the
same configuration `chartLocusAffineLocal_of_presentation` carries and for the same reason: the
affine-openness route runs through the rigid engine, which needs finiteness. -/
theorem chartLocusAffineLocal_of_plusFibre
    (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T)
    (hfib : ∀ U : T.left.affineOpens,
      ∃ D : BasicOpenCocycleDatum C (Γ(T.left, U.1)) π,
        IsChartDatumPlusFibre C π
          (chartTwist C m Z _ (picEtMap C (Over.fromSpecAffine T U) lam)) D) :
    ChartLocusAffineLocal C m Z T lam :=
  chartLocusAffineLocal_of_presentation C π hπ m Z T lam fun U =>
    let ⟨D, hD⟩ := hfib U
    ⟨D, isChartDatumPresentation_of_plusFibre_tower C π hD⟩

/-! ## CHART-U(b) at a general test -/

set_option linter.overlappingInstances false in
variable (C π) in
/-- **CHART-U(b) AT A GENERAL TEST, from the plus-class identity alone.**

`chartLocus` is open over an arbitrary test object `T`, given for each affine piece of `T` a
datum whose fibre class agrees with the twisted class as plus classes.  No iso-invariance
hypothesis (discharged at r5), no `haff` (discharged above), no presentation (discharged by the
r7 transport), no certificate and no `divRep`.

This is the statement the `chart-u` roadmap row names as CHART-U(b), and the reading of
"unconditional" that row was set `done` on at r5 and had to retract at r6 — the retraction was
that `haff` survived, and `haff` is what is discharged here.  What remains between this and an
unconditional theorem is a *producer* of the per-piece datum, which is a different obligation and
is not claimed; see this file's header. -/
theorem isOpen_chartLocus_of_plusFibre
    (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T)
    (hfib : ∀ U : T.left.affineOpens,
      ∃ D : BasicOpenCocycleDatum C (Γ(T.left, U.1)) π,
        IsChartDatumPlusFibre C π
          (chartTwist C m Z _ (picEtMap C (Over.fromSpecAffine T U) lam)) D) :
    IsOpen (chartLocus C m Z lam) :=
  isOpen_chartLocus_of_affineLocal' C m Z T lam
    (chartLocusAffineLocal_of_plusFibre C π hπ m Z T lam hfib)

set_option linter.overlappingInstances false in
variable (C π) in
/-- **The chart locus as an OPEN OF THE TEST**, from the plus-class identity alone.

This is the form the `W` field of a chart datum consumes: not the `Prop` that the locus is open,
but the `T.left.Opens` it determines.  `chartLocusOpens'` already takes `ChartLocusAffineLocal` as
an explicit argument (so the dependency is visible in the API rather than hidden in an argument
position); this is the same open with that argument discharged.

Recorded as data rather than left to the caller because the c9b row's clause (i) needs an *open*,
and a lane holding only `IsOpen (chartLocus …)` still has to build the bundled `Opens` — which is
exactly the step at which the `haff` cost got lost the first time. -/
def chartLocusOpensOfPlusFibre
    (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T)
    (hfib : ∀ U : T.left.affineOpens,
      ∃ D : BasicOpenCocycleDatum C (Γ(T.left, U.1)) π,
        IsChartDatumPlusFibre C π
          (chartTwist C m Z _ (picEtMap C (Over.fromSpecAffine T U) lam)) D) :
    T.left.Opens :=
  chartLocusOpens' C m Z T lam (chartLocusAffineLocal_of_plusFibre C π hπ m Z T lam hfib)

@[simp]
lemma mem_chartLocusOpensOfPlusFibre
    {hπ : π ≫ P1.structureMap k = C.hom}
    {m : ℕ} {Z : (C ⊗ overSpec k k).left.CurveDivisor}
    {T : Over (Spec (.of k))} {lam : picEt C T}
    {hfib : ∀ U : T.left.affineOpens,
      ∃ D : BasicOpenCocycleDatum C (Γ(T.left, U.1)) π,
        IsChartDatumPlusFibre C π
          (chartTwist C m Z _ (picEtMap C (Over.fromSpecAffine T U) lam)) D}
    {t : T.left} :
    t ∈ chartLocusOpensOfPlusFibre C π hπ m Z T lam hfib ↔ t ∈ chartLocus C m Z lam :=
  Iff.rfl

end

end AlgebraicGeometry
