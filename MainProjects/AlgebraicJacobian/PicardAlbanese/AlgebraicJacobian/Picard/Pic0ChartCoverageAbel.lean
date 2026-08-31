/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoveragePointwise

/-!
# B-5 at the Abel chart: what the pointwise datum unfolds to, and what it costs

`Picard/Pic0ChartCoveragePointwise.lean` reduces `ChartsCoverLocally` — hence B-6 — to a
four-part datum at each point of each test.  That reduction is stated for an *arbitrary*
family of presheaf maps, so it says nothing about how hard the datum is at the family that
matters.  This file instantiates it at `abelSigmaChart` and computes the answer.

## The computation, and the one thing it makes visible

A section of `pic0SigmaSheaf C` over a **bare** test scheme `T` is by definition a *pair*
`⟨a, λ⟩` with `a : T ⟶ Spec k` and `λ` a degree-zero class on the slice object `Over.mk a`
(`Over.sigmaExtension`, `Picard/OverSigmaExtension.lean`).  And `(Over.mk a).left` is `T`
itself, definitionally.  So the big-site/slice crossing that looks like it needs a bridge does
not: the pointwise datum's `t : ↥T` *is* a point of the slice test, and `chartLocus` applies to
it with no transport.  `abelChartApp_eq` below records the crossing as an equation rather than
leaving it to unfold at a use site.

What the computation *does* make visible is where the cost sits.  `abelSigmaChart`'s value at
`x : W ⟶ D.left` is `⟨x ≫ D.hom, chartValue … (rep.homEquiv …)⟩`, so matching it against the
restriction of `⟨a, λ⟩` needs **both** components: the Σ-component is an equation between
morphisms to `Spec k`, and only then is there a class equation.  A producer that supplies the
class half alone has not supplied the datum — the Σ-component is what pins the chart point to
lie *over* the test, and it is free only because `W.ι ≫ a` is what `D.hom` must equal.

## THE CORRECTION THIS FILE CARRIES, against this lane's own headline

`Pic0ChartUnivReduce.lean:40` says of its `chartLocusOpens`:

> `chartLocusOpens` is **constructed**, not hypothesised — the `W` field costs zero, which is
> a real reduction of the datum from four fields to three

**The second clause is false, and the roadmap `c9b` row repeats it** ("`W` needs nothing").
`chartLocusOpens` takes an argument `haff`, the affine-local openness of the locus at every
affine open of the test, and *nothing in the tree discharges it*:
`isOpen_chartLocus_of_affineLocal'` (`Pic0ChartLocusIsoInvariance.lean`) removed the
`IsSplitWitnessIsoInvariant` hypothesis and passes `haff` straight through, as does
`isOpen_chartLocus_of_affineLocal` before it.  The affine case that would feed it is
`isOpen_setOf_isSplitWitness_of_presentation` (`Pic0ChartLocusIsOpen.lean:321`), which is
itself conditional on `IsChartDatumPresentation` — B-4's *named residue*.

**Update, same session** (`Picard/Pic0ChartPresentationConverse.lean`): that residue is now
*entirely witness-free*.  Its forward half already was (the trivial splitting), and its
converse `hconv` — the descent direction, open for three sessions — is discharged by plus-unit
injectivity.  So what `haff` ultimately costs is a `cechPicClass` base-change identity: no
witness, no `H¹`, no divisor, and nothing certificate- or divRep-gated.

So the honest accounting is: **`W` costs `haff`, which costs B-4's presentation residue.**  The
datum went from four fields to three *shapes* but not to three *obligations*.  What is
genuinely free is the type-level crossing above, and `chartLocusHaff` below is the residue
named so it cannot be lost again.

## Main declarations

* `AlgebraicGeometry.abelChartApp_eq` — the Abel chart's value at a point of the divisor
  scheme, as an explicit `Sigma.mk`.  Both components, since the datum needs both.
* `AlgebraicGeometry.ChartLocusAffineLocal` — the `haff` residue, named.  This is what
  `chartLocusOpens` silently costs.
* `AlgebraicGeometry.chartLocusOpens_of_affineLocal` — `chartLocusOpens` from it, so the
  dependency is explicit in the API rather than in an argument position.
* `AlgebraicGeometry.chartLocusAffineLocal_of_presentation` — the residue **reduced to B-4's
  own named obligation**: a per-affine-piece `IsChartDatumPresentation` gives it.  This is the
  link that was asserted in `Pic0ChartLocusIsOpen`'s docstring and never written.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The Abel chart's value, both components -/

/-- **The Abel chart map evaluated at a point of the divisor scheme.**

`abelSigmaChart` is `rep.toSigmaExtension ≫ Over.sigmaExtensionNat (chartValueTrans …)`, and
both factors act componentwise on the Σ-extension, so the value at `x : Y ⟶ D.left` is the
pair whose structure morphism is `x ≫ D.hom` and whose class is the chart value of the divisor
family `rep.homEquiv (Over.homMk x rfl)`.

Recorded as an equation because a coverage producer has to match this against a *given*
section, and the match is two equations rather than one: the Σ-components must agree before
the classes are even in the same type.  Leaving it to unfold at the use site is how the
Σ-component gets forgotten. -/
@[simp]
theorem abelChartApp_eq {D : Over (Spec (.of k))} (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (Y : Scheme.{u}) (x : Y ⟶ D.left) :
    (abelSigmaChart C π n rep m Z hdeg).app (op Y) x
      = ⟨x ≫ D.hom, ⟨chartValue C π n m Z (Over.mk (x ≫ D.hom))
          (rep.homEquiv (Over.homMk x rfl)),
        chartValue_mem_pic0Subgroup C π n m Z hdeg _ _⟩⟩ :=
  rfl

/-! ## The `haff` residue, named

`chartLocusOpens` takes the affine-local openness as an argument.  Naming it is not cosmetic:
an argument in a definition's signature is invisible to a census of open obligations, which is
how "the `W` field costs zero" survived into two roadmap rows. -/

variable (C) in
/-- **The affine-local openness residue of `chartLocus`** — what `chartLocusOpens` costs.

For a test `T` and a class `lam` on it, this says the chart locus is open over every affine
open piece of `T`.  It is exactly the `haff` argument of `isOpen_chartLocus_of_affineLocal'`,
and it is the *only* remaining input to CHART-U(b) at a general test: the iso-invariance
hypothesis that used to sit beside it was discharged
(`isSplitWitnessIsoInvariant_holds`), but this one was passed through, not proved.

Named as a `Prop` so that it appears in searches for open obligations. -/
def ChartLocusAffineLocal (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T) : Prop :=
  ∀ U : T.left.affineOpens,
    IsOpen (chartLocus C m Z (picEtMap C (Over.fromSpecAffine T U) lam))

variable (C) in
/-- `chartLocusOpens` with its cost made explicit in the API.

Identical in content to `chartLocusOpens` — the point is that the dependency is now a named
`Prop` a reader can grep for, rather than an unnamed argument that reads as bookkeeping. -/
def chartLocusOpens' (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T)
    (haff : ChartLocusAffineLocal C m Z T lam) : T.left.Opens :=
  chartLocusOpens C m Z T lam haff

@[simp]
lemma mem_chartLocusOpens' {m : ℕ} {Z : (C ⊗ overSpec k k).left.CurveDivisor}
    {T : Over (Spec (.of k))} {lam : picEt C T} {haff : ChartLocusAffineLocal C m Z T lam}
    {t : T.left} :
    t ∈ chartLocusOpens' C m Z T lam haff ↔ t ∈ chartLocus C m Z lam :=
  Iff.rfl

/-! ## Reducing the residue to B-4's own named obligation

`Pic0ChartLocusIsOpen.lean:321`'s docstring says the general-test statement follows from the
affine one "by the affine-piece locality of the (b-amendment)'s transport (iii)", and adds that
it "is not stated here only because it would need the presentation hypothesis *per affine
piece*".  That is right, and this is the statement it describes. -/

set_option linter.overlappingInstances false in
variable (C π) in
/-- **The `haff` residue from a per-affine-piece presentation** — the link
`Pic0ChartLocusIsOpen`'s docstring describes and does not state.

For each affine open `U` of the test, a `BasicOpenCocycleDatum` over `Γ(T.left, U)` presenting
the restricted twisted class gives openness of the locus on that piece
(`isOpen_setOf_isSplitWitness_of_presentation`), and `chartLocus` over the piece *is* that set
by definition (`chartLocus` unfolds to the split-witness set of the twisted class, and the
twist commutes with restriction by `picEtMap_chartTwist`).

So the affine-local residue is **exactly** B-4's presentation obligation, quantified over
affine pieces — no extra geometry, and in particular nothing certificate- or divRep-gated.
Combined with `isOpen_chartLocus_of_affineLocal'` this closes CHART-U(b) at a general test the
moment `IsChartDatumPresentation` is available per piece.

The `hπ` and `IsFinite π` hypotheses are the ones
`isOpen_setOf_isSplitWitness_of_presentation` carries.  `IsFinite π` is strictly stronger than
the file-level `IsAffineHom π` (whence the overlapping-instance warning, disabled below): the
affine openness route runs through the rigid engine, which needs finiteness, while the rest of
this file needs only affineness. -/
theorem chartLocusAffineLocal_of_presentation [IsFinite π]
    (hπ : π ≫ P1.structureMap k = C.hom)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T)
    (hpres : ∀ U : T.left.affineOpens,
      ∃ D : BasicOpenCocycleDatum C (Γ(T.left, U.1)) π,
        IsChartDatumPresentation C π
          (chartTwist C m Z _ (picEtMap C (Over.fromSpecAffine T U) lam)) D) :
    ChartLocusAffineLocal C m Z T lam := by
  intro U
  obtain ⟨D, hD⟩ := hpres U
  exact isOpen_setOf_isSplitWitness_of_presentation C π hπ hD

end

end AlgebraicGeometry
