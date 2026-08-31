/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartLocusFibreGuard

/-!
# DECIDING THE FORK: what non-injectivity of the unrestricted Abel chart actually costs

`Picard/Pic0ChartLocusFibreGuard.lean` makes the fork precise and machine-checked:
`IsChartLocusFibre` implies the Abel chart is a monomorphism, which three headers
(`Pic0AtlasFromDivRep.lean:54`, `Pic0ChartPair.lean:14`,
`Pic0ChartOpenImmersionCriterion.lean:214`) assert it is not.  Exactly one side is right, and
the guard leaves the deciding statement — non-injectivity — as prose.

**This file reduces that statement to divisor data.**  The reduction is what was missing: the
Abel chart's app does not take divisors, it takes `D.left`-points, so "two divisors in one
linear system" is not by itself a witness.  Reading `abelChartApp_eq`
(`Pic0ChartCoverageAbel.lean:105`), a point `x : Y ⟶ D.left` is sent to the **pair**

  `⟨x ≫ D.hom, chartValue … (rep.homEquiv (Over.homMk x rfl))⟩`

so a non-injectivity witness owes *two* agreements, not one: the Σ-components `x ≫ D.hom` must
agree before the classes are in the same type at all.  That is the trap the c9b row names.

## What is proved here

The reduction, in the direction a witness-builder needs, and its converse:

* `not_injective_abelSigmaChart_of_points` — from two `D.left`-points over one test with
  **equal structure morphism** and **equal chart value** but distinct as points, the Abel chart
  fails to be injective; `not_isChartLocusFibre_of_points` composes that with the guard to
  refute `IsChartLocusFibre`.
* `not_isChartLocusFibre_of_divFamZar` — the same reduction **reparameterised onto divisor
  families**: two distinct elements of `divFamZar C π n T` with equal chart value.  Here the
  Σ-component hypothesis is not passed in: both points are `(rep.homEquiv.symm sᵢ).left`, whose
  structure morphism is the test's own by `Over.w`, so `hstruct` holds by construction.
  **This is a change of parameterisation, not a strengthening** — the two forms are
  inter-derivable (from the family form, take `T := Over.mk (x₁ ≫ D.hom)` and use
  `rep.homEquiv.injective` for distinctness), so `hstruct` is absorbed by the choice of test
  rather than eliminated.  Its value is that the family form is the shape a divisor argument
  produces, with no scheme-theoretic side condition to discharge first.
* `abelChartApp_inj_iff` — the unfolded shape of injectivity at a test, by `Iff.rfl`.  A
  documentation lemma only: it has no call site below, and `abelChartApp_eq`
  (`Pic0ChartCoverageAbel.lean:105`) already exposes both components.

## What is NOT proved here, stated so this file is not over-read

**Nothing here exhibits a curve on which the hypothesis holds, and no theorem below closes the
fork.**  Every statement here is an implication whose antecedent is open.  What remains is
exactly:

  for some curve, some test `T`, and some `n`: two *distinct* elements of `divFamZar C π n T`
  whose `chartValue` agree.

Three things to know before pricing that, and the third is the one that moves.

1. Over a field test it is the classical `h⁰(𝒪(D)) ≥ 2 ⇒ |D|` has two points.
   `Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one` (`RiemannRoch/EffectiveUniqueness.lean:144`)
   is the exact boundary: uniqueness holds **at** `h⁰ = 1`, so the hypothesis to arrange is
   `h⁰ ≥ 2`.  It is the statement to contradict, not to apply.
2. The passage from two *divisors* to two distinct *elements of `divFamZar`* is not free: the
   families are a quotient of local-equation data (`DivisorFamilyZar.lean:235`), so distinct
   divisors need not give distinct families until that equivalence is read.  Nothing here
   assumes otherwise.
3. **`n` is not free.**  At `n = g` the chart's own degree calibration makes the *fibrewise*
   linear system a single point for free: over a field `K`, an effective `K`-divisor of degree
   `g` with `Subsingleton H¹` has `h⁰ = 1` exactly (`degAt_chartTwist`'s `+g` discussion in
   `Pic0ChartLocus.lean:178-201`, and the rank anchor
   `h0_eq_deg_add_chi_of_subsingleton_hModule_one`, `RiemannRoch/FLVClass.lean:412`, giving
   `h⁰ = g + (1 − g) = 1`).  So the *fibrewise* form of the headers' reason — a
   positive-dimensional `|D|` — is unavailable at `n = g` wherever `H¹` vanishes.

**AND HERE IS THE LIMIT OF THAT OBSERVATION, which item 3 must not be read past.**  Every anchor
in item 3 is fibrewise over one field: `CurveDivisor` over `K`, `h⁰` a `finrank` over `K`,
`degAt` evaluated at `overSpec k K`-points.  The obligation is **general-test**: injectivity of
`.app (op Y)` at arbitrary `Y`, and correspondingly distinctness in `divFamZar C π n T` at
arbitrary `T`.  A fibrewise anchor does not settle a general-test statement, and the brick that
would bridge them is *relative* GAP-2 — exactly `ChartFibrePresented.exists_factor`
(`Pic0ChartOpenImmersionCriterion.lean:140`), which `Pic0ChartUnivReduce.lean:160-161` names as
"the relative form of DAT-C GAP-2" and which **nothing in the tree produces**: no declaration
concludes `s₁ = s₂` for two `divFamZar` sections from an equality of their classes.

So item 3 **relocates** the fork; it does not shrink it.  What it changes is what a witness
should aim at: a bare "two divisors in one linear system" is the wrong target, because at `n = g`
with `h¹ = 0` there are none fibrewise — so a witness wants a point of the divisor scheme where
`H¹` fails to vanish, or a genuinely relative failure of uniqueness that no fibre sees.  Which
of those two it is, is undecided here.  (The degree-`g`/`h⁰ = 1` link is `ajcr-p4`'s measurement,
I-0888; the fibrewise/general-test caveat is a fresh-context review's, I-0923/I-0924.)

**A SECOND ROUTE TO THE SAME FORK, added 2026-07-30
(`Picard/Pic0ChartCoverForcesNonInj.lean`), and it does not go through the carve at all.**  The
discussion above — and the `abel-noninj` row — treat the fork as a question about `DivScheme g`:
does it carry a point where `H¹` fails to vanish?  It is *also* a question coverage answers.
`not_injective_of_pointwiseCoverage_of_ne_top` shows that for a **one-chart** atlas,
`PointwiseCoverage` at any open `V ≠ ⊤` produces a test on which the chart is not injective:
instantiate coverage at the test `D.left` itself and at the *tautological* section, at a point
outside `V`; the coverage witness factors through `V` and the tautological one does not.  No
divisor, no `H¹`, no carve fact enters.

Two consequences for a lane on this row:

* the fork's **negative** branch is implied by coverage at any proper `V`, so a witness of the
  kind item 3 describes is not the only way to it — and the composites
  `not_isChartLocusFibre_of_pointwiseCoverage_of_ne_top` /
  `not_restrictedChartFibre_top_of_pointwiseCoverage_of_ne_top` land it directly;
* the fork's **positive** branch — the one item 3 argues for at `n = g` — now has a *cost*:
  by the contrapositive `not_pointwiseCoverage_of_injective_of_ne_top`, an injective chart
  admits coverage at no proper `V`, and `⊥` is refuted too (`not_coverageContainment_bot`), so
  the seam could then close only at `V = ⊤`.  The two branches are no longer "one kills the old
  route, the other is the cheap outcome": each carries a commitment about `V`.

Nothing there is discharged — coverage at a proper `V` has no producer — and the general-test
caveat above is untouched: the new route sidesteps it rather than answering it, because it never
needs a fibrewise statement in the first place. -/

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

variable {D : Over (Spec (.of k))} (rep : (divFunctor C π n).RepresentableBy D)
variable (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
variable (hdeg : Scheme.CurveDivisor.deg k Z
  = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))

/-! ## The exact shape of injectivity at a test -/

/-- **Injectivity of the Abel chart at a test, unfolded.**

`abelChartApp_eq` is `rfl`, so injectivity of the app at `op Y` is *literally* injectivity of
the pair-valued map below.  Recorded as an `Iff` on the nose so that a lane attacking either
branch of the fork works with the two components explicitly and cannot silently drop the
Σ-component. -/
theorem abelChartApp_inj_iff (Y : Scheme.{u}) :
    Function.Injective ((abelSigmaChart C π n rep m Z hdeg).app (op Y))
      ↔ Function.Injective (fun x : Y ⟶ D.left =>
          (⟨x ≫ D.hom, ⟨chartValue C π n m Z (Over.mk (x ≫ D.hom))
              (rep.homEquiv (Over.homMk x rfl)),
            chartValue_mem_pic0Subgroup C π n m Z hdeg _ _⟩⟩ :
            (pic0SigmaSheaf C).1.obj (op Y))) :=
  Iff.rfl

/-! ## The reduction, in the direction a witness-builder needs -/

/-- **Two `D.left`-points over one test with the same chart value refute the certificate.**

The hypotheses are exactly the two agreements `abelChartApp_eq` demands — equal structure
morphism (`hstruct`) and equal chart value after that identification (`hval`) — together with
distinctness of the points themselves.

Note `hval` is stated at the *transported* family: once `hstruct` identifies the Σ-components,
both chart values live over `Over.mk (x₁ ≫ D.hom)` and the equation typechecks. -/
theorem not_injective_abelSigmaChart_of_points {Y : Scheme.{u}} (x₁ x₂ : Y ⟶ D.left)
    (hne : x₁ ≠ x₂) (hstruct : x₁ ≫ D.hom = x₂ ≫ D.hom)
    (hval : chartValue C π n m Z (Over.mk (x₁ ≫ D.hom))
        (rep.homEquiv (Over.homMk x₁ rfl))
      = chartValue C π n m Z (Over.mk (x₁ ≫ D.hom))
          (rep.homEquiv (Over.homMk x₂ hstruct.symm))) :
    ¬ Function.Injective ((abelSigmaChart C π n rep m Z hdeg).app (op Y)) := by
  intro hinj
  refine hne (hinj ?_)
  -- both values are Σ-elements over the *same* structure morphism after `hstruct`
  refine Over.sigmaExtension_ext (pic0TypeFunctor C) hstruct ?_
  -- the transport of `x₂`'s family along `mkCongr hstruct` is `x₂` read over `x₁`'s base
  have hmap : (divFunctor C π n).map (Over.mkCongr hstruct).op
        (rep.homEquiv (Over.homMk x₂ rfl))
      = rep.homEquiv (Over.homMk x₂ hstruct.symm) := by
    rw [← rep.homEquiv_comp]
    exact congrArg rep.homEquiv (Over.OverMorphism.ext (Category.id_comp x₂))
  have hnat := ConcreteCategory.congr_hom
    ((chartValueTrans C π n m Z hdeg).naturality (Over.mkCongr hstruct).op)
    (rep.homEquiv (Over.homMk x₂ rfl))
  refine hnat.symm.trans ?_
  rw [ConcreteCategory.comp_apply, hmap]
  exact Subtype.ext hval.symm

/-- **Hence `IsChartLocusFibre` is false** — the composite with the landed guard
`not_isChartLocusFibre_of_not_injective` (`Pic0ChartLocusFibreGuard.lean:159`).

This is the deliverable of the fork's negative branch: a witness at ONE test kills the only
non-circular route to `IsChartUniv`, hence to antecedent 1 of `pic0RepresentableByOfCharts`. -/
theorem not_isChartLocusFibre_of_points {Y : Scheme.{u}} (x₁ x₂ : Y ⟶ D.left)
    (hne : x₁ ≠ x₂) (hstruct : x₁ ≫ D.hom = x₂ ≫ D.hom)
    (hval : chartValue C π n m Z (Over.mk (x₁ ≫ D.hom))
        (rep.homEquiv (Over.homMk x₁ rfl))
      = chartValue C π n m Z (Over.mk (x₁ ≫ D.hom))
          (rep.homEquiv (Over.homMk x₂ hstruct.symm))) :
    ¬ IsChartLocusFibre C π n rep m Z hdeg :=
  not_isChartLocusFibre_of_not_injective rep m Z hdeg (op Y)
    (not_injective_abelSigmaChart_of_points rep m Z hdeg x₁ x₂ hne hstruct hval)

/-! ## The divisor-family form: where `rep` does the work -/

/-- **The obligation stated on divisor families rather than on points.**

This is the shape the linear-system argument produces: two *families* over one test with equal
chart value.  Transporting along `rep.homEquiv` (a bijection) turns them into two points of
`D.left` over that test, and `Over.homMk`'s structure morphism is the test's own, so the
Σ-components agree by construction rather than by hypothesis.

So the fork's negative branch reduces to a statement with **no** scheme-theoretic side
condition: distinctness in `divFamZar C π n T` plus equality of `chartValue`. -/
theorem not_injective_abelSigmaChart_of_divFamZar {T : Over (Spec (.of k))}
    (s₁ s₂ : divFamZar C π n T) (hne : s₁ ≠ s₂)
    (hval : chartValue C π n m Z T s₁ = chartValue C π n m Z T s₂) :
    ¬ Function.Injective ((abelSigmaChart C π n rep m Z hdeg).app (op T.left)) := by
  set x₁ : T.left ⟶ D.left := (rep.homEquiv.symm s₁).left with hx₁
  set x₂ : T.left ⟶ D.left := (rep.homEquiv.symm s₂).left with hx₂
  -- both points have the test's own structure morphism, so the Σ-components agree
  have hs₁ : x₁ ≫ D.hom = T.hom := Over.w _
  have hs₂ : x₂ ≫ D.hom = T.hom := Over.w _
  have hstruct : x₁ ≫ D.hom = x₂ ≫ D.hom := hs₁.trans hs₂.symm
  -- `Over.homMk xᵢ` recovers the slice morphism `rep.homEquiv.symm sᵢ` was, hence `sᵢ`
  have hrec₁ : rep.homEquiv (Over.homMk x₁ hs₁) = s₁ := by
    refine (congrArg rep.homEquiv (Over.OverMorphism.ext ?_)).trans
      (rep.homEquiv.apply_symm_apply s₁)
    rfl
  have hrec₂ : rep.homEquiv (Over.homMk x₂ (hstruct.symm.trans hs₁)) = s₂ := by
    refine (congrArg rep.homEquiv (Over.OverMorphism.ext ?_)).trans
      (rep.homEquiv.apply_symm_apply s₂)
    rfl
  refine not_injective_abelSigmaChart_of_points rep m Z hdeg x₁ x₂ ?_ hstruct ?_
  · -- distinct families give distinct points, `rep.homEquiv.symm` being injective
    intro h
    exact hne (hrec₁.symm.trans ((congrArg rep.homEquiv
      (Over.OverMorphism.ext h)).trans hrec₂))
  · -- the two chart values are `hval` restricted along the identity-on-`T.left` slice
    -- morphism `e`, so naturality of `chartValue` transports it
    set e : Over.mk (x₁ ≫ D.hom) ⟶ T :=
      Over.homMk (𝟙 T.left) ((Category.id_comp T.hom).trans hs₁.symm) with he
    have hfac₁ : (Over.homMk x₁ rfl : Over.mk (x₁ ≫ D.hom) ⟶ D)
        = e ≫ rep.homEquiv.symm s₁ :=
      Over.OverMorphism.ext (Category.id_comp x₁).symm
    have hfac₂ : (Over.homMk x₂ hstruct.symm : Over.mk (x₁ ≫ D.hom) ⟶ D)
        = e ≫ rep.homEquiv.symm s₂ :=
      Over.OverMorphism.ext (Category.id_comp x₂).symm
    have hpull : ∀ s : divFamZar C π n T,
        rep.homEquiv (e ≫ rep.homEquiv.symm s) = divFamZar.map C π n e s := by
      intro s
      rw [rep.homEquiv_comp, rep.homEquiv.apply_symm_apply]
      rfl
    have hstep : ∀ (s : divFamZar C π n T) (y : Over.mk (x₁ ≫ D.hom) ⟶ D),
        y = e ≫ rep.homEquiv.symm s →
        chartValue C π n m Z (Over.mk (x₁ ≫ D.hom)) (rep.homEquiv y)
          = picEtMap C e (chartValue C π n m Z T s) := by
      intro s y hy
      subst hy
      exact (congrArg (chartValue C π n m Z (Over.mk (x₁ ≫ D.hom))) (hpull s)).trans
        (picEtMap_chartValue C π n m Z e s).symm
    exact (hstep s₁ _ hfac₁).trans
      ((congrArg (picEtMap C e) hval).trans (hstep s₂ _ hfac₂).symm)

/-- Two distinct divisor families with equal chart value also refute the stronger chart-fibre
certificate. This is the original consumer of `not_injective_abelSigmaChart_of_divFamZar`. -/
theorem not_isChartLocusFibre_of_divFamZar {T : Over (Spec (.of k))}
    (s₁ s₂ : divFamZar C π n T) (hne : s₁ ≠ s₂)
    (hval : chartValue C π n m Z T s₁ = chartValue C π n m Z T s₂) :
    ¬ IsChartLocusFibre C π n rep m Z hdeg :=
  not_isChartLocusFibre_of_not_injective rep m Z hdeg (op T.left)
    (not_injective_abelSigmaChart_of_divFamZar rep m Z hdeg s₁ s₂ hne hval)

end

end AlgebraicGeometry
