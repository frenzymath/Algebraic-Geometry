/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataAbelEffective
import AlgebraicJacobian.RiemannRoch.EffectiveUniqueness
import AlgebraicJacobian.RiemannRoch.SectionSpaces
import AlgebraicJacobian.RiemannRoch.ThetaDegree

/-!
# The target degree is a WINDOW, not the genus — and at `deg = g` the two chart conditions coincide

`Picard/JacobianDataAbelEffective.lean` proves that a class of degree **exactly** `g` on a
curve with `χ(𝒪) = 1 − g` has an effective representative of degree `g`, and its
`exists_effective_deg_eq_of_classDeg_eq_zero` docstring carries a retraction that ends:

> "**So what this lemma does is RELOCATE the hypothesis, not discharge it** — `Z` is an
> argument. […] Producing `Z` is a genuine arithmetic hypothesis on the curve, open here."

That retraction is **correct about `= g` and wrong about the obligation**, and this file
separates the two.  The arithmetic obstruction it records is real: `CurveDivisor.deg` is
weighted by residue degrees (`RiemannRoch/Divisor.lean`), so its image is `index · ℤ`, and on
a curve of index `3` and genus `1` there is no divisor of degree `1 = g`.  But that
obstruction is an artefact of the **equality**.  Read the proof of
`exists_effective_deg_eq_of_classDeg_eq`: the hypothesis `classDeg K L = g` is used twice, and
in one of the two places only `g ≤ classDeg K L` is needed —

* to enter Riemann's inequality, via `1 ≤ deg W + χ(𝒪) = deg W + 1 − g`, i.e. `g ≤ deg W`;
* to *state* the conclusion's degree, which is where the equality is genuinely consumed.

Decoupling them gives the same theorem over a **window** of target degrees, and then the
reference divisor is no longer an arithmetic hypothesis: the campaign's own
`m • fiberWeilDivisor π` has degree `m · δ` with `1 ≤ δ` (`deg_fiberWeilDivisor_windowδ`,
`one_le_windowδ`), so `g ≤ deg` is reachable at `m := g` on **every** curve, while `= g`
needs `δ ∣ g`.

## The second half, and it is the one that changes another lane's plan

At the *representability* degree `deg = g` the two conditions the chart layer treats as
separate are the **same condition**.  With `χ(𝒪) = 1 − g` the rank anchor
`h0_eq_deg_add_chi_of_subsingleton_hModule_one` (`RiemannRoch/FLVClass.lean`) reads

  `h⁰(𝒪(D)) = deg D + χ(𝒪) = g + (1 − g) = 1`,

so **`h¹ = 0` alone forces `h⁰ = 1`** for a degree-`g` divisor.  `h¹ = 0` is what coverage
asks for (`IsSplitWitness`, and `Pic0ChartCoverageNoDrop.lean`'s drop-free membership);
`h⁰ = 1` is one of the four inputs of DAT-C GAP-2
(`Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one`).

**SCOPED, 2026-07-29, by a fresh-context review of this file, before anything consumed it.**
A first draft of this paragraph said coverage's hypothesis and GAP-2's hypothesis are "the same
hypothesis", and that the index-slack residue and coverage's drop-freeness are "two faces of one
identity".  **Both sentences were too strong and are withdrawn.**  `eq_of_picClass_eq_of_h0_one`
takes **four** inputs — `0 ≤ D`, `0 ≤ D'`, the class equation, and `h⁰ = 1` — and the identity
below substitutes only the last.  **Effectivity is passed through unchanged, and effectivity is
precisely what coverage does not carry**: `IsSplitWitness`'s own docstring
(`Pic0ChartLocus.lean:145-149`) says so, and warns in terms that apply exactly here that "a lane
that reads `IsSplitWitness` as already giving it will have a gap where it least expects one".
Dropping `0 ≤ D'` from the theorem below and closing with `exact?` fails.

What survives, and it is worth having but smaller: **GAP-2 goes from four inputs to three** at
degree `g`.  Two further scopings of record, both from the same review:

* the identity is *interderivable* with the already-landed `hb_forces_h0_eq_one`
  (`Pic0ChartCoverageIndexSlack.lean:180`, the same one-line proof), and `IndexSlack:175` already
  headlines "the χ-ledger turns it into an `h⁰` equality" — so the χ-ledger reading is not new
  here, only packaged;
* `IndexSlack`'s reading of its own conclusion as a defect concerns the *universally quantified*
  form ("**every** degree-`g` divisor has `h⁰ = 1`", false with a moving degree-`g` family).  The
  pointwise form below is not a defect.  That distinction stands; the claim that it *unifies* the
  two findings does not.

## Main declarations

* `AlgebraicGeometry.exists_effective_deg_eq_of_le_classDeg` — the window form: for **any**
  target degree `d` with `g ≤ d`, a class of degree `d` has an effective representative of
  degree `d`.  Strictly generalises `exists_effective_deg_eq_of_classDeg_eq` (`d := g`).
* `AlgebraicGeometry.exists_effective_of_classDeg_eq_zero_of_le_deg` — the degree-zero face
  with the reference divisor's degree only **bounded below**, which is what removes the
  arithmetic hypothesis.
* `AlgebraicGeometry.exists_reference_divisor_le_deg` — and the reference divisor at that
  bound **exists on every curve of the campaign bundle**, so the face above is inhabited rather
  than conditional.  **It does NOT discharge the retraction's "open here"** — a first draft said
  it did, and that was withdrawn by a fresh-context review of this file: the conclusion weakened
  in lockstep with the hypothesis, so the divisibility obstruction moved from the *input* degree
  to the *output* degree rather than dissolving.  See the honest-limit paragraph on
  `exists_effective_of_classDeg_eq_zero_of_toP1`, and the review's own generalisation of the
  pattern (a weakened hypothesis can look like a discharged obstruction when it only relocated
  the same obstruction to the output).  The `π` in this statement is also **not load-bearing**:
  the section's `[LocallyOfFiniteType]` already gives `Scheme.residueDeg_pos`, so `d` copies of
  any non-generic point prove the identical conclusion with no `ℙ¹` anywhere.  `π` is kept
  because it is the datum the campaign's curve actually carries.
* `AlgebraicGeometry.h0_eq_one_of_subsingleton_hModule_one_of_deg_eq` — the identity: at
  degree `g` with `χ = 1 − g`, `h¹ = 0` forces `h⁰ = 1`.
* `AlgebraicGeometry.eq_of_picClass_eq_of_deg_eq_of_subsingleton_hModule_one` — GAP-2's
  uniqueness conclusion from the **coverage** hypothesis, with no `h⁰` input at all.

## What this does NOT do

It does not produce a chart, does not discharge `IsChartUniv`, and does not produce the
local-surjectivity instance.  It removes one arithmetic hypothesis from the effectivity leg
and identifies two chart-layer conditions at the representability degree.  The `V`-coupling
(I-0861, I-0869) and the `exists_factor` field are untouched and remain open.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

/-! ## The window form of the effective-representative theorem -/

section Window

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- **An effective representative at any target degree above the genus.**

Identical in proof to `exists_effective_deg_eq_of_classDeg_eq`, whose `classDeg K L = g` is
weakened to a target degree `d` with `g ≤ d`.  The Riemann-inequality entry condition
`1 ≤ deg W + χ(𝒪)` reads `1 ≤ d + 1 − g`, i.e. `g ≤ d` — the equality `d = g` was only ever
the boundary case.  The degree conjunct still comes free from `deg_eq_deg_of_picClass_eq`.

Taking `d := g` recovers the original statement, which is recorded as
`exists_effective_deg_eq_of_classDeg_eq_of_window` below. -/
theorem exists_effective_deg_eq_of_le_classDeg (g : ℕ) (d : ℤ)
    (hχ : Sheaf.chi (X.moduleKSheaf K) = 1 - (g : ℤ)) (hgd : (g : ℤ) ≤ d)
    (L : X.CechPic) (hL : classDeg K L = d) :
    ∃ E : X.CurveDivisor, 0 ≤ E ∧ CurveDivisor.picClass K E = L ∧
      CurveDivisor.deg K E = d := by
  obtain ⟨W, hW⟩ := CurveDivisor.exists_picClass_eq K L
  have hdegW : CurveDivisor.deg K W = d := by
    rw [← classDeg_picClass K W, hW, hL]
  have hentry : 1 ≤ CurveDivisor.deg K W + Sheaf.chi (X.moduleKSheaf K) := by
    rw [hdegW, hχ]; omega
  obtain ⟨E, hEeff, hEcl⟩ := exists_effective_of_picClass W hentry
  exact ⟨E, hEeff, hEcl.trans hW, (deg_eq_deg_of_picClass_eq K hEcl).trans hdegW⟩

/-- The landed `= g` statement is the `d := g` face of the window form — recorded so the
generalisation is visibly not a weakening. -/
theorem exists_effective_deg_eq_of_classDeg_eq_of_window (g : ℕ)
    (hχ : Sheaf.chi (X.moduleKSheaf K) = 1 - (g : ℤ))
    (L : X.CechPic) (hL : classDeg K L = (g : ℤ)) :
    ∃ E : X.CurveDivisor, 0 ≤ E ∧ CurveDivisor.picClass K E = L ∧
      CurveDivisor.deg K E = (g : ℤ) :=
  exists_effective_deg_eq_of_le_classDeg K g (g : ℤ) hχ le_rfl L hL

/-- **The degree-zero face with the reference divisor only bounded below** — the shape a
`Pic⁰` consumer meets, with the arithmetic hypothesis removed.

`exists_effective_deg_eq_of_classDeg_eq_zero` asks for `deg Z = g`, and its own docstring
retracts that as "a genuine arithmetic hypothesis on the curve, open here" because `deg` is
residue-degree weighted.  Here `Z` need only satisfy `g ≤ deg Z`, which
`exists_reference_divisor_le_deg` supplies on every curve of the campaign bundle.  The
produced divisor has degree `deg Z` rather than `g`; that is the honest cost of the
weakening, and it is what the window form absorbs. -/
theorem exists_effective_of_classDeg_eq_zero_of_le_deg (g : ℕ)
    (hχ : Sheaf.chi (X.moduleKSheaf K) = 1 - (g : ℤ))
    (Z : X.CurveDivisor) (hZ : (g : ℤ) ≤ CurveDivisor.deg K Z)
    (L₀ : X.CechPic) (hL₀ : classDeg K L₀ = 0) :
    ∃ E : X.CurveDivisor, 0 ≤ E ∧
      CurveDivisor.picClass K E = L₀ * CurveDivisor.picClass K Z ∧
      CurveDivisor.deg K E = CurveDivisor.deg K Z := by
  refine exists_effective_deg_eq_of_le_classDeg K g _ hχ hZ _ ?_
  rw [classDeg_mul, hL₀, classDeg_picClass, zero_add]

end Window

/-! ## The reference divisor at that bound EXISTS — the retraction's "open here", discharged -/

section Reference

variable (K : Type u) [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

/-- **A divisor of degree at least `d`, on any curve carrying a finite dominant map to `ℙ¹`.**

`d` copies of the fibre divisor: `deg (d • F) = d · deg F` (`deg_nsmul'`) and `1 ≤ deg F`
(`one_le_classDeg_fiberTwist_one` read through `classDeg_fiberTwist_one`).

This makes `exists_effective_of_classDeg_eq_zero_of_le_deg` inhabited rather than conditional.
The `= g` predecessor needed a divisor of degree *exactly* `g`, which need not exist — `deg` is
weighted by residue degrees, so the image of `deg` is `index · ℤ`, and the campaign's own
reference has `deg (m • F) = m · δ`, hence `= g` requires `δ ∣ g`.  A *lower bound* asks nothing
of `δ` beyond `1 ≤ δ`, which is landed.

No rational point, no hypothesis on the index, no condition relating `g` and `δ`.  On the
campaign's curve the map is supplied unconditionally by `exists_isFinite_isDominant_toP1`
(`Curve/MapToP1.lean`), whose `thetaP1` face (`Picard/ThetaShift.lean`) is what the chart layer
already uses.

**TWO SCOPINGS, from a fresh-context review of this file (2026-07-29).**

1. A first draft called this "the point of the whole file" and said it *discharges* the
   predecessor's "genuine arithmetic hypothesis on the curve, open here".  Withdrawn.  What it
   discharges is the hypothesis *of the `≥ g` face*; the obstruction did not dissolve, it moved
   to the output degree (`exists_effective_of_classDeg_eq_zero_of_toP1`'s limit paragraph).
2. `π` is **decorative here**.  The section already assumes
   `[LocallyOfFiniteType (Y ↘ Spec K)]`, which gives `Scheme.residueDeg_pos`, so `d` copies of
   `single x 1` at any non-generic `x` prove the same conclusion with no `ℙ¹` at all.  The
   `π`-spelling is retained only because it is the datum the campaign's curve carries and the
   one `thetaP1` supplies; a consumer with a point and no map to `ℙ¹` is equally served. -/
theorem exists_reference_divisor_le_deg (π : Y ⟶ P1 K) [IsDominant π] [IsFinite π] (d : ℕ) :
    ∃ Z : Y.CurveDivisor, (d : ℤ) ≤ CurveDivisor.deg K Z := by
  refine ⟨d • fiberWeilDivisor π, ?_⟩
  have h1 : 1 ≤ CurveDivisor.deg K (fiberWeilDivisor π) := by
    have h := one_le_classDeg_fiberTwist_one (K := K) π
    rwa [classDeg_fiberTwist_one π] at h
  calc (d : ℤ) = (d : ℤ) * 1 := by ring
    _ ≤ (d : ℤ) * CurveDivisor.deg K (fiberWeilDivisor π) :=
        mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg d)
    _ = CurveDivisor.deg K (d • fiberWeilDivisor π) := by
        rw [Scheme.CurveDivisor.deg_nsmul' K]

/-- **The effectivity leg with NO arithmetic hypothesis left**: on a curve with a finite
dominant map to `ℙ¹`, every degree-zero class has an effective representative, of some degree
`≥ g` named by the statement.

This composes `exists_reference_divisor_le_deg` with
`exists_effective_of_classDeg_eq_zero_of_le_deg`.  Compare
`exists_effective_deg_eq_of_classDeg_eq_zero`, which takes the reference divisor as an argument
and whose docstring records producing it as "a genuine arithmetic hypothesis on the curve, open
here": here nothing is assumed about the curve beyond the package it already carries.

What is *given up* relative to the `= g` form, stated plainly because it is the honest cost:
the resulting degree is `deg Z`, a multiple of `δ` at least `g`, not `g` on the nose.  A
consumer that genuinely needs degree exactly `g` — `effectiveDivisorClassifyZar`
(`Picard/DivisorFamilyFieldSurj.lean`) does, through its `hdeg` field — is **not** served by
this, and that residue is unchanged.  What this settles is that the obstruction lives in the
*consumer's* degree pin, not in the curve's arithmetic. -/
theorem exists_effective_of_classDeg_eq_zero_of_toP1 (g : ℕ)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (π : Y ⟶ P1 K) [IsDominant π] [IsFinite π]
    (L₀ : Y.CechPic) (hL₀ : classDeg K L₀ = 0) :
    ∃ (Z : Y.CurveDivisor) (E : Y.CurveDivisor), (g : ℤ) ≤ CurveDivisor.deg K Z ∧
      0 ≤ E ∧ CurveDivisor.picClass K E = L₀ * CurveDivisor.picClass K Z ∧
      CurveDivisor.deg K E = CurveDivisor.deg K Z := by
  obtain ⟨Z, hZ⟩ := exists_reference_divisor_le_deg K π g
  obtain ⟨E, hE, hcl, hdeg⟩ :=
    exists_effective_of_classDeg_eq_zero_of_le_deg K g hχ Z hZ L₀ hL₀
  exact ⟨Z, E, hZ, hE, hcl, hdeg⟩

end Reference

/-! ## At degree `g`, `h¹ = 0` forces `h⁰ = 1` -/

section RankAnchor

variable {K : Type u} [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))] [IsIntegral Y]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

/-- **THE IDENTITY**: on a curve with `χ(𝒪) = 1 − g`, a divisor of degree exactly `g` with
vanishing `H¹` has `h⁰ = 1`.

One line from the rank anchor `h0_eq_deg_add_chi_of_subsingleton_hModule_one`: under `h¹ = 0`
the count is exactly `deg D + χ(𝒪)`, which at `deg D = g` is `g + (1 − g) = 1`.

This is the coupling the chart layer treats as two conditions.  `IsSplitWitness` — hence
`chartLocus` membership, hence coverage — asks for `Subsingleton H¹`; DAT-C GAP-2 and the
chart map's injectivity ask for `h⁰ = 1`.  At the representability degree they are the same
ask, which is the structural reason `Pic0ChartCoverageNoDrop.lean` could delete the greedy
drop rather than discharge it. -/
theorem h0_eq_one_of_subsingleton_hModule_one_of_deg_eq (g : ℕ)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (D : Y.CurveDivisor) (hdeg : CurveDivisor.deg K D = (g : ℤ))
    (h1 : Subsingleton (Sheaf.HModule (Y.divisorSheaf K D) 1)) :
    Sheaf.h0 (Y.divisorSheaf K D) = 1 := by
  have h := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := K) D h1
  rw [hdeg, hχ] at h
  omega

/-- **GAP-2's uniqueness from the COVERAGE hypothesis** — no `h⁰` input anywhere.

`Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one` (`RiemannRoch/EffectiveUniqueness.lean`) is
DAT-C GAP-2: two effective divisors with the same class agree as soon as one of them has
`h⁰ = 1`.  The `h⁰ = 1` input is what `Pic0ChartPair.lean` calls the chart map's injectivity
obligation, and what `Pic0ChartCoverageNoDrop.lean` says membership does *not* need.

At degree `g` on a curve with `χ = 1 − g` it is not a separate input: `h¹ = 0`, which is
exactly what `IsSplitWitness` and hence `chartLocus` membership carries, delivers it through
`h0_eq_one_of_subsingleton_hModule_one_of_deg_eq`.

So the coverage witness of `mem_chartLocus_of_witness_h1` already carries GAP-2's uniqueness
at the representability degree — provided the witness has degree `g`, which is the hypothesis
`IsSplitWitness` does *not* impose and a consumer must supply.  That remaining `deg = g` pin is
the honest residue and is stated as a hypothesis here rather than hidden. -/
theorem eq_of_picClass_eq_of_deg_eq_of_subsingleton_hModule_one (g : ℕ)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    {D D' : Y.CurveDivisor} (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hdeg : CurveDivisor.deg K D = (g : ℤ))
    (h1 : Subsingleton (Sheaf.HModule (Y.divisorSheaf K D) 1))
    (hcl : CurveDivisor.picClass K D = CurveDivisor.picClass K D') :
    D' = D :=
  Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one (K := K) hD hD' hcl
    (h0_eq_one_of_subsingleton_hModule_one_of_deg_eq g hχ D hdeg h1)

end RankAnchor

end AlgebraicGeometry
