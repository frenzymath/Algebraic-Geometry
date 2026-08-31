/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartRestrictedFibreSat
import AlgebraicJacobian.Picard.Pic0ChartCoverForcesNonInj
import AlgebraicJacobian.Picard.Pic0ChartLocusH0Rank

/-!
# THE `abel-noninj` FORK IS `Mono D.hom`, AND WHERE THAT HOLDS THE `V`-COUPLING IS IDLE

Three headers of this project assert that the unrestricted Abel chart is **not** injective —
the linear system `|D|` being its fibres (`Pic0AtlasFromDivRep.lean:54`,
`Pic0ChartPair.lean:14`, `Pic0ChartOpenImmersionCriterion.lean:214`).  That assertion is the
`abel-noninj` fork, and *nothing proves it*: every statement conditioned on it takes
`¬ Function.Injective` as a hypothesis.  The whole restriction apparatus — `restrictChart`,
`RestrictedChartFibre`, `chartLocus`, the `V`-coupling of
`pic0RepresentableBy_of_restrictedChartFibre_of_coverage` — exists because that assertion is
believed, since it is what kills `V = ⊤`.

This file answers the fork, and the answer is cheaper than the question looked: **the Abel chart
is injective on every test as soon as `D.hom` is a monomorphism** — two lines, at arbitrary `n`,
with no divisor, certificate or functor value in the proof.  The Σ-component of the chart at a
point `u` is `u ≫ D.hom`, so `cancel_mono` is the whole argument.  A subsingleton-valued divisor
functor is one sufficient condition (`mono_hom_of_divFunctorObjSubsingleton`), and an earlier
version of this file stated *only* that form and priced it as the content — wrong in this lane's
own favour, corrected below with the reason the self-check missed it.

## What a `Mono` parameter buys at the seam

The hypothesis is not invented here.  `Picard/DivisorFamilyDegreeZeroUnique.lean` proves
`Subsingleton (DivFamZar C K π 0)` over a **field** test and the general-`R` half has since
landed downstream, so the sufficient condition has producers.  What was missing is what they
*buy at the seam*, and the answer is not "one more `rep`":

* `injective_abelSigmaChart_of_mono` — the chart is injective on **every** test.  So
  `not_restrictedChartFibre_top_of_not_injective`, the landed fact that kills `⊤`, cannot fire
  (it *consumes* non-injectivity), and by `not_pointwiseCoverage_of_injective_of_ne_top` coverage
  holds at **no** proper `V`; `not_coverageContainment_bot` refutes `⊥`.
* `restrictedChartFibre_top_iff` (landed) then says the hypothesis at `⊤` **is**
  `IsChartLocusFibre`, the unrestricted certificate.

**What that does and does not say about `⊤`, stated carefully because an earlier version of this
header got it wrong in this lane's own favour.**  It does *not* say `⊤` is where the seam closes,
and "the only survivor" — the phrasing used here previously — reads as if it did.
`Pic0ChartCoverForcesNonInj.lean`, which this file imports, already retracted exactly that
sentence (audit `I-1378`): under injectivity the seam is unsatisfiable at every *proper* `V` and
at `⊥`, and nothing exhibits an inhabitant of the pair at `⊤` either.  Two refutations are not an
inhabitation (`Pic0ChartRestrictedFibreSat.lean:96-104` files this as the standing error for this
seam).  The defensible statement is about *elimination*, not survival: at a `Mono`-parameter the
landed endpoint refutations no longer rule `⊤` out, and the obligation there is the pair
(`IsChartLocusFibre`, unrestricted `PointwiseCoverage`).

So the `V`-interval has no interior to search there, and what the seam owes is named rather than
reduced.  That converts a caveat this lane wrote in prose (inbox `I-1493`: "even a full `rep` at
`0` does not feed `mixedParamChart` alone") into a theorem about *which* obligations remain.

## Main declarations

Every name below is in this file; the list was re-checked against the elaborated module rather
than transcribed from a draft.

* `CategoryTheory.Functor.RepresentableBy.eq_of_comp_hom_eq_of_subsingleton` — the generic core.
* `CategoryTheory.Functor.RepresentableBy.injective_toSigmaExtension_app` — its Σ-extension form.
* `AlgebraicGeometry.DivFunctorObjSubsingleton` — the sufficient condition, named; no producer
  here.
* `AlgebraicGeometry.divFunctorObjSubsingleton_of_forall_ring` — the bridge from the
  affine-ring form, using none of the curve's geometry.
* `AlgebraicGeometry.injective_abelSigmaChart_of_mono` — **the fork, answered**, from
  `Mono D.hom` alone at arbitrary `n`.
* `AlgebraicGeometry.mono_hom_of_divFunctorObjSubsingleton` — the subsingleton implies it, so it
  sits strictly below `Mono D.hom` in strength.
* `AlgebraicGeometry.injective_abelSigmaChart_of_subsingleton` — the corollary a producer lands.
* `AlgebraicGeometry.not_pointwiseCoverage_of_subsingleton_of_ne_top` — coverage dies at every
  proper `V`.
* `AlgebraicGeometry.isChartLocusFibre_iff_restrictedChartFibre_top_of_subsingleton` — the
  surviving hypothesis IS the unrestricted certificate.
* `AlgebraicGeometry.pic0RepresentableBy_of_isChartLocusFibre_of_coverage` — the seam stated
  with no `V` and no containment.
* `AlgebraicGeometry.not_mem_chartLocus_of_two_le_genus_zero_param` — **the boundary**: at
  parameter `0` and genus `≥ 2` the chart **locus** is empty, so the *locus-mediated* route to
  the coverage half is dead at the parameter where the subsingleton is landed.  (Not a refutation
  of `hcov`, which never mentions the locus — see the bullet above.)

For the record, `isChartUniv_top_of_isChartLocusFibre` was in an earlier version of this list and
has been **deleted**, not renamed: `isChartUniv_of_isChartLocusFibre` already does it at arbitrary
`V`.  See the note before the boundary section.

## The generic core, and why it is stated separately

`eq_of_comp_hom_eq_of_subsingleton` is pure category theory: in a slice `Over S`, if a presheaf
represented by `J` has a subsingleton value at `Over.mk (v₁ ≫ J.hom)`, then two `T`-points of
`J.left` agreeing after `J.hom` are equal.  No scheme, no divisor, no curve, no `π` — and the
proof is `Equiv.subsingleton` of `α.homEquiv` plus `Over.homMk`.  It is stated on its own
because the geometric statements below are *only* its instances, and because the same argument
applies to any other slice-represented functor this project introduces.

## What this does NOT establish, stated as hypotheses rather than left implicit

* **It does not produce `rep`, and it does not produce the subsingleton.**  Both are
  hypotheses here.  `divFunctorObjSubsingleton` is a `Prop` about the functor, not a class, and
  this file exhibits no witness for it — that is the `deg-zero` row's business.
* **It does not close the seam at `⊤`.**  It relocates the cost: `IsChartLocusFibre` at that
  parameter, plus unrestricted coverage.  `Pic0ChartLocusFibreGuard.lean` records why the
  certificate is expensive; nothing here makes it cheap.  The claim is about *which* hypothesis
  is owed, not that fewer are.
* **It does not settle `n = g`, and an earlier version of this bullet was backwards about what
  the tree already knows there.**  That version said the subsingleton "is expected to FAIL at the
  parameter the classical route targets — that is exactly what 'the fibres are the linear system
  `|D|`' means".  But `Pic0ChartAbelNonInjective.lean:67-73` — the `abel-noninj` row's own file —
  already measured that the headers' *reason* is unavailable at `n = g`: over a field an effective
  divisor of degree `g` with vanishing `H¹` has `h⁰ = g + (1 - g) = 1` exactly, so the fibrewise
  `|D|` is a single point there, not positive-dimensional.  What that file then records is the
  limit of its own observation: the anchor is **fibrewise over one field**, while the obligation
  is general-test, and the bridge is relative GAP-2.  So the state is not "the headers are right
  at `n = g` and this file covers the complement" — it is that the headers' reason is refuted
  fibrewise at `n = g` and unsettled relatively, and `Mono D.hom` is a *general-test* hypothesis
  of exactly the kind that bridge would supply.  Read this file as: the fork reduces to whether
  `D.hom` is a monomorphism, at whatever parameter.
* **AND THE COLLAPSE DOES NOT DELIVER A REPRESENTATION AT `n = 0`.**  The sharp limit is proved
  below rather than hedged: `not_mem_chartLocus_of_two_le_genus_zero_param` shows that at
  parameter `0` on a curve of genus `≥ 2` the chart **locus** is empty —
  `Pic0ChartLocusH0Rank`'s rank formula gives `h⁰ = n + 1 - g`, negative at `n = 0`, while `h⁰`
  is a natural number.

  **What that refutes is the chartLocus-mediated ROUTE to coverage, not `hcov` itself, and an
  earlier version of this header claimed the stronger thing.**  `PointwiseCoverage`
  (`Pic0ChartAtlasCoupling.lean:99`) quantifies over an *arbitrary* open `W ∋ t` and never
  mentions `chartLocus`; `chartsCoverLocally_of_pointwise` calls `chartLocusOpens` only the
  *intended* instantiation of `W`, and `Pic0ChartAtlasCoupling.lean:50-53` records that the two
  carriers do not even meet without the `haff` bridge (dat-b B-4).  So "coverage needs the locus
  inhabited" was false as stated.  Whether `hcov` itself fails at `n = 0` is **open and strictly
  stronger than what is proved here**.  The error ran in the direction that made this limit look
  harsher and better-audited than it was, which is the same failure mode as an over-generous gap
  list with the sign flipped.
* **The `⊥`/`⊤` dichotomy is not needed for the collapse, and is now landed anyway at the one
  carrier where it is meaningful.**  The collapse below goes through injectivity and the landed
  endpoint refutations, which need no fact about the topology of `D.left`; an earlier draft of
  this header asserted a two-element `Opens` as if proved, and I retracted it as unmeasured.
  The retraction was right about my own file and too pessimistic about the mathematics:
  `opens_eq_bot_or_top_of_terminalRep` below proves it in one line at the *terminal* representing
  object — which is exactly the carrier the landed `n = 0` producer returns.  It is stated
  separately from the collapse because the collapse does not use it.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe v u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

/-! ## The generic core -/

namespace CategoryTheory.Functor.RepresentableBy

/-- **A slice representation with subsingleton values separates points over the base.**

If `F : (Over S)ᵒᵖ ⥤ Type v` is represented by `J` and its value at `Over.mk (v₁ ≫ J.hom)` is a
subsingleton, then two `T`-points of `J.left` with the same composite to `S` coincide.

Pure category theory: `α.homEquiv` transports the subsingleton to the slice hom-set
`Over.mk (v₁ ≫ J.hom) ⟶ J`, where `Over.homMk v₁ rfl` and `Over.homMk v₂ ha.symm` are two
elements; comparing their `left` components is the conclusion.  The `Over.mk` on which the value
is taken is `v₁`'s, and `ha` is what lets `v₂` be typed there too. -/
theorem eq_of_comp_hom_eq_of_subsingleton
    {C : Type u} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}
    {J : Over S} (α : F.RepresentableBy J) {T : C} {v₁ v₂ : T ⟶ J.left}
    (hsub : Subsingleton (F.obj (op (Over.mk (v₁ ≫ J.hom)))))
    (ha : v₁ ≫ J.hom = v₂ ≫ J.hom) :
    v₁ = v₂ := by
  haveI := hsub
  haveI : Subsingleton (Over.mk (v₁ ≫ J.hom) ⟶ J) := Equiv.subsingleton α.homEquiv
  exact congrArg (fun z : Over.mk (v₁ ≫ J.hom) ⟶ J => z.left)
    (Subsingleton.elim (Over.homMk v₁ rfl : Over.mk (v₁ ≫ J.hom) ⟶ J)
      (Over.homMk v₂ ha.symm))

/-- **The Σ-extension map of such a representation is injective on every test.**

The Σ-component of `toSigmaExtension` at `v` is `v ≫ J.hom`, so equality of Σ-elements gives the
hypothesis of `eq_of_comp_hom_eq_of_subsingleton` by `congrArg Sigma.fst`. -/
theorem injective_toSigmaExtension_app
    {C : Type u} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}
    {J : Over S} (α : F.RepresentableBy J) (T : Cᵒᵖ)
    (hsub : ∀ a : T.unop ⟶ S, Subsingleton (F.obj (op (Over.mk a)))) :
    Function.Injective ((α.toSigmaExtension).app T) :=
  fun _ _ h => eq_of_comp_hom_eq_of_subsingleton α (hsub _) (congrArg Sigma.fst h)

end CategoryTheory.Functor.RepresentableBy

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The hypothesis, named -/

variable (C π n) in
/-- **The divisor functor is subsingleton-valued**: at most one degree-`n` divisor class over
every test object of the slice.

A `Prop` about `divFunctor C π n` and nothing else — in particular it mentions the object it is
about, and it has no producer *in this file*.  `Picard/DivisorFamilyDegreeZeroUnique.lean`
proves the affine-field instance at `n = 0`; `divFunctorObjSubsingleton_of_forall_ring` below is
the bridge from the affine-ring form a producer naturally lands. -/
def DivFunctorObjSubsingleton : Prop :=
  ∀ T : (Over (Spec (.of k)))ᵒᵖ, Subsingleton ((divFunctor C π n).obj T)

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
variable (C π n) in
/-- **From the affine-ring subsingleton to the functor-value subsingleton.**

The functor value at an arbitrary test `T` is a *compatible family* of `DivFamZar` classes over
the affine opens of `T.left` (`divFamZar`, `Picard/DivisorFamilyZarVehicle.lean:187`), i.e. a
subtype of a `Π`-type.  So the subsingleton passes componentwise: two sections agreeing at every
affine open are equal by `Subtype.ext`, and they agree because each component lands in a
subsingleton.

This is the form a producer working on affine test rings should target — it needs the
subsingleton at *every* `k`-algebra, which is precisely the general-`R` uniqueness question, and
nothing about general test objects.

The `omit` is a measurement, not tidying: this bridge uses **none** of the curve's geometry —
not smoothness, not properness, not geometric irreducibility.  It is the vehicle's `Π`-shape and
nothing else, so it will not decay if the curve binders move. -/
theorem divFunctorObjSubsingleton_of_forall_ring
    (hR : ∀ (R : Type u) (_ : CommRing R) (_ : Algebra k R),
      Subsingleton (DivFamZar C R π n)) :
    DivFunctorObjSubsingleton C π n :=
  fun _ => ⟨fun _ _ => Subtype.ext (funext fun _ => (hR _ _ _).elim _ _)⟩

/-! ## The fork, answered: the Abel chart is a monomorphism there -/

/-- **THE `abel-noninj` FORK, ANSWERED — and the honest hypothesis is `Mono D.hom`, not the
subsingleton.**

The Σ-component of `abelSigmaChart` at a point `u` is `u ≫ D.hom`
(`CategoryTheory.Over.sigmaExtensionNat_app_fst` composed with
`CategoryTheory.Functor.RepresentableBy.toSigmaExtension_app_fst` — both fully qualified, because
neither lives in the `AlgebraicGeometry` namespace this section is inside), so equal chart values
give
`u ≫ D.hom = v ≫ D.hom`, and `cancel_mono` finishes.  **No subsingleton, no divisor, no
certificate, at arbitrary `n`.**

An earlier version of this file stated only the subsingleton form and priced it as the content.
That was wrong in this lane's own favour: a fresh-context audit exhibited this two-line proof from
`Mono D.hom` alone, at arbitrary `n`, and the self-check that was supposed to catch it — "`exact?`
cannot close the goal with the subsingleton hypothesis DELETED" — cannot discriminate, because
deleting a hypothesis tests *needed vs not needed* and never *needed vs far stronger than
needed*.  The subsingleton form below is now a corollary, which is what it always was. -/
theorem injective_abelSigmaChart_of_mono {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    [Mono D.hom] (T : Scheme.{u}ᵒᵖ) :
    Function.Injective ((abelSigmaChart C π n rep m Z hdeg).app T) :=
  fun _ _ h => (cancel_mono D.hom).mp (congrArg Sigma.fst h)

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- **A subsingleton-valued divisor functor forces `Mono D.hom`** — so the subsingleton is a
*sufficient condition* for the fork's positive branch, and the previous theorem is the general
statement.

Worth landing as an implication rather than leaving the two hypotheses side by side: it locates
the subsingleton strictly below `Mono D.hom` in strength, which is the fact the earlier draft of
this file got backwards.

Like the affine-ring bridge this uses **none** of the curve's geometry — it is the generic core at
`J := D`, so the same statement holds for any slice-represented functor. -/
theorem mono_hom_of_divFunctorObjSubsingleton {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (hsub : DivFunctorObjSubsingleton C π n) :
    Mono D.hom :=
  ⟨fun _ _ huv =>
    Functor.RepresentableBy.eq_of_comp_hom_eq_of_subsingleton rep (hsub _) huv⟩

/-- **The subsingleton corollary**, kept because it is the form a `deg-zero`-style producer lands.

Now visibly a composite: the subsingleton gives `Mono D.hom`, and `Mono D.hom` gives injectivity
at arbitrary `n`. -/
theorem injective_abelSigmaChart_of_subsingleton {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (hsub : DivFunctorObjSubsingleton C π n) (T : Scheme.{u}ᵒᵖ) :
    Function.Injective ((abelSigmaChart C π n rep m Z hdeg).app T) :=
  haveI := mono_hom_of_divFunctorObjSubsingleton rep hsub
  injective_abelSigmaChart_of_mono rep m Z hdeg T

/-! ## Consequence 1: coverage is refuted at EVERY proper `V` -/

/-- **No proper open supports coverage there.**

`not_pointwiseCoverage_of_injective_of_ne_top` turns injectivity on every test into the
refutation of coverage at any `V ≠ ⊤`.  Combined with `not_coverageContainment_bot`, which
refutes the containment at `⊥`, this leaves `V = ⊤` as the **only** candidate value — so the
"any working `V` is a proper intermediate open" reading of the `V`-interval is exactly inverted
at a subsingleton parameter.

Stated at the one-chart index `PUnit` because that is the shape
`not_pointwiseCoverage_of_injective_of_ne_top` takes.  **No multi-index consequence is proved
here**; an earlier version of this docstring cited one "below" under a name that exists in
neither project — the `cited-names-need-check-not-grep` failure, in a docstring body rather than
in the Main-declarations list, which is where that lesson says the misses survive.  For the
multi-index reading see `Picard/Pic0ChartMultiIndexInterval.lean`, whose point-independent-index
results are *not* instances of this theorem.  (That module is **outside this file's import
closure**, so its names cannot be `#check`ed from here — the reference is deliberately to the file
rather than to a declaration, since a name I cannot check is a name I should not cite.) -/
theorem not_pointwiseCoverage_of_subsingleton_of_ne_top {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (hsub : DivFunctorObjSubsingleton C π n)
    (V : D.left.Opens) (hV : V ≠ ⊤) :
    ¬ PointwiseCoverage C
      (fun _ : PUnit.{u+1} => restrictChart (abelSigmaChart C π n rep m Z hdeg) V) :=
  not_pointwiseCoverage_of_injective_of_ne_top C _ V hV
    (injective_abelSigmaChart_of_subsingleton rep m Z hdeg hsub)

/-! ## Consequence 2: the surviving hypothesis is the UNRESTRICTED certificate

`restrictedChartFibre_top_iff` (`Pic0ChartRestrictedFibreSat.lean`) is an equivalence at `⊤`,
already landed.  It is restated in the orientation the assembly below consumes; at a `Mono`
parameter `⊤` is the value the previous section stops eliminating, so this equivalence names the
seam's remaining obligation. -/

/-- **At a `Mono` parameter the `V`-coupling costs the unrestricted certificate.**

The hypothesis `huniv` of the coupled assembly, at `⊤`, *is* `IsChartLocusFibre` — the datum
`Pic0ChartRestrictedFibre.lean` was written to avoid.  So the restriction repair, whose whole
purpose was to replace a badly-gated route, has nothing to replace there.

This is the honest form of the collapse: it does not make the seam cheaper, it identifies which
single hypothesis it costs.  (Orientation only — the mathematical content is entirely
`restrictedChartFibre_top_iff`'s.) -/
theorem isChartLocusFibre_iff_restrictedChartFibre_top_of_subsingleton
    {D : Over (Spec (.of k))} (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) :
    IsChartLocusFibre C π n rep m Z hdeg
      ↔ RestrictedChartFibre C π n rep m Z hdeg ⊤ :=
  (restrictedChartFibre_top_iff C π n rep m Z hdeg).symm

/-- **THE SEAM WITH THE `V`-COUPLING ELIMINATED** — the form the collapse makes available.

`pic0RepresentableBy_of_restrictedChartFibre_of_coverage` couples its two geometric hypotheses
through a shared `V`, and that coupling is its whole reason for existing: neither lane may
retreat to a convenient open.  At `V = ⊤` the coupling is *vacuous* in the good direction —
the containment conjunct is free (`range_subset_range_top_ι`), so `hcov` degenerates to plain
`PointwiseCoverage` at the **unrestricted** Abel charts, and `huniv` degenerates to
`IsChartLocusFibre` (`restrictedChartFibre_top_iff`).

So this is the same representation with **no `V` and no containment anywhere in its hypothesis
list**: the two inputs are the unrestricted certificate and unrestricted coverage.  At a `Mono`
parameter that is not an arbitrary *choice* of `V` — `⊥` is refuted by
`not_coverageContainment_bot` and every proper `V` by
`not_pointwiseCoverage_of_subsingleton_of_ne_top`, so `⊤` is the value the landed refutations stop
eliminating.  It is **not** claimed that the pair is satisfiable at `⊤`; nothing exhibits an
inhabitant at any `V`.

**The hypotheses are not weaker, and this is the point rather than a caveat.**  Unrestricted
coverage is what `Pic0ChartCoveragePointwise.lean` expects to fail, and the unrestricted
certificate is what `Pic0ChartLocusFibreGuard.lean` calls badly gated.  What the statement
records is that at a subsingleton parameter those two are *exactly* the debt — the restriction
apparatus is not a route around them, because there is no interior for it to work in.  Stated at
arbitrary `ι` so it meets `mixedParamChart` where the assembly consumes it, not at a one-chart
stand-in. -/
def pic0RepresentableBy_of_isChartLocusFibre_of_coverage {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (hcert : ∀ i, IsChartLocusFibre C π (nn i) (rep i) (m i) (Z i) (hdeg i))
    (hcov : PointwiseCoverage C
      (fun i => abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i))) :
    Σ J : Over (Spec (.of k)), (pic0TypeFunctor C).RepresentableBy J :=
  pic0RepresentableBy_of_restrictedChartFibre_of_coverage C π nn D rep m Z hdeg
    (fun _ => ⊤)
    (fun i => (restrictedChartFibre_top_iff C π (nn i) (rep i) (m i) (Z i)
      (hdeg i)).mpr (hcert i))
    (fun T s t => by
      obtain ⟨W, htW, i, x, hx⟩ := hcov T s t
      exact ⟨W, htW, i, x, hx, range_subset_range_top_ι x⟩)

/-- **The `V`-interval really does degenerate to `{⊥, ⊤}` at the terminal representing object.**

`Spec k` for a field `k` has a one-point space, so every open is `⊥` or `⊤`
(`TopologicalSpace.Opens.eq_bot_or_top`).  At the representing object `Over.mk (𝟙 (Spec k))` —
which is what the landed degree-`0` producer returns — there is therefore **no proper intermediate
open at all**, and the search the `V`-interval literature describes has an empty domain.

Stated as its own lemma, with `D.left` instantiated rather than hypothesised, because the general
claim is what I got wrong earlier: I asserted a two-element `Opens` for any subsingleton parameter,
retracted it as unmeasured, and the retraction was correct about the *general* statement (a
subsingleton-valued functor pins `D` only up to iso in the slice, and this file proves no such
transport).  What is true and cheap is the statement at the terminal carrier, which is the only
one where a producer exists. -/
theorem opens_eq_bot_or_top_of_terminalRep
    (V : (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left.Opens) :
    V = ⊥ ∨ V = ⊤ :=
  TopologicalSpace.Opens.eq_bot_or_top
    (α := (Spec (CommRingCat.of k)).carrier) V

/-! ### A declaration this file used to carry, and why it is gone

An earlier version had `isChartUniv_top_of_isChartLocusFibre`, advertised as "the route from the
certificate to antecedent 1 in one name rather than two compositions".  **The one name already
existed**: `isChartUniv_of_isChartLocusFibre` (`Pic0ChartUnivReduce.lean:184`), in this file's
import closure, concluding `IsChartUniv` at *arbitrary* `V` and needing no composition.  Mine was
a longer proof of a strictly weaker statement, and telling a lane to cite it would have scheduled
a detour.  Deleted rather than renamed, and recorded here so the deletion is not re-added: a lane
holding `IsChartLocusFibre` should cite the landed name directly. -/

/-! ## THE BOUNDARY: the collapse's coverage input is unavailable at the parameter where its
other input is known

Everything above is conditional on `DivFunctorObjSubsingleton`, and the only parameter where that
is landed is `n = 0` (over a field, `instSubsingletonDivFamZarZero`; the general-`R` half is the
`deg-zero` row).  So the natural next move is to feed
`pic0RepresentableBy_of_isChartLocusFibre_of_coverage` at `n = 0`.  **That is blocked, and not by
the certificate**: `Picard/Pic0ChartLocusH0Rank.lean`'s rank formula makes the chart locus
literally empty there for a curve of genus `≥ 2`.

Landing this as a theorem rather than a caveat, because a limit stated in prose is the part of a
file nobody re-checks — and here the limit is what stops the collapse from being read as a route
to representability at `0`. -/

/-- **At parameter `0` on a curve of genus `≥ 2` the chart locus is EMPTY.**

`exists_splitting_h0_formula_of_mem_chartLocus` extracts from chart-locus membership a splitting
witness with `h⁰ = n + 1 - g`.  At `n = 0` that is `1 - g ≤ -1`, while `h⁰` is a cast natural
number, hence nonnegative — contradiction.

**Consequence, stated at the strength actually proved.**  What dies at `n = 0` is the
*chartLocus-mediated route* to coverage — the intended instantiation of `PointwiseCoverage`'s open
`W` by `chartLocusOpens`.  It is **not** a refutation of `hcov`, which quantifies over an
arbitrary `W ∋ t` and never mentions `chartLocus`; that stronger statement is open.  An earlier
version of this docstring asserted it, and the assertion made the limit look harsher and more
audited than it was.

So: the collapse names *which* obligation the seam owes at a `Mono` parameter, and the
locus-mediated way of paying the coverage half is unavailable at the one parameter where the
subsingleton is landed.  Whether some other `W` pays it there is not settled.

The complement is the high-parameter branch: above the genus the same formula gives `h⁰ ≥ 2`
(`exists_splitting_two_le_h0_of_mem_chartLocus`), which is where coverage is available and where
the subsingleton must fail.  That is the same inequality read from the other side, and it is why
these are two branches rather than one route. -/
theorem not_mem_chartLocus_of_two_le_genus_zero_param
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) (g : ℕ)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (0 : ℤ))
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hlam : degAt lam (Over.testPoint t) = 0) (hg : 2 ≤ g) :
    t ∉ chartLocus C m Z lam := by
  intro ht
  obtain ⟨L, hLf, hLa, hLKa, hLtow, hLfin, hLsep, M, W, hM, hWcl, hWdeg, hWh1, hrank⟩ :=
    exists_splitting_h0_formula_of_mem_chartLocus lam t m Z 0 g (by simpa using hdeg) hχ
      hlam ht
  have h0nonneg : (0 : ℤ)
      ≤ (Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L W) : ℤ) := Int.natCast_nonneg _
  rw [hrank] at h0nonneg
  omega

end

end AlgebraicGeometry
