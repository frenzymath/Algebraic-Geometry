/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.P1H1Vanishing
import AlgebraicJacobian.RiemannRoch.GenusZeroDegreeTrivial
import AlgebraicJacobian.Cohomology.H1BaseFieldInvariance

/-!
# A DEGREE-ZERO PICARD CLASS ON `ℙ¹_K` IS TRIVIAL, FOR EVERY FIELD EXTENSION `K/k`

`RiemannRoch/GenusZeroDegreeTrivial.lean` proves `classDeg K L = 0 → L = 1` from `χ(𝒪_X) = 1`
at an abstract curve `X` over `K`.  This file instantiates it at `ℙ¹`, which needs `χ = 1` at
the *base-changed* curve for every extension `K/k` rather than only over the base field.

**READ THE STATUS NOTE BELOW BEFORE CITING THIS FILE.**  An earlier version of this paragraph
attributed the "not instantiated at any concrete curve" observation to a note *inside*
`GenusZeroDegreeTrivial.lean`.  That is **false** — grep finds no such phrase there, at the
commit that wrote it or at HEAD.  The observation came from inbox `I-1616`, a message from the
lane that wrote that file, and a docstring is the wrong place to have laundered an inbox
message into a citation.

## STATUS: this file is a COROLLARY LAYER, not an independent result

Measured by a fresh-context audit (`I-1633`), and it is the honest framing: **all four
declarations below follow from `Picard/Pic0VanishingFieldGenusZero.lean` alone**, which landed
seven minutes earlier and is general in the curve.  `chi_baseChange_eq_one` is one application
of that file's `chi_moduleKSheaf_baseChange_eq_one_of_genus_zero` to
`P1.genus_asOver_eq_zero`; I re-verified the subsumption myself rather than take it on report.

What is genuinely not duplicated is `eq_of_classDeg_eq_baseChange` — no
`Injective (classDeg …)` statement exists elsewhere in the tree — and the value of the rest is
that the specialisation at `ℙ¹` is spelled out where a reader of the `ℙ¹` material will find it.
That is a convenience, and it should not be quoted as new mathematics.

## Why the base-changed curve and not just `ℙ¹_k`

The consumer is the `∀ T` binder of the `pic⁰` vanishing.  `pic0Subgroup C T` is cut out by
`degAt` at *every field point* `t : overSpec k K ⟶ T` (`Picard/Pic0Functor.lean:107`), and
`degAt` is read through `relPicDeg K` on `relPic C (overSpec k K)`, which is a quotient of
`CechPic ((C ⊗ overSpec k K).left)` — the Čech Picard group of the curve base-changed to `K`.
So the field-point content of the vanishing is a statement about `ℙ¹_K` for every `K`, and a
computation over `k` alone does not touch it.

## The composite, and where each input comes from

`genus (baseChangeBundle C K) = genus C` is base-field invariance of the genus
(`Cohomology/H1BaseFieldInvariance.lean:373`), and `χ(𝒪) = 1 - genus`
(`RiemannRoch/ChiCurve.lean:148`).  At `C = P1.asOver k` the genus is `0`
(`Curve/P1H1Vanishing.lean:187`), so `χ = 1` at `ℙ¹_K` for **every** `K`.  Feed that to
`eq_one_of_classDeg_eq_zero_of_chi_one`.

Nothing here is new mathematics; all four inputs were landed and unconnected.  The reason it
was worth a file is that the composite is what turns a theorem about an abstract curve
carrying a `χ` hypothesis into a fact about an object this project has built.

## What this does NOT do

It does **not** discharge `∀ T : Over (Spec k), Subsingleton (pic0Subgroup (P1.asOver k) T)`,
and the gap is not a quantifier shuffle.  `pic0Subgroup C T` at a general test `T` consists of
classes on `C ⊗ T` whose restriction to every *field* point has degree zero; this file says
each of those restrictions is trivial, which is **fibrewise triviality**, not triviality.
Concluding the class itself is trivial is the descent step — for `T = overSpec k A` it is
`Pic(ℙ¹_A) ≅ Pic(A) × ℤ`, cohomology and base change — and it is untouched here.

Recorded because the distance is easy to misread: the field case being closed makes the ring
case look like bookkeeping, and it is not.  In particular a chart-by-chart argument does not
extend from fields to rings, and the reason is worth separating into what is measured here and
what is quoted from outside:

* **measured.** `Subsingleton (CommRing.Pic (Polynomial k))` is `inferInstance` for a *field*
  `k` (through `NormalizedGCDMonoid`), which is what makes the charts of `ℙ¹_k` have trivial
  Picard group.  The same query for a general `[CommRing A]` **fails**, and it fails even
  given `Subsingleton (CommRing.Pic A)` as a hypothesis.  So the instance that carries the
  field argument is simply absent over a ring.
* **measured.** `grep -rli` over all of mathlib returns **zero** files matching `seminormal`
  and zero matching `traverso`; the `suslin` hit is Suslin's theorem in descriptive set
  theory, and every `quillen` hit is the model-structure Quillen.  So no route through that
  literature is available in the library as it stands.
* **quoted, not verified here.** That `Pic(A[t]) = Pic(A)` holds *exactly* for seminormal `A`
  is Traverso–Swan, mathematics from outside this formalization.  Nothing in this tree proves
  it or its failure, and the sentence is here to explain why the instance search above is not
  merely missing a lemma — not as a formalized no-go.

## Main declarations

* `AlgebraicGeometry.P1.chi_baseChange_eq_one` — `χ(𝒪) = 1` on `ℙ¹_K` for every field
  extension `K/k`.
* `AlgebraicGeometry.P1.eq_one_of_classDeg_eq_zero_baseChange` — **a degree-zero Čech Picard
  class on `ℙ¹_K` is trivial**, and `classDeg_eq_zero_iff_baseChange`, the iff.
* `AlgebraicGeometry.P1.eq_of_classDeg_eq_baseChange` — the degree determines the class, which
  is the shape a degree-cut-out subgroup consumes.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

namespace P1

variable (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]

/-- **`χ(𝒪) = 1` on `ℙ¹_K`, for every field extension `K/k`.**

`χ = 1 - genus` at any curve, and the genus is a base-field invariant, so this is
`genus (P1.asOver k) = 0` transported along `K/k`.  This is the input
`eq_one_of_classDeg_eq_zero_of_chi_one` needs and the one its author flagged as not
elaborated at a concrete curve. -/
theorem chi_baseChange_eq_one :
    Sheaf.chi (((P1.asOver k) ⊗ overSpec k K).left.moduleKSheaf K) = 1 := by
  haveI : IsProper (baseChangeBundle (P1.asOver k) K).hom :=
    instIsProperSndLeft (P1.asOver k) K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle (P1.asOver k) K).hom :=
    instSmoothOfRelativeDimensionSndLeft (P1.asOver k) K
  haveI : GeometricallyIrreducible (baseChangeBundle (P1.asOver k) K).hom :=
    instGeometricallyIrreducibleSndLeft (P1.asOver k) K
  have hg : genus (baseChangeBundle (P1.asOver k) K) = genus (P1.asOver k) :=
    genus_baseField (P1.asOver k) K
  have h0 : genus (P1.asOver k) = 0 := P1.genus_asOver_eq_zero k
  have hchi := chi_moduleKSheaf (baseChangeBundle (P1.asOver k) K)
  rw [hg, h0] at hchi
  -- `(baseChangeBundle C K).left` is `(C ⊗ overSpec k K).left` by `rfl`; the two spellings
  -- differ only in which one typeclass resolution keys the `Over` instance on.
  change Sheaf.chi ((baseChangeBundle (P1.asOver k) K).left.moduleKSheaf K) = 1
  simpa using hchi

/-- **A degree-zero Čech Picard class on `ℙ¹_K` is trivial**, for every field extension
`K/k`.

The instantiation `GenusZeroDegreeTrivial` was missing: its `χ(𝒪_X) = 1` hypothesis is
discharged at this carrier by `chi_baseChange_eq_one`. -/
theorem eq_one_of_classDeg_eq_zero_baseChange
    (L : ((P1.asOver k) ⊗ overSpec k K).left.CechPic)
    (hL : classDeg K L = 0) : L = 1 :=
  eq_one_of_classDeg_eq_zero_of_chi_one K (chi_baseChange_eq_one k K) L hL

/-- The iff, so `classDeg` is visibly **injective** on `CechPic (ℙ¹_K)` rather than merely
having trivial kernel on the nose. -/
theorem classDeg_eq_zero_iff_baseChange
    (L : ((P1.asOver k) ⊗ overSpec k K).left.CechPic) :
    classDeg K L = 0 ↔ L = 1 :=
  ⟨eq_one_of_classDeg_eq_zero_baseChange k K L, fun h => by rw [h, classDeg_one]⟩

/-- **The degree determines the class on `ℙ¹_K`**: two Picard classes of the same degree are
equal.  (Injectivity of `classDeg`, stated on the multiplicative Picard group rather than on
`Additive`, which is the spelling every consumer in this tree uses.)

This is the form the degree-zero *subgroup* consumes: `pic0Subgroup` is cut out by a degree
condition, and a subgroup lying in the kernel of an injective homomorphism is trivial. -/
theorem eq_of_classDeg_eq_baseChange
    (L L' : ((P1.asOver k) ⊗ overSpec k K).left.CechPic)
    (h : classDeg K L = classDeg K L') : L = L' := by
  have hdiv : classDeg K (L * L'⁻¹) = 0 := by
    rw [classDeg_mul, classDeg_inv, h]
    omega
  exact mul_inv_eq_one.mp (eq_one_of_classDeg_eq_zero_baseChange k K _ hdiv)

end P1

end AlgebraicGeometry
