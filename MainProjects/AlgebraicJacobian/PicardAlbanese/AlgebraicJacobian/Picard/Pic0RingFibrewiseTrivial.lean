/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0VanishingRigidityReduction
import AlgebraicJacobian.Picard.DegreeSeam

/-!
# A `pic⁰` CLASS OVER A TEST **RING** IS TRIVIAL ON EVERY FIBRE

The one surviving instance of the hypothesis both live routes to a `rep` producer pass through
is the **ring** case of the degree-zero vanishing:

  `∀ (A : Type u) [CommRing A] [Algebra k A], Subsingleton (pic0Subgroup C (overSpec k A))`

`Picard/Pic0VanishingFieldTest.lean` closed every **field** instance at genus `0`, and
`Picard/Pic0VanishingAffineReduction.lean` proved the affine binder *is* the `∀ T` binder.  What
separates the two is a rigidity statement over a base ring, and the classical route to it —
cohomology and base change — consumes a **fibrewise** hypothesis.

**This file supplies that hypothesis, as a theorem rather than a binder.**  For a `pic⁰` class
over an arbitrary test ring `A`, at genus `0`:

* its restriction along every field point of `overSpec k A` is `1` (`fibre_eq_one`);
* its fibre Čech class at every prime `p` of `A` has `classDeg κ(p) = 0`
  (`classDeg_fibre_eq_zero_of_cocyclePresented`, via the DAT-4 seam).

## SUPERSEDED IN PART — read this before citing the first two theorems

A fresh-context audit of this file (accepted in full) established two things about its own
content, and both are recorded here rather than in a commit message nobody reads:

1. **`Picard/Pic0VanishingRigidityReduction.lean:104` has the same statement at an ARBITRARY
   test object.**  `fibre_eq_one_of_mem_pic0Subgroup` is `pic0_fibre_eq_one_of_genus_zero`
   without the affineness of the test, by the same `Subsingleton.elim`, and it landed twenty
   minutes after this file.  So the first two theorems below are *affine specializations of a
   landed more general lemma* and should not be cited as independent results; cite that one.
   The residue-field corollary is a one-line instantiation of it too.
2. **The lead theorem's proof does not use its own subject.**  `pic0_fibre_eq_one_of_genus_zero`
   is `Subsingleton.elim` on the target group, so `lam`, `t` and `pic0Map` appear in the
   statement and contribute nothing to the proof — the probe replacing the subject by an
   arbitrary element of the target closes identically.  The "mechanism" the docstring below
   describes (`pic0Map` landing in `pic0Subgroup` through `degAt_picEtMap`) is work done by the
   *type ascription*, not by the proof term.  That is not a defect in the statement, which is
   true and is the shape consumers want; it does mean the theorem is cheap, and it was first
   presented here as though the mechanism were the content.

**What survives as this file's own contribution** is the third theorem,
`classDeg_fibre_eq_zero_of_cocyclePresented`: the DAT-4 seam application that turns the
membership into a *degree* equation at each prime, which is the spelling
`Picard/Pic0RingDatumEngine.lean` consumes.  It is two tactic lines and it is not duplicated.

## What consumes this, and in which spelling

`Picard/Pic0RingDatumEngine.lean` fires the RE-4 rigid engine on a
`BasicOpenCocycleDatum C B π` under exactly

  `htriv : ∀ p : PrimeSpectrum B, (D.baseChange p.asIdeal.ResidueField).cechPicClass = 1`

and its own `fibre_cechPicClass_eq_one_of_classDeg_eq_zero` converts a *degree-`0`* hypothesis at
a prime into that triviality at genus `0`.  So the engine's binder is reachable from a `pic⁰`
membership, and this file is the reduction that reaches it: `htriv_of_pic0` composes the two.

The residue-field instantiation is written out and is **not** a restatement of the field-point
form: `pic0Subgroup` membership quantifies over `k`-algebra maps `A →ₐ[k] K` into fields, and the
engine quantifies over primes of `A`.  A prime's residue field is such a `K` and
`IsLocalRing.residue ∘ algebraMap` such a map, but the instantiation has to be written for the
consumer to fire — recorded because the two spellings look interchangeable and are not
(the caveat pic-c raised on `I-1640`).

## Why the degree condition is *entirely* consumed here

Membership in `pic0Subgroup C (overSpec k A)` is degree vanishing at every field point.  The
*triviality* statements spend that binder and return a conclusion with no degree in it, so the
distance from them to the ring case carries no Riemann–Roch, no `χ`, no chart and no divisor: it
is the pure rigidity implication "trivial at every fibre ⟹ trivial".  That is a repricing of the
ring case, not a discharge of it.

**Corrected after audit:** this claim is *false about the third theorem*, and an earlier version
of this paragraph asserted it of every statement in the file.
`classDeg_fibre_eq_zero_of_cocyclePresented` has a degree equation **in its conclusion** — that
is its purpose, since the engine's converse consumes a degree — and it takes no `genus C = 0`
binder at all, so the sentence "both statements consume `genus C = 0`" was wrong about it as
well.  Three of the four theorems consume the genus; the degree one does not.

## What this does NOT do

* **It does not prove the ring case.**  Fibrewise triviality is strictly weaker than triviality
  over `A`: `Subsingleton (CommRing.Pic (Polynomial A))` fails to synthesize even *given*
  `Subsingleton (CommRing.Pic A)` (measured, `lake env lean`), so no chart or fibre argument
  closes the gap by itself; Traverso–Swan is why.  What closes it is the rigid engine's
  invertibility conclusion plus a section, which is another lane's route.
* **The `classDeg` statement is conditional on a cocycle presentation** of the class
  (`h : picEtAffineEquiv C A lam = PicEtAff.unit C A (relPicMk C _ L)`), because the DAT-4 seam
  is.  `fibre_eq_one` is unconditional.
* **Nothing here is about positive genus.**  Both statements consume `genus C = 0` through the
  landed field-test vanishing; at positive genus the fibre classes are *not* trivial and the
  conclusion is false.

## Main declarations

* `AlgebraicGeometry.pic0_fibre_eq_one_of_genus_zero` — **the fibrewise triviality**: a `pic⁰`
  class over a test ring restricts to `1` at every field point, at genus `0`.
* `AlgebraicGeometry.pic0_fibre_residueField_eq_one_of_genus_zero` — the same at the residue
  field of a prime, the spelling the ring-datum engine quantifies over.
* `AlgebraicGeometry.classDeg_fibre_eq_zero_of_cocyclePresented` — the fibre Čech class of a
  cocycle-presented `pic⁰` class has degree `0` at every prime.
* `AlgebraicGeometry.P1.pic0_fibre_eq_one` — non-vacuity: the same at `ℙ¹` over an arbitrary
  field, with no hypothesis at all.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## Fibrewise triviality of a degree-zero class over a test ring -/

/-- **A `pic⁰` class over a test RING is trivial at every field point**, at `genus C = 0`.

The mechanism is that `pic0Map` *lands in* `pic0Subgroup` at the target test — the degree-zero
condition is stable under restriction, definitionally through `degAt_picEtMap`
(`Pic0Functor.lean:87`).  At a **field** test the whole degree-zero subgroup is a subsingleton
(`subsingleton_pic0Subgroup_overSpec_field_of_genus_zero`), so the restricted class equals `1`
there.

This consumes the degree binder completely: the conclusion mentions no degree.  It is the
fibrewise hypothesis of cohomology-and-base-change, available at genus `0` for *every* class at
*every* prime simultaneously — no locus, no openness, no spreading-out. -/
theorem pic0_fibre_eq_one_of_genus_zero (hg : genus C = 0)
    {A : Type u} [CommRing A] [Algebra k A] (lam : pic0Subgroup C (overSpec k A))
    (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ overSpec k A) :
    pic0Map C t lam = 1 :=
  @Subsingleton.elim _
    (subsingleton_pic0Subgroup_overSpec_field_of_genus_zero C K hg) _ _

/-- The same in the underlying `picEt` group: the restricted class is the trivial class. -/
theorem picEtMap_pic0_fibre_eq_one_of_genus_zero (hg : genus C = 0)
    {A : Type u} [CommRing A] [Algebra k A] (lam : pic0Subgroup C (overSpec k A))
    (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ overSpec k A) :
    picEtMap C t (lam : picEt C (overSpec k A)) = 1 :=
  fibre_eq_one_of_mem_pic0Subgroup C hg lam K t

/-! ## The residue-field spelling: what the ring-datum engine quantifies over -/

/-- **The fibrewise triviality at the residue field of a prime.**

`Picard/Pic0RingDatumEngine.lean` quantifies its `htriv` binder over `PrimeSpectrum B`, while
`pic0Subgroup` membership quantifies over `k`-algebra maps into fields.  A prime's residue field
`κ(p)` is a field extension of `k` (through `A`), and the field point of `overSpec k A` at `p` is
`Over.overSpecMap` of the composite algebra map — so the two quantifiers match, but only once
this instantiation is written.

Recorded as its own declaration for exactly that reason: "residue fields are field points" is
true and is not a proof that a consumer indexed by primes can fire. -/
theorem pic0_fibre_residueField_eq_one_of_genus_zero (hg : genus C = 0)
    {A : Type u} [CommRing A] [Algebra k A] (lam : pic0Subgroup C (overSpec k A))
    (p : PrimeSpectrum A) :
    pic0Map C (Over.overSpecMap
        ((Algebra.ofId A p.asIdeal.ResidueField).restrictScalars k)) lam = 1 :=
  pic0_fibre_eq_one_of_genus_zero C hg lam _ _

/-! ## The degree of the fibre Čech class -/

/-- **The fibre Čech class of a cocycle-presented `pic⁰` class has degree zero**, at every
`k`-algebra map into a field — in particular at every residue field.

Route: the DAT-4 seam `degAt_of_affineEquiv_eq_unit_relPicMk` (`Picard/DegreeSeam.lean:81`)
identifies `degAt lam (Over.overSpecMap φ)` with `classDeg K` of the pulled-back Čech class, and
membership in `pic0Subgroup` says the left side is `0`.

This is the form a consumer holding a *degree* hypothesis at a prime wants: the ring-datum
engine's `fibre_cechPicClass_eq_one_of_classDeg_eq_zero` converts it to triviality of the fibre
class at genus `0`. -/
theorem classDeg_fibre_eq_zero_of_cocyclePresented
    {A : Type u} [CommRing A] [Algebra k A] {K : Type u} [Field K] [Algebra k K]
    (lam : pic0Subgroup C (overSpec k A)) (L : (C ⊗ overSpec k A).left.CechPic)
    (h : picEtAffineEquiv C A (lam : picEt C (overSpec k A))
      = PicEtAff.unit C A (relPicMk C (overSpec k A) L))
    (φ : A →ₐ[k] K) :
    classDeg K (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left) L) = 0 := by
  rw [← degAt_of_affineEquiv_eq_unit_relPicMk φ (lam : picEt C (overSpec k A)) L h]
  exact lam.2 K (Over.overSpecMap φ)

/-! ## Non-vacuity: the statements fire at a curve, unconditionally -/

/-- **Fibrewise triviality at `ℙ¹`, with no hypothesis.**

`Curve/P1H1Vanishing.lean` supplies `genus (P1.asOver k) = 0` over an arbitrary field and
`Curve/P1Curve.lean` the three curve binders, so the theorem above applies with nothing left to
discharge.  Recorded because a fibrewise hypothesis nobody can instantiate is worth nothing, and
this one is instantiated at a real curve over an arbitrary field. -/
theorem P1.pic0_fibre_eq_one (k : Type u) [Field k]
    {A : Type u} [CommRing A] [Algebra k A]
    (lam : pic0Subgroup (P1.asOver k) (overSpec k A))
    (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ overSpec k A) :
    pic0Map (P1.asOver k) t lam = 1 :=
  pic0_fibre_eq_one_of_genus_zero (P1.asOver k) (P1.genus_asOver_eq_zero k) lam K t

/-- Non-vacuity of the residue-field spelling at `ℙ¹`. -/
theorem P1.pic0_fibre_residueField_eq_one (k : Type u) [Field k]
    {A : Type u} [CommRing A] [Algebra k A]
    (lam : pic0Subgroup (P1.asOver k) (overSpec k A)) (p : PrimeSpectrum A) :
    pic0Map (P1.asOver k) (Over.overSpecMap
        ((Algebra.ofId A p.asIdeal.ResidueField).restrictScalars k)) lam = 1 :=
  pic0_fibre_residueField_eq_one_of_genus_zero (P1.asOver k) (P1.genus_asOver_eq_zero k) lam p

end

end AlgebraicGeometry
