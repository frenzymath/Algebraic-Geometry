/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RingFibrewiseTrivial
import AlgebraicJacobian.Picard.Pic0RingDatumEngine
import AlgebraicJacobian.Cohomology.GluedSheafExtraction

/-!
# THE RIGID ENGINE FIRES FROM A `pic⁰` MEMBERSHIP, WITH NO FIBREWISE BINDER LEFT

`Picard/Pic0RingDatumEngine.lean` fires the RE-4 rigid engine at genus `0` on a
`BasicOpenCocycleDatum C B π` under the fibrewise binder

  `htriv : ∀ p : PrimeSpectrum B, (D.baseChange p.asIdeal.ResidueField).cechPicClass = 1`

and `Picard/Pic0RingFibrewiseTrivial.lean` proves the corresponding statement for a class in
`pic0Subgroup C (overSpec k B)`.  **This file joins the two**: for a cocycle-presented `pic⁰`
class the binder is discharged, so the engine's conclusions hold with no fibrewise hypothesis
anywhere in the statement.

## What had to be written, and why it is not a restatement

Three spelling seams, each of which had to be crossed rather than asserted:

1. **`relCurveMap` vs the whiskering.**  The engine's base-change naturality
   (`cechPicClass_baseChange`) is stated on `relCurveMap C B B'`, which is *defined* as
   `(C ◁ overSpecMap B B').left` (`Cohomology/RelativeSectionsLinear.lean:160`); the degree
   seam (`Picard/DegreeSeam.lean:81`) is stated on `(C ◁ Over.overSpecMap φ).left`.  The two
   `overSpecMap`s are **independent definitions in different namespaces** — the duplicate pair
   recorded as `I-0144` — and they agree by `rfl` only when `φ` is the canonical algebra map
   `(Algebra.ofId B κ(p)).restrictScalars k`.  `relCurveMap_eq_whiskerLeft_residueField` is
   that identification, and everything downstream needs it.
2. **Field points vs primes.**  `pic0Subgroup` membership quantifies over `k`-algebra maps
   into fields; the engine quantifies over `PrimeSpectrum B`.  A residue field *is* such a
   field but the instantiation is a written step, not an observation.
3. **Degree vs triviality.**  What the membership gives at a prime is a vanishing `classDeg`;
   what the engine wants is a trivial class.  The engine's own
   `fibre_cechPicClass_eq_one_of_classDeg_eq_zero` converts one to the other at genus `0`, and
   it carries **five fibre instance binders** that do not synthesize through the `relCurve`
   `def` barrier; they are installed by hand here, as they are there.

## What this buys, stated exactly

The remaining distance from a `pic⁰` class over a test ring to *triviality* of that class is
now: `H¹(C_B, F) = 0` and `H⁰(C_B, F)` invertible (stalk rank `1` at every prime) **are
available**, unconditionally on the class beyond its being degree-zero and presented.  On the
**divisor/pushforward route** the step that turns an invertible pushforward into a
trivialization of the class is the evaluation map `π^*π_*L → L`, which my search did not find in
this tree.

**Scope corrected after review.**  An earlier version of this paragraph called that evaluation
map "the remaining step" for the ring case as such, and asserted its absence from the sibling
project and mathlib as measured.  Both were too strong.  It is the remaining step on *this*
route only: `Picard/Pic0VanishingRigidityReduction.lean` reaches the same vanishing through
field-point rigidity, which never produces a divisor and so never needs the evaluation map at
all.  And I verified absence only in AJCR — not in `Algebraic-Jacobian-Challenge`, which has
adjunction/counit material, and not in mathlib.

## What this does NOT do

* **It does not prove the ring case**, and it is not on the shortest route to it.  The
  evaluation step above is not built here; a fibrewise-trivial class over a ring need not be
  trivial (Traverso–Swan: `Subsingleton (CommRing.Pic (Polynomial A))` fails even *given*
  `Subsingleton (CommRing.Pic A)`, measured).  A lane wanting only the vanishing should read
  `Pic0VanishingRigidityReduction.lean` first: it reduces the same goal to field-point rigidity
  with no cohomology, no pushforward and no divisor.  What *this* file is for is the
  pushforward route, where `π_*L` invertible is the object of interest in its own right.
* **`IsNoetherianRing B` is inherited**, not introduced: it is the engine's own binder, which
  `Cohomology/DatumDescent.lean:547` is designed to remove.  Nothing here re-proves it and a
  consumer should remove it through that route.
* **The cocycle presentation is a real hypothesis** on the `pic⁰` class, inherited from the
  DAT-4 degree seam.  `exists_cechPicClass_eq` produces a datum for any Čech class on `C_B`,
  but relating *that* datum's class to the plus-class presentation of a `picEt` element is the
  `picEtAffineEquiv`/`unit` seam, and it is assumed here rather than proved.

  **What the binder is, exactly, after measurement — and a first answer CORRECTED.**  The
  *datum* half is free: `exists_datum_pic0_presentation` below produces a presenting datum for
  any class whose affine collapse is `PicEtAff.unit` of *some* relative class (`relPicMk` is
  surjective and `exists_cechPicClass_eq` is total over every `k`-algebra).

  An earlier version of this paragraph then named ring-level surjectivity of `PicEtAff.unit` as
  the remaining brick, on the ground that `PicEtAff.unit_surjective_of_section`
  (`Picard/EffectivityClose.lean:141`) is field-only and section-dependent.  **That was wrong**,
  and a fresh-context audit caught it: `picEtAffineEquiv_relPicToPicEt`
  (`Picard/PicEtUnit.lean:161`) supplies the seam at an **arbitrary test ring**, with no field,
  no section and no curve hypothesis, for every class in the range of `relPicToPicEt`.  So the
  seam is not the obstruction it was priced as; `presentation_of_relPicToPicEt` below is that
  observation made usable, and `rigidEngine_of_relPicToPicEt` fires the engine with the
  presentation binder **eliminated** for such classes.

  What is genuinely missing is therefore **surjectivity of `relPicToPicEt` onto `picEt`** — that
  every étale-plus class over a ring comes from a relative Picard class — which is a different
  statement about a different map, and is what a lane wanting these conclusions at an
  *arbitrary* degree-zero class should target.  `Pic0ChartPlusFibreProducer.lean:199` calls
  membership in that range "honesty" and treats it as a real condition, which is consistent.
* **Genus `0` only.**  At positive genus the fibre classes are not trivial.

## Main declarations

* `AlgebraicGeometry.relCurveMap_eq_whiskerLeft_residueField` — the `I-0144` spelling bridge.
* `AlgebraicGeometry.exists_datum_relPicMk_eq` / `exists_datum_pic0_presentation` — the datum in
  the presentation binder is produced, not assumed, at every test ring.
* `AlgebraicGeometry.BasicOpenCocycleDatum.htriv_of_pic0` — **the discharge**: the engine's
  fibrewise binder, from a cocycle-presented `pic⁰` class.
* `AlgebraicGeometry.BasicOpenCocycleDatum.rigidEngine_of_pic0` — the engine's three
  conclusions with no fibrewise hypothesis.
* `AlgebraicGeometry.BasicOpenCocycleDatum.rankAtStalk_hModule_zero_eq_one_of_pic0` —
  **`π_*L` invertible** from a `pic⁰` membership.
* `AlgebraicGeometry.P1.rankAtStalk_hModule_zero_eq_one_of_pic0` — non-vacuity at `ℙ¹` over an
  arbitrary field.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable section

/-! ## The spelling bridge (`I-0144`) -/

/-- **The two `overSpecMap`s agree at a residue field.**

`overSpecMap B κ(p)` (`Cohomology/RelativeSectionsLinear.lean:147`) is built from the
`algebraMap`; `Over.overSpecMap φ` (`Picard/RelPicAlgebra.lean:44`) from an arbitrary
`k`-algebra map.  These are two independent definitions of the same morphism in different
namespaces — the duplicate pair filed as `I-0144` — and at the canonical map
`(Algebra.ofId B κ(p)).restrictScalars k` they are definitionally equal.

Stated because the engine's base-change lemmas live on the first spelling and the degree seam
on the second, so no composition of the two is possible without it. -/
theorem relCurveMap_eq_whiskerLeft_residueField (C : Over (Spec (.of k)))
    (B : Type u) [CommRing B] [Algebra k B] (p : PrimeSpectrum B) :
    relCurveMap C B p.asIdeal.ResidueField
      = (C ◁ Over.overSpecMap
          ((Algebra.ofId B p.asIdeal.ResidueField).restrictScalars k)).left :=
  rfl

/-! ## The datum in the presentation binder is not a real constraint -/

/-- **Every relative Picard class over a test ring is presented by a cocycle datum.**

`relPicMk` is surjective (`RelPic.lean:75`) and `exists_cechPicClass_eq`
(`Cohomology/GluedSheafExtraction.lean:301`) turns the resulting Čech class into a
`BasicOpenCocycleDatum` with the same class, at **every** `k`-algebra `B`.

This is what makes the presentation binder of the theorems below a condition on the *class*
rather than on a choice of datum: a `pic⁰` class that is `PicEtAff.unit` of some relative class
at all is presented by some datum, and `exists_datum_pic0_presentation` extracts it. -/
theorem exists_datum_relPicMk_eq (C : Over (Spec (.of k)))
    (B : Type u) [CommRing B] [Algebra k B] (π : C.left ⟶ P1 k) [IsFinite π]
    (z : relPic C (overSpec k B)) :
    ∃ D : BasicOpenCocycleDatum C B π, relPicMk C (overSpec k B) D.cechPicClass = z := by
  obtain ⟨L, hL⟩ := relPicMk_surjective C (overSpec k B) z
  obtain ⟨D, hD⟩ := BasicOpenCocycleDatum.exists_cechPicClass_eq (π := π) L
  exact ⟨D, by rw [hD, hL]⟩

/-- **The presentation binder, in its weakest form**: if the affine collapse of `lam` is
`PicEtAff.unit` of *any* relative class, then it is `PicEtAff.unit` of `relPicMk` of some
datum's Čech class — which is the hypothesis the theorems below take.

So those theorems do not secretly quantify over a lucky datum: the datum is produced, and the
surviving hypothesis is the `picEtAffineEquiv`/`unit` seam on `lam` alone. -/
theorem exists_datum_pic0_presentation (C : Over (Spec (.of k)))
    (B : Type u) [CommRing B] [Algebra k B] (π : C.left ⟶ P1 k) [IsFinite π]
    (lam : picEt C (overSpec k B))
    (h : ∃ z : relPic C (overSpec k B), picEtAffineEquiv C B lam = PicEtAff.unit C B z) :
    ∃ D : BasicOpenCocycleDatum C B π,
      picEtAffineEquiv C B lam
        = PicEtAff.unit C B (relPicMk C (overSpec k B) D.cechPicClass) := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨D, hD⟩ := exists_datum_relPicMk_eq C B π z
  exact ⟨D, by rw [hz, hD]⟩

namespace BasicOpenCocycleDatum

/-! ## The fibrewise binder, discharged -/

/-- **THE DISCHARGE**: the engine's fibrewise binder holds for a cocycle-presented `pic⁰`
class, at genus `0`.

Composition of three landed steps and the bridge above:
`cechPicClass_baseChange` moves the fibre class onto `Scheme.CechPic.map (relCurveMap …)`;
the bridge rewrites that as the whiskering the degree seam speaks about;
`classDeg_fibre_eq_zero_of_cocyclePresented` gives `classDeg κ(p) = 0` from the membership;
and the engine's `fibre_cechPicClass_eq_one_of_classDeg_eq_zero` converts degree `0` to
triviality at genus `0`.

The five fibre instances are installed by hand — they do not synthesize through the `relCurve`
`def` barrier, exactly as `Pic0RingDatumEngine` records. -/
theorem htriv_of_pic0 (D : BasicOpenCocycleDatum C B π) (hg : genus C = 0)
    (lam : pic0Subgroup C (overSpec k B))
    (h : picEtAffineEquiv C B (lam : picEt C (overSpec k B))
      = PicEtAff.unit C B (relPicMk C (overSpec k B) D.cechPicClass))
    (p : PrimeSpectrum B) :
    (D.baseChange p.asIdeal.ResidueField).cechPicClass = 1 := by
  haveI : IsIntegral (relCurve C p.asIdeal.ResidueField) :=
    instIsIntegralBaseChange C p.asIdeal.ResidueField
  haveI : SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instSmoothOfRelativeDimensionBaseChange C p.asIdeal.ResidueField
  haveI : QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instQuasiCompactBaseChange C p.asIdeal.ResidueField
  haveI : Module.Finite p.asIdeal.ResidueField (Sheaf.HModule
      ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 0) :=
    instModuleFiniteHModuleZeroBaseChange C p.asIdeal.ResidueField
  haveI : Module.Finite p.asIdeal.ResidueField (Sheaf.HModule
      ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 1) :=
    instModuleFiniteHModuleOneBaseChange C p.asIdeal.ResidueField
  refine D.fibre_cechPicClass_eq_one_of_classDeg_eq_zero hg p ?_
  rw [D.cechPicClass_baseChange p.asIdeal.ResidueField,
    relCurveMap_eq_whiskerLeft_residueField C B p]
  exact classDeg_fibre_eq_zero_of_cocyclePresented C lam D.cechPicClass h _

/-! ## The engine, with no fibrewise hypothesis -/

/-- **The rigid engine from a `pic⁰` membership**: `H¹(C_B, F_D) = 0` and `H⁰(C_B, F_D)` finite
projective over `B`, for a cocycle-presented degree-zero class at genus `0`.

No fibrewise clause appears in the statement: the hypotheses are the membership, its
presentation, and the engine's own `IsNoetherianRing B`. -/
theorem rigidEngine_of_pic0 (D : BasicOpenCocycleDatum C B π) [IsNoetherianRing B]
    (hπ : π ≫ P1.structureMap k = C.hom) (hg : genus C = 0)
    (lam : pic0Subgroup C (overSpec k B))
    (h : picEtAffineEquiv C B (lam : picEt C (overSpec k B))
      = PicEtAff.unit C B (relPicMk C (overSpec k B) D.cechPicClass)) :
    Subsingleton (Sheaf.HModule D.sheaf 1) ∧
      Module.Finite B (Sheaf.HModule D.sheaf 0) ∧
      Module.Projective B (Sheaf.HModule D.sheaf 0) :=
  D.rigidEngine_of_genus_zero hπ hg (D.htriv_of_pic0 hg lam h)

/-- **`π_*L` IS INVERTIBLE, FROM A `pic⁰` MEMBERSHIP** — the stalk rank of `H⁰` is `1` at every
prime of the test ring, for a cocycle-presented degree-zero class at genus `0`.

This is the cohomological output the classical seesaw argument consumes next.  What it does not
supply is the evaluation map `π^*π_*L → L`; see the module docstring. -/
theorem rankAtStalk_hModule_zero_eq_one_of_pic0 (D : BasicOpenCocycleDatum C B π)
    [IsNoetherianRing B] (hπ : π ≫ P1.structureMap k = C.hom) (hg : genus C = 0)
    (lam : pic0Subgroup C (overSpec k B))
    (h : picEtAffineEquiv C B (lam : picEt C (overSpec k B))
      = PicEtAff.unit C B (relPicMk C (overSpec k B) D.cechPicClass))
    (p : PrimeSpectrum B) :
    Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p = 1 :=
  D.rankAtStalk_hModule_zero_eq_one_of_genus_zero hπ hg (D.htriv_of_pic0 hg lam h) p

end BasicOpenCocycleDatum

/-! ## The presentation binder is FREE for classes from `relPic`

The correction recorded in the module docstring, made usable.  `picEtAffineEquiv_relPicToPicEt`
(`Picard/PicEtUnit.lean:161`) holds at an arbitrary test **ring**, so for a `pic⁰` class whose
underlying `picEt` class comes from `relPicToPicEt` the presentation is not a hypothesis at
all — it is produced, and with it the datum. -/

/-- **The presentation, produced at a test ring**, for a class in the range of `relPicToPicEt`.

No field, no curve section, no `IsProper`-flavoured input beyond the standing binders: the
ring-level affine-consistency lemma gives the `unit` form directly, and
`exists_datum_pic0_presentation` upgrades it to the datum form. -/
theorem presentation_of_relPicToPicEt (C : Over (Spec (.of k)))
    (B : Type u) [CommRing B] [Algebra k B] (π : C.left ⟶ P1 k) [IsFinite π]
    (z : relPic C (overSpec k B)) :
    ∃ D : BasicOpenCocycleDatum C B π,
      picEtAffineEquiv C B (relPicToPicEt C (overSpec k B) z)
        = PicEtAff.unit C B (relPicMk C (overSpec k B) D.cechPicClass) :=
  exists_datum_pic0_presentation C B π _ ⟨z, picEtAffineEquiv_relPicToPicEt C B z⟩

/-- **`π_*L` IS INVERTIBLE WITH NO PRESENTATION BINDER**, for a degree-zero class coming from a
relative Picard class over an arbitrary Noetherian test ring, at genus `0`.

This is the form the earlier statements should have had: the only hypotheses left are the
membership itself, that the class comes from `relPic` (`hz`), the covering datum and the
engine's `IsNoetherianRing`.  The datum is existentially produced rather than supplied.

**Non-vacuity of `hz`, stated at the level it is actually known.**  `hz` holds at the trivial
class (`map_one`, verified), so the statement is not empty.  Whether it holds at a *non-trivial*
degree-zero class is precisely the open surjectivity of `relPicToPicEt` discussed above — the
classes satisfying it form the intersection of `pic0Subgroup` with a subgroup, and this file
does not measure that intersection.  So: non-vacuous, and non-vacuous at a degenerate value
until that surjectivity lands. -/
theorem exists_rankAtStalk_hModule_zero_eq_one_of_relPicToPicEt (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (B : Type u) [CommRing B] [Algebra k B] [IsNoetherianRing B]
    (π : C.left ⟶ P1 k) [IsFinite π] (hπ : π ≫ P1.structureMap k = C.hom)
    (hg : genus C = 0) (lam : pic0Subgroup C (overSpec k B))
    (z : relPic C (overSpec k B))
    (hz : (lam : picEt C (overSpec k B)) = relPicToPicEt C (overSpec k B) z) :
    ∃ D : BasicOpenCocycleDatum C B π,
      ∀ p : PrimeSpectrum B, Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p = 1 := by
  obtain ⟨D, hD⟩ := presentation_of_relPicToPicEt C B π z
  exact ⟨D, fun p => D.rankAtStalk_hModule_zero_eq_one_of_pic0 hπ hg lam (by rw [hz]; exact hD) p⟩

/-! ## Non-vacuity at `ℙ¹` -/

/-- **The invertibility of `π_*L` at `ℙ¹` over an arbitrary field**, with the genus hypothesis
discharged by `Curve/P1H1Vanishing.lean`.

Recorded because the chain above is worth nothing if its curve hypothesis has no witness; the
remaining hypotheses are the membership, its cocycle presentation, the covering map datum and
the engine's Noetherian binder — none of them about the genus. -/
theorem P1.rankAtStalk_hModule_zero_eq_one_of_pic0 (k : Type u) [Field k]
    {B : Type u} [CommRing B] [Algebra k B] [IsNoetherianRing B]
    {π : (P1.asOver k).left ⟶ P1 k} [IsFinite π]
    (D : BasicOpenCocycleDatum (P1.asOver k) B π)
    (hπ : π ≫ P1.structureMap k = (P1.asOver k).hom)
    (lam : pic0Subgroup (P1.asOver k) (overSpec k B))
    (h : picEtAffineEquiv (P1.asOver k) B (lam : picEt (P1.asOver k) (overSpec k B))
      = PicEtAff.unit (P1.asOver k) B
          (relPicMk (P1.asOver k) (overSpec k B) D.cechPicClass))
    (p : PrimeSpectrum B) :
    Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p = 1 :=
  D.rankAtStalk_hModule_zero_eq_one_of_pic0 hπ (P1.genus_asOver_eq_zero k) lam h p

end

end AlgebraicGeometry
