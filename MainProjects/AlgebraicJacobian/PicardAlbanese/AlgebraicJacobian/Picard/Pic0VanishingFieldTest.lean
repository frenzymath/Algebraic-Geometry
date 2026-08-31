/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0VanishingFieldGenusZero
import AlgebraicJacobian.Picard.Pic0VanishingAffineReduction
import AlgebraicJacobian.Curve.P1H1Vanishing

/-!
# `pic⁰` VANISHES AT EVERY FIELD TEST, AT GENUS `0`

`Picard/Pic0VanishingAffineReduction.lean` proved the `∀ T` binder of the degree-zero Picard
vanishing is *equivalent* to the same statement at affine tests `overSpec k A`.  This file
discharges every **field** instance of that: at `genus C = 0`,

  `Subsingleton (pic0Subgroup C (overSpec k K))` for every field extension `K/k`.

`hvan` is the hypothesis that `Pic0VanishingRoute.jacobianData_of_subsingleton` turns into a
`JacobianData` and that `Pic0ChartSeamPairDecided.isLocallySurjective_abelSigmaChartZero_iff`
shows *is* the seam's coverage antecedent at parameter `0`.  It therefore now has all of its
field instances closed on a genus-`0` curve, and only its **ring** instances open.

**A COUNT CORRECTED.**  An earlier version of this paragraph called `hvan` "the hypothesis with
93 consumers and no producer".  That figure is from the task brief and is about
`JacobianData.rep`, a *different* object; restating it here made it look like a measurement of
`hvan`.  Measured at HEAD: the `hvan`-shaped binder occurs in **3** files, `pic0Subgroup` is
mentioned in 50, and `RepresentableBy` occurs 392 times.  What matters about `hvan` is not a
count but that both live routes to a `rep` producer pass through it and neither had an
instance; do not quote a number from this header — run the grep.

## The two steps, and what each costs

**Step 1, through the plus construction** (`eq_one_of_degAff_eq_zero_of_genus_zero`).  A plus
class of `PicEtAff C K` is `mk E x` for some étale cover `E` of `K`; its degree is by
definition read on a finite separable *field* refinement of `E`
(`PicEtAff.degAff_mk`), and `Pic0VanishingFieldGenusZero` kills the transported class there.
Transport back is free: `PicEtAff.mk_descentMap` says the plus class does not change along a
refinement, and `PicEtAff.mk_one` closes it.

Note what is *not* needed: **no surjectivity of the plus unit**.  The landed
`PicEtAff.unit_surjective_of_section` (`EffectivityClose.lean:141`) requires a curve section
over the test field, which this project constructs nowhere; the argument here never asks
whether the class comes from `relPic C (overSpec k K)` itself, only what happens on its own
cover carrier.  So the field case needs no rational point.

**Step 2, off the degree condition** (`subsingleton_pic0Subgroup_overSpec_field_of_genus_zero`).
Membership in `pic0Subgroup` quantifies over *all* field points of the test; at an affine test
over a field, the identity `𝟙 (overSpec k K)` is one of them, and `degAt` at the identity is
`degAff` of the class by `picEtMap_id`.  So a single instantiation of the membership binder
supplies the hypothesis of step 1 — the other field points are not consulted.

## What remains, stated exactly

  `∀ (A : Type u) [CommRing A] [Algebra k A], Subsingleton (pic0Subgroup C (overSpec k A))`

for `A` **not** a field.  That is fibrewise-degree-zero implies globally trivial over a base
ring, i.e. cohomology and base change; nothing in this tree proves it, and it is the whole
remaining distance from here to a `JacobianData` at a genus-`0` curve via
`jacobianData_of_overSpec_subsingleton`.

Two things this does **not** do, to forestall the obvious misreadings:

* it does not compute `Pic(ℙ¹)` or any Picard group — degree-zero classes are killed without
  identifying the group they sit in;
* it says nothing at positive genus, and exhibits no positive-genus curve.

## Main declarations

* `AlgebraicGeometry.eq_one_of_degAff_eq_zero_of_genus_zero` — a plus class of degree `0` over
  a field test is trivial, at genus `0`.  Needs no curve section.
* `AlgebraicGeometry.subsingleton_pic0Subgroup_overSpec_field_of_genus_zero` — **the field-test
  vanishing**.
* `AlgebraicGeometry.P1.subsingleton_pic0Subgroup_overSpec_field` — **non-vacuity at a real
  curve**: the same at `P1.asOver k` with *no hypothesis at all*, since
  `Curve/P1H1Vanishing.lean` supplies `genus (P1.asOver k) = 0` over an arbitrary field.

Both are stated with **three** curve binders: `GeometricallyReduced` is unused in each
(measured — the linter reports it), even though the surrounding `picEt` descent material
carries four.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

-- Carries the base-change instance stack of the field layer through the plus quotient's
-- cover-refinement calculus; within the DAT-2/PicEtMap precedent.
omit [GeometricallyReduced C.hom] in
/-- **A plus class of degree zero over a field test is trivial, at genus `0`.**

`degAff` is *defined* by reading the relative degree on a finite separable field refinement of
the class's own cover (`PicEtAff.degAff_mk`), which is exactly where the field layer
`relPic_eq_one_of_relPicDeg_eq_zero_of_genus_zero` applies.  Transport back to the original
cover is free — `PicEtAff.mk_descentMap` — so no comparison between covers is needed.

**No curve section over `K` is required**, and hence no rational point: the landed plus-unit
surjectivity `PicEtAff.unit_surjective_of_section` is not used, because the argument works on
the representative's own cover carrier rather than asking the class to come from `relPic`. -/
theorem eq_one_of_degAff_eq_zero_of_genus_zero
    (K : Type u) [Field K] [Algebra k K] (hg : genus C = 0)
    (q : PicEtAff C K) (hq : PicEtAff.degAff (C := C) K q = 0) : q = 1 := by
  induction q using PicEtAff.ind with
  | mk E x =>
    obtain ⟨L, hLf, hLa, hLfin, hLsep, ⟨j⟩⟩ := E.exists_finiteSeparableField_algHom
    letI := hLf; letI := hLa; letI := hLfin; letI := hLsep
    letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    -- the degree is the relative degree of the transported representative over `L`
    have hdeg : relPicDeg (C := C) L (relPicAlgMap C (j.restrictScalars k)
        (x : relPic C (overSpec k E.Carrier))) = 0 := by
      rw [← PicEtAff.degAff_mk (C := C) (K := K) E x L j]
      exact hq
    have htriv : relPicAlgMap C (j.restrictScalars k)
        (x : relPic C (overSpec k E.Carrier)) = 1 :=
      relPic_eq_one_of_relPicDeg_eq_zero_of_genus_zero C L hg _ hdeg
    -- transport to the field cover does not change the plus class
    have hstep : PicEtAff.mk C (Algebra.EtaleCover.ofField (K := K) L)
        (descentMap C ((Algebra.EtaleCover.ofFieldEquiv (K := K) L).symm.toAlgHom.comp j) x)
        = PicEtAff.mk C E x := PicEtAff.mk_descentMap C _ x
    rw [← hstep]
    convert PicEtAff.mk_one C (Algebra.EtaleCover.ofField (K := K) L) using 2
    refine Subtype.ext ?_
    rw [descentMap_coe]
    have hcomp :
        ((Algebra.EtaleCover.ofFieldEquiv (K := K) L).symm.toAlgHom.comp j).restrictScalars k
          = ((Algebra.EtaleCover.ofFieldEquiv (K := K) L).symm.toAlgHom.restrictScalars k).comp
            (j.restrictScalars k) := rfl
    rw [hcomp, relPicAlgMap_comp, htriv, map_one]
    rfl

-- Same instance stack, plus the affine comparison.
omit [GeometricallyReduced C.hom] in
/-- **THE FIELD-TEST VANISHING**: at `genus C = 0`, the degree-zero Picard group of the curve
vanishes at every affine test over a *field*.

Only **one** field point of the test is consulted — the identity `𝟙 (overSpec k K)`, at which
`degAt` is `degAff` of the class by `picEtMap_id`.  So the `∀ K, ∀ t` binder of
`pic0Subgroup`'s membership is used at a single instantiation, and the remaining field points
carry no weight in this direction. -/
theorem subsingleton_pic0Subgroup_overSpec_field_of_genus_zero
    (K : Type u) [Field K] [Algebra k K] (hg : genus C = 0) :
    Subsingleton (pic0Subgroup C (overSpec k K)) := by
  refine ⟨fun s t => Subtype.ext ?_⟩
  refine (picEtAffineEquiv C K).injective ?_
  have hs : PicEtAff.degAff (C := C) K (picEtAffineEquiv C K s.1) = 0 := by
    have h := s.2 K (𝟙 (overSpec k K))
    rwa [degAt, picEtMap_id] at h
  have ht : PicEtAff.degAff (C := C) K (picEtAffineEquiv C K t.1) = 0 := by
    have h := t.2 K (𝟙 (overSpec k K))
    rwa [degAt, picEtMap_id] at h
  have h1 := eq_one_of_degAff_eq_zero_of_genus_zero C K hg (picEtAffineEquiv C K s.1) hs
  have h2 := eq_one_of_degAff_eq_zero_of_genus_zero C K hg (picEtAffineEquiv C K t.1) ht
  exact h1.trans h2.symm

/-! ## Non-vacuity: the statement fires at a curve, unconditionally -/

/-- **The field-test vanishing at `ℙ¹`, with no hypothesis.**

`Curve/P1Curve.lean` gives `P1.asOver k` the three curve binders over an arbitrary field and
`Curve/P1H1Vanishing.lean` gives `genus (P1.asOver k) = 0`, so the theorem above applies with
nothing left to discharge.  Recorded because a conditional statement whose antecedent has no
witness is worth exactly nothing, and this one has one. -/
theorem P1.subsingleton_pic0Subgroup_overSpec_field
    (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K] :
    Subsingleton (pic0Subgroup (P1.asOver k) (overSpec k K)) :=
  subsingleton_pic0Subgroup_overSpec_field_of_genus_zero (P1.asOver k) K
    (P1.genus_asOver_eq_zero k)

end AlgebraicGeometry
