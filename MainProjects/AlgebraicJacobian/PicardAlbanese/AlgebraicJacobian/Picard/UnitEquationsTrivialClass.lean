/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyDegreeZeroGeneral
import AlgebraicJacobian.Picard.FamilyCoboundary

/-!
# A LOCAL-EQUATION SYSTEM OF UNITS PRESENTS THE TRIVIAL PICARD CLASS

`Scheme.LocalEquations.picClass` (`Picard/DivisorClass.lean:238`) is the Čech class of the
cocycle of transition units `g x y = eqn x / eqn y`.  The landed API around it computes the
class *from* a system in every direction except one: **nothing concluded that a class is
trivial**.  The producers of `picClass … = 1` were `picClass_zero` (the zero *divisor*, a
different carrier) and `picClass_eq_of_divEq` (which only transports triviality between two
systems, never establishes it).

This file supplies the missing producer, and it is generic: no curve, no base ring, no
degree, no cohomology.

  **`eqn x` a unit at every point ⟹ `picClass = 1`.**

## The mechanism, and why it is not the obvious `simp`

The defining relation `eqn x = g x y · eqn y` (`eqn_restrict_eq`) says exactly that the family
`α x := (eqn x)⁻¹` is a **coboundary datum** for the transition cocycle, once every `eqn x` is
invertible.  `Scheme.unitsH1_eq_one_of_family` (`Picard/FamilyCoboundary.lean:107`) turns a
coboundary datum on a refining family into triviality of the `H¹` class, and here the refining
family is the cover itself — index type `X`, opens `d.cover.opens`, refinement `le_rfl`.

Two mechanical points:

* the family lemma restricts the cocycle along `inf_le_inf le_rfl le_rfl`, so the proof needs
  "restriction along `U ≤ U` is the identity".  That is `Scheme.resHom_refl` on sections, but a
  `rw` with a `unitsRestrict`-level version **fails to match** — the `le`-witness sits inside a
  proof argument and the rewrite motive is not type-correct at `instances` transparency.  The
  fix is to `have` the identity with the inequality *universally quantified* (`hself` below), so
  unification picks the witness rather than matching it.  **This obstacle is specific to the
  `unitsH1_eq_one_of_family` route chosen here** — an audit (`I-1652`) found the landed
  `picClass_rescale` (`Picard/DivisorClass.lean:450`) reaches the same conclusion in about
  fourteen lines with no motive problem at all, so do not read the note above as an intrinsic
  cost of the statement;
* `Scheme.CechPic.mk_one` supplies the `1` in the class group on the same cover, so the two
  sides are `mk` of the same cover and `congr 1` reduces to the `unitsH1` statement.

## What consumes it, immediately

`Picard/DivisorFamilyDegreeZeroGeneral.lean` proves, over an **arbitrary** test ring, that a
degree-`0` certified adaptation has unit equations
(`isUnit_eqn_of_isCertified_zero`) and is `DivEq` to the trivial system
(`divEq_trivEqns_of_isCertified_zero`).  Until now that chain ended at `DivEq`, i.e. at the
*quotient* carrier `DivFam`, and said nothing about the **class** in `CechPic` — which is the
object the `pic⁰` vanishing is about.  Composing with the theorem here closes that gap:

  **a degree-`0` certified divisor family has trivial Picard class, at every test ring.**

That is `picClass_eq_one_of_isCertified_zero` below, and it needs no field, no integrality, no
smoothness and no Noetherian hypothesis — it inherits exactly the hypotheses of the landed
degree-`0` certificate lemma.

## What this does NOT do

* **It does not prove the `pic⁰` vanishing over a ring.**  The gap that remains there is the
  *converse* production step: given a degree-`0` class on `C_A`, exhibit a certified family
  presenting it.  The field case of that is `exists_divFam_divFamDivisor_eq`
  (`Picard/DivisorFamilyFieldSurj.lean:147`) and it is field-only; over a ring the section
  route (`Picard/DivisorDatumRankOne.lean:248` then
  `Picard/SectionsToDivisorsClass.lean:212`) is the live candidate and is not completed here.
* It says nothing about `picFromBase` membership, which is the `relPic`-level statement and a
  strictly weaker conclusion than `picClass = 1` in `CechPic`.

## Main declarations

* `AlgebraicGeometry.Scheme.LocalEquations.picClass_eq_one_of_isUnit_eqn` — **the keystone**:
  unit equations present the trivial class.  Generic in the scheme.
* `AlgebraicGeometry.DivFamZar.picClass_trivEqns` — the trivial system has trivial class.
* `AlgebraicGeometry.DivisorAdaptation.picClass_eq_one_of_isCertified_zero` — **a degree-`0`
  certified system has trivial class, at every test ring**.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## The keystone, generic in the scheme -/

namespace Scheme.LocalEquations

variable {X : Scheme.{u}}

/-- **A LOCAL-EQUATION SYSTEM OF UNITS PRESENTS THE TRIVIAL CLASS.**

The defining relation `eqn x = g x y · eqn y` says the family `α x := (eqn x)⁻¹` is a
coboundary datum for the transition cocycle; `Scheme.unitsH1_eq_one_of_family` on the cover
itself (index type `X`, refinement `le_rfl`) converts that into triviality of the `H¹` class,
and `CechPic.mk_one` puts the two sides on the same cover.

This is the only producer of `picClass … = 1` in the tree that establishes triviality rather
than transporting it: `picClass_eq_of_divEq` moves it between systems and `picClass_zero` is
about the zero *divisor*, a different carrier. -/
theorem picClass_eq_one_of_isUnit_eqn (d : X.LocalEquations)
    (hu : ∀ x : X, IsUnit (d.eqn x)) : d.picClass = 1 := by
  rw [Scheme.LocalEquations.picClass, show (1 : X.CechPic)
      = Scheme.CechPic.mk d.cover 1 from (Scheme.CechPic.mk_one d.cover).symm]
  congr 1
  refine Scheme.unitsH1_eq_one_of_family d.unitsCocycle (fun x => x) d.cover.opens
    (fun _ => le_rfl) (fun x => ⟨x, d.cover.mem_opens x⟩)
    (fun x => (hu x).unit⁻¹) ?_
  intro x y
  -- Restriction along `U ≤ U` is the identity.  The inequality must stay *quantified*: with a
  -- fixed witness the `rw` motive is not type-correct at `instances` transparency.
  have hself : ∀ (h : d.cover.opens x ⊓ d.cover.opens y ≤ d.cover.opens x ⊓ d.cover.opens y)
      (w : Γ(X, d.cover.opens x ⊓ d.cover.opens y)ˣ), X.unitsRestrict h w = w :=
    fun h w => Units.ext (X.resHom_refl (w : Γ(X, d.cover.opens x ⊓ d.cover.opens y)))
  -- The unit form of `eqn_restrict_eq`: `eqn x = g x y · eqn y` as an identity of units.
  have key : X.unitsRestrict (inf_le_left : d.cover.opens x ⊓ d.cover.opens y ≤ d.cover.opens x)
        (hu x).unit
      = d.ratioUnit x y * X.unitsRestrict
        (inf_le_right : d.cover.opens x ⊓ d.cover.opens y ≤ d.cover.opens y) (hu y).unit :=
    Units.ext (by
      rw [Units.val_mul, Scheme.coe_unitsRestrict, Scheme.coe_unitsRestrict,
        IsUnit.unit_spec, IsUnit.unit_spec]
      exact d.eqn_restrict_eq x y)
  rw [map_inv, map_inv, Scheme.LocalEquations.unitsCocycle_evInf, hself, key]
  group

end Scheme.LocalEquations

/-! ## The degree-`0` consequence, at every test ring -/

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

/-- **The trivial system has trivial Picard class.**  Its equations are literally `1`. -/
theorem DivFamZar.picClass_trivEqns : (DivFamZar.trivEqns C R).picClass = 1 :=
  Scheme.LocalEquations.picClass_eq_one_of_isUnit_eqn _ fun y => by
    rw [DivFamZar.trivEqns_eqn]
    exact isUnit_one

/-- **A DEGREE-`0` CERTIFIED SYSTEM HAS TRIVIAL PICARD CLASS, AT EVERY TEST RING.**

`isUnit_eqn_of_isCertified_zero` (`Picard/DivisorFamilyDegreeZeroGeneral.lean:125`) spends the
degree-`0` rank clause on making every *chart* equation a unit; `eqn_rel` then makes the
system's own equations units on the piece overlaps, which is what
`divEq_trivEqns_of_isCertified_zero` packages as `DivEq` with the trivial system.  Composing
that with `picClass_eq_of_divEq` and the class of the trivial system gives the statement at the
level of `CechPic`, which is where the `pic⁰` vanishing lives — the landed chain stopped at the
`DivFam` quotient.

Hypotheses are exactly the landed lemma's: **no field, no integrality, no smoothness, no
Noetherian ring.** -/
theorem DivisorAdaptation.picClass_eq_one_of_isCertified_zero
    {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R pi d)
    (hc : A.IsCertified 0) : d.picClass = 1 :=
  (Scheme.LocalEquations.picClass_eq_of_divEq
    (A.divEq_trivEqns_of_isCertified_zero hc)).trans DivFamZar.picClass_trivEqns

end AlgebraicGeometry
