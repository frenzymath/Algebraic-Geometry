/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyDegreeZero
import AlgebraicJacobian.Picard.DivisorFamilyZariskiSep

/-!
# THE DEGREE-ZERO DIVISOR VALUE IS A SINGLETON OVER **EVERY** TEST RING

`Picard/DivisorFamilyDegreeZeroUnique.lean` proves `Subsingleton (DivFamZar C K π 0)` for a
**field** `K`, and its own docstring records the boundary:

> Whether `DivFamZar C R π 0` is a subsingleton for a general `R` is **open and not measured
> here**; the inhabitation half of the previous file holds for every `R`, the uniqueness half
> does not transfer, and I do not claim it does.

This file closes that gap, and the argument needs **no** field: it does not mention
`presentationDivisor`, effectivity, `divEq_of_presentationDivisor_eq` or
`DivFam.exists_toZar_eq`, the four ingredients that made the field proof field-local.

## The argument

The certificate's rank clause is read *backwards*.  `Glued` is the equalizer
`ker (deltaLeft - deltaRight)` inside `chartProd = Π j, Γ(pieces j) ⧸ (eqn j)`, and the
**constant family** `1` always lies in it — both overlap maps are algebra maps, so both send
`1` to `1`.  At degree `0` the certificate says `rankAtStalk Glued = 0` with `Glued` finite
projective, so `Module.rankAtStalk_eq_zero_iff_subsingleton` makes `Glued` a subsingleton;
hence that constant family is `0`, i.e. `1 = 0` in every `colength j`, i.e.
`Ideal.span {eqn j} = ⊤`, i.e. **every chart equation is a unit**
(`Ideal.span_singleton_eq_top`).

A system whose adaptation has unit equations is divisor-equal to the trivial one: `eqn_rel`
compares `eqn j` with `d.eqn y` up to a unit on `pieces j ⊓ d.cover.opens y`, and a unit times
a unit is a unit, so each `d.eqn y` is a unit *on the part of its member covered by a piece*.
The pieces cover the relative curve (`FinCoverData.cover₀`/`cover₁` and `relCover_sup`), so
that is a cover of `d.cover.opens y`, and `DivEq` only asks for a **common refinement** on
which the equations agree up to units — which the pieces provide.

So the whole degree-`0` uniqueness is a statement about the *unit ideal*, not about divisors,
and it is available over any commutative ring.

## Main declarations

* `AlgebraicGeometry.DivisorAdaptation.isUnit_eqn_of_isCertified_zero` — **the unit
  extraction**: a degree-`0` certificate forces every chart equation to be a unit.
* `AlgebraicGeometry.DivisorAdaptation.divEq_trivEqns_of_isCertified_zero` — hence the system
  is divisor-equal to the trivial one.
* `AlgebraicGeometry.instSubsingletonDivFamZeroGeneral` — `Subsingleton (DivFam C R π 0)` for
  **every** `R`: the globally certified quotient, since `divFamSetoid` is `DivEq`.

Two declarations an earlier draft of this list advertised **live in
`Picard/DivisorFamilyDegreeZeroRep.lean`, not here**, and the list said otherwise:
`instSubsingletonDivFamZarZeroGeneral` (the *locally* certified carrier `DivFamZar`, which
needs the Zariski descent of `DivEq` along the localization immersions) and
`DivFamZar.uniqueZero`.  That draft also named `instSubsingletonDivFamZeroGeneral` while **no
such declaration existed anywhere** — the `cited-names-need-check-not-grep` failure, in the
list a reader hits first.  It is landed above now rather than struck from the list, because the
statement was the right one to make: the chain ends on `DivEq`, which is the relation *both*
quotients use, so the globally certified carrier costs three lines.

## Relation to the field file

`instSubsingletonDivFamZero` (field) is **subsumed**, not merely paralleled: this file's
instance applies at `R := K`.  The field file is kept because its route through the
presentation divisor is the one the degree ledger consumes elsewhere, and because its
statement is the one already cited in the tree.

**And "needs `Field K` twice" understates what is dropped.**  Comparing the two signatures:
`instSubsingletonDivFamZero` binds `{K} [Field K] [Algebra k K]` *and four `relCurve C K`
geometry instances* — `IsIntegral`, `SmoothOfRelativeDimension 1`, `QuasiCompact`,
`LocallyOfFiniteType` — while the instance above binds `[CommRing R] [Algebra k R]` and nothing
else.  Those four are the part a general-test consumer cannot supply at all, so they, not the
field, are the real barrier the unit argument removes.  `Field k` (the *base* field) is in both
signatures and is not dropped by anything here.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

noncomputable section

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R pi d)

/-! ## The constant family lies in the glued equalizer -/

/-- **`1` is always a glued section.**  The two arrows of the equalizer are induced by
*algebra* maps `colength → ovlColength`, so both send the constant family `1` to `1`.  No
hypothesis on the equations, the degree, or the ring. -/
theorem one_mem_gluedSubmodule : (1 : A.chartProd) ∈ A.gluedSubmodule := by
  rw [A.mem_gluedSubmodule_iff]
  intro p
  change A.toOvlLeft p.1 p.2 1 = A.toOvlRight p.1 p.2 1
  rw [map_one, map_one]

/-! ## The unit extraction -/

/-- **A degree-`0` certificate forces every chart equation to be a unit.**

The rank clause read backwards: `Glued` is finite projective of rank `0` at every prime, so
it is a subsingleton (`Module.rankAtStalk_eq_zero_iff_subsingleton`); the constant family `1`
lies in it (`one_mem_gluedSubmodule`); therefore `1 = 0` in each `colength j`, i.e. the ideal
generated by `eqn j` is everything.

This is where degree `0` is spent, and it is spent on *nothing else* — no field, no
integrality, no smoothness, no divisor theory. -/
theorem isUnit_eqn_of_isCertified_zero (hc : A.IsCertified 0) (j : A.index) :
    IsUnit (A.eqn j) := by
  haveI := hc.finite_glued
  haveI := hc.projective_glued
  haveI : Module.Flat R A.Glued := Module.Flat.of_projective
  haveI : Subsingleton A.Glued :=
    Module.rankAtStalk_eq_zero_iff_subsingleton.mp (funext fun p => hc.rankAtStalk_glued p)
  -- the constant family, as an element of `Glued`, is `0`
  have h0 : (⟨(1 : A.chartProd), A.one_mem_gluedSubmodule⟩ : A.Glued) = 0 :=
    Subsingleton.elim _ _
  have hj : (1 : A.colength j) = 0 := congrFun (congrArg Subtype.val h0) j
  rw [← Ideal.span_singleton_eq_top (x := A.eqn j), Ideal.eq_top_iff_one]
  have hmk : Ideal.Quotient.mk (Ideal.span {A.eqn j}) 1 = 0 := hj
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmk

/-! ## From unit equations to divisor equality with the trivial system -/

/-- **A degree-`0` certified system is divisor-equal to the trivial one.**

The common refinement is the *piece* cover: at each point `y` pick a piece containing it
(`FinCoverData.exists_mem_pieces`) and intersect with `d.cover.opens y`.  On that open,
`eqn_rel` says `eqn j = u · d.eqn y` with `u` a unit, and `isUnit_eqn_of_isCertified_zero`
says `eqn j` is a unit, so `d.eqn y` is a unit there — and `trivEqns` carries the section
`1`, so the comparison unit is `(d.eqn y)⁻¹`.

Note what does *not* appear: no degree of a divisor, no effectivity, no field.  The
`Subsingleton` results below are corollaries of this one. -/
theorem divEq_trivEqns_of_isCertified_zero (hc : A.IsCertified 0) :
    Scheme.LocalEquations.DivEq d (DivFamZar.trivEqns C R) := by
  classical
  choose piece hpiece using A.toFinCoverData.exists_mem_pieces
  refine ⟨⟨fun y => A.pieces (piece y) ⊓ d.cover.opens y,
      fun y => ⟨hpiece y, d.cover.mem_opens y⟩⟩,
    fun y => inf_le_right, fun y => le_top, fun y => ?_⟩
  -- `d.eqn y` restricted to the piece overlap is a unit
  obtain ⟨u, hu⟩ := A.eqn_rel (piece y) y
  have hL : IsUnit (((relCurve C R).presheaf.map (homOfLE
      (inf_le_left : A.pieces (piece y) ⊓ d.cover.opens y
        ≤ A.pieces (piece y))).op).hom (A.eqn (piece y))) :=
    (A.isUnit_eqn_of_isCertified_zero hc (piece y)).map _
  rw [hu] at hL
  have hunit : IsUnit (((relCurve C R).presheaf.map (homOfLE
      (inf_le_right : A.pieces (piece y) ⊓ d.cover.opens y
        ≤ d.cover.opens y)).op).hom (d.eqn y)) :=
    isUnit_of_mul_isUnit_right hL
  -- and the trivial system's equation is `1`, so that unit *is* the comparison unit
  refine ⟨hunit.unit, ?_⟩
  rw [DivFamZar.trivEqns_eqn, map_one, mul_one]
  exact hunit.unit_spec.symm

end DivisorAdaptation

/-! ## The globally certified quotient, at every test ring

The chain above lands on `DivEq`, which is the relation *both* quotients are taken by, so the
globally certified carrier follows in three lines — and it must be stated, because an earlier
draft of this file's `Main declarations` list advertised it while the file only proved the
locally certified version. -/

/-- **`DivFam C R π 0` is a subsingleton at EVERY test ring**, dropping the `Field K` *and* the
four `relCurve C K` geometry instances (`IsIntegral`, `SmoothOfRelativeDimension 1`,
`QuasiCompact`, `LocallyOfFiniteType`) that `instSubsingletonDivFamZero`
(`Picard/DivisorFamilyDegreeZeroUnique.lean`) carries.

`divFamSetoid` relates two certified families exactly when their systems are `DivEq`, and
`divEq_trivEqns_of_isCertified_zero` says every degree-`0` system is `DivEq` to the same
trivial one. -/
instance instSubsingletonDivFamZeroGeneral : Subsingleton (DivFam C R pi 0) := by
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.ind with | _ F =>
  induction y using Quotient.ind with | _ G =>
  exact Quotient.sound
    ((F.adaptation.divEq_trivEqns_of_isCertified_zero F.certified).trans
      (G.adaptation.divEq_trivEqns_of_isCertified_zero G.certified).symm)

end

end AlgebraicGeometry
