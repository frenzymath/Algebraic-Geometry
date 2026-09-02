/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.DivisionFiber

/-!
# Transport of integer-division fibres

An additive equivalence carries the fibre of multiplication by an integer to
the corresponding fibre in the target.  This is independent of divisibility:
the equivalence transports empty fibres as well as inhabited ones.  The
construction is useful when changing coordinates on a period quotient, while
the cardinality and finiteness corollaries avoid repeating the subtype
argument at each use site.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

/-- An additive equivalence transports a `zsmul` division fibre to the fibre
over the transported target point. -/
def zsmulDivisionFiberEquivOfAddEquiv
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) (x : X) :
    zsmulDivisionFiber X n x ≃ zsmulDivisionFiber Y n (e x) := by
  exact e.toEquiv.subtypeEquiv (fun y => by
    change (n • (y : X) = x) ↔ n • e (y : X) = e x
    constructor
    · intro hy
      have h := congrArg e hy
      simpa only [map_zsmul] using h
    · intro hy
      apply e.injective
      simpa only [map_zsmul] using hy)

@[simp]
theorem zsmulDivisionFiberEquivOfAddEquiv_apply
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) (x : X)
    (a : zsmulDivisionFiber X n x) :
    ((zsmulDivisionFiberEquivOfAddEquiv e n x) a : Y) = e (a : X) := by
  rfl

@[simp]
theorem zsmulDivisionFiberEquivOfAddEquiv_symm_apply
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) (x : X)
    (b : zsmulDivisionFiber Y n (e x)) :
    ((zsmulDivisionFiberEquivOfAddEquiv e n x).symm b : X) =
      e.symm (b : Y) := by
  rfl

/-- Fibre transport is compatible with composition of additive equivalences. -/
theorem zsmulDivisionFiberEquivOfAddEquiv_trans
    {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (e : X ≃+ Y) (f : Y ≃+ Z) (n : ℤ) (x : X) :
    (zsmulDivisionFiberEquivOfAddEquiv e n x).trans
        (zsmulDivisionFiberEquivOfAddEquiv f n (e x)) =
      zsmulDivisionFiberEquivOfAddEquiv (e.trans f) n x := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  rfl

@[simp]
theorem zsmulDivisionFiberEquivOfAddEquiv_refl
    {X : Type*} [AddCommGroup X] (n : ℤ) (x : X) :
    zsmulDivisionFiberEquivOfAddEquiv (AddEquiv.refl X) n x =
      Equiv.refl _ := by
  apply Equiv.ext
  intro a
  rfl

/-- Additive-equivalence transport preserves the cardinality of a division
fibre. -/
theorem zsmulDivisionFiber_card_eq_of_addEquiv
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) (x : X) :
    Nat.card (zsmulDivisionFiber X n x) =
      Nat.card (zsmulDivisionFiber Y n (e x)) := by
  exact Nat.card_congr (zsmulDivisionFiberEquivOfAddEquiv e n x)

/-- Finiteness of a division fibre is invariant under additive-equivalence
transport. -/
theorem zsmulDivisionFiber_finite_iff_of_addEquiv
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) (x : X) :
    Finite (zsmulDivisionFiber X n x) ↔
      Finite (zsmulDivisionFiber Y n (e x)) :=
  (zsmulDivisionFiberEquivOfAddEquiv e n x).finite_iff

end
end Uniformization
end Mumford
