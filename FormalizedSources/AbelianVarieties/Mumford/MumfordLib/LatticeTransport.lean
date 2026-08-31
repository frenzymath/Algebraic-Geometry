/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.Lattice
import MumfordLib.TorsionBridge

/-!
# Transport between period-lattice quotients

An additive equivalence carrying one period subgroup onto another induces an
additive equivalence of the corresponding quotients.  This file keeps that
construction separate from any analytic or topological hypotheses.  A linear
equivalence is accepted through its underlying additive equivalence, and the
same map then transports the integer-torsion subgroups.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

/-- The quotient additive equivalence induced by an additive equivalence of
ambient groups and an explicit equality of the transported subgroups. -/
def periodLatticeQuotientAddEquivOfAddEquiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (L : AddSubgroup G) (M : AddSubgroup H)
    (e : G ≃+ H)
    (he : AddSubgroup.map (e : G →+ H) L = M) :
    G ⧸ L ≃+ H ⧸ M :=
  QuotientAddGroup.congr L M e he

@[simp]
theorem periodLatticeQuotientAddEquivOfAddEquiv_mk
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (L : AddSubgroup G) (M : AddSubgroup H)
    (e : G ≃+ H)
    (he : AddSubgroup.map (e : G →+ H) L = M) (x : G) :
    periodLatticeQuotientAddEquivOfAddEquiv L M e he
        (QuotientAddGroup.mk' L x) =
      QuotientAddGroup.mk' M (e x) := by
  change QuotientAddGroup.congr L M e he
      (QuotientAddGroup.mk' L x) = _
  rfl

@[simp]
theorem periodLatticeQuotientAddEquivOfAddEquiv_symm_mk
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (L : AddSubgroup G) (M : AddSubgroup H)
    (e : G ≃+ H)
    (he : AddSubgroup.map (e : G →+ H) L = M) (y : H) :
    (periodLatticeQuotientAddEquivOfAddEquiv L M e he).symm
        (QuotientAddGroup.mk' M y) =
      QuotientAddGroup.mk' L (e.symm y) := by
  change (QuotientAddGroup.congr L M e he).symm
      (QuotientAddGroup.mk' M y) = _
  rfl

/-- The quotient additive equivalence induced by a linear equivalence and an
explicit equality of the transported period subgroups. -/
def periodLatticeQuotientAddEquivOfLinearEquiv
    {R G H : Type*} [Semiring R]
    [AddCommGroup G] [AddCommGroup H] [Module R G] [Module R H]
    (L : AddSubgroup G) (M : AddSubgroup H)
    (e : G ≃ₗ[R] H)
    (he : AddSubgroup.map (e.toAddEquiv : G →+ H) L = M) :
    G ⧸ L ≃+ H ⧸ M :=
  periodLatticeQuotientAddEquivOfAddEquiv L M e.toAddEquiv he

@[simp]
theorem periodLatticeQuotientAddEquivOfLinearEquiv_mk
    {R G H : Type*} [Semiring R]
    [AddCommGroup G] [AddCommGroup H] [Module R G] [Module R H]
    (L : AddSubgroup G) (M : AddSubgroup H)
    (e : G ≃ₗ[R] H)
    (he : AddSubgroup.map (e.toAddEquiv : G →+ H) L = M) (x : G) :
    periodLatticeQuotientAddEquivOfLinearEquiv L M e he
        (QuotientAddGroup.mk' L x) =
      QuotientAddGroup.mk' M (e x) := by
  exact periodLatticeQuotientAddEquivOfAddEquiv_mk L M e.toAddEquiv he x

@[simp]
theorem periodLatticeQuotientAddEquivOfLinearEquiv_symm_mk
    {R G H : Type*} [Semiring R]
    [AddCommGroup G] [AddCommGroup H] [Module R G] [Module R H]
    (L : AddSubgroup G) (M : AddSubgroup H)
    (e : G ≃ₗ[R] H)
    (he : AddSubgroup.map (e.toAddEquiv : G →+ H) L = M) (y : H) :
    (periodLatticeQuotientAddEquivOfLinearEquiv L M e he).symm
        (QuotientAddGroup.mk' M y) =
      QuotientAddGroup.mk' L (e.symm y) := by
  exact periodLatticeQuotientAddEquivOfAddEquiv_symm_mk L M e.toAddEquiv he y

/-- Integer torsion in two quotient groups is transported by the induced
quotient equivalence. -/
def periodLatticeQuotientTorsionAddEquivOfAddEquiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (L : AddSubgroup G) (M : AddSubgroup H)
    (e : G ≃+ H)
    (he : AddSubgroup.map (e : G →+ H) L = M) (n : ℤ) :
    zsmulTorsionSubgroup (G ⧸ L) n ≃+
      zsmulTorsionSubgroup (H ⧸ M) n :=
  zsmulTorsion_addEquiv_of_addEquiv
    (periodLatticeQuotientAddEquivOfAddEquiv L M e he) n

@[simp]
theorem periodLatticeQuotientTorsionAddEquivOfAddEquiv_apply
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (L : AddSubgroup G) (M : AddSubgroup H)
    (e : G ≃+ H)
    (he : AddSubgroup.map (e : G →+ H) L = M) (n : ℤ)
    (q : zsmulTorsionSubgroup (G ⧸ L) n) :
    ((periodLatticeQuotientTorsionAddEquivOfAddEquiv L M e he n) q : H ⧸ M) =
      periodLatticeQuotientAddEquivOfAddEquiv L M e he (q : G ⧸ L) := by
  rfl

/-- The torsion transport associated to a linear equivalence of ambient groups. -/
def periodLatticeQuotientTorsionAddEquivOfLinearEquiv
    {R G H : Type*} [Semiring R]
    [AddCommGroup G] [AddCommGroup H] [Module R G] [Module R H]
    (L : AddSubgroup G) (M : AddSubgroup H)
    (e : G ≃ₗ[R] H)
    (he : AddSubgroup.map (e.toAddEquiv : G →+ H) L = M) (n : ℤ) :
    zsmulTorsionSubgroup (G ⧸ L) n ≃+
      zsmulTorsionSubgroup (H ⧸ M) n :=
  periodLatticeQuotientTorsionAddEquivOfAddEquiv L M e.toAddEquiv he n

@[simp]
theorem periodLatticeQuotientTorsionAddEquivOfLinearEquiv_apply
    {R G H : Type*} [Semiring R]
    [AddCommGroup G] [AddCommGroup H] [Module R G] [Module R H]
    (L : AddSubgroup G) (M : AddSubgroup H)
    (e : G ≃ₗ[R] H)
    (he : AddSubgroup.map (e.toAddEquiv : G →+ H) L = M) (n : ℤ)
    (q : zsmulTorsionSubgroup (G ⧸ L) n) :
    ((periodLatticeQuotientTorsionAddEquivOfLinearEquiv L M e he n) q : H ⧸ M) =
      periodLatticeQuotientAddEquivOfLinearEquiv L M e he (q : G ⧸ L) := by
  rfl

end
end Uniformization
end Mumford
