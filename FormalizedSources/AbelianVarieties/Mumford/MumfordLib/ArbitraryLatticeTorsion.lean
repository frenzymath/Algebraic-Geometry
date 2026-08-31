/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ComplexLattice
import MumfordLib.TorsionBridge

/-!
# Torsion for arbitrary complex period lattices

The explicit `ZMod` coordinate formula is available for the rectangular
period lattice.  For an arbitrary full lattice, the analytic certificate still
gives a canonical torsion identification with the target, and the quotient
representative criterion below isolates the remaining finite-basis step.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

namespace ComplexLatticeExponentialData

/-- A quotient representative is killed by an integer exactly when its scalar
multiple lies in the arbitrary period lattice. -/
theorem quotient_mk_mem_zsmulTorsion_iff
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) (n : ℤ)
    (z : GenusComplexVector g) :
    QuotientAddGroup.mk' d.periodLattice.toAddSubgroup z ∈
        zsmulTorsionSubgroup
          (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) n ↔
      n • z ∈ d.periodLattice := by
  simpa only [Submodule.mem_toAddSubgroup] using
    (PeriodLatticeQuotient.quotient_mk_mem_zsmulTorsion_iff
      d.periodLattice.toAddSubgroup n z)

/-- Torsion in an arbitrary period quotient transports canonically to torsion
in the target of its exponential. -/
def quotientTorsionAddEquiv
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) (n : ℤ) :
    zsmulTorsionSubgroup
        (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) n ≃+
      zsmulTorsionSubgroup X n :=
  zsmulTorsion_addEquiv_of_addEquiv d.quotientAddEquiv n

@[simp]
theorem quotientTorsionAddEquiv_apply
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) (n : ℤ)
    (q : zsmulTorsionSubgroup
      (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) n) :
    ((d.quotientTorsionAddEquiv n) q : X) =
      d.quotientAddEquiv (q : GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) := by
  rfl

/-- The arbitrary-lattice quotient and the exponential target have equal
integer-torsion cardinalities. -/
theorem quotientTorsion_card_eq_target
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) (n : ℤ) :
    Nat.card (zsmulTorsionSubgroup
      (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) n) =
      Nat.card (zsmulTorsionSubgroup X n) := by
  exact zsmulTorsion_card_eq_of_addEquiv d.quotientAddEquiv n

/-- Finiteness of integer torsion is equivalent across the arbitrary-lattice
quotient and the target of its exponential. -/
theorem quotientTorsion_finite_iff_target
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) (n : ℤ) :
    Finite (zsmulTorsionSubgroup
      (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) n) ↔
      Finite (zsmulTorsionSubgroup X n) := by
  exact zsmulTorsion_finite_iff_of_addEquiv d.quotientAddEquiv n

end ComplexLatticeExponentialData

end
end Uniformization
end Mumford
