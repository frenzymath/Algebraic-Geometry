/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ArbitraryLatticeTorsion

/-!
# Finite torsion for an arbitrary lattice quotient

An `IsZLattice` certificate identifies the lattice quotient with its
exponential target, but does not by itself provide a finite `ℤ`-module
presentation of the ambient real vector space.  Once a genus-torus additive
uniformization of the target is supplied, the finite `ZMod` torsion
classification follows by composing the two canonical torsion transports.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

namespace ComplexLatticeExponentialData

/-- Torsion in an arbitrary lattice quotient, classified after a chosen
genus-torus uniformization of the exponential target. -/
def quotientTorsionAddEquiv_of_uniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g)
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0) :
    zsmulTorsionSubgroup
        (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) n ≃+
      (Fin (2 * g) → ZMod n.natAbs) :=
  (d.quotientTorsionAddEquiv n).trans
    (zsmulTorsion_addEquiv_of_uniformization u hn)

@[simp]
theorem quotientTorsionAddEquiv_of_uniformization_apply
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g)
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0)
    (q : zsmulTorsionSubgroup
      (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) n) :
    (d.quotientTorsionAddEquiv_of_uniformization u hn) q =
      (zsmulTorsion_addEquiv_of_uniformization u hn)
        ((d.quotientTorsionAddEquiv n) q) := by
  rfl

/-- The arbitrary-lattice quotient has torsion order `|n| ^ (2*g)` whenever
its target is equipped with a genus-torus uniformization. -/
theorem quotientTorsion_card_of_uniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g)
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0) :
    Nat.card (zsmulTorsionSubgroup
      (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) n) =
      n.natAbs ^ (2 * g) := by
  rw [Nat.card_congr
    (d.quotientTorsionAddEquiv_of_uniformization u hn).toEquiv]
  simp [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]

/-- The arbitrary-lattice torsion cardinality in the usual positive-natural
notation. -/
theorem quotientTorsion_card_of_uniformization_natCast
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g n : ℕ}
    (d : ComplexLatticeExponentialData X g)
    (u : GenusTorusUniformization X g) (hn : 0 < n) :
    Nat.card (zsmulTorsionSubgroup
      (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) (n : ℤ)) =
      n ^ (2 * g) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  simpa using (d.quotientTorsion_card_of_uniformization u hne)

/-- The same hypotheses imply finiteness of every nonzero-integer torsion
subgroup of the arbitrary lattice quotient. -/
theorem quotientTorsion_finite_of_uniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g)
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0) :
    Finite (zsmulTorsionSubgroup
      (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) n) := by
  letI : NeZero n.natAbs := ⟨Int.natAbs_pos.mpr hn |>.ne'⟩
  exact (d.quotientTorsionAddEquiv_of_uniformization u hn).toEquiv.finite_iff.mpr
    (by infer_instance)

end ComplexLatticeExponentialData

end
end Uniformization
end Mumford
