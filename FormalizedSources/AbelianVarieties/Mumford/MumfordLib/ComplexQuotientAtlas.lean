/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ComplexVectorLatticeTopology

/-!
# Local branches for the ambient lattice quotient

The lattice quotient projection is a local homeomorphism.  This file names
the local inverse supplied by that fact, retaining the representative used to
choose a branch.  The declarations are purely topological; no smooth or
holomorphic structure is asserted here.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

namespace ComplexVectorLatticeExponentialData

/-- The local inverse branch of the ambient quotient projection at `v`. -/
noncomputable def quotientLocalBranchAt
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    OpenPartialHomeomorph (V ⧸ d.ambientPeriodLattice) V :=
  d.quotient_mk_isLocalHomeomorph.localInverseAt v

/-- The chosen representative belongs to the target of its local branch. -/
@[simp]
theorem quotientLocalBranchAt_mem_target
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    v ∈ (d.quotientLocalBranchAt v).target := by
  simp [quotientLocalBranchAt]

/-- A branch sends the quotient point of its chosen representative back to it. -/
@[simp]
theorem quotientLocalBranchAt_apply_quotient_mk
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.quotientLocalBranchAt v
        ((QuotientAddGroup.mk : V → V ⧸ d.ambientPeriodLattice) v) = v := by
  simp [quotientLocalBranchAt]

/-- The quotient point of the selected representative lies in the branch source. -/
@[simp]
theorem quotientLocalBranchAt_quotient_mk_mem_source
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    (QuotientAddGroup.mk : V → V ⧸ d.ambientPeriodLattice) v ∈
      (d.quotientLocalBranchAt v).source := by
  simp [quotientLocalBranchAt]

/-- The inverse of a local quotient branch is the ambient quotient projection. -/
@[simp]
theorem quotientLocalBranchAt_symm
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    (d.quotientLocalBranchAt v).symm =
      (QuotientAddGroup.mk : V → V ⧸ d.ambientPeriodLattice) := by
  simp [quotientLocalBranchAt]

/-- Projection after a local branch is the identity on the branch source. -/
theorem quotient_mk_apply_quotientLocalBranchAt
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V)
    {q : V ⧸ d.ambientPeriodLattice}
    (hq : q ∈ (d.quotientLocalBranchAt v).source) :
    (QuotientAddGroup.mk : V → V ⧸ d.ambientPeriodLattice)
        (d.quotientLocalBranchAt v q) = q := by
  exact d.quotient_mk_isLocalHomeomorph.apply_localInverseAt_of_mem hq

/- The local inverse branch is continuous on its open source.  Naming this
   restriction keeps later atlas arguments independent of the implementation
   of `localInverseAt`. -/
theorem quotientLocalBranchAt_continuousOn
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    ContinuousOn (d.quotientLocalBranchAt v)
      (d.quotientLocalBranchAt v).source :=
  (d.quotientLocalBranchAt v).continuousOn

/- The inverse branch, viewed on its target, is the quotient projection and is
   therefore continuous there as well. -/
theorem quotientLocalBranchAt_symm_continuousOn
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    ContinuousOn (d.quotientLocalBranchAt v).symm
      (d.quotientLocalBranchAt v).target := by
  rw [d.quotientLocalBranchAt_symm]
  exact QuotientAddGroup.continuous_mk.continuousOn

/-- The local quotient branch covers its entire open target. -/
theorem quotientLocalBranchAt_image_source_eq_target
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.quotientLocalBranchAt v '' (d.quotientLocalBranchAt v).source =
      (d.quotientLocalBranchAt v).target :=
  (d.quotientLocalBranchAt v).image_source_eq_target

end ComplexVectorLatticeExponentialData

end
end Uniformization
end Mumford
