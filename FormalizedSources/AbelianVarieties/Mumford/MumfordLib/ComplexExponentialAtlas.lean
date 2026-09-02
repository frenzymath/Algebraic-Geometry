/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ComplexQuotientAtlas

/-!
# Local exponential branches

The quotient atlas gives local inverses of the ambient quotient projection.  We
transport these branches across the quotient homeomorphism to obtain local
inverse branches of the exponential itself.  All assertions here are
topological and additive; no holomorphic structure is used.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

namespace ComplexVectorLatticeExponentialData

/-- The local inverse branch of the exponential at a chosen representative. -/
noncomputable def exponentialBranch
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    OpenPartialHomeomorph X V :=
  d.quotientHomeomorph.symm.toOpenPartialHomeomorph.trans
    (d.quotientLocalBranchAt v)

@[simp]
theorem exponential_source_mem
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.exponential v ∈ (d.exponentialBranch v).source := by
  rw [exponentialBranch, OpenPartialHomeomorph.trans_source]
  constructor
  · simp
  · rw [Set.mem_preimage]
    change d.quotientHomeomorph.symm (d.exponential v) ∈
      (d.quotientLocalBranchAt v).source
    rw [d.quotientHomeomorph_symm_exponential]
    exact d.quotientLocalBranchAt_quotient_mk_mem_source v

/-- The source of a transported branch is the inverse image of the quotient
    branch source under the quotient homeomorphism. -/
theorem exponentialBranch_source_eq_preimage
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    (d.exponentialBranch v).source =
      d.quotientHomeomorph.symm ⁻¹' (d.quotientLocalBranchAt v).source := by
  rw [exponentialBranch, OpenPartialHomeomorph.trans_source]
  simp

@[simp]
theorem exponential_apply_exponential
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.exponentialBranch v (d.exponential v) = v := by
  rw [exponentialBranch, OpenPartialHomeomorph.trans_apply]
  change d.quotientLocalBranchAt v
    (d.quotientHomeomorph.symm (d.exponential v)) = v
  rw [d.quotientHomeomorph_symm_exponential]
  exact d.quotientLocalBranchAt_apply_quotient_mk v

/-- The target of a transported branch is the target of the quotient branch. -/
theorem exponentialBranch_target_eq_quotientLocalBranchAt_target
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    (d.exponentialBranch v).target =
      (d.quotientLocalBranchAt v).target := by
  rw [exponentialBranch, OpenPartialHomeomorph.trans_target]
  simp

/-- The selected representative belongs to the target of its exponential
    branch. -/
theorem exponentialBranch_mem_target
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    v ∈ (d.exponentialBranch v).target := by
  have h := (d.exponentialBranch v).map_source
    (d.exponential_source_mem v)
  simpa using h

/-- The transported branch covers its open target. -/
theorem exponentialBranch_image_source_eq_target
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.exponentialBranch v '' (d.exponentialBranch v).source =
      (d.exponentialBranch v).target :=
  (d.exponentialBranch v).image_source_eq_target

/-- On a branch target, the inverse branch recovers the original exponential. -/
theorem exponential_symm_apply_eq_exponential
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V)
    {y : V} (hy : y ∈ (d.exponentialBranch v).target) :
    (d.exponentialBranch v).symm y = d.exponential y := by
  have hy' : y ∈ (d.quotientLocalBranchAt v).target := by
    rw [exponentialBranch, OpenPartialHomeomorph.trans_target] at hy
    exact hy.1
  rw [exponentialBranch]
  change d.quotientHomeomorph
      ((d.quotientLocalBranchAt v).symm y) = d.exponential y
  have hsource : (d.quotientLocalBranchAt v).symm y ∈
      (d.quotientLocalBranchAt v).source :=
    (d.quotientLocalBranchAt v).map_target hy'
  have hmk : (QuotientAddGroup.mk : V → V ⧸ d.ambientPeriodLattice) y =
      (d.quotientLocalBranchAt v).symm y := by
    rw [← d.quotient_mk_apply_quotientLocalBranchAt v hsource]
    rw [(d.quotientLocalBranchAt v).right_inv hy']
  rw [← hmk]
  change d.quotientHomeomorph
      (QuotientAddGroup.mk' d.ambientPeriodLattice y) = d.exponential y
  rw [d.quotientHomeomorph_mk]

/-- Applying the exponential after a branch returns the original source point. -/
theorem exponential_apply_exponential_apply
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V)
    {x : X} (hx : x ∈ (d.exponentialBranch v).source) :
    d.exponential ((d.exponentialBranch v) x) = x := by
  have hxt : (d.exponentialBranch v) x ∈ (d.exponentialBranch v).target :=
    (d.exponentialBranch v).map_source hx
  rw [← d.exponential_symm_apply_eq_exponential v hxt]
  exact (d.exponentialBranch v).left_inv hx

/- The transported branch and its inverse are continuous on their respective
   open sets. -/
theorem exponentialBranch_continuousOn
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    ContinuousOn (d.exponentialBranch v) (d.exponentialBranch v).source :=
  (d.exponentialBranch v).continuousOn

theorem exponentialBranch_symm_continuousOn
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    ContinuousOn (d.exponentialBranch v).symm (d.exponentialBranch v).target :=
  (d.exponentialBranch v).symm.continuousOn

/-- Two local quotient representatives differ by an ambient period. -/
theorem quotientLocalBranchAt_sub_mem_ambientPeriodLattice
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g)
    (v w : V) {q : V ⧸ d.ambientPeriodLattice}
    (hqv : q ∈ (d.quotientLocalBranchAt v).source)
    (hqw : q ∈ (d.quotientLocalBranchAt w).source) :
    d.quotientLocalBranchAt v q - d.quotientLocalBranchAt w q ∈
      d.ambientPeriodLattice := by
  apply (PeriodLatticeQuotient.quotientAddEquiv_mk_eq_iff
    d.toPeriodLatticeQuotient
    (d.quotientLocalBranchAt v q)
    (d.quotientLocalBranchAt w q)).mp
  change d.quotientAddEquiv
      (QuotientAddGroup.mk' d.ambientPeriodLattice
        (d.quotientLocalBranchAt v q)) =
    d.quotientAddEquiv
      (QuotientAddGroup.mk' d.ambientPeriodLattice
        (d.quotientLocalBranchAt w q))
  exact congrArg d.quotientAddEquiv
    ((d.quotient_mk_apply_quotientLocalBranchAt v hqv).trans
      (d.quotient_mk_apply_quotientLocalBranchAt w hqw).symm)

/- Branches that are simultaneously defined at a point differ by an ambient
   period. -/
theorem exponentialBranch_sub_mem_ambientPeriodLattice
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g)
    (v w : V) {x : X}
    (hxv : x ∈ (d.exponentialBranch v).source)
    (hxw : x ∈ (d.exponentialBranch w).source) :
    d.exponentialBranch v x - d.exponentialBranch w x ∈
      d.ambientPeriodLattice := by
  rw [exponentialBranch, OpenPartialHomeomorph.trans_source] at hxv hxw
  have hqv : d.quotientHomeomorph.symm x ∈
      (d.quotientLocalBranchAt v).source := hxv.2
  have hqw : d.quotientHomeomorph.symm x ∈
      (d.quotientLocalBranchAt w).source := hxw.2
  have hdiff := d.quotientLocalBranchAt_sub_mem_ambientPeriodLattice v w hqv hqw
  simpa [exponentialBranch, OpenPartialHomeomorph.trans_apply] using hdiff

/-- Surjectivity makes the transported branch sources cover the target. -/
theorem exists_exponentialBranch_source
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (x : X) :
    ∃ v : V, x ∈ (d.exponentialBranch v).source := by
  obtain ⟨v, hv⟩ := d.surjective x
  refine ⟨v, ?_⟩
  rw [← hv]
  exact d.exponential_source_mem v

/-- Every point has a branch representative that inverts the exponential at
    that point. -/
theorem exists_exponentialBranch_apply_eq
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (x : X) :
    ∃ v : V, x ∈ (d.exponentialBranch v).source ∧
      d.exponentialBranch v x = v := by
  obtain ⟨v, hv⟩ := d.surjective x
  refine ⟨v, ?_, ?_⟩
  · rw [← hv]
    exact d.exponential_source_mem v
  · rw [← hv]
    exact d.exponential_apply_exponential v

/-- The exponential branch sources form an open cover of the target. -/
theorem exponentialBranch_source_iUnion_eq_univ
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) :
    (⋃ v : V, (d.exponentialBranch v).source) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨v, hx⟩ := d.exists_exponentialBranch_source x
  exact Set.mem_iUnion.2 ⟨v, hx⟩

/- The overlap transition between two transported inverse branches.  Its
   source consists precisely of those tangent representatives whose image
   under the first branch lands in the second branch source. -/
noncomputable def exponentialBranchTransition
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V) :
    OpenPartialHomeomorph V V :=
  (d.exponentialBranch v).symm.trans (d.exponentialBranch w)

@[simp]
theorem exponentialBranchTransition_apply
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V)
    (y : V) :
    d.exponentialBranchTransition v w y =
      d.exponentialBranch w ((d.exponentialBranch v).symm y) := by
  rw [exponentialBranchTransition, OpenPartialHomeomorph.trans_apply]

theorem exponentialBranchTransition_source_isOpen
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V) :
    IsOpen (d.exponentialBranchTransition v w).source := by
  exact (d.exponentialBranchTransition v w).open_source

theorem exponentialBranchTransition_target_isOpen
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V) :
    IsOpen (d.exponentialBranchTransition v w).target := by
  exact (d.exponentialBranchTransition v w).open_target

/- On an overlap, the transition has pointwise difference in the period
   subgroup (the sign is immaterial for membership in that subgroup). -/
theorem exponentialBranchTransition_sub_mem_ambientPeriodLattice
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V)
    {y : V} (hy : y ∈ (d.exponentialBranchTransition v w).source) :
    d.exponentialBranchTransition v w y - y ∈ d.ambientPeriodLattice := by
  rw [exponentialBranchTransition, OpenPartialHomeomorph.trans_source] at hy
  have hyv : y ∈ (d.exponentialBranch v).target := hy.1
  let x : X := (d.exponentialBranch v).symm y
  have hxv : x ∈ (d.exponentialBranch v).source :=
    (d.exponentialBranch v).map_target hyv
  have hxw : x ∈ (d.exponentialBranch w).source := hy.2
  have hdiff := d.exponentialBranch_sub_mem_ambientPeriodLattice v w hxv hxw
  have hrv : d.exponentialBranch v x = y :=
    (d.exponentialBranch v).right_inv hyv
  change d.exponentialBranch w x - y ∈ d.ambientPeriodLattice
  simpa only [hrv, neg_sub] using (neg_mem hdiff)

/- The period-valued form is convenient when treating overlap maps as deck
   translations rather than merely comparing their differences. -/
theorem exponentialBranchTransition_exists_period
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V)
    {y : V} (hy : y ∈ (d.exponentialBranchTransition v w).source) :
    ∃ period : d.ambientPeriodLattice,
      d.exponentialBranchTransition v w y = y + (period : V) := by
  have hdiff := d.exponentialBranchTransition_sub_mem_ambientPeriodLattice v w hy
  refine ⟨⟨d.exponentialBranchTransition v w y - y, hdiff⟩, ?_⟩
  change d.exponentialBranchTransition v w y =
    y + (d.exponentialBranchTransition v w y - y)
  exact (add_sub_cancel y (d.exponentialBranchTransition v w y)).symm

theorem exponentialBranchTransition_self_apply
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V)
    {y : V} (hy : y ∈ (d.exponentialBranchTransition v v).source) :
    d.exponentialBranchTransition v v y = y := by
  rw [exponentialBranchTransition, OpenPartialHomeomorph.trans_source] at hy
  rw [exponentialBranchTransition, OpenPartialHomeomorph.trans_apply]
  exact (d.exponentialBranch v).right_inv hy.1

/- Every overlap transition preserves the exponential, as expected for a
   deck transformation of the quotient map. -/
theorem exponentialBranchTransition_exponential_eq
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V)
    {y : V} (hy : y ∈ (d.exponentialBranchTransition v w).source) :
    d.exponential (d.exponentialBranchTransition v w y) = d.exponential y := by
  rw [d.exponentialBranchTransition_apply v w y]
  have hyv : y ∈ (d.exponentialBranch v).target := by
    rw [exponentialBranchTransition, OpenPartialHomeomorph.trans_source] at hy
    exact hy.1
  let x : X := (d.exponentialBranch v).symm y
  have hxw : x ∈ (d.exponentialBranch w).source := by
    rw [exponentialBranchTransition, OpenPartialHomeomorph.trans_source] at hy
    exact hy.2
  have hleft : d.exponential (d.exponentialBranch w x) = x :=
    d.exponential_apply_exponential_apply w hxw
  have hright : d.exponential y = x := by
    exact (d.exponential_symm_apply_eq_exponential v hyv).symm
  rw [hleft, hright]

/- The overlap maps inherit the local-homeomorphism structure of their two
   constituent branches. -/
theorem exponentialBranchTransition_continuousOn
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V) :
    ContinuousOn (d.exponentialBranchTransition v w)
      (d.exponentialBranchTransition v w).source :=
  (d.exponentialBranchTransition v w).continuousOn

theorem exponentialBranchTransition_symm_continuousOn
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V) :
    ContinuousOn (d.exponentialBranchTransition v w).symm
      (d.exponentialBranchTransition v w).target :=
  (d.exponentialBranchTransition v w).continuousOn_symm

theorem exponentialBranchTransition_image_source_eq_target
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V) :
    d.exponentialBranchTransition v w ''
        (d.exponentialBranchTransition v w).source =
      (d.exponentialBranchTransition v w).target :=
  (d.exponentialBranchTransition v w).image_source_eq_target

/- Exchanging the two branch labels reverses the transition. -/
@[simp]
theorem exponentialBranchTransition_symm_eq
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v w : V) :
    (d.exponentialBranchTransition v w).symm =
      d.exponentialBranchTransition w v := by
  rw [exponentialBranchTransition,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  rfl

/- The transition maps satisfy the usual Cech cocycle law whenever the two
   successive transitions are defined.  The explicit source hypotheses keep
   the statement honest for partial homeomorphisms. -/
theorem exponentialBranchTransition_cocycle
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g)
    (v w u : V) {y : V}
    (hyvw : y ∈ (d.exponentialBranchTransition v w).source)
    (hwyu : d.exponentialBranchTransition v w y ∈
      (d.exponentialBranchTransition w u).source) :
    y ∈ (d.exponentialBranchTransition v u).source ∧
      d.exponentialBranchTransition v u y =
        d.exponentialBranchTransition w u
          (d.exponentialBranchTransition v w y) := by
  have hyvw' := hyvw
  rw [exponentialBranchTransition, OpenPartialHomeomorph.trans_source] at hyvw'
  have hvtarget : y ∈ (d.exponentialBranch v).target := by
    simpa only [OpenPartialHomeomorph.symm_source] using hyvw'.1
  let x : X := (d.exponentialBranch v).symm y
  have hxw : x ∈ (d.exponentialBranch w).source := by
    exact hyvw'.2
  have htw : d.exponentialBranchTransition v w y =
      d.exponentialBranch w x := by
    change d.exponentialBranch w
      ((d.exponentialBranch v).symm y) = d.exponentialBranch w x
    rfl
  have hwyu' := hwyu
  rw [exponentialBranchTransition, OpenPartialHomeomorph.trans_source] at hwyu'
  have hxu : x ∈ (d.exponentialBranch u).source := by
    have hz := hwyu'.2
    change (d.exponentialBranch w).symm
      (d.exponentialBranchTransition v w y) ∈
        (d.exponentialBranch u).source at hz
    rw [htw, (d.exponentialBranch w).left_inv hxw] at hz
    exact hz
  have hyv_u : y ∈ (d.exponentialBranchTransition v u).source := by
    rw [exponentialBranchTransition, OpenPartialHomeomorph.trans_source]
    exact ⟨hvtarget, hxu⟩
  refine ⟨hyv_u, ?_⟩
  have htv_u : d.exponentialBranchTransition v u y =
      d.exponentialBranch u x := by
    change d.exponentialBranch u
      ((d.exponentialBranch v).symm y) = d.exponentialBranch u x
    rfl
  have htw_u : d.exponentialBranchTransition w u
      (d.exponentialBranchTransition v w y) =
      d.exponentialBranch u x := by
    change d.exponentialBranch u
      ((d.exponentialBranch w).symm
        (d.exponentialBranchTransition v w y)) =
      d.exponentialBranch u x
    rw [htw, (d.exponentialBranch w).left_inv hxw]
  exact htv_u.trans htw_u.symm

end ComplexVectorLatticeExponentialData

end
end Uniformization
end Mumford
