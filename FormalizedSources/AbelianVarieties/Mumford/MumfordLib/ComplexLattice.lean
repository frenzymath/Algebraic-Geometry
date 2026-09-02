/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ComplexUniformization
import MumfordLib.ZLattice
import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.Topology.Covering.Quotient

/-!
# Arbitrary complex period lattices

The analytic uniformization theorem starts with an arbitrary lattice in the
complex tangent space.  The earlier `ComplexTorusUniformization` interface is
deliberately tied to the canonical rectangular lattice used for the explicit
torus model.  This file keeps the analytic boundary separate: a
`ComplexLatticeExponentialData` certificate records an arbitrary full
`ℤ`-lattice, its continuous surjective exponential, and the kernel identity.
The topological consequences that follow from these data are proved here;
holomorphic and complex-manifold structure is not asserted without a suitable
mathlib interface.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

/-- Analytic exponential data with an arbitrary full period lattice.

`IsZLattice ℝ periodLattice` is the realification of the usual lattice
condition on a finite-dimensional complex vector space.  The two lattice
instances are stored in the certificate so that downstream results can use
the data without introducing a global instance for an arbitrary subgroup.
-/
structure ComplexLatticeExponentialData
    (X : Type*) [AddCommGroup X] [TopologicalSpace X] (g : ℕ) where
  periodLattice : Submodule ℤ (GenusComplexVector g)
  [periodLatticeDiscrete : DiscreteTopology periodLattice]
  [periodLatticeFull : IsZLattice ℝ periodLattice]
  exponential : GenusComplexVector g →+ X
  surjective : Function.Surjective exponential
  continuous : Continuous exponential
  kernel : exponential.ker = periodLattice.toAddSubgroup

namespace ComplexLatticeExponentialData

/-- The additive quotient certificate carried by the exponential data. -/
def toPeriodLatticeQuotient
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    PeriodLatticeQuotient (GenusComplexVector g) X where
  periodLattice := d.periodLattice.toAddSubgroup
  exponential := d.exponential
  exponential_surjective := d.surjective
  kernel_exponential := d.kernel

/-- The quotient additive equivalence induced by the exponential. -/
def quotientAddEquiv
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup ≃+ X :=
  d.toPeriodLatticeQuotient.quotientAddEquiv

@[simp]
theorem quotientAddEquiv_mk
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g)
    (z : GenusComplexVector g) :
    d.quotientAddEquiv
        (QuotientAddGroup.mk' d.periodLattice.toAddSubgroup z) =
      d.exponential z :=
  PeriodLatticeQuotient.quotientAddEquiv_mk d.toPeriodLatticeQuotient z

/-- The lattice has the real rank expected of a complex `g`-space. -/
theorem periodLattice_finrank
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    Module.finrank ℤ d.periodLattice = 2 * g := by
  letI : DiscreteTopology d.periodLattice := d.periodLatticeDiscrete
  letI : IsZLattice ℝ d.periodLattice := d.periodLatticeFull
  rw [ZLattice.rank ℝ]
  simp [GenusComplexVector, Module.finrank_pi_fintype,
    Complex.finrank_real_complex, Nat.mul_comm]

/-- The kernel identity gives a pointwise zero criterion for the exponential. -/
theorem exponential_eq_zero_iff_mem_periodLattice
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) (z : GenusComplexVector g) :
    d.exponential z = 0 ↔ z ∈ d.periodLattice := by
  rw [← AddMonoidHom.mem_ker, d.kernel]
  simp only [Submodule.mem_toAddSubgroup]

/-- Translation by a period does not change the exponential. -/
theorem exponential_periodic
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g)
    (z w : GenusComplexVector g) (hw : w ∈ d.periodLattice) :
    d.exponential (z + w) = d.exponential z := by
  have hw0 : d.exponential w = 0 :=
    d.exponential_eq_zero_iff_mem_periodLattice w |>.2 hw
  rw [map_add, hw0, add_zero]

/-- The period subgroup is discrete in the ambient complex vector space. -/
theorem periodLattice_isDiscrete
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    IsDiscrete (d.periodLattice.toAddSubgroup : Set (GenusComplexVector g)) := by
  letI : DiscreteTopology d.periodLattice := d.periodLatticeDiscrete
  exact isDiscrete_iff_discreteTopology.mpr
    (inferInstance : DiscreteTopology d.periodLattice.toAddSubgroup)

/- A discrete period subgroup is closed in the Hausdorff topological vector
   group, so its additive quotient is Hausdorff as well. -/
theorem periodLattice_isClosed
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    IsClosed (d.periodLattice.toAddSubgroup : Set (GenusComplexVector g)) := by
  letI : DiscreteTopology d.periodLattice := d.periodLatticeDiscrete
  exact AddSubgroup.isClosed_of_discrete

/- The Hausdorff quotient statement is kept as a theorem (rather than a
   global instance) because the lattice is use-site data. -/
theorem quotient_isT2Space
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    T2Space (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) := by
  letI : IsClosed (d.periodLattice.toAddSubgroup : Set (GenusComplexVector g)) :=
    d.periodLattice_isClosed
  infer_instance

/-- Translation by the period subgroup acts properly discontinuously on the
complex vector space. -/
theorem periodLattice_properlyDiscontinuousVAdd
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    ProperlyDiscontinuousVAdd d.periodLattice.toAddSubgroup
      (GenusComplexVector g) := by
  apply AddSubgroup.properlyDiscontinuousVAdd_of_tendsto_cofinite
  exact AddSubgroup.tendsto_coe_cofinite_of_discrete
    d.periodLattice.toAddSubgroup d.periodLattice_isDiscrete

/- The quotient projection is a covering map in the topological-group sense;
   the stronger holomorphic covering assertion remains outside this interface. -/
theorem quotient_mk_isAddQuotientCoveringMap
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    IsAddQuotientCoveringMap
      (QuotientAddGroup.mk : GenusComplexVector g →
        GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup)
      d.periodLattice.toAddSubgroup := by
  exact AddSubgroup.isAddQuotientCoveringMap_of_comm
    d.periodLattice.toAddSubgroup d.periodLattice_isDiscrete

/-- The quotient projection is a covering map after forgetting its deck-group
    structure. -/
theorem quotient_mk_isCoveringMap
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    IsCoveringMap
      (QuotientAddGroup.mk : GenusComplexVector g →
        GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) :=
  d.quotient_mk_isAddQuotientCoveringMap.isCoveringMap

/-- The quotient projection is a local homeomorphism. -/
theorem quotient_mk_isLocalHomeomorph
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    IsLocalHomeomorph
      (QuotientAddGroup.mk : GenusComplexVector g →
        GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) :=
  d.quotient_mk_isCoveringMap.isLocalHomeomorph

/-- The full period lattice induces a charted-space structure on its quotient.

This is kept as an explicit value because the lattice belongs to the analytic
certificate rather than to a global instance.  Smoothness and holomorphicity
of the quotient charts require additional manifold infrastructure. -/
@[reducible]
noncomputable def quotientChartedSpace
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    ChartedSpace (GenusComplexVector g)
      (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) := by
  letI : ProperlyDiscontinuousVAdd d.periodLattice.toAddSubgroup
      (GenusComplexVector g) := d.periodLattice_properlyDiscontinuousVAdd
  letI : ProperlyDiscontinuousVAdd d.periodLattice.toAddSubgroup.op
      (GenusComplexVector g) := by
    exact AddSubgroup.properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite
      d.periodLattice.toAddSubgroup
      (AddSubgroup.tendsto_coe_cofinite_of_discrete
        d.periodLattice.toAddSubgroup d.periodLattice_isDiscrete)
  letI : IsCancelVAdd d.periodLattice.toAddSubgroup.op
      (GenusComplexVector g) :=
    (AddSubgroup.isAddQuotientCoveringMap
      d.periodLattice.toAddSubgroup d.periodLattice_isDiscrete).isCancelVAdd
  exact AddAction.instChartedSpaceQuotient

theorem quotientAddEquiv_mk_eq_iff
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g)
    (z w : GenusComplexVector g) :
    d.quotientAddEquiv
        (QuotientAddGroup.mk' d.periodLattice.toAddSubgroup z) =
      d.quotientAddEquiv
        (QuotientAddGroup.mk' d.periodLattice.toAddSubgroup w) ↔
      z - w ∈ d.periodLattice := by
  rw [d.quotientAddEquiv_mk, d.quotientAddEquiv_mk]
  constructor
  · intro h
    have hz : d.exponential (z - w) = 0 := by
      rw [map_sub, h, sub_self]
    exact d.exponential_eq_zero_iff_mem_periodLattice (z - w) |>.1 hz
  · intro h
    have hz : d.exponential (z - w) = 0 :=
      d.exponential_eq_zero_iff_mem_periodLattice (z - w) |>.2 h
    have heq : d.exponential z - d.exponential w = 0 := by
      simpa only [map_sub] using hz
    exact sub_eq_zero.mp heq

/-- A continuous exponential with a full lattice kernel has compact range. -/
theorem target_isCompact
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    IsCompact (Set.univ : Set X) := by
  letI : DiscreteTopology d.periodLattice := d.periodLatticeDiscrete
  letI : IsZLattice ℝ d.periodLattice := d.periodLatticeFull
  have hcompact :=
    IsZLattice.isCompact_range_of_periodic d.periodLattice
      d.exponential d.continuous d.exponential_periodic
  rw [d.surjective.range_eq] at hcompact
  exact hcompact

/-- The compact-space instance forced by the lattice-periodicity argument. -/
@[reducible]
noncomputable def targetCompactSpace
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) : CompactSpace X :=
  ⟨d.target_isCompact⟩

/-- The target is path connected because the source vector space is. -/
@[reducible]
noncomputable def targetPathConnectedSpace
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) : PathConnectedSpace X :=
  d.surjective.pathConnectedSpace d.continuous

/-- Connectedness is a direct consequence of the preceding path-connectedness. -/
@[reducible]
noncomputable def targetConnectedSpace
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) : ConnectedSpace X := by
  letI : PathConnectedSpace X := d.targetPathConnectedSpace
  infer_instance

/-- The exponential is an open quotient under the usual Hausdorff group
assumptions on the target.  Compactness supplies local compactness. -/
theorem isOpenQuotientMap
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [T2Space X] [ContinuousAdd X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    IsOpenQuotientMap d.exponential := by
  letI : CompactSpace X := d.targetCompactSpace
  exact isOpenQuotientMap_of_continuous_surjective_of_locallyCompact
    d.exponential d.surjective d.continuous

/-- A continuous exponential with discrete kernel is a quotient covering map
    once its target is a Hausdorff topological additive group. -/
theorem exponential_isAddQuotientCoveringMap
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    IsAddQuotientCoveringMap d.exponential d.periodLattice.toAddSubgroup := by
  have hdisc : IsDiscrete
      (d.exponential.ker : Set (GenusComplexVector g)) := by
    rw [d.kernel]
    exact d.periodLattice_isDiscrete
  have h := d.isOpenQuotientMap.isQuotientMap
    |>.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom hdisc
  rw [d.kernel] at h
  exact h

/-- The exponential itself is a topological covering map under the same
    Hausdorff topological-group hypotheses. -/
theorem exponential_isCoveringMap
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    IsCoveringMap d.exponential :=
  d.exponential_isAddQuotientCoveringMap.isCoveringMap

/- Surjectivity of the exponential transports the divisibility of the
   complex torus target.  The witness is obtained by dividing upstairs and
   then applying the additive homomorphism. -/
@[reducible]
noncomputable def targetDivisibleBy
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) : DivisibleBy X ℤ :=
  Function.Surjective.divisibleBy (fun z => d.exponential z) d.surjective
    (fun z n => d.exponential.map_zsmul n z)

theorem exists_zsmul_eq
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) (x : X) {n : ℤ} (hn : n ≠ 0) :
    ∃ y : X, n • y = x := by
  letI : DivisibleBy X ℤ := d.targetDivisibleBy
  exact DivisibleBy.surjective_smul X ℤ hn x

/-- The arbitrary period quotient is homeomorphic to the target. -/
noncomputable def quotientHomeomorph
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [T2Space X] [ContinuousAdd X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) :
    GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup ≃ₜ X :=
  d.toPeriodLatticeQuotient.quotientHomeomorph d.isOpenQuotientMap

@[simp]
theorem quotientHomeomorph_mk
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [T2Space X] [ContinuousAdd X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g)
    (z : GenusComplexVector g) :
    d.quotientHomeomorph
        (QuotientAddGroup.mk' d.periodLattice.toAddSubgroup z) =
      d.exponential z :=
  PeriodLatticeQuotient.quotientHomeomorph_mk
    d.toPeriodLatticeQuotient d.isOpenQuotientMap z

/-- The inverse quotient homeomorphism recovers the class of an exponential
representative. -/
theorem quotientHomeomorph_symm_exponential
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [T2Space X] [ContinuousAdd X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g)
    (z : GenusComplexVector g) :
    d.quotientHomeomorph.symm (d.exponential z) =
      QuotientAddGroup.mk' d.periodLattice.toAddSubgroup z := by
  rw [← d.quotientHomeomorph_mk z]
  exact d.quotientHomeomorph.symm_apply_apply _

/-- The topological quotient identification has the same underlying map as
the additive quotient equivalence.  This lets later analytic arguments switch
between the topological and algebraic interfaces without redoing quotient
induction. -/
theorem quotientHomeomorph_eq_quotientAddEquiv
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [T2Space X] [ContinuousAdd X] {g : ℕ}
    (d : ComplexLatticeExponentialData X g) (q :
      GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) :
  d.quotientHomeomorph q = d.quotientAddEquiv q := by
  refine QuotientAddGroup.induction_on q ?_
  intro z
  change d.quotientHomeomorph
      (QuotientAddGroup.mk' d.periodLattice.toAddSubgroup z) =
    d.quotientAddEquiv (QuotientAddGroup.mk' d.periodLattice.toAddSubgroup z)
  rw [d.quotientHomeomorph_mk, d.quotientAddEquiv_mk]

/- The canonical complex-coordinate exponential is a concrete instance of the
   full-lattice certificate.  Keeping this witness explicit makes the lattice
   hypotheses available to the topological APIs without introducing a global
   instance for arbitrary period subgroups. -/
def standardComplexGenusTorusLatticeExponentialData (g : ℕ) :
    ComplexLatticeExponentialData (GenusTorus g) g where
  periodLattice := complexPeriodLatticeSubmodule g
  periodLatticeDiscrete := inferInstance
  periodLatticeFull := inferInstance
  exponential := complexGenusTorusExponential g
  surjective := complexGenusTorusExponential_surjective g
  continuous := complexGenusTorusExponential_continuous g
  kernel := by
    rw [complexPeriodLatticeSubmodule_toAddSubgroup]
    exact complexGenusTorusExponential_ker g

@[simp]
theorem standardComplexGenusTorusLatticeExponentialData_exponential_apply
    (g : ℕ) (z : GenusComplexVector g) :
    (standardComplexGenusTorusLatticeExponentialData g).exponential z =
      complexGenusTorusExponential g z :=
  rfl

@[simp]
theorem standardComplexGenusTorusLatticeExponentialData_periodLattice
    (g : ℕ) :
    (standardComplexGenusTorusLatticeExponentialData g).periodLattice.toAddSubgroup =
      complexPeriodLattice g :=
  complexPeriodLatticeSubmodule_toAddSubgroup g

/-- The canonical exponential data for the quotient by any full lattice. -/
def ofLattice
    (g : ℕ) (L : Submodule ℤ (GenusComplexVector g))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ComplexLatticeExponentialData
      (GenusComplexVector g ⧸ L.toAddSubgroup) g where
  periodLattice := L
  periodLatticeDiscrete := inferInstance
  periodLatticeFull := inferInstance
  exponential := QuotientAddGroup.mk' L.toAddSubgroup
  surjective := QuotientAddGroup.mk'_surjective L.toAddSubgroup
  continuous := QuotientAddGroup.continuous_mk
  kernel := QuotientAddGroup.ker_mk' L.toAddSubgroup

/-- A compact-space instance for a quotient by a full lattice.  It is explicit
because the lattice is a use-site datum and should not become a global
instance for every subgroup. -/
@[reducible]
noncomputable def quotientCompactSpace
    (g : ℕ) (L : Submodule ℤ (GenusComplexVector g))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    CompactSpace (GenusComplexVector g ⧸ L.toAddSubgroup) :=
  (ofLattice g L).targetCompactSpace

/- The canonical quotient by a full lattice is Hausdorff. -/
@[reducible]
noncomputable def quotientT2Space
    (g : ℕ) (L : Submodule ℤ (GenusComplexVector g))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    T2Space (GenusComplexVector g ⧸ L.toAddSubgroup) :=
  (ofLattice g L).quotient_isT2Space

@[simp]
theorem ofLattice_exponential_apply
    (g : ℕ) (L : Submodule ℤ (GenusComplexVector g))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (z : GenusComplexVector g) :
    (ofLattice g L).exponential z =
      QuotientAddGroup.mk' L.toAddSubgroup z :=
  rfl

theorem quotient_isCompact
    (g : ℕ) (L : Submodule ℤ (GenusComplexVector g))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    IsCompact
      (Set.univ : Set (GenusComplexVector g ⧸ L.toAddSubgroup)) :=
  (ofLattice g L).target_isCompact

theorem quotient_isPathConnected
    (g : ℕ) (L : Submodule ℤ (GenusComplexVector g))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    IsPathConnected
      (Set.univ : Set (GenusComplexVector g ⧸ L.toAddSubgroup)) := by
  letI : PathConnectedSpace
      (GenusComplexVector g ⧸ L.toAddSubgroup) :=
    (ofLattice g L).targetPathConnectedSpace
  exact isPathConnected_univ

@[reducible]
noncomputable def quotientPathConnectedSpace
    (g : ℕ) (L : Submodule ℤ (GenusComplexVector g))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    PathConnectedSpace (GenusComplexVector g ⧸ L.toAddSubgroup) :=
  (ofLattice g L).targetPathConnectedSpace

theorem quotient_isConnected
    (g : ℕ) (L : Submodule ℤ (GenusComplexVector g))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    IsConnected
      (Set.univ : Set (GenusComplexVector g ⧸ L.toAddSubgroup)) := by
  letI : PathConnectedSpace
      (GenusComplexVector g ⧸ L.toAddSubgroup) :=
    quotientPathConnectedSpace g L
  exact isConnected_univ

end ComplexLatticeExponentialData

namespace ComplexTorusUniformization

/-- A complex uniformization witness with continuous inverse supplies the
full-lattice exponential certificate used by the topological interface. -/
def toComplexLatticeExponentialData
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont_symm : Continuous u.equiv.symm) :
    ComplexLatticeExponentialData X g where
  periodLattice := complexPeriodLatticeSubmodule g
  periodLatticeDiscrete := inferInstance
  periodLatticeFull := inferInstance
  exponential := u.exponential
  surjective := u.exponential_surjective
  continuous := u.exponential_continuous hcont_symm
  kernel := by
    rw [u.exponential_ker]
    exact (complexPeriodLatticeSubmodule_toAddSubgroup g).symm

@[simp]
theorem toComplexLatticeExponentialData_exponential_apply
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont_symm : Continuous u.equiv.symm) (z : GenusComplexVector g) :
    (u.toComplexLatticeExponentialData hcont_symm).exponential z = u.exponential z :=
  rfl

@[simp]
theorem toComplexLatticeExponentialData_periodLattice
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont_symm : Continuous u.equiv.symm) :
    (u.toComplexLatticeExponentialData hcont_symm).periodLattice.toAddSubgroup =
      complexPeriodLattice g :=
  complexPeriodLatticeSubmodule_toAddSubgroup g

end ComplexTorusUniformization
end
end Uniformization
end Mumford
