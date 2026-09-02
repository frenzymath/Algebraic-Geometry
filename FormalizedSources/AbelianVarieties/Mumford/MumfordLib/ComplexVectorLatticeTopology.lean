/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ComplexVectorLattice

/-!
# Topology of an arbitrary tangent-space lattice quotient

`ComplexVectorLatticeExponentialData` records the continuous additive part of
the analytic uniformization theorem in an arbitrary finite-dimensional complex
tangent space.  This file transports the standard lattice topology facts to
that ambient space.  The holomorphic and complex-manifold assertions remain
outside the interface.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

namespace ComplexVectorLatticeExponentialData

/-- The additive equivalence underlying the chosen complex coordinates. -/
def coordinateAddEquiv
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    V ≃+ GenusComplexVector g :=
  d.coordinate.toLinearEquiv.toAddEquiv

/-- The coordinate equivalence carries the ambient period subgroup onto the
stored standard period subgroup. -/
theorem coordinate_map_ambientPeriodLattice
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    AddSubgroup.map (d.coordinateAddEquiv : V →+ GenusComplexVector g)
        d.ambientPeriodLattice = d.periodLattice.toAddSubgroup := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (d.ambientPeriodLattice_mem_iff v).mp hv
  · intro hz
    refine ⟨d.coordinate.symm z, ?_, ?_⟩
    · exact (d.ambientPeriodLattice_mem_iff _).mpr (by simpa using hz)
    · simp [coordinateAddEquiv]

/-- The quotient additive equivalence induced by the tangent coordinates. -/
def quotientCoordinateAddEquiv
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    (V ⧸ d.ambientPeriodLattice) ≃+
      (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) :=
  QuotientAddGroup.congr d.ambientPeriodLattice d.periodLattice.toAddSubgroup
    d.coordinateAddEquiv d.coordinate_map_ambientPeriodLattice

@[simp]
theorem quotientCoordinateAddEquiv_mk
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.quotientCoordinateAddEquiv
      (QuotientAddGroup.mk' d.ambientPeriodLattice v) =
      QuotientAddGroup.mk' d.periodLattice.toAddSubgroup (d.coordinate v) := by
  change QuotientAddGroup.congr d.ambientPeriodLattice d.periodLattice.toAddSubgroup
      d.coordinateAddEquiv d.coordinate_map_ambientPeriodLattice
      (QuotientAddGroup.mk' d.ambientPeriodLattice v) = _
  rfl

/-- The coordinate quotient map and the canonical quotient map compose to the
    direct quotient equivalence of the ambient tangent model. -/
theorem quotientCoordinateAddEquiv_trans_quotientAddEquiv
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    d.quotientCoordinateAddEquiv.trans d.toCanonical.quotientAddEquiv =
      d.quotientAddEquiv := by
  apply AddEquiv.ext
  intro q
  refine QuotientAddGroup.induction_on q ?_
  intro v
  change d.toCanonical.quotientAddEquiv
      (QuotientAddGroup.mk' d.toCanonical.periodLattice.toAddSubgroup
        (d.coordinate v)) = d.exponential v
  rw [ComplexLatticeExponentialData.quotientAddEquiv_mk]
  simp [ComplexVectorLatticeExponentialData.toCanonical]

/-- The transported ambient period subgroup is discrete in the tangent space.

The explicit equality with `ZLattice.comap` is needed because the certificate
stores the lattice using the scalar-restricted linear map, while Mathlib's
discreteness theorem is stated for the complex-linear comap.
-/
theorem ambientPeriodLattice_discreteTopology
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    DiscreteTopology d.ambientPeriodLattice := by
  letI : DiscreteTopology d.periodLattice := d.periodLatticeDiscrete
  let L : Submodule ℤ V :=
    ZLattice.comap ℂ d.periodLattice d.coordinate.toLinearEquiv
  letI : DiscreteTopology L :=
    instDiscreteTopologySubtypeMemSubmoduleIntComap ℂ d.periodLattice d.coordinate
  have hL : DiscreteTopology L.toAddSubgroup := inferInstance
  have hEq : d.ambientPeriodLattice = L.toAddSubgroup := by
    ext v
    simp [ComplexVectorLatticeExponentialData.ambientPeriodLattice,
      ComplexVectorLatticeExponentialData.ambientPeriodLatticeSubmodule, L,
      ZLattice.comap]
  rw [hEq]
  exact hL

/-- The ambient period subgroup is a discrete subset of the tangent space. -/
theorem ambientPeriodLattice_isDiscrete
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    IsDiscrete (d.ambientPeriodLattice : Set V) := by
  letI : DiscreteTopology d.ambientPeriodLattice :=
    d.ambientPeriodLattice_discreteTopology
  exact isDiscrete_iff_discreteTopology.mpr inferInstance

/-- Translation by the ambient period subgroup acts properly discontinuously
on the tangent space. -/
theorem ambientPeriodLattice_properlyDiscontinuousVAdd
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    ProperlyDiscontinuousVAdd d.ambientPeriodLattice V := by
  apply AddSubgroup.properlyDiscontinuousVAdd_of_tendsto_cofinite
  exact AddSubgroup.tendsto_coe_cofinite_of_discrete
    d.ambientPeriodLattice d.ambientPeriodLattice_isDiscrete

/-- A transported full lattice is closed in the ambient normed group. -/
theorem ambientPeriodLattice_isClosed
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    IsClosed (d.ambientPeriodLattice : Set V) := by
  letI : DiscreteTopology d.ambientPeriodLattice :=
    d.ambientPeriodLattice_discreteTopology
  exact AddSubgroup.isClosed_of_discrete

/-- The arbitrary tangent-space quotient is Hausdorff. -/
theorem quotient_isT2Space
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    T2Space (V ⧸ d.ambientPeriodLattice) := by
  letI : IsClosed (d.ambientPeriodLattice : Set V) :=
    d.ambientPeriodLattice_isClosed
  infer_instance

/- The canonical projection of the tangent space onto its lattice quotient is
   a covering map.  The statement is kept conditional on the certificate's
   lattice data, so it does not introduce a global topology instance. -/
theorem quotient_mk_isAddQuotientCoveringMap
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    IsAddQuotientCoveringMap
      (QuotientAddGroup.mk : V → V ⧸ d.ambientPeriodLattice)
      d.ambientPeriodLattice := by
  exact AddSubgroup.isAddQuotientCoveringMap_of_comm
    d.ambientPeriodLattice d.ambientPeriodLattice_isDiscrete

/-- The ambient lattice quotient projection is a covering map. -/
theorem quotient_mk_isCoveringMap
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    IsCoveringMap
      (QuotientAddGroup.mk : V → V ⧸ d.ambientPeriodLattice) :=
  d.quotient_mk_isAddQuotientCoveringMap.isCoveringMap

/-- A covering projection is a local homeomorphism. -/
theorem quotient_mk_isLocalHomeomorph
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    IsLocalHomeomorph
      (QuotientAddGroup.mk : V → V ⧸ d.ambientPeriodLattice) :=
  d.quotient_mk_isCoveringMap.isLocalHomeomorph

/-- The ambient period lattice induces a charted-space structure on the
arbitrary tangent-space quotient. -/
@[reducible]
noncomputable def quotientChartedSpace
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    ChartedSpace V (V ⧸ d.ambientPeriodLattice) := by
  letI : FiniteDimensional ℂ V :=
    FiniteDimensional.of_injective d.coordinate.toLinearEquiv.toLinearMap
      d.coordinate.injective
  letI : ProperlyDiscontinuousVAdd d.ambientPeriodLattice V :=
    d.ambientPeriodLattice_properlyDiscontinuousVAdd
  letI : ProperlyDiscontinuousVAdd d.ambientPeriodLattice.op V := by
    exact AddSubgroup.properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite
      d.ambientPeriodLattice
      (AddSubgroup.tendsto_coe_cofinite_of_discrete
        d.ambientPeriodLattice d.ambientPeriodLattice_isDiscrete)
  letI : IsCancelVAdd d.ambientPeriodLattice.op V :=
    (AddSubgroup.isAddQuotientCoveringMap
      d.ambientPeriodLattice d.ambientPeriodLattice_isDiscrete).isCancelVAdd
  exact AddAction.instChartedSpaceQuotient

/-- A continuous full-lattice exponential has compact target. -/
theorem target_isCompact
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    IsCompact (Set.univ : Set X) :=
  d.toCanonical.target_isCompact

/-- The compact-space structure forced by lattice periodicity. -/
@[reducible]
noncomputable def targetCompactSpace
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) : CompactSpace X :=
  ⟨d.target_isCompact⟩

/-- The target is path connected because the tangent space is path connected. -/
@[reducible]
noncomputable def targetPathConnectedSpace
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) : PathConnectedSpace X :=
  d.surjective.pathConnectedSpace d.continuous

/-- A full-lattice exponential has connected target. -/
theorem target_isConnected
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    IsConnected (Set.univ : Set X) := by
  letI : PathConnectedSpace X := d.targetPathConnectedSpace
  exact isConnected_univ

/-- The arbitrary tangent-space exponential is an open quotient map.

The coordinate equivalence supplies the finite-dimensional instance needed by
the topological-group open mapping theorem; compactness of the target supplies
local compactness on the codomain.
-/
theorem isOpenQuotientMap
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) :
    IsOpenQuotientMap d.exponential := by
  letI : FiniteDimensional ℂ V :=
    FiniteDimensional.of_injective d.coordinate.toLinearEquiv.toLinearMap
      d.coordinate.injective
  letI : CompactSpace X := d.targetCompactSpace
  rw [isOpenQuotientMap_iff]
  exact ⟨d.surjective, d.continuous,
    AddMonoidHom.isOpenMap_of_sigmaCompact d.exponential d.surjective d.continuous⟩

/-- The quotient by the ambient period lattice is homeomorphic to the target. -/
noncomputable def quotientHomeomorph
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) :
    V ⧸ d.ambientPeriodLattice ≃ₜ X :=
  d.toPeriodLatticeQuotient.quotientHomeomorph d.isOpenQuotientMap

@[simp]
theorem quotientHomeomorph_mk
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.quotientHomeomorph
        (QuotientAddGroup.mk' d.ambientPeriodLattice v) =
      d.exponential v :=
  PeriodLatticeQuotient.quotientHomeomorph_mk
    d.toPeriodLatticeQuotient d.isOpenQuotientMap v

/-- The inverse quotient homeomorphism recovers an exponential representative. -/
theorem quotientHomeomorph_symm_exponential
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.quotientHomeomorph.symm (d.exponential v) =
      QuotientAddGroup.mk' d.ambientPeriodLattice v := by
  rw [← d.quotientHomeomorph_mk v]
  exact d.quotientHomeomorph.symm_apply_apply _

/-- The topological quotient identification agrees with the additive one. -/
theorem quotientHomeomorph_eq_quotientAddEquiv
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g)
    (q : V ⧸ d.ambientPeriodLattice) :
    d.quotientHomeomorph q = d.quotientAddEquiv q := by
  refine QuotientAddGroup.induction_on q ?_
  intro v
  change d.quotientHomeomorph
      (QuotientAddGroup.mk' d.ambientPeriodLattice v) =
    d.quotientAddEquiv (QuotientAddGroup.mk' d.ambientPeriodLattice v)
  rw [d.quotientHomeomorph_mk, d.quotientAddEquiv_mk]

/-- The arbitrary tangent quotient is topologically identified with the
canonical standard-coordinate quotient. -/
noncomputable def quotientCoordinateHomeomorph
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) :
    (V ⧸ d.ambientPeriodLattice) ≃ₜ
      (GenusComplexVector g ⧸ d.periodLattice.toAddSubgroup) :=
  d.quotientHomeomorph.trans d.toCanonical.quotientHomeomorph.symm

@[simp]
theorem quotientCoordinateHomeomorph_mk
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.quotientCoordinateHomeomorph
      (QuotientAddGroup.mk' d.ambientPeriodLattice v) =
      QuotientAddGroup.mk' d.periodLattice.toAddSubgroup (d.coordinate v) := by
  change d.toCanonical.quotientHomeomorph.symm
      (d.quotientHomeomorph
        (QuotientAddGroup.mk' d.ambientPeriodLattice v)) = _
  rw [d.quotientHomeomorph_mk]
  have hcoord : d.canonicalExponential (d.coordinate v) = d.exponential v := by
    simp [canonicalExponential]
  rw [← hcoord]
  exact d.toCanonical.quotientHomeomorph_symm_exponential (d.coordinate v)

/-- The coordinate quotient homeomorphism has the same underlying map as the
coordinate additive equivalence. -/
theorem quotientCoordinateHomeomorph_eq_quotientCoordinateAddEquiv
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g)
    (q : V ⧸ d.ambientPeriodLattice) :
    d.quotientCoordinateHomeomorph q =
      d.quotientCoordinateAddEquiv q := by
  refine QuotientAddGroup.induction_on q ?_
  intro v
  change d.quotientCoordinateHomeomorph
      (QuotientAddGroup.mk' d.ambientPeriodLattice v) =
    d.quotientCoordinateAddEquiv
      (QuotientAddGroup.mk' d.ambientPeriodLattice v)
  rw [d.quotientCoordinateHomeomorph_mk,
    d.quotientCoordinateAddEquiv_mk]

/-- The arbitrary tangent-space exponential is a covering map when the target
is a Hausdorff topological additive group. -/
theorem exponential_isAddQuotientCoveringMap
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) :
    IsAddQuotientCoveringMap d.exponential d.ambientPeriodLattice := by
  have hdisc : IsDiscrete (d.exponential.ker : Set V) := by
    rw [d.exponential_ker]
    exact d.ambientPeriodLattice_isDiscrete
  have h := d.isOpenQuotientMap.isQuotientMap
    |>.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom hdisc
  rw [d.exponential_ker] at h
  exact h

/-- The covering-map form of the arbitrary tangent-space exponential. -/
theorem exponential_isCoveringMap
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) :
    IsCoveringMap d.exponential :=
  d.exponential_isAddQuotientCoveringMap.isCoveringMap

/- A covering map supplies the local-homeomorphism interface needed by the
   quotient charts, without asserting any additional holomorphic structure. -/
theorem exponential_isLocalHomeomorph
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    {g : ℕ} (d : ComplexVectorLatticeExponentialData V X g) :
    IsLocalHomeomorph d.exponential :=
  d.exponential_isCoveringMap.isLocalHomeomorph

end ComplexVectorLatticeExponentialData

end
end Uniformization
end Mumford
