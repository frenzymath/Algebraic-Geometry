/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ComplexLattice

/-!
# A coordinate-free boundary for complex lattice uniformization

The analytic statement starts with a lattice in an arbitrary finite-dimensional
complex tangent space.  `ComplexVectorLatticeExponentialData` records that
input together with an explicit continuous complex-linear coordinate to the
standard genus model.  The coordinate is used only to transport the lattice;
the structure itself still exposes the original tangent space and exponential.

This is an additive/continuous interface.  It deliberately does not assert a
holomorphic or complex-manifold structure, so the analytic existence boundary
of the blueprint remains visible.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

/-- An exponential from an arbitrary complex tangent model with a full period
lattice.  The lattice is stored in standard genus coordinates, and its inverse
image under `coordinate` is the period subgroup in `V`. -/
structure ComplexVectorLatticeExponentialData
    (V X : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] (g : ℕ) where
  /-- A continuous complex-linear coordinate on the tangent space. -/
  coordinate : V ≃L[ℂ] GenusComplexVector g
  /-- The full integral lattice in the standard coordinates. -/
  periodLattice : Submodule ℤ (GenusComplexVector g)
  /-- The lattice is discrete in its subtype topology. -/
  [periodLatticeDiscrete : DiscreteTopology periodLattice]
  /-- The lattice spans the underlying real tangent space. -/
  [periodLatticeFull : IsZLattice ℝ periodLattice]
  /-- The additive exponential from the chosen tangent space. -/
  exponential : V →+ X
  /-- The exponential reaches every target point. -/
  surjective : Function.Surjective exponential
  /-- The exponential is continuous. -/
  continuous : Continuous exponential
  /-- Its kernel is the lattice transported back to `V`. -/
  kernel : exponential.ker =
    (periodLattice.comap
      (coordinate.toLinearEquiv.restrictScalars ℤ).toLinearMap).toAddSubgroup

namespace ComplexVectorLatticeExponentialData

/-- The period subgroup in the original tangent-space coordinates. -/
def ambientPeriodLattice
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) : AddSubgroup V :=
  (d.periodLattice.comap
    (d.coordinate.toLinearEquiv.restrictScalars ℤ).toLinearMap).toAddSubgroup

@[simp]
theorem ambientPeriodLattice_mem_iff
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    v ∈ d.ambientPeriodLattice ↔ d.coordinate v ∈ d.periodLattice := by
  simp [ambientPeriodLattice]

/-- The kernel field in terms of the named ambient period subgroup. -/
theorem exponential_ker
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    d.exponential.ker = d.ambientPeriodLattice :=
  d.kernel

/-- The additive quotient certificate carried by the arbitrary tangent model. -/
def toPeriodLatticeQuotient
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    PeriodLatticeQuotient V X where
  periodLattice := d.ambientPeriodLattice
  exponential := d.exponential
  exponential_surjective := d.surjective
  kernel_exponential := d.exponential_ker

/-- The first-isomorphism quotient equivalence for the ambient tangent model. -/
def quotientAddEquiv
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    V ⧸ d.ambientPeriodLattice ≃+ X :=
  d.toPeriodLatticeQuotient.quotientAddEquiv

@[simp]
theorem quotientAddEquiv_mk
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.quotientAddEquiv (QuotientAddGroup.mk' d.ambientPeriodLattice v) =
      d.exponential v :=
  PeriodLatticeQuotient.quotientAddEquiv_mk d.toPeriodLatticeQuotient v

/-- The same exponential expressed in the standard genus coordinates. -/
def canonicalExponential
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    GenusComplexVector g →+ X :=
  d.exponential.comp d.coordinate.symm.toAddEquiv.toAddMonoidHom

@[simp]
theorem canonicalExponential_apply
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g)
    (z : GenusComplexVector g) :
    d.canonicalExponential z = d.exponential (d.coordinate.symm z) :=
  rfl

/-- Surjectivity is preserved when the tangent coordinates are changed. -/
theorem canonicalExponential_surjective
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    Function.Surjective d.canonicalExponential := by
  intro x
  obtain ⟨v, hv⟩ := d.surjective x
  exact ⟨d.coordinate v, by
    change d.exponential (d.coordinate.symm (d.coordinate v)) = x
    simpa using hv⟩

/-- Continuity is preserved when the tangent coordinates are changed. -/
theorem canonicalExponential_continuous
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    Continuous d.canonicalExponential :=
  d.continuous.comp d.coordinate.symm.continuous

/-- The normalized exponential has exactly the stored standard period lattice. -/
theorem canonicalExponential_kernel
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    d.canonicalExponential.ker = d.periodLattice.toAddSubgroup := by
  ext z
  change d.exponential (d.coordinate.symm z) = 0 ↔ z ∈ d.periodLattice
  rw [← AddMonoidHom.mem_ker, d.kernel]
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_comap]
  simp

/-- Forgetting the arbitrary tangent coordinates recovers the fixed-coordinate
`ComplexLatticeExponentialData` interface. -/
def toCanonical
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    ComplexLatticeExponentialData X g where
  periodLattice := d.periodLattice
  periodLatticeDiscrete := d.periodLatticeDiscrete
  periodLatticeFull := d.periodLatticeFull
  exponential := d.canonicalExponential
  surjective := d.canonicalExponential_surjective
  continuous := d.canonicalExponential_continuous
  kernel := d.canonicalExponential_kernel

/-- Torsion cardinality for an arbitrary tangent-space lattice, once the target
has a genus-torus uniformization. -/
theorem quotientTorsion_card_of_uniformization
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g)
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0) :
    Nat.card (zsmulTorsionSubgroup (V ⧸ d.ambientPeriodLattice) n) =
      n.natAbs ^ (2 * g) := by
  calc
    Nat.card (zsmulTorsionSubgroup (V ⧸ d.ambientPeriodLattice) n) =
        Nat.card (zsmulTorsionSubgroup X n) :=
      zsmulTorsion_card_eq_of_addEquiv d.quotientAddEquiv n
    _ = n.natAbs ^ (2 * g) :=
      zsmulTorsion_card_of_uniformization u hn

/-- The corresponding finite-torsion consequence for the ambient quotient. -/
theorem quotientTorsion_finite_of_uniformization
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g)
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0) :
    Finite (zsmulTorsionSubgroup (V ⧸ d.ambientPeriodLattice) n) := by
  exact (zsmulTorsion_addEquiv_of_addEquiv d.quotientAddEquiv n).toEquiv.finite_iff.mpr
    (zsmulTorsion_finite_of_uniformization u hn)

end ComplexVectorLatticeExponentialData

end
end Uniformization
end Mumford
