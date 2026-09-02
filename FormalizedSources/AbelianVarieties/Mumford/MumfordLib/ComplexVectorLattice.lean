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

/-- The integral period lattice in the original tangent-space coordinates. -/
def ambientPeriodLatticeSubmodule
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) : Submodule ℤ V :=
  d.periodLattice.comap
    (d.coordinate.toLinearEquiv.restrictScalars ℤ).toLinearMap

/-- The named transported lattice inherits the discrete subtype topology from
the stored standard-coordinate lattice. -/
instance ambientPeriodLatticeSubmodule_discreteTopology
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    DiscreteTopology d.ambientPeriodLatticeSubmodule := by
  letI : DiscreteTopology d.periodLattice := d.periodLatticeDiscrete
  exact instDiscreteTopologySubtypeMemSubmoduleIntComap ℂ d.periodLattice d.coordinate

/-- The period subgroup in the original tangent-space coordinates. -/
def ambientPeriodLattice
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) : AddSubgroup V :=
  d.ambientPeriodLatticeSubmodule.toAddSubgroup

theorem ambientPeriodLatticeSubmodule_toAddSubgroup
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    d.ambientPeriodLatticeSubmodule.toAddSubgroup = d.ambientPeriodLattice :=
  rfl

@[simp]
theorem ambientPeriodLattice_mem_iff
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    v ∈ d.ambientPeriodLattice ↔ d.coordinate v ∈ d.periodLattice := by
  simp [ambientPeriodLattice, ambientPeriodLatticeSubmodule]

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

/-- A representative in the arbitrary tangent quotient is torsion exactly
    when its scalar multiple lies in the transported period lattice. -/
theorem quotient_mk_mem_zsmulTorsion_iff
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (n : ℤ) (v : V) :
    QuotientAddGroup.mk' d.ambientPeriodLattice v ∈
        zsmulTorsionSubgroup (V ⧸ d.ambientPeriodLattice) n ↔
      n • v ∈ d.ambientPeriodLattice := by
  exact PeriodLatticeQuotient.quotient_mk_mem_zsmulTorsion_iff
    d.ambientPeriodLattice n v

@[simp]
theorem exponential_eq_zero_iff_mem_ambientPeriodLattice
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v : V) :
    d.exponential v = 0 ↔ v ∈ d.ambientPeriodLattice := by
  rw [← AddMonoidHom.mem_ker, d.exponential_ker]

/- Two tangent representatives have the same exponential image exactly when
   their difference is an ambient period.  This is the coordinate-free form
   of the quotient representative criterion and is useful on overlaps of
   local exponential branches. -/
theorem exponential_eq_iff_sub_mem_ambientPeriodLattice
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) (v w : V) :
    d.exponential v = d.exponential w ↔
      v - w ∈ d.ambientPeriodLattice := by
  constructor
  · intro h
    have hz : d.exponential (v - w) = 0 := by
      rw [map_sub, h, sub_self]
    exact d.exponential_eq_zero_iff_mem_ambientPeriodLattice (v - w) |>.1 hz
  · intro h
    have hz : d.exponential (v - w) = 0 :=
      d.exponential_eq_zero_iff_mem_ambientPeriodLattice (v - w) |>.2 h
    have heq : d.exponential v - d.exponential w = 0 := by
      simpa only [map_sub] using hz
    exact sub_eq_zero.mp heq

/-- Signed-integer torsion in the arbitrary tangent quotient, transported
    through its exponential and a chosen genus-torus uniformization. -/
noncomputable def quotientTorsionAddEquiv_of_uniformization
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g)
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0) :
    zsmulTorsionSubgroup (V ⧸ d.ambientPeriodLattice) n ≃+
      (Fin (2 * g) → ZMod n.natAbs) :=
  (zsmulTorsion_addEquiv_of_addEquiv d.quotientAddEquiv n).trans
    (zsmulTorsion_addEquiv_of_uniformization u hn)

@[simp]
theorem quotientTorsionAddEquiv_of_uniformization_apply
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g)
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0)
    (q : zsmulTorsionSubgroup (V ⧸ d.ambientPeriodLattice) n) :
    (d.quotientTorsionAddEquiv_of_uniformization u hn) q =
      (zsmulTorsion_addEquiv_of_uniformization u hn)
        ((zsmulTorsion_addEquiv_of_addEquiv d.quotientAddEquiv n) q) := by
  rfl

/-- The positive-natural notation for the arbitrary tangent quotient torsion
    equivalence. -/
noncomputable def quotientTorsionAddEquiv_of_uniformization_natCast
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g n : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g)
    (u : GenusTorusUniformization X g) (hn : 0 < n) :
    zsmulTorsionSubgroup (V ⧸ d.ambientPeriodLattice) (n : ℤ) ≃+
      (Fin (2 * g) → ZMod n) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  let castEquiv : (Fin (2 * g) → ZMod (n : ℤ).natAbs) ≃+
      (Fin (2 * g) → ZMod n) :=
    AddEquiv.cast (M := fun m : ℕ => Fin (2 * g) → ZMod m)
      (Int.natAbs_ofNat' n)
  exact (d.quotientTorsionAddEquiv_of_uniformization u hne).trans castEquiv

/-- The arbitrary tangent quotient has the expected positive-natural torsion
    cardinality. -/
theorem quotientTorsion_card_of_uniformization_natCast
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g n : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g)
    (u : GenusTorusUniformization X g) (hn : 0 < n) :
    Nat.card (zsmulTorsionSubgroup (V ⧸ d.ambientPeriodLattice) (n : ℤ)) =
      n ^ (2 * g) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  rw [Nat.card_congr
    (d.quotientTorsionAddEquiv_of_uniformization u hne).toEquiv]
  simp [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]

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

/-- The transported period lattice has integral rank twice the complex
dimension of the tangent space. -/
theorem ambientPeriodLattice_finrank
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    Module.finrank ℤ d.ambientPeriodLatticeSubmodule = 2 * g := by
  let e : d.periodLattice ≃ₗ[ℤ] d.ambientPeriodLatticeSubmodule :=
    ZLattice.comap_equiv ℂ d.periodLattice d.coordinate.toLinearEquiv
  rw [← e.finrank_eq]
  exact d.toCanonical.periodLattice_finrank

/-- The transported period lattice spans the real tangent space. -/
theorem ambientPeriodLattice_isZLattice
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    IsZLattice ℝ d.ambientPeriodLatticeSubmodule := by
  letI : DiscreteTopology d.periodLattice := d.periodLatticeDiscrete
  letI : IsZLattice ℝ d.periodLattice := d.periodLatticeFull
  let e : V ≃ₗ[ℝ] GenusComplexVector g :=
    d.coordinate.toLinearEquiv.restrictScalars ℝ
  let ce : V ≃L[ℝ] GenusComplexVector g :=
    ContinuousLinearEquiv.mk e d.coordinate.continuous d.coordinate.symm.continuous
  let L : Submodule ℤ V := ZLattice.comap ℝ d.periodLattice ce.toLinearMap
  letI : DiscreteTopology L :=
    instDiscreteTopologySubtypeMemSubmoduleIntComap ℝ d.periodLattice ce
  have hL : IsZLattice ℝ L := instIsZLatticeComap ℝ d.periodLattice ce
  have hEq : d.ambientPeriodLatticeSubmodule = L := by
    ext v
    simp [ambientPeriodLatticeSubmodule, L, ce, e, ZLattice.comap]
  simpa only [hEq] using hL

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
