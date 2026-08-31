/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.QuotientTopology

/-!
# Topology transported by uniformization

The standard genus torus is compact, connected, and path connected.  A
uniformization whose equivalence and inverse are continuous therefore
transports these properties to the uniformized topological group.  When the
source is compact, continuity of the inverse follows from continuity of the
equivalence because the target is Hausdorff.
-/

namespace Mumford
namespace Uniformization

noncomputable section

/-- Upgrade a genus-torus additive uniformization to a homeomorphism. -/
def GenusTorusUniformization.toHomeomorph
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    X ≃ₜ GenusTorus g :=
  { toEquiv := u.equiv.toEquiv
    continuous_toFun := hcont
    continuous_invFun := hcont_symm }

@[simp]
theorem GenusTorusUniformization.toHomeomorph_apply
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) (x : X) :
    u.toHomeomorph hcont hcont_symm x = u.equiv x :=
  rfl

/-- Upgrade a genus-torus additive uniformization from a compact source to a
homeomorphism; continuity of the inverse follows from the Hausdorff target. -/
def GenusTorusUniformization.toHomeomorph_of_compact
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [CompactSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv) :
    X ≃ₜ GenusTorus g :=
  Continuous.homeoOfEquivCompactToT2 (f := u.equiv.toEquiv) hcont

@[simp]
theorem GenusTorusUniformization.toHomeomorph_of_compact_apply
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [CompactSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv) (x : X) :
    u.toHomeomorph_of_compact hcont x = u.equiv x :=
  rfl

theorem GenusTorusUniformization.toHomeomorph_of_compact_eq_toHomeomorph
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [CompactSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    u.toHomeomorph_of_compact hcont = u.toHomeomorph hcont hcont_symm :=
  Homeomorph.ext fun _ => rfl

/-- Upgrade a complex-torus additive uniformization from a compact source to a
homeomorphism; continuity of the inverse follows from the Hausdorff target. -/
def ComplexTorusUniformization.toHomeomorph_of_compact
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [CompactSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv) :
    X ≃ₜ (GenusComplexVector g ⧸ complexPeriodLattice g) :=
  Continuous.homeoOfEquivCompactToT2 (f := u.equiv.toEquiv) hcont

@[simp]
theorem ComplexTorusUniformization.toHomeomorph_of_compact_apply
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [CompactSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv) (x : X) :
    u.toHomeomorph_of_compact hcont x = u.equiv x :=
  rfl

theorem ComplexTorusUniformization.toHomeomorph_of_compact_eq_toHomeomorph
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [CompactSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    u.toHomeomorph_of_compact hcont = u.toHomeomorph hcont hcont_symm :=
  Homeomorph.ext fun _ => rfl

/- Compactness of arbitrary subsets is invariant under an explicit topological
   uniformization.  The continuity assumptions remain visible because the
   additive equivalence alone does not determine the topology. -/
theorem genusTorusUniformization_isCompact_image_iff
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm)
    (s : Set X) :
    IsCompact (u.equiv '' s) ↔ IsCompact s := by
  exact (u.toHomeomorph hcont hcont_symm).isCompact_image

/- The same subset-level compactness transport for a complex period-quotient
   witness, expressed through its canonical real-torus model. -/
theorem complexTorusUniformization_isCompact_image_iff
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm)
    (s : Set X) :
    IsCompact (u.toGenusTorusUniformization.equiv '' s) ↔ IsCompact s := by
  simpa only [ComplexTorusUniformization.toGenusTorusHomeomorph_apply] using
    ((u.toGenusTorusHomeomorph hcont hcont_symm).isCompact_image (s := s))

theorem isCompact_of_genusTorusHomeomorph
    {X : Type*} [TopologicalSpace X] {g : ℕ}
    (e : X ≃ₜ GenusTorus g) :
    IsCompact (Set.univ : Set X) := by
  have h := e.isCompact_preimage (s := (Set.univ : Set (GenusTorus g)))
  simpa using h.mpr (genusTorus_isCompact g)

theorem t2Space_of_genusTorusHomeomorph
    {X : Type*} [TopologicalSpace X] {g : ℕ}
    (e : X ≃ₜ GenusTorus g) : T2Space X :=
  e.symm.t2Space

theorem isConnected_of_genusTorusHomeomorph
    {X : Type*} [TopologicalSpace X] {g : ℕ}
    (e : X ≃ₜ GenusTorus g) :
    IsConnected (Set.univ : Set X) := by
  have h := e.isConnected_preimage (s := (Set.univ : Set (GenusTorus g)))
  simpa using h.mpr (genusTorus_isConnected g)

theorem isPathConnected_of_genusTorusHomeomorph
    {X : Type*} [TopologicalSpace X] {g : ℕ}
    (e : X ≃ₜ GenusTorus g) :
    IsPathConnected (Set.univ : Set X) := by
  letI : PathConnectedSpace (GenusTorus g) := genusTorus_isPathConnected g
  have h := e.isPathConnected_preimage (s := (Set.univ : Set (GenusTorus g)))
  simpa using h.mpr (isPathConnected_univ :
    IsPathConnected (Set.univ : Set (GenusTorus g)))

theorem nonempty_of_genusTorusHomeomorph
    {X : Type*} [TopologicalSpace X] {g : ℕ}
    (e : X ≃ₜ GenusTorus g) :
    Nonempty X := by
  rcases (isConnected_of_genusTorusHomeomorph e).nonempty with ⟨x, hx⟩
  exact ⟨x⟩

/-- The compact-space instance obtained from a topological uniformization. -/
@[reducible]
def compactSpace_of_genusTorusHomeomorph
    {X : Type*} [TopologicalSpace X] {g : ℕ}
    (e : X ≃ₜ GenusTorus g) : CompactSpace X :=
  ⟨isCompact_of_genusTorusHomeomorph e⟩

/-- The connected-space instance obtained from a topological uniformization. -/
@[reducible]
def connectedSpace_of_genusTorusHomeomorph
    {X : Type*} [TopologicalSpace X] {g : ℕ}
    (e : X ≃ₜ GenusTorus g) : ConnectedSpace X :=
  (connectedSpace_iff_univ).2 (isConnected_of_genusTorusHomeomorph e)

/-- The path-connected-space instance obtained from a topological uniformization. -/
@[reducible]
def pathConnectedSpace_of_genusTorusHomeomorph
  {X : Type*} [TopologicalSpace X] {g : ℕ}
    (e : X ≃ₜ GenusTorus g) : PathConnectedSpace X := by
  letI : PathConnectedSpace (GenusTorus g) := genusTorus_isPathConnected g
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous

/-- The locally compact space instance obtained from a topological
uniformization. -/
@[reducible]
def locallyCompactSpace_of_genusTorusHomeomorph
    {X : Type*} [TopologicalSpace X] {g : ℕ}
    (e : X ≃ₜ GenusTorus g) : LocallyCompactSpace X := by
  exact e.locallyCompactSpace_iff.mpr inferInstance

/-! The same bridge stated directly for the two uniformization interfaces. -/

theorem genusTorusUniformization_isCompact
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    IsCompact (Set.univ : Set X) :=
  isCompact_of_genusTorusHomeomorph (u.toHomeomorph hcont hcont_symm)

theorem genusTorusUniformization_isT2
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : T2Space X :=
  t2Space_of_genusTorusHomeomorph (u.toHomeomorph hcont hcont_symm)

theorem genusTorusUniformization_isConnected
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    IsConnected (Set.univ : Set X) :=
  isConnected_of_genusTorusHomeomorph (u.toHomeomorph hcont hcont_symm)

theorem genusTorusUniformization_isPathConnected
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    IsPathConnected (Set.univ : Set X) :=
  isPathConnected_of_genusTorusHomeomorph (u.toHomeomorph hcont hcont_symm)

theorem genusTorusUniformization_nonempty
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    Nonempty X :=
  nonempty_of_genusTorusHomeomorph (u.toHomeomorph hcont hcont_symm)

theorem complexTorusUniformization_isCompact
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    IsCompact (Set.univ : Set X) :=
  isCompact_of_genusTorusHomeomorph (u.toGenusTorusHomeomorph hcont hcont_symm)

theorem complexTorusUniformization_isT2
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : T2Space X :=
  t2Space_of_genusTorusHomeomorph (u.toGenusTorusHomeomorph hcont hcont_symm)

theorem complexTorusUniformization_isConnected
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    IsConnected (Set.univ : Set X) :=
  isConnected_of_genusTorusHomeomorph (u.toGenusTorusHomeomorph hcont hcont_symm)

theorem complexTorusUniformization_isPathConnected
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    IsPathConnected (Set.univ : Set X) :=
  isPathConnected_of_genusTorusHomeomorph (u.toGenusTorusHomeomorph hcont hcont_symm)

theorem complexTorusUniformization_nonempty
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    Nonempty X :=
  nonempty_of_genusTorusHomeomorph (u.toGenusTorusHomeomorph hcont hcont_symm)

@[reducible]
def compactSpace_of_genusTorusUniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : CompactSpace X :=
  ⟨genusTorusUniformization_isCompact u hcont hcont_symm⟩

@[reducible]
def connectedSpace_of_genusTorusUniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : ConnectedSpace X :=
  (connectedSpace_iff_univ).2 (genusTorusUniformization_isConnected u hcont hcont_symm)

@[reducible]
def pathConnectedSpace_of_genusTorusUniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : PathConnectedSpace X := by
  exact pathConnectedSpace_of_genusTorusHomeomorph (u.toHomeomorph hcont hcont_symm)

@[reducible]
def locallyCompactSpace_of_genusTorusUniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : GenusTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : LocallyCompactSpace X :=
  locallyCompactSpace_of_genusTorusHomeomorph
    (u.toHomeomorph hcont hcont_symm)

@[reducible]
def compactSpace_of_complexTorusUniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : CompactSpace X :=
  ⟨complexTorusUniformization_isCompact u hcont hcont_symm⟩

@[reducible]
def connectedSpace_of_complexTorusUniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : ConnectedSpace X :=
  (connectedSpace_iff_univ).2 (complexTorusUniformization_isConnected u hcont hcont_symm)

@[reducible]
def pathConnectedSpace_of_complexTorusUniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : PathConnectedSpace X := by
  exact pathConnectedSpace_of_genusTorusHomeomorph
    (u.toGenusTorusHomeomorph hcont hcont_symm)

@[reducible]
def locallyCompactSpace_of_complexTorusUniformization
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : LocallyCompactSpace X :=
  locallyCompactSpace_of_genusTorusHomeomorph
    (u.toGenusTorusHomeomorph hcont hcont_symm)

end
end Uniformization
end Mumford
