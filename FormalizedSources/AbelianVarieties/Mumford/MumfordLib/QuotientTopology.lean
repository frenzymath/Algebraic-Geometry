/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ComplexUniformization

/-!
# Topology of the standard period quotients

The real and complex period quotients inherit the elementary topology of the
finite product of unit additive circles through the homeomorphisms constructed
in `ComplexUniformization` and `ComplexModel`.
-/

namespace Mumford
namespace Uniformization

noncomputable section

/- The finite product torus is compact by the compactness of the unit circle. -/
theorem genusTorus_isCompact (g : ℕ) :
    IsCompact (Set.univ : Set (GenusTorus g)) := by
  change IsCompact (Set.univ : Set (Fin (2 * g) → UnitAddCircle))
  simpa only [Set.pi_univ] using
    (isCompact_univ_pi
      (X := fun _ : Fin (2 * g) => UnitAddCircle)
      (s := fun _ => (Set.univ : Set UnitAddCircle))
      (fun _ => isCompact_univ))

/- Compactness transported across the standard real quotient homeomorphism. -/
theorem genusRealVectorQuotient_isCompact (g : ℕ) :
    IsCompact
      (Set.univ : Set (GenusRealVector g ⧸ integerPeriodLattice g)) := by
  have h := (genusRealVectorQuotientHomeomorph g).symm.isCompact_preimage
    (s := (Set.univ : Set (GenusRealVector g ⧸ integerPeriodLattice g)))
  simpa using h.mp (genusTorus_isCompact g)

/- Compactness transported across the complex-to-real quotient homeomorphism. -/
theorem complexGenusQuotient_isCompact (g : ℕ) :
    IsCompact
      (Set.univ : Set (GenusComplexVector g ⧸ complexPeriodLattice g)) := by
  have h := (complexQuotientToRealQuotientHomeomorph g).isCompact_preimage
    (s := (Set.univ : Set (GenusRealVector g ⧸ integerPeriodLattice g)))
  simpa using h.mpr (genusRealVectorQuotient_isCompact g)

/- Connectedness transported across the standard real quotient homeomorphism. -/
theorem genusRealVectorQuotient_isConnected (g : ℕ) :
    IsConnected
      (Set.univ : Set (GenusRealVector g ⧸ integerPeriodLattice g)) := by
  have h := (genusRealVectorQuotientHomeomorph g).isConnected_preimage
    (s := (Set.univ : Set (GenusTorus g)))
  simpa using h.mpr (genusTorus_isConnected g)

/- Connectedness transported across the complex-to-real quotient homeomorphism. -/
theorem complexGenusQuotient_isConnected (g : ℕ) :
    IsConnected
      (Set.univ : Set (GenusComplexVector g ⧸ complexPeriodLattice g)) := by
  have h := (complexQuotientToRealQuotientHomeomorph g).isConnected_preimage
    (s := (Set.univ : Set (GenusRealVector g ⧸ integerPeriodLattice g)))
  simpa using h.mpr (genusRealVectorQuotient_isConnected g)

/- Path connectedness transported across the standard real quotient homeomorphism. -/
theorem genusRealVectorQuotient_isPathConnected (g : ℕ) :
    IsPathConnected
      (Set.univ : Set (GenusRealVector g ⧸ integerPeriodLattice g)) := by
  letI : PathConnectedSpace (GenusTorus g) := genusTorus_isPathConnected g
  have h := (genusRealVectorQuotientHomeomorph g).isPathConnected_preimage
    (s := (Set.univ : Set (GenusTorus g)))
  simpa using h.mpr (isPathConnected_univ :
    IsPathConnected (Set.univ : Set (GenusTorus g)))

/- Path connectedness transported across the complex-to-real quotient homeomorphism. -/
theorem complexGenusQuotient_isPathConnected (g : ℕ) :
    IsPathConnected
      (Set.univ : Set (GenusComplexVector g ⧸ complexPeriodLattice g)) := by
  have h := (complexQuotientToRealQuotientHomeomorph g).isPathConnected_preimage
    (s := (Set.univ : Set (GenusRealVector g ⧸ integerPeriodLattice g)))
  simpa using h.mpr (genusRealVectorQuotient_isPathConnected g)

/- The corresponding spaces are nonempty as a direct consequence of the
   preceding compact/connected/path-connected statements. -/
theorem genusRealVectorQuotient_nonempty (g : ℕ) :
    Nonempty (GenusRealVector g ⧸ integerPeriodLattice g) := by
  rcases (genusRealVectorQuotient_isConnected g).1 with ⟨x, _⟩
  exact ⟨x⟩

theorem complexGenusQuotient_nonempty (g : ℕ) :
    Nonempty (GenusComplexVector g ⧸ complexPeriodLattice g) := by
  rcases (complexGenusQuotient_isConnected g).1 with ⟨x, _⟩
  exact ⟨x⟩

/- Typeclass forms make the quotient topology available to downstream lemmas. -/
instance genusRealVectorQuotient_compactSpace (g : ℕ) :
    CompactSpace (GenusRealVector g ⧸ integerPeriodLattice g) :=
  ⟨genusRealVectorQuotient_isCompact g⟩

instance complexGenusQuotient_compactSpace (g : ℕ) :
    CompactSpace (GenusComplexVector g ⧸ complexPeriodLattice g) :=
  ⟨complexGenusQuotient_isCompact g⟩

/- The quotient spaces are Hausdorff because they are homeomorphic to the
   finite product of Hausdorff additive circles. -/
instance genusRealVectorQuotient_t2Space (g : ℕ) :
    T2Space (GenusRealVector g ⧸ integerPeriodLattice g) :=
  (genusRealVectorQuotientHomeomorph g).symm.t2Space

instance complexGenusQuotient_t2Space (g : ℕ) :
    T2Space (GenusComplexVector g ⧸ complexPeriodLattice g) := by
  letI : T2Space (GenusRealVector g ⧸ integerPeriodLattice g) :=
    (genusRealVectorQuotientHomeomorph g).symm.t2Space
  exact (complexQuotientToRealQuotientHomeomorph g).symm.t2Space

theorem genusRealVectorQuotient_isClosed_of_isCompact
    {g : ℕ} {s : Set (GenusRealVector g ⧸ integerPeriodLattice g)}
    (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

theorem complexGenusQuotient_isClosed_of_isCompact
    {g : ℕ} {s : Set (GenusComplexVector g ⧸ complexPeriodLattice g)}
    (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

instance genusRealVectorQuotient_connectedSpace (g : ℕ) :
    ConnectedSpace (GenusRealVector g ⧸ integerPeriodLattice g) :=
  (connectedSpace_iff_univ).2 (genusRealVectorQuotient_isConnected g)

instance complexGenusQuotient_connectedSpace (g : ℕ) :
    ConnectedSpace (GenusComplexVector g ⧸ complexPeriodLattice g) :=
  (connectedSpace_iff_univ).2 (complexGenusQuotient_isConnected g)

instance genusRealVectorQuotient_pathConnectedSpace (g : ℕ) :
    PathConnectedSpace (GenusRealVector g ⧸ integerPeriodLattice g) :=
  by
    letI : PathConnectedSpace (GenusTorus g) := genusTorus_isPathConnected g
    exact (genusRealVectorQuotientHomeomorph g).symm.surjective.pathConnectedSpace
      (genusRealVectorQuotientHomeomorph g).symm.continuous

instance complexGenusQuotient_pathConnectedSpace (g : ℕ) :
    PathConnectedSpace (GenusComplexVector g ⧸ complexPeriodLattice g) :=
  by
    exact (complexQuotientToRealQuotientHomeomorph g).symm.surjective.pathConnectedSpace
      (complexQuotientToRealQuotientHomeomorph g).symm.continuous

end
end Uniformization
end Mumford
