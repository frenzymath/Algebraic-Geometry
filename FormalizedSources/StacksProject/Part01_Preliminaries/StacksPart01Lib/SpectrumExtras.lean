/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import StacksPart01Lib.Spectrum
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Spectral.Basic

/-!
# Compact-open topology on affine spectra

The spectrum of a commutative semiring is spectral.  These declarations expose
the compact-open consequences used in the Stacks Project's topology lemma
(Tag 04PM) in the project's `IsQuasiCompact` terminology.
-/

namespace StacksPart01

open Set Topology

/-- The prime spectrum is a spectral space (Stacks, Tag 04PM). -/
theorem spectrum_spectralSpace {R : Type*} [CommSemiring R] :
    SpectralSpace (PrimeSpectrum R) := by
  infer_instance

/-- The prime spectrum is quasi-separated (the third assertion of Stacks,
Tag 04PM). -/
theorem spectrum_quasiSeparatedSpace {R : Type*} [CommSemiring R] :
    QuasiSeparatedSpace (PrimeSpectrum R) := by
  infer_instance

/-- Every standard open is both open and quasi-compact (Stacks, Tags 00E4 and
04PM). -/
theorem standardOpen_isOpen_and_quasiCompact {R : Type*} [CommSemiring R] (f : R) :
    IsOpen (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∧
      IsQuasiCompact (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  exact ⟨PrimeSpectrum.isOpen_basicOpen, PrimeSpectrum.isCompact_basicOpen f⟩

/-- Intersections of quasi-compact opens in an affine spectrum are
quasi-compact (Stacks, Tag 04PM). -/
theorem quasiCompactOpen_inter_quasiCompactOpen {R : Type*} [CommSemiring R]
    {U V : Set (PrimeSpectrum R)} (hUopen : IsOpen U)
    (hUcompact : IsQuasiCompact U) (hVopen : IsOpen V)
    (hVcompact : IsQuasiCompact V) :
    IsQuasiCompact (U ∩ V) := by
  exact IsCompact.inter_of_isOpen hUcompact hVcompact hUopen hVopen

/-- In particular, the intersection of two standard opens is quasi-compact. -/
theorem standardOpen_inter_quasiCompact {R : Type*} [CommSemiring R] (f g : R) :
    IsQuasiCompact
      ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R))) := by
  exact quasiCompactOpen_inter_quasiCompactOpen
    PrimeSpectrum.isOpen_basicOpen (PrimeSpectrum.isCompact_basicOpen f)
    PrimeSpectrum.isOpen_basicOpen (PrimeSpectrum.isCompact_basicOpen g)

end StacksPart01
