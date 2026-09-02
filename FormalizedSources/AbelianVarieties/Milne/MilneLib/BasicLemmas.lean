/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Basic affine dimension adapters

The underlying topological space of an affine scheme is the prime spectrum of
its coordinate ring.  These adapters keep that identification explicit when a
dimension argument moves between scheme and ring language.
-/

open AlgebraicGeometry

namespace MilneLib

/-- The Krull dimension of an affine scheme is the Krull dimension of its
coordinate ring. -/
theorem topologicalKrullDim_spec_eq_ringKrullDim
    (R : CommRingCat) :
    topologicalKrullDim (Spec R) = ringKrullDim ↑R := by
  change topologicalKrullDim (PrimeSpectrum ↑R) = ringKrullDim ↑R
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim ↑R

/-- The spectrum of a field is zero-dimensional. -/
theorem topologicalKrullDim_spec_of_field
    (K : Type*) [Field K] :
    topologicalKrullDim (Spec (CommRingCat.of K)) = 0 := by
  rw [topologicalKrullDim_spec_eq_ringKrullDim]
  exact ringKrullDim_eq_zero_of_field K

end MilneLib
