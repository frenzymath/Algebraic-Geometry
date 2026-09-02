/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import StacksPart01Lib.Spectrum

/-!
# Irreducible subsets of affine spectra

This module exposes the correspondence between prime ideals and irreducible
closed subsets of an affine spectrum (Stacks, Tag 00ES).
-/

namespace StacksPart01

open Set Topology

/-- The closure of a prime ideal in the Zariski topology is its zero locus
(Stacks, Tag 00ES, part (1)). -/
theorem spectrum_closure_singleton {R : Type*} [CommSemiring R]
    (p : PrimeSpectrum R) :
    closure ({p} : Set (PrimeSpectrum R)) =
      PrimeSpectrum.zeroLocus (p.asIdeal : Set R) := by
  exact PrimeSpectrum.closure_singleton p

/-- Every irreducible closed subset of an affine spectrum is the zero locus
of a prime ideal (Stacks, Tag 00ES, part (2)). -/
theorem irreducible_closed_eq_zeroLocus_prime {R : Type*} [CommSemiring R]
    {Z : Set (PrimeSpectrum R)} (hZ : IsClosed Z) (hZirr : IsIrreducible Z) :
    ∃ p : PrimeSpectrum R,
      Z = PrimeSpectrum.zeroLocus (p.asIdeal : Set R) := by
  let p : PrimeSpectrum R :=
    ⟨PrimeSpectrum.vanishingIdeal Z,
      PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hZirr⟩
  refine ⟨p, ?_⟩
  change Z = PrimeSpectrum.zeroLocus
    (PrimeSpectrum.vanishingIdeal Z : Set R)
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq]

/-- Minimal prime ideals are order-equivalent to irreducible components of
the affine spectrum, with the order reversed (Stacks, Tag 00ES, part (3)). -/
noncomputable def minimalPrimesEquivIrreducibleComponents
    {R : Type*} [CommSemiring R] :
    minimalPrimes R ≃o
      (irreducibleComponents (PrimeSpectrum R))ᵒᵈ :=
  minimalPrimes.equivIrreducibleComponents R

end StacksPart01
