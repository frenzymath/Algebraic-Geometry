/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Nilradicals and minimal primes

The Stacks Project repeatedly identifies vanishing on the whole spectrum
with the nilradical and describes radicals as intersections of primes.  These
wrappers keep those identities available under the Part 01 namespace.
-/

namespace StacksPart01

open Set

/-- The nilradical is the intersection of all prime ideals. -/
theorem nilradical_eq_iInf_primeSpectrum {R : Type*} [CommSemiring R] :
    nilradical R = ⨅ p : PrimeSpectrum R, p.asIdeal := by
  exact PrimeSpectrum.nilradical_eq_iInf

/-- The vanishing ideal of the whole spectrum is the nilradical. -/
theorem vanishingIdeal_univ_eq_nilradical {R : Type*} [CommSemiring R] :
    PrimeSpectrum.vanishingIdeal (Set.univ : Set (PrimeSpectrum R)) = nilradical R := by
  exact PrimeSpectrum.vanishingIdeal_univ

/-- The nilradical is contained in every prime ideal. -/
theorem nilradical_le_prime {R : Type*} [CommSemiring R]
    (P : Ideal R) [hP : P.IsPrime] : nilradical R ≤ P := by
  exact _root_.nilradical_le_prime P

/-- The radical of an ideal is the intersection of the prime ideals above it. -/
theorem radical_eq_sInf_prime {R : Type*} [CommSemiring R] (I : Ideal R) :
    I.radical = sInf {P : Ideal R | I ≤ P ∧ P.IsPrime} := by
  exact Ideal.radical_eq_sInf I

/-- The radical is the intersection of the minimal primes over an ideal. -/
theorem sInf_minimalPrimes_eq_radical {R : Type*} [CommSemiring R]
    {I : Ideal R} : sInf I.minimalPrimes = I.radical := by
  exact Ideal.sInf_minimalPrimes

/-- Every nontrivial ring has a minimal prime ideal (Stacks, Tag 00E0). -/
theorem minimal_prime_exists {R : Type*} [CommSemiring R] [Nontrivial R] :
    Nonempty ((⊥ : Ideal R).minimalPrimes) := by
  exact Ideal.nonempty_minimalPrimes bot_ne_top

end StacksPart01
