/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1CoordinateRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Hartshorne I.1/II.2: affine spectra

Mathlib's `PrimeSpectrum` is the set-theoretic affine spectrum.  This file
records the source-facing names for its closed and basic open sets, together
with the quotient-spectrum map attached to an affine coordinate ring.
-/

namespace Hartshorne

noncomputable section

/-! ### The affine spectrum and its closed sets -/

/-- The affine spectrum of a commutative semiring, viewed as its prime ideals. -/
abbrev AffineSpectrum (R : Type*) [CommSemiring R] := PrimeSpectrum R

/-- The closed subset `V(I)` of the affine spectrum. -/
def spectrumZeroLocus {R : Type*} [CommSemiring R] (I : Ideal R) :
    Set (AffineSpectrum R) :=
  PrimeSpectrum.zeroLocus (I : Set R)

@[simp]
theorem mem_spectrumZeroLocus {R : Type*} [CommSemiring R]
    (I : Ideal R) (p : AffineSpectrum R) :
    p ∈ spectrumZeroLocus I ↔ I ≤ p.asIdeal := by
  exact PrimeSpectrum.mem_zeroLocus p (I : Set R)

theorem spectrumZeroLocus_span {R : Type*} [CommSemiring R]
    (s : Set R) :
    spectrumZeroLocus (Ideal.span s) =
      PrimeSpectrum.zeroLocus s := by
  exact PrimeSpectrum.zeroLocus_span s

theorem spectrumZeroLocus_sup {R : Type*} [CommSemiring R]
    (I J : Ideal R) :
    spectrumZeroLocus (I ⊔ J) = spectrumZeroLocus I ∩ spectrumZeroLocus J := by
  exact PrimeSpectrum.zeroLocus_sup I J

theorem spectrumZeroLocus_iSup {R : Type*} [CommSemiring R] {ι : Sort*}
    (I : ι → Ideal R) :
    spectrumZeroLocus (⨆ i, I i) = ⋂ i, spectrumZeroLocus (I i) := by
  exact PrimeSpectrum.zeroLocus_iSup I

theorem spectrumZeroLocus_eq_iff {R : Type*} [CommSemiring R]
    {I J : Ideal R} :
    spectrumZeroLocus I = spectrumZeroLocus J ↔ I.radical = J.radical := by
  exact PrimeSpectrum.zeroLocus_eq_iff

theorem spectrumZeroLocus_mul {R : Type*} [CommRing R]
    (I J : Ideal R) :
    spectrumZeroLocus (I * J) = spectrumZeroLocus I ∪ spectrumZeroLocus J := by
  exact PrimeSpectrum.zeroLocus_mul I J

@[simp]
theorem spectrumZeroLocus_radical {R : Type*} [CommSemiring R]
    (I : Ideal R) :
    spectrumZeroLocus I.radical = spectrumZeroLocus I := by
  exact PrimeSpectrum.zeroLocus_radical I

/-! ### Basic opens -/

/-- The standard open `D(f)` in the affine spectrum. -/
abbrev spectrumBasicOpen {R : Type*} [CommSemiring R] (f : R) :
    TopologicalSpace.Opens (AffineSpectrum R) :=
  PrimeSpectrum.basicOpen f

@[simp]
theorem mem_spectrumBasicOpen {R : Type*} [CommSemiring R]
    (f : R) (p : AffineSpectrum R) :
    p ∈ spectrumBasicOpen f ↔ f ∉ p.asIdeal := by
  exact PrimeSpectrum.mem_basicOpen f p

theorem isOpen_spectrumBasicOpen {R : Type*} [CommSemiring R] (f : R) :
    IsOpen (spectrumBasicOpen f : Set (AffineSpectrum R)) := by
  exact PrimeSpectrum.isOpen_basicOpen

theorem spectrumBasicOpen_isTopologicalBasis {R : Type*} [CommSemiring R]
    : TopologicalSpace.IsTopologicalBasis
      (Set.range (fun f : R => (spectrumBasicOpen f : Set (AffineSpectrum R)))) := by
  exact PrimeSpectrum.isTopologicalBasis_basic_opens

@[simp]
theorem spectrumBasicOpen_eq_compl_zeroLocus {R : Type*} [CommSemiring R]
    (f : R) :
    (spectrumBasicOpen f : Set (AffineSpectrum R)) =
      (spectrumZeroLocus (Ideal.span ({f} : Set R)))ᶜ := by
  rw [spectrumZeroLocus_span]
  exact PrimeSpectrum.basicOpen_eq_zeroLocus_compl f

@[simp]
theorem spectrumBasicOpen_one {R : Type*} [CommSemiring R] :
    spectrumBasicOpen (1 : R) = ⊤ := by
  exact PrimeSpectrum.basicOpen_one

@[simp]
theorem spectrumBasicOpen_zero {R : Type*} [CommSemiring R] :
    spectrumBasicOpen (0 : R) = ⊥ := by
  exact PrimeSpectrum.basicOpen_zero

theorem spectrumBasicOpen_mul {R : Type*} [CommSemiring R] (f g : R) :
    spectrumBasicOpen (f * g) = spectrumBasicOpen f ⊓ spectrumBasicOpen g := by
  exact PrimeSpectrum.basicOpen_mul f g

/-! ### Functoriality and affine coordinate rings -/

theorem continuous_spectrum_comap {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) : Continuous (PrimeSpectrum.comap f) := by
  exact PrimeSpectrum.continuous_comap f

/-- The map on spectra induced by the quotient defining an affine coordinate ring. -/
def coordinateRingSpectrumMap {k : Type*} [Field k] (n : Nat)
    (Y : Set (AffinePoint k n)) :
    AffineSpectrum (AffineCoordinateRing k n Y) → AffineSpectrum (AffinePolynomial k n) :=
  PrimeSpectrum.comap (coordinateRingMk k n Y).toRingHom

theorem coordinateRingSpectrumMap_continuous {k : Type*} [Field k] (n : Nat)
    (Y : Set (AffinePoint k n)) :
    Continuous (coordinateRingSpectrumMap (k := k) n Y) := by
  exact PrimeSpectrum.continuous_comap (coordinateRingMk k n Y).toRingHom

theorem coordinateRingSpectrumMap_isClosedEmbedding {k : Type*} [Field k] (n : Nat)
    (Y : Set (AffinePoint k n)) :
    Topology.IsClosedEmbedding (coordinateRingSpectrumMap (k := k) n Y) := by
  apply PrimeSpectrum.isClosedEmbedding_comap_of_surjective
  simpa [coordinateRingMk] using
    (Ideal.Quotient.mkₐ_surjective k (vanishingIdeal k n Y))

theorem coordinateRingSpectrumMap_range {k : Type*} [Field k] (n : Nat)
    (Y : Set (AffinePoint k n)) :
    Set.range (coordinateRingSpectrumMap (k := k) n Y) =
      spectrumZeroLocus (vanishingIdeal k n Y) := by
  have hsurj : Function.Surjective (coordinateRingMk k n Y).toRingHom := by
    simpa [coordinateRingMk] using
      (Ideal.Quotient.mkₐ_surjective k (vanishingIdeal k n Y))
  have h := range_comap_of_surjective (AffineCoordinateRing k n Y)
    (coordinateRingMk k n Y).toRingHom hsurj
  rw [coordinateRingMk_ker] at h
  simpa [coordinateRingSpectrumMap, spectrumZeroLocus] using h

end

end Hartshorne
