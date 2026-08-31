/-
Copyright (c) 2026 The StacksPart02Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart02Lib Contributors
-/

import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Affine spectra and standard opens

The Stacks Project writes `D(f)` for the standard open of an element `f` in a
commutative ring.  Mathlib calls this open `PrimeSpectrum.basicOpen f`; this
module records the elementary identities and functoriality used throughout
the affine part of the Schemes chapter.
-/

namespace StacksPart02

open Set

/- Membership and elementary identities for standard opens. -/

/-- Membership in `D(f)` means that `f` is not contained in the prime ideal
represented by the point (Stacks, Tag 00E1). -/
theorem mem_standardOpen_iff {R : Type*} [CommSemiring R]
    (f : R) (x : PrimeSpectrum R) :
    x ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ↔
      f ∉ x.asIdeal := by
  exact PrimeSpectrum.mem_basicOpen f x

/-- The standard open `D(1)` is the whole spectrum. -/
@[simp] theorem standardOpen_one {R : Type*} [CommSemiring R] :
    PrimeSpectrum.basicOpen (1 : R) = ⊤ := by
  exact PrimeSpectrum.basicOpen_one

/-- The standard open `D(0)` is empty. -/
@[simp] theorem standardOpen_zero {R : Type*} [CommSemiring R] :
    PrimeSpectrum.basicOpen (0 : R) = ⊥ := by
  exact PrimeSpectrum.basicOpen_zero

/-- A standard open is empty exactly when its defining element is nilpotent. -/
theorem standardOpen_eq_bot_iff_isNilpotent {R : Type*} [CommSemiring R] (f : R) :
    PrimeSpectrum.basicOpen f = ⊥ ↔ IsNilpotent f := by
  exact PrimeSpectrum.basicOpen_eq_bot_iff f

/-- The standard open of a product is the intersection of the standard opens
(Stacks, Tag 00E0). -/
theorem standardOpen_mul {R : Type*} [CommSemiring R] (f g : R) :
    PrimeSpectrum.basicOpen (f * g) =
      PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g := by
  exact PrimeSpectrum.basicOpen_mul f g

/-- Standard opens are open subsets of the spectrum. -/
theorem isOpen_standardOpen {R : Type*} [CommSemiring R] (f : R) :
    IsOpen (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  exact PrimeSpectrum.isOpen_basicOpen

/-- The set underlying `D(fg)` is the intersection `D(f) ∩ D(g)`. -/
theorem standardOpen_mul_set {R : Type*} [CommSemiring R] (f g : R) :
    (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  have h := PrimeSpectrum.basicOpen_mul f g
  exact congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) =>
    (U : Set (PrimeSpectrum R))) h

/-- A positive power does not change a standard open (Stacks, Tag 00E0). -/
@[simp] theorem standardOpen_pow {R : Type*} [CommSemiring R] (f : R) (n : ℕ)
    (hn : 0 < n) :
    PrimeSpectrum.basicOpen (f ^ n) = PrimeSpectrum.basicOpen f := by
  exact PrimeSpectrum.basicOpen_pow f n hn

/-- Every standard open in an affine spectrum is quasi-compact. -/
theorem standardOpen_isQuasiCompact {R : Type*} [CommSemiring R] (f : R) :
    IsCompact (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  exact PrimeSpectrum.isCompact_basicOpen f

/-- A family of standard opens covers an affine spectrum exactly when its
elements generate the unit ideal (Stacks, Tag 00E0). -/
theorem standardOpen_iSup_eq_top_iff {R : Type*} [CommSemiring R] {ι : Type*}
    (f : ι → R) :
    (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔
      Ideal.span (Set.range f) = ⊤ := by
  exact PrimeSpectrum.iSup_basicOpen_eq_top_iff

/-- A cover of a standard open by standard opens has a finite refinement. -/
theorem exists_finset_standardOpen_cover {R : Type*} [CommSemiring R] {ι : Type*}
    (g : R) (f : ι → R)
    (hcover : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆
      ⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R))) :
    ∃ s : Finset ι,
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆
        ⋃ i ∈ s, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R)) := by
  exact (PrimeSpectrum.isCompact_basicOpen g).elim_finite_subcover
    (fun i => (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R)))
    (fun i => PrimeSpectrum.isOpen_basicOpen) hcover

/-- Standard opens form a basis for the Zariski topology. -/
theorem standardOpen_isTopologicalBasis {R : Type*} [CommSemiring R] :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : R =>
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) :=
  PrimeSpectrum.isTopologicalBasis_basic_opens

/- Functoriality under maps of rings. -/

/-- The map on spectra induced by a ring homomorphism is continuous
(Stacks, Tag 00E2). -/
theorem continuous_spectrum_comap {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    Continuous (PrimeSpectrum.comap f) := by
  exact PrimeSpectrum.continuous_comap f

/-- Pulling back `D(f)` along the map induced by a ring homomorphism gives
`D(φ(f))`. -/
theorem spectrum_comap_preimage_standardOpen {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : R) :
    (PrimeSpectrum.comap f) ⁻¹' (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum S)) := by
  have h := PrimeSpectrum.comap_basicOpen f x
  have h' := congrArg
    (fun U : TopologicalSpace.Opens (PrimeSpectrum S) => (U : Set (PrimeSpectrum S))) h
  simpa only [TopologicalSpace.Opens.coe_comap, ContinuousMap.coe_mk] using h'

/-- Pullback on spectra respects composition of ring homomorphisms. -/
theorem spectrum_comap_comp {R S T : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (f : R →+* S) (g : S →+* T) :
    PrimeSpectrum.comap (g.comp f) =
      (PrimeSpectrum.comap f).comp (PrimeSpectrum.comap g) := by
  exact PrimeSpectrum.comap_comp f g

/-- Pointwise form of `spectrum_comap_comp`. -/
theorem spectrum_comap_comp_apply {R S T : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (f : R →+* S) (g : S →+* T) (x : PrimeSpectrum T) :
    PrimeSpectrum.comap (g.comp f) x =
      PrimeSpectrum.comap f (PrimeSpectrum.comap g x) := by
  exact PrimeSpectrum.comap_comp_apply f g x

end StacksPart02
