/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import StacksPart01Lib.Zariski

/-!
# Further standard-open identities

These elementary identities fill out the set-theoretic parts of the Stacks
Project's Zariski-topology lemma (Tag 00E0).
-/

namespace StacksPart01

open Set

namespace Zariski

/-- A standard open and its zero locus form a complementary partition
(Stacks, Tag 00E0, part (11)). -/
theorem standardOpen_union_zeroLocus {R : Type*} [CommSemiring R] (f : R) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∪
      PrimeSpectrum.zeroLocus ({f} : Set R) = Set.univ := by
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  exact Set.compl_union_self _

/-- Multiplication by a unit does not change a standard open
(Stacks, Tag 00E0, part (13)). -/
theorem standardOpen_unit_mul {R : Type*} [CommSemiring R] (u f : R) (hu : IsUnit u) :
    (PrimeSpectrum.basicOpen (u * f) : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  ext x
  change x ∈ PrimeSpectrum.basicOpen (u * f) ↔ x ∈ PrimeSpectrum.basicOpen f
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.mem_basicOpen]
  exact not_congr (x.asIdeal.unit_mul_mem_iff_mem hu)

/-- A standard open is the whole spectrum exactly when its element is a unit
(Stacks, Tag 00E0, part (17)). -/
theorem standardOpen_eq_univ_iff_isUnit {R : Type*} [CommSemiring R] (f : R) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) = Set.univ ↔ IsUnit f := by
  constructor
  · intro h
    have hv : PrimeSpectrum.zeroLocus ({f} : Set R) = (∅ : Set (PrimeSpectrum R)) := by
      have hc := congrArg (fun s : Set (PrimeSpectrum R) => sᶜ) h
      rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl] at hc
      simpa using hc
    have hv' : PrimeSpectrum.zeroLocus
        (↑(Ideal.span ({f} : Set R)) : Set R) = (∅ : Set (PrimeSpectrum R)) := by
      rw [PrimeSpectrum.zeroLocus_span]
      exact hv
    have htop : Ideal.span ({f} : Set R) = ⊤ :=
      (PrimeSpectrum.zeroLocus_empty_iff_eq_top).mp hv'
    exact Ideal.span_singleton_eq_top.mp htop
  · intro hu
    ext x
    change x ∈ PrimeSpectrum.basicOpen f ↔ x ∈ (Set.univ : Set (PrimeSpectrum R))
    simp only [Set.mem_univ, iff_true, PrimeSpectrum.mem_basicOpen]
    intro hf
    exact x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem hf hu)

/-- The intersection of two standard opens can be written with the product
of their defining elements (Stacks, Tag `00E0`). -/
theorem standardOpen_inter_set {R : Type*} [CommSemiring R] (f g : R) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)) := by
  rw [standardOpen_mul_set]

/-- A standard-open cover of a standard open admits a finite refinement
(Stacks, Tags `00E8` and `04PM`). -/
theorem exists_finset_standardOpen_cover {R : Type*} [CommSemiring R]
    {ι : Type*} (g : R) (f : ι → R)
    (hcover : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆
      ⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R))) :
    ∃ s : Finset ι,
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆
        ⋃ i ∈ s, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R)) := by
  exact (PrimeSpectrum.isCompact_basicOpen g).elim_finite_subcover
    (fun i => (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R)))
    (fun i => PrimeSpectrum.isOpen_basicOpen) hcover

/-- The containment `D(g) ⊆ D(f)` is equivalent to a power of `g` being a
multiple of `f` (Stacks, Tag 01HS(1)(b)). -/
theorem standardOpen_subset_iff_exists_pow_eq_mul {R : Type*} [CommSemiring R]
    {f g : R} (hsub : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ∃ n : ℕ, ∃ a : R, g ^ n = a * f := by
  have h' := (PrimeSpectrum.basicOpen_le_basicOpen_iff g f).mp hsub
  rw [Ideal.mem_radical_iff] at h'
  obtain ⟨n, hn⟩ := h'
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hn
  exact ⟨n, a, by simpa [mul_comm] using ha.symm⟩

/-- The defining element of a larger standard open is a unit in the
localization at a smaller standard open. -/
theorem standardOpen_isUnit_of_subset {R : Type*} [CommSemiring R]
    {f g : R} (hsub : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    IsUnit (algebraMap R (Localization.Away g) f) := by
  exact (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
    (S := Localization.Away g) (f := g) (g := f)).mp hsub

/-- A ring map whose map on affine spectra is surjective detects units
(Stacks, Tag 0B7C). -/
theorem isUnit_iff_of_surjective_spectrum
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hsurj : Function.Surjective (PrimeSpectrum.comap f)) (x : R) :
    IsUnit x ↔ IsUnit (f x) := by
  constructor
  · exact fun hx => hx.map f
  · intro hx
    apply (standardOpen_eq_univ_iff_isUnit x).mp
    apply Set.eq_univ_iff_forall.mpr
    intro p
    obtain ⟨q, hq⟩ := hsurj p
    have hqopen : q ∈ (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum S)) :=
      (standardOpen_eq_univ_iff_isUnit (f x)).mpr hx ▸ Set.mem_univ q
    have hpre : (PrimeSpectrum.comap f) ⁻¹'
        (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum R)) =
        (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum S)) :=
      spectrum_comap_preimage_standardOpen f x
    have hp : PrimeSpectrum.comap f q ∈
        (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum R)) := by
      have hqpre : q ∈ (PrimeSpectrum.comap f) ⁻¹'
          (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum R)) := by
        rw [hpre]
        exact hqopen
      exact hqpre
    simpa [hq] using hp

end Zariski

end StacksPart01
