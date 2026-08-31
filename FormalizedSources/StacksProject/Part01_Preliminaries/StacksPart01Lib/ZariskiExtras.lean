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

end Zariski

end StacksPart01
