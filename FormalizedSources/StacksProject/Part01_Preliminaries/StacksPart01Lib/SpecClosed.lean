/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import StacksPart01Lib.Spectrum

/-!
# The spectrum of a quotient

The quotient map identifies `Spec (R / I)` with the closed zero locus `V(I)`
(Stacks, Tag 00E5).  The underlying range and closed-embedding statements are
recorded here alongside the homeomorphism in `Spectrum.lean`.
-/

namespace StacksPart01

open Set

/-- The range of the quotient-induced map on spectra is `V(I)`
(Stacks, Tag 00E5). -/
theorem spec_quotient_comap_range {R : Type*} [CommRing R] (I : Ideal R) :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective]
  simp

/-- The quotient-induced map on spectra is a closed embedding
(Stacks, Tag 00E5). -/
theorem spec_quotient_comap_isClosedEmbedding {R : Type*} [CommRing R]
    (I : Ideal R) :
    Topology.IsClosedEmbedding (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
  exact PrimeSpectrum.isClosedEmbedding_comap_of_surjective
    (R ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- The quotient homeomorphism has the expected map on points. -/
@[simp] theorem spec_quotient_homeomorph_apply {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum (R ⧸ I)) :
    ((spec_quotient_homeomorph I p : PrimeSpectrum.zeroLocus (I : Set R)) :
      PrimeSpectrum R) =
      PrimeSpectrum.comap (Ideal.Quotient.mk I) p := by
  rfl

end StacksPart01
