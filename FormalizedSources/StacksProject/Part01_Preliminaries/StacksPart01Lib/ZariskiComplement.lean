/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import StacksPart01Lib.Zariski

/-!
# Complements of standard opens

The standard open `D(f)` and the vanishing locus `V(f)` form a complementary
pair in the spectrum.  This file records the disjointness consequence used in
the Zariski-topology preliminaries.
-/

namespace StacksPart01

open Set

namespace Zariski

/-- A standard open is disjoint from its defining vanishing locus
(Stacks, Tag 00E0). -/
theorem standardOpen_inter_zeroLocus_empty {R : Type*} [CommSemiring R] (f : R) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩
        PrimeSpectrum.zeroLocus ({f} : Set R) = ∅ := by
  rw [standardOpen_eq_compl_zeroLocus]
  exact Set.compl_inter_self _

end Zariski

end StacksPart01
