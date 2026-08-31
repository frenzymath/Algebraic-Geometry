/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.FiniteType

/-!
# StacksPart01Lib.FiniteTypeExtras

Finite ring maps give finite-type ring maps (Stacks Project, Tag `0D46`).
-/

namespace StacksPart01Lib

/-- A finite ring homomorphism is of finite type.

The finite condition says that the target is finite as a module over the
source, and hence its module generators also generate it as an algebra.  This
is the first assertion of the Stacks Project's finite-to-finite-type lemma
(Tag `0D46`); the finite transitivity lemmas are Tags `00GJ` and `00GL`.
-/
theorem ringHom_finiteType_of_finite {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) : f.FiniteType := by
  exact RingHom.FiniteType.of_finite hf

end StacksPart01Lib
