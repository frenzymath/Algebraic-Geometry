/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.Localization.Basic

/-!
# The zero localization criterion

The localization of a ring is the zero ring exactly when zero belongs to the
chosen multiplicative system (Stacks, Tag 00CQ).
-/

namespace StacksPart01

/-- A localization is subsingleton exactly when its denominator submonoid
contains zero (Stacks, Tag 00CQ). -/
theorem localization_subsingleton_iff
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S] :
    Subsingleton S ↔ 0 ∈ M := by
  exact IsLocalization.subsingleton_iff

end StacksPart01
