/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.FiniteType

/-!
# StacksPart01Lib.FiniteType

Finite-type ring maps are closed under composition (Stacks Project, Tag 00F4).
-/

namespace StacksPart01Lib

/-- Finite-type ring maps are stable under composition.

This is the first permanence assertion in the Stacks Project's composition
lemma (Tag `00F4`): if `R ⟶ S` and `S ⟶ T` are finite type, then the composite
`R ⟶ T` is finite type. -/
theorem ringHom_finiteType_comp {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T) (hf : f.FiniteType)
    (hg : g.FiniteType) : (g.comp f).FiniteType := by
  exact RingHom.FiniteType.comp hg hf

end StacksPart01Lib
