/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Artinian algebras

Finite-dimensional algebras over fields are Artinian (Stacks, Tag 00J6).
The proof is the standard finite-module argument, exposed by Mathlib's
`IsArtinianRing.of_finite` theorem.
-/

namespace StacksPart01

/-- A finite-dimensional algebra over a field is Artinian (Stacks, Tag 00J6). -/
theorem finite_dimensional_algebra_artinian
    {K R : Type*} [Field K] [Ring R] [Algebra K R]
    [FiniteDimensional K R] : IsArtinianRing R := by
  exact IsArtinianRing.of_finite K R

end StacksPart01
