/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness under change of scalars

The finiteness lemmas in this file package the scalar-tower arguments used in
the Stacks Project's discussion of finite modules (Tags 0560 and 00GJ).
-/

namespace StacksPart01

/-- If an `R`-module is finite, then it is finite over any larger scalar ring
`S` acting through a scalar tower (Stacks, Tag 0560). -/
theorem finite_over_subring
    {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R M] [Module S M] [SMul R S] [IsScalarTower R S M]
    [Module.Finite R M] :
    Module.Finite S M := by
  exact Module.Finite.of_restrictScalars_finite R S M

/-- For a finite scalar extension, finiteness of a module over the two scalar
rings is equivalent (Stacks, Tag 00GJ). -/
theorem finite_module_iff_of_finite_extension
    {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R S] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite R S] :
    Module.Finite R M ↔ Module.Finite S M := by
  constructor
  · intro h
    letI : Module.Finite R M := h
    exact Module.Finite.of_restrictScalars_finite R S M
  · intro h
    letI : Module.Finite S M := h
    exact Module.Finite.trans S M

end StacksPart01
