/-
Copyright (c) 2026 Frenzymath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frenzymath
-/
module

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Ideal.Span

import AGLib.RingTheory.Nilpotent.InvertibleModule

/-!
# Smoke test for nilpotent invertible-module freeness

This internal consumer exercises the pointwise theorem on the nonzero
square-zero ideal `(2)` of `ZMod 4`.  It is imported by the AGLib umbrella so
that the package build checks a concrete use of the public API without adding
the example to the umbrella's public API.
-/

set_option autoImplicit false
-- This module intentionally contains only an anonymous compile-time smoke test.
set_option linter.privateModule false

namespace Smoke

private abbrev I : Ideal (ZMod 4) := Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4))

private lemma htwo : (2 : ZMod 4) ^ 2 = 0 := by
  decide

private lemma hI_square_zero : I * I = ⊥ := by
  rw [← pow_two, Ideal.span_singleton_pow, htwo]
  exact Ideal.span_zero

private lemma hI_nilpotent : IsNilpotent I :=
  Ideal.isNilpotent_of_mul_self_eq_bot hI_square_zero

private lemma hI_nonzero : I ≠ ⊥ := by
  intro h
  have hzero : (2 : ZMod 4) = 0 := by
    have hmem : (2 : ZMod 4) ∈ (⊥ : Ideal (ZMod 4)) :=
      h ▸ Ideal.mem_span_singleton_self 2
    simpa using hmem
  have htwo_ne : (2 : ZMod 4) ≠ 0 := by
    decide
  exact htwo_ne hzero

-- The public API handles a module over a genuinely nonzero square-zero ideal.
example :
    Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4)) ≠ ⊥ ∧
      Module.Free (ZMod 4) (ZMod 4) := by
  refine ⟨hI_nonzero, ?_⟩
  apply Module.Invertible.free_of_nilpotent_of_exists_sub_smul_mem
    hI_nilpotent (m := (1 : ZMod 4))
  intro x
  refine ⟨x, ?_⟩
  simp

end Smoke
