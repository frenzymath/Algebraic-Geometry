/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

/-!
# Characteristic polynomials of finite modules

The characteristic-polynomial annihilation statements from the commutative
algebra preliminaries (Stacks Project, Tags `05BT` and `05G7`).
-/

namespace StacksPart01

open Polynomial

/-- An endomorphism of a finite module is annihilated by a monic polynomial
(Stacks, Tag 05BT). -/
theorem charpoly_module
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (φ : Module.End R M) :
    ∃ p : R[X], p.Monic ∧ Polynomial.aeval φ p = 0 := by
  exact LinearMap.exists_monic_and_aeval_eq_zero R φ

/-- If an endomorphism has image in `I M`, its annihilating polynomial has
the expected powers of `I` in its coefficients (Stacks, Tag 05G7). -/
theorem charpoly_module_ideal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (φ : Module.End R M)
    (hφ : LinearMap.range φ ≤ I • (⊤ : Submodule R M)) :
    ∃ p : R[X], p.Monic ∧
      (∀ k, p.coeff k ∈ I ^ (p.natDegree - k)) ∧
      Polynomial.aeval φ p = 0 := by
  obtain ⟨p, hp, _hdeg, hcoeff, haeval⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      R φ I hφ
  exact ⟨p, hp, hcoeff, haeval⟩

end StacksPart01
