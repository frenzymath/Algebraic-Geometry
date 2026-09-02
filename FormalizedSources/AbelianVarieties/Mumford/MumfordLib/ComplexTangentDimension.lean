/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ComplexVectorLattice

/-!
# Dimensions of the complex tangent model

The coordinate equivalence in `ComplexVectorLatticeExponentialData` identifies
the chosen tangent space with the standard complex `g`-coordinate model.  This
file records the resulting complex and real dimensions for downstream use.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

namespace ComplexVectorLatticeExponentialData

/-- The chosen tangent space has complex dimension `g`. -/
theorem finrank_complex
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    Module.finrank ℂ V = g := by
  rw [d.coordinate.toLinearEquiv.finrank_eq, Module.finrank_pi]
  simp

/-- The underlying real tangent space has dimension `2 * g`. -/
theorem finrank_real
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    Module.finrank ℝ V = 2 * g := by
  let e : V ≃ₗ[ℝ] GenusComplexVector g :=
    d.coordinate.toLinearEquiv.restrictScalars ℝ
  rw [e.finrank_eq]
  rw [← Module.finrank_mul_finrank ℝ ℂ (GenusComplexVector g)]
  rw [Complex.finrank_real_complex, Module.finrank_pi]
  simp

/-- The integral rank of the transported period lattice agrees with the
    underlying real tangent-space dimension. -/
theorem ambientPeriodLattice_finrank_eq_finrank_real
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (d : ComplexVectorLatticeExponentialData V X g) :
    Module.finrank ℤ d.ambientPeriodLatticeSubmodule = Module.finrank ℝ V := by
  rw [d.ambientPeriodLattice_finrank, d.finrank_real]

end ComplexVectorLatticeExponentialData

end
end Uniformization
end Mumford
