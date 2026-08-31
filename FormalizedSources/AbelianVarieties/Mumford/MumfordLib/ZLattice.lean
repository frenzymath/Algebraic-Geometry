/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.Lattice
import MumfordLib.ComplexModel
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# The integer period lattice as a `ZLattice`

The coordinatewise integer period subgroup is the standard integer span of the
finite-coordinate basis.  This file records that identification in Mathlib's
integer-submodule API and exposes its discreteness and full-span property.
-/

namespace Mumford
namespace Uniformization

noncomputable section

/-- The integer period subgroup viewed as an integer submodule. -/
def integerPeriodLatticeSubmodule (g : ℕ) : Submodule ℤ (GenusRealVector g) :=
  AddSubgroup.toIntSubmodule (integerPeriodLattice g)

/-- The coordinatewise integer period subgroup is the integer span of the standard basis. -/
theorem integerPeriodLatticeSubmodule_eq_span (g : ℕ) :
    integerPeriodLatticeSubmodule g =
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin (2 * g)))) := by
  ext x
  change x ∈ integerPeriodLattice g ↔ _
  rw [Module.Basis.mem_span_iff_repr_mem]
  change (∀ i ∈ Set.univ, x i ∈ AddSubgroup.zmultiples (1 : ℝ)) ↔
    ∀ i : Fin (2 * g), ∃ y : ℤ, (y : ℝ) = x i
  simp only [Set.mem_univ, forall_true_left, AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro hx i
    obtain ⟨k, hk⟩ := hx i
    have hk' := hk
    rw [← Int.cast_smul_eq_zsmul ℝ] at hk'
    exact ⟨k, by simpa only [smul_eq_mul, mul_one] using hk'⟩
  · intro hx i
    obtain ⟨k, hk⟩ := hx i
    refine ⟨k, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ]
    simpa only [smul_eq_mul, mul_one] using hk

/-- The integer period lattice has the discrete topology on its subtype. -/
instance integerPeriodLatticeSubmodule_discreteTopology (g : ℕ) :
    DiscreteTopology (integerPeriodLatticeSubmodule g) := by
  rw [integerPeriodLatticeSubmodule_eq_span]
  infer_instance

/-- The integer period lattice is a full `ℝ`-lattice in the real coordinate space. -/
instance integerPeriodLatticeSubmodule_isZLattice (g : ℕ) :
    IsZLattice ℝ (integerPeriodLatticeSubmodule g) := by
  refine ⟨?_⟩
  rw [integerPeriodLatticeSubmodule_eq_span]
  exact ZSpan.span_top (Pi.basisFun ℝ (Fin (2 * g)))

/-- The realification equivalence, with its finite-dimensional topology. -/
noncomputable def genusComplexVectorRealificationContinuousLinearEquiv (g : ℕ) :
    GenusComplexVector g ≃L[ℝ] GenusRealVector g :=
  (genusComplexVectorRealification g).toContinuousLinearEquiv

/-- The complex period subgroup viewed as an integer submodule. -/
def complexPeriodLatticeSubmodule (g : ℕ) :
    Submodule ℤ (GenusComplexVector g) :=
  ZLattice.comap ℝ (integerPeriodLatticeSubmodule g)
    (genusComplexVectorRealificationContinuousLinearEquiv g).toLinearMap

@[simp]
theorem complexPeriodLatticeSubmodule_mem_iff (g : ℕ)
    (z : GenusComplexVector g) :
    z ∈ complexPeriodLatticeSubmodule g ↔ z ∈ complexPeriodLattice g := by
  change genusComplexVectorRealification g z ∈ integerPeriodLattice g ↔
    z ∈ complexPeriodLattice g
  rfl

instance complexPeriodLatticeSubmodule_discreteTopology (g : ℕ) :
    DiscreteTopology (complexPeriodLatticeSubmodule g) := by
  unfold complexPeriodLatticeSubmodule
  infer_instance

instance complexPeriodLatticeSubmodule_isZLattice (g : ℕ) :
    IsZLattice ℝ (complexPeriodLatticeSubmodule g) := by
  unfold complexPeriodLatticeSubmodule
  infer_instance

theorem complexPeriodLatticeSubmodule_toAddSubgroup (g : ℕ) :
    (complexPeriodLatticeSubmodule g).toAddSubgroup = complexPeriodLattice g := by
  ext z
  exact complexPeriodLatticeSubmodule_mem_iff g z

end
end Uniformization
end Mumford
