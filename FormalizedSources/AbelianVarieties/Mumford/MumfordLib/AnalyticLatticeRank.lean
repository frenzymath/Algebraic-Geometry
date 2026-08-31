/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ZLattice

/-!
# Rank of the period lattice

The explicit period submodules are full `ℤ`-lattices.  Mathlib's
`ZLattice.rank` therefore computes their integral rank as the real dimension
of the ambient vector space, namely `2 * g`.
-/

namespace Mumford
namespace Uniformization

noncomputable section

theorem integerPeriodLatticeSubmodule_finrank (g : ℕ) :
    Module.finrank ℤ (integerPeriodLatticeSubmodule g) = 2 * g := by
  rw [ZLattice.rank ℝ]
  simp [GenusRealVector, Module.finrank_fintype_fun_eq_card]

theorem complexPeriodLatticeSubmodule_finrank (g : ℕ) :
    Module.finrank ℤ (complexPeriodLatticeSubmodule g) = 2 * g := by
  rw [ZLattice.rank ℝ]
  simp [GenusComplexVector, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Nat.mul_comm]

end
end Uniformization
end Mumford
