/-
Copyright (c) 2026 The StacksPart03Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart03Lib Contributors
-/

import StacksPart03Lib.Periodic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Cohomology of two-periodic complexes

The two cohomology modules in the Chow blueprint are kernel/image quotients.
The quotient is taken inside the relevant kernel, so the construction retains
the module structure supplied by `Submodule.Quotient` and does not require a
choice of representatives.
-/

namespace StacksPart03

namespace TwoPeriodicComplex

variable {R M N : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-! ## Cohomology carriers -/

/-- The even cohomology module `ker d₀ / im d₁` of a two-periodic complex. -/
abbrev HZero (C : TwoPeriodicComplex R M N) : Type _ :=
  (LinearMap.ker C.d₀) ⧸
    (LinearMap.range C.d₁).comap (LinearMap.ker C.d₀).subtype

/-- The odd cohomology module `ker d₁ / im d₀` of a two-periodic complex. -/
abbrev HOne (C : TwoPeriodicComplex R M N) : Type _ :=
  (LinearMap.ker C.d₁) ⧸
    (LinearMap.range C.d₀).comap (LinearMap.ker C.d₁).subtype

theorem hZero_subsingleton_iff (C : TwoPeriodicComplex R M N) :
    Subsingleton (C.HZero) ↔ LinearMap.ker C.d₀ = LinearMap.range C.d₁ := by
  rw [HZero, Submodule.Quotient.subsingleton_iff]
  constructor
  · intro h
    apply le_antisymm
    · exact Submodule.comap_subtype_eq_top.mp h
    · exact C.range_d₁_le_ker_d₀
  · intro h
    apply Submodule.comap_subtype_eq_top.mpr
    rw [h]

theorem hOne_subsingleton_iff (C : TwoPeriodicComplex R M N) :
    Subsingleton (C.HOne) ↔ LinearMap.ker C.d₁ = LinearMap.range C.d₀ := by
  rw [HOne, Submodule.Quotient.subsingleton_iff]
  constructor
  · intro h
    apply le_antisymm
    · exact Submodule.comap_subtype_eq_top.mp h
    · exact C.range_d₀_le_ker_d₁
  · intro h
    apply Submodule.comap_subtype_eq_top.mpr
    rw [h]

/-- Exactness is equivalent to vanishing of both cohomology carriers. -/
theorem isExact_iff_cohomology_subsingleton (C : TwoPeriodicComplex R M N) :
    C.IsExact ↔ Subsingleton C.HZero ∧ Subsingleton C.HOne := by
  rw [TwoPeriodicComplex.IsExact]
  constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨(C.hZero_subsingleton_iff.mpr h₀.symm),
      (C.hOne_subsingleton_iff.mpr h₁.symm)⟩
  · rintro ⟨h₀, h₁⟩
    exact ⟨(C.hZero_subsingleton_iff.mp h₀).symm,
      (C.hOne_subsingleton_iff.mp h₁).symm⟩

end TwoPeriodicComplex

end StacksPart03
