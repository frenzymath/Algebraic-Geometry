/-
Copyright (c) 2026 The StacksPart03Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart03Lib Contributors
-/

import Mathlib.Algebra.Module.Submodule.Range

/-!
# Two-periodic complexes

The Chow chapter starts with two-periodic complexes (Stacks, Tag 02PG).
This module records the linear-algebraic data and the exactness predicate;
finite-length cohomology and its additivity are deliberately left for a
later module.
-/

namespace StacksPart03

/-! ## Periodic complexes -/

/-- A two-periodic complex of modules.  The two displayed compositions are
the consecutive differentials in each parity and are required to vanish. -/
structure TwoPeriodicComplex (R M N : Type*) [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] where
  d₀ : M →ₗ[R] N
  d₁ : N →ₗ[R] M
  d₀_d₁ : d₀.comp d₁ = 0
  d₁_d₀ : d₁.comp d₀ = 0

variable {R M N : Type*} [Semiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

namespace TwoPeriodicComplex

/-- The image of the odd differential is contained in the even cycles. -/
theorem range_d₁_le_ker_d₀ (C : TwoPeriodicComplex R M N) :
    LinearMap.range C.d₁ ≤ LinearMap.ker C.d₀ := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact LinearMap.congr_fun C.d₀_d₁ y

/-- The image of the even differential is contained in the odd cycles. -/
theorem range_d₀_le_ker_d₁ (C : TwoPeriodicComplex R M N) :
    LinearMap.range C.d₀ ≤ LinearMap.ker C.d₁ := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact LinearMap.congr_fun C.d₁_d₀ y

/-- Exactness of a two-periodic complex, expressed by vanishing of both
cohomology objects as kernel/image equalities. -/
def IsExact (C : TwoPeriodicComplex R M N) : Prop :=
  LinearMap.range C.d₁ = LinearMap.ker C.d₀ ∧
    LinearMap.range C.d₀ = LinearMap.ker C.d₁

theorem exact_iff_ker_eq_range (C : TwoPeriodicComplex R M N) :
    C.IsExact ↔
      LinearMap.ker C.d₀ = LinearMap.range C.d₁ ∧
        LinearMap.ker C.d₁ = LinearMap.range C.d₀ := by
  constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨h₀.symm, h₁.symm⟩
  · rintro ⟨h₀, h₁⟩
    exact ⟨h₀.symm, h₁.symm⟩

end TwoPeriodicComplex

/-- A `(2, 1)`-periodic complex is the equal-object specialization of a
two-periodic complex. -/
abbrev TwoOnePeriodicComplex (R M : Type*) [Semiring R]
    [AddCommMonoid M] [Module R M] :=
  TwoPeriodicComplex R M M

end StacksPart03
