/-
Copyright (c) 2026 The StacksPart03Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart03Lib Contributors
-/

import Mathlib.LinearAlgebra.Prod
import StacksPart03Lib.PeriodicLength

/-!
# Split sums of two-periodic complexes

This file packages the componentwise product of two two-periodic complexes.
For finite-length ambient modules, its multiplicity is the sum of the two
multiplicities.  This is the split case of the additivity statement in Stacks,
Tag 0EA7.
-/

namespace StacksPart03

namespace TwoPeriodicComplex

variable {R M N M' N' : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  [Module R M] [Module R N] [Module R M'] [Module R N']

/-! ## Componentwise product -/

/-- The componentwise product of two two-periodic complexes. -/
def prod (C : TwoPeriodicComplex R M N) (D : TwoPeriodicComplex R M' N') :
    TwoPeriodicComplex R (M × M') (N × N') where
  d₀ := C.d₀.prodMap D.d₀
  d₁ := C.d₁.prodMap D.d₁
  d₀_d₁ := by
    rw [LinearMap.prodMap_comp, C.d₀_d₁, D.d₀_d₁]
    exact LinearMap.prodMap_zero
  d₁_d₀ := by
    rw [LinearMap.prodMap_comp, C.d₁_d₀, D.d₁_d₀]
    exact LinearMap.prodMap_zero

@[simp]
theorem prod_d₀ (C : TwoPeriodicComplex R M N)
    (D : TwoPeriodicComplex R M' N') :
    (C.prod D).d₀ = C.d₀.prodMap D.d₀ :=
  rfl

@[simp]
theorem prod_d₁ (C : TwoPeriodicComplex R M N)
    (D : TwoPeriodicComplex R M' N') :
    (C.prod D).d₁ = C.d₁.prodMap D.d₁ :=
  rfl

/-- Kernels of the product differential split componentwise. -/
theorem prod_ker_d₀ (C : TwoPeriodicComplex R M N)
    (D : TwoPeriodicComplex R M' N') :
    (C.prod D).d₀.ker = C.d₀.ker.prod D.d₀.ker := by
  exact LinearMap.ker_prodMap _ _

theorem prod_ker_d₁ (C : TwoPeriodicComplex R M N)
    (D : TwoPeriodicComplex R M' N') :
    (C.prod D).d₁.ker = C.d₁.ker.prod D.d₁.ker := by
  exact LinearMap.ker_prodMap _ _

/-- Ranges of the product differential split componentwise. -/
theorem prod_range_d₀ (C : TwoPeriodicComplex R M N)
    (D : TwoPeriodicComplex R M' N') :
    (C.prod D).d₀.range = C.d₀.range.prod D.d₀.range := by
  exact LinearMap.range_prodMap _ _

theorem prod_range_d₁ (C : TwoPeriodicComplex R M N)
    (D : TwoPeriodicComplex R M' N') :
    (C.prod D).d₁.range = C.d₁.range.prod D.d₁.range := by
  exact LinearMap.range_prodMap _ _

/-! ## Finite lengths -/

/-- A product of finite-length modules has finite length. -/
theorem isFiniteLength_prod
    {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    [Module R P] [Module R Q]
    (hP : IsFiniteLength R P) (hQ : IsFiniteLength R Q) :
    IsFiniteLength R (P × Q) := by
  apply Module.length_ne_top_iff.mp
  rw [Module.length_prod]
  exact ne_of_lt (ENat.add_lt_top.mpr
    ⟨lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr hP),
      lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr hQ)⟩)

/-- The integer length of a finite product is the sum of its factors. -/
theorem finiteLengthInt_prod
    {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    [Module R P] [Module R Q]
    (hP : IsFiniteLength R P) (hQ : IsFiniteLength R Q)
    (hPQ : IsFiniteLength R (P × Q)) :
    finiteLengthInt R (P × Q) hPQ =
      finiteLengthInt R P hP + finiteLengthInt R Q hQ := by
  have hPtop : Module.length R P ≠ ⊤ := Module.length_ne_top_iff.mpr hP
  have hQtop : Module.length R Q ≠ ⊤ := Module.length_ne_top_iff.mpr hQ
  change Int.ofNat (Module.length R (P × Q)).toNat =
    Int.ofNat (Module.length R P).toNat + Int.ofNat (Module.length R Q).toNat
  rw [Module.length_prod, ENat.toNat_add hPtop hQtop]
  exact Nat.cast_add _ _

/-! ## Split additivity -/

/-- In the split/product case, periodic multiplicity is additive.

The hypotheses give finite length to all four ambient modules, hence to the
cohomology of each factor and of the product.  The result is the split case of
the short-exact additivity lemma from the source. -/
theorem multiplicity_prod_eq_add_of_finite_ambient
    (C : TwoPeriodicComplex R M N) (D : TwoPeriodicComplex R M' N')
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (hM' : IsFiniteLength R M') (hN' : IsFiniteLength R N') :
    (C.prod D).multiplicity
        ((C.prod D).hasFiniteLength_of_finite_ambient
          (isFiniteLength_prod hM hM') (isFiniteLength_prod hN hN')) =
      C.multiplicity (C.hasFiniteLength_of_finite_ambient hM hN) +
        D.multiplicity (D.hasFiniteLength_of_finite_ambient hM' hN') := by
  rw [(C.prod D).multiplicity_eq_ambient_length_sub
    (isFiniteLength_prod hM hM') (isFiniteLength_prod hN hN'),
    C.multiplicity_eq_ambient_length_sub hM hN,
    D.multiplicity_eq_ambient_length_sub hM' hN']
  rw [finiteLengthInt_prod hM hM' (isFiniteLength_prod hM hM'),
    finiteLengthInt_prod hN hN' (isFiniteLength_prod hN hN')]
  ring

end TwoPeriodicComplex

end StacksPart03
