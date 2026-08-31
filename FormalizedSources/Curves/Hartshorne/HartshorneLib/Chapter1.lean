/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Set.Lattice

/-!
# Hartshorne I.1: affine algebraic sets

This file records the elementary set-theoretic part of the affine-variety
construction. Points of affine space are coordinate functions and polynomials
are multivariate polynomials in those coordinates.
-/

namespace Hartshorne

noncomputable section

section AffineSpace

variable (k : Type*) [Field k] (n : Nat)

/-- The set of `k`-valued points of affine `n`-space. -/
abbrev AffinePoint := Fin n -> k

/-- The polynomial ring in the `n` affine coordinates. -/
abbrev AffinePolynomial := MvPolynomial (Fin n) k

/-- Evaluation of a polynomial at an affine point. -/
def evaluate (f : AffinePolynomial k n) (P : AffinePoint k n) : k :=
  MvPolynomial.eval P f

@[simp]
theorem evaluate_zero (P : AffinePoint k n) : evaluate k n 0 P = 0 := by
  simp [evaluate]

@[simp]
theorem evaluate_one (P : AffinePoint k n) : evaluate k n 1 P = 1 := by
  simp [evaluate]

@[simp]
theorem evaluate_add (f g : AffinePolynomial k n) (P : AffinePoint k n) :
    evaluate k n (f + g) P = evaluate k n f P + evaluate k n g P := by
  simp [evaluate]

@[simp]
theorem evaluate_mul (f g : AffinePolynomial k n) (P : AffinePoint k n) :
    evaluate k n (f * g) P = evaluate k n f P * evaluate k n g P := by
  simp [evaluate]

@[simp]
theorem evaluate_pow (f : AffinePolynomial k n) (r : Nat) (P : AffinePoint k n) :
    evaluate k n (f ^ r) P = (evaluate k n f P) ^ r := by
  simp [evaluate]

/-- The zero set of one polynomial. -/
def zeroSet (f : AffinePolynomial k n) : Set (AffinePoint k n) :=
  {P | evaluate k n f P = 0}

@[simp]
theorem mem_zeroSet (f : AffinePolynomial k n) (P : AffinePoint k n) :
    P ∈ zeroSet k n f ↔ evaluate k n f P = 0 := Iff.rfl

/-- The common zero set of a family of polynomials. -/
def commonZeroSet (T : Set (AffinePolynomial k n)) : Set (AffinePoint k n) :=
  {P | ∀ f, f ∈ T -> evaluate k n f P = 0}

theorem mem_commonZeroSet (T : Set (AffinePolynomial k n)) (P : AffinePoint k n) :
    P ∈ commonZeroSet k n T ↔ ∀ f, f ∈ T -> evaluate k n f P = 0 := Iff.rfl

theorem zeroSet_eq_commonZeroSet_singleton (f : AffinePolynomial k n) :
    zeroSet k n f = commonZeroSet k n ({f} : Set (AffinePolynomial k n)) := by
  ext P
  simp [zeroSet, commonZeroSet]

theorem commonZeroSet_mono {T U : Set (AffinePolynomial k n)} (hTU : T ⊆ U) :
    commonZeroSet k n U ⊆ commonZeroSet k n T := by
  intro P hP f hf
  exact hP f (hTU hf)

theorem commonZeroSet_union (T U : Set (AffinePolynomial k n)) :
    commonZeroSet k n (T ∪ U) = commonZeroSet k n T ∩ commonZeroSet k n U := by
  ext P
  constructor
  · intro hP
    constructor
    · intro f hf
      exact hP f (Or.inl hf)
    · intro f hf
      exact hP f (Or.inr hf)
  · rintro ⟨hT, hU⟩ f (hf | hf)
    · exact hT f hf
    · exact hU f hf

@[simp]
theorem commonZeroSet_empty :
    commonZeroSet k n (∅ : Set (AffinePolynomial k n)) = Set.univ := by
  ext P
  simp [commonZeroSet]

@[simp]
theorem zeroSet_zero :
    zeroSet k n (0 : AffinePolynomial k n) = Set.univ := by
  ext P
  simp [zeroSet, evaluate]

@[simp]
theorem zeroSet_one :
    zeroSet k n (1 : AffinePolynomial k n) = (∅ : Set (AffinePoint k n)) := by
  ext P
  simp [zeroSet, evaluate]

theorem zeroSet_mul (f g : AffinePolynomial k n) :
    zeroSet k n (f * g) = zeroSet k n f ∪ zeroSet k n g := by
  ext P
  change evaluate k n (f * g) P = 0 ↔
    evaluate k n f P = 0 ∨ evaluate k n g P = 0
  rw [evaluate_mul, mul_eq_zero]

/-- Products of two families, used to express the union of their zero sets. -/
def polynomialProducts (T U : Set (AffinePolynomial k n)) :
    Set (AffinePolynomial k n) :=
  {p | ∃ f ∈ T, ∃ g ∈ U, p = f * g}

theorem commonZeroSet_products (T U : Set (AffinePolynomial k n)) :
    commonZeroSet k n (polynomialProducts k n T U) =
      commonZeroSet k n T ∪ commonZeroSet k n U := by
  ext P
  constructor
  · intro hP
    by_cases hT : P ∈ commonZeroSet k n T
    · exact Or.inl hT
    · right
      change ∀ g, g ∈ U -> evaluate k n g P = 0
      intro g hg
      change ¬ (∀ f, f ∈ T -> evaluate k n f P = 0) at hT
      obtain ⟨f, hf⟩ := Classical.not_forall.mp hT
      obtain ⟨hfT, hne⟩ := Classical.not_imp.mp hf
      have hprod : evaluate k n (f * g) P = 0 :=
        hP (f * g) (by exact ⟨f, hfT, g, hg, rfl⟩)
      rw [evaluate_mul] at hprod
      exact Or.resolve_left (mul_eq_zero.mp hprod) hne
  · rintro (hT | hU) p hp
    · rcases hp with ⟨f, hf, g, hg, rfl⟩
      rw [evaluate_mul, hT f hf, zero_mul]
    · rcases hp with ⟨f, hf, g, hg, rfl⟩
      rw [evaluate_mul, hU g hg, mul_zero]

/-- A subset of affine space cut out by a family of polynomials. -/
def IsAlgebraicSet (Y : Set (AffinePoint k n)) : Prop :=
  ∃ T : Set (AffinePolynomial k n), commonZeroSet k n T = Y

theorem isAlgebraicSet_iff (Y : Set (AffinePoint k n)) :
    IsAlgebraicSet k n Y ↔ ∃ T : Set (AffinePolynomial k n), commonZeroSet k n T = Y := Iff.rfl

theorem isAlgebraicSet_zeroSet (f : AffinePolynomial k n) :
    IsAlgebraicSet k n (zeroSet k n f) := by
  exact ⟨{f}, (zeroSet_eq_commonZeroSet_singleton k n f).symm⟩

theorem isAlgebraicSet_empty : IsAlgebraicSet k n (∅ : Set (AffinePoint k n)) := by
  refine ⟨{1}, ?_⟩
  ext P
  simp [commonZeroSet, evaluate]

theorem isAlgebraicSet_univ : IsAlgebraicSet k n (Set.univ : Set (AffinePoint k n)) := by
  exact ⟨∅, commonZeroSet_empty k n⟩

theorem isAlgebraicSet_inter {Y Z : Set (AffinePoint k n)}
    (hY : IsAlgebraicSet k n Y) (hZ : IsAlgebraicSet k n Z) :
    IsAlgebraicSet k n (Y ∩ Z) := by
  rcases hY with ⟨T, hT⟩
  rcases hZ with ⟨U, hU⟩
  refine ⟨T ∪ U, ?_⟩
  rw [commonZeroSet_union, hT, hU]

theorem isAlgebraicSet_union {Y Z : Set (AffinePoint k n)}
    (hY : IsAlgebraicSet k n Y) (hZ : IsAlgebraicSet k n Z) :
    IsAlgebraicSet k n (Y ∪ Z) := by
  rcases hY with ⟨T, hT⟩
  rcases hZ with ⟨U, hU⟩
  refine ⟨polynomialProducts k n T U, ?_⟩
  rw [commonZeroSet_products, hT, hU]

/-- The ideal of polynomials vanishing at every point of a subset. -/
def vanishingIdeal (Y : Set (AffinePoint k n)) : Ideal (AffinePolynomial k n) :=
  { carrier := {f | ∀ P ∈ Y, evaluate k n f P = 0}
    zero_mem' := by
      intro P hP
      simp [evaluate]
    add_mem' := by
      intro f g hf hg P hP
      rw [evaluate_add, hf P hP, hg P hP, add_zero]
    smul_mem' := by
      intro a f hf P hP
      rw [show a • f = a * f by rfl, evaluate_mul, hf P hP, mul_zero] }

theorem mem_vanishingIdeal (Y : Set (AffinePoint k n)) (f : AffinePolynomial k n) :
    f ∈ vanishingIdeal k n Y ↔ ∀ P ∈ Y, evaluate k n f P = 0 := Iff.rfl

theorem vanishingIdeal_mono {Y Z : Set (AffinePoint k n)} (hYZ : Y ⊆ Z) :
    vanishingIdeal k n Z ≤ vanishingIdeal k n Y := by
  intro f hf P hP
  exact hf P (hYZ hP)

theorem vanishingIdeal_union (Y Z : Set (AffinePoint k n)) :
    vanishingIdeal k n (Y ∪ Z) = vanishingIdeal k n Y ⊓ vanishingIdeal k n Z := by
  ext f
  constructor
  · intro hf
    constructor
    · intro P hP
      exact hf P (Or.inl hP)
    · intro P hP
      exact hf P (Or.inr hP)
  · rintro ⟨hfY, hfZ⟩ P (hP | hP)
    · exact hfY P hP
    · exact hfZ P hP

end AffineSpace

end

end Hartshorne
