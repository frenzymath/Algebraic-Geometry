/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1Variety
import HartshorneLib.Chapter1Ideals
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Operations

/-!
# Hartshorne I.1: irreducibility and prime vanishing ideals

An irreducible algebraic set has a prime vanishing ideal.  The proof uses only
the closed-cover characterization of topological irreducibility and the
product law for polynomial zero sets, so it is independent of the affine
Nullstellensatz.
-/

namespace Hartshorne

noncomputable section

section AffinePrime

variable (k : Type*) [Field k] (n : Nat)

/-- The vanishing ideal of an affine variety is prime. -/
theorem vanishingIdeal_isPrime_of_isAffineVariety
    {Y : Set (AffinePoint k n)} (hY : IsAffineVariety k n Y) :
    (vanishingIdeal k n Y).IsPrime := by
  rw [Ideal.isPrime_iff]
  constructor
  · intro htop
    rcases hY.nonempty with ⟨P, hP⟩
    have hone : (1 : AffinePolynomial k n) ∈ vanishingIdeal k n Y := by
      rw [htop]
      exact Submodule.mem_top
    have hzero := hone P hP
    simp [evaluate] at hzero
  · intro f g hfg
    have hcover : Y ⊆ zeroSet k n f ∪ zeroSet k n g := by
      have hcover0 : Y ⊆ zeroSet k n (f * g) := by
        intro P hP
        change evaluate k n (f * g) P = 0
        exact hfg P hP
      rw [zeroSet_mul] at hcover0
      exact hcover0
    have hsplit :
        Y ⊆ zeroSet k n f ∨ Y ⊆ zeroSet k n g :=
      (isPreirreducible_iff_isClosed_union_isClosed.mp hY.isIrreducible.isPreirreducible
        (zeroSet k n f) (zeroSet k n g)
        (isClosed_zeroSet k n f) (isClosed_zeroSet k n g) hcover)
    rcases hsplit with hf | hg
    · left
      intro P hP
      exact hf hP
    · right
      intro P hP
      exact hg hP

/-- An algebraic set with prime vanishing ideal is irreducible. -/
theorem isAffineVariety_of_isAlgebraicSet_of_vanishingIdeal_isPrime
    {Y : Set (AffinePoint k n)} (hY : IsAlgebraicSet k n Y)
    (hprime : (vanishingIdeal k n Y).IsPrime) :
    IsAffineVariety k n Y := by
  have hne : Y.Nonempty := by
    by_contra hne
    have hYempty : Y = (∅ : Set (AffinePoint k n)) :=
      Set.not_nonempty_iff_eq_empty.mp hne
    subst Y
    exact hprime.ne_top (vanishingIdeal_empty k n)
  refine ⟨hY, ⟨hne, ?_⟩⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro Z₁ Z₂ hZ₁ hZ₂ hcover
  rcases (isClosed_iff_isAlgebraicSet k n Z₁).1 hZ₁ with ⟨T₁, hT₁⟩
  rcases (isClosed_iff_isAlgebraicSet k n Z₂).1 hZ₂ with ⟨T₂, hT₂⟩
  by_cases hsub₁ : Y ⊆ Z₁
  · exact Or.inl hsub₁
  by_cases hsub₂ : Y ⊆ Z₂
  · exact Or.inr hsub₂
  exfalso
  obtain ⟨P₁, hP₁Y, hP₁Z₁⟩ := Set.not_subset.mp hsub₁
  obtain ⟨P₂, hP₂Y, hP₂Z₂⟩ := Set.not_subset.mp hsub₂
  have hP₁not : P₁ ∉ commonZeroSet k n T₁ := by
    rw [hT₁]
    exact hP₁Z₁
  have hP₂not : P₂ ∉ commonZeroSet k n T₂ := by
    rw [hT₂]
    exact hP₂Z₂
  have hpoly₁ : ∃ f ∈ T₁, evaluate k n f P₁ ≠ 0 := by
    simpa [commonZeroSet] using hP₁not
  have hpoly₂ : ∃ g ∈ T₂, evaluate k n g P₂ ≠ 0 := by
    simpa [commonZeroSet] using hP₂not
  rcases hpoly₁ with ⟨f, hfT₁, hfP₁⟩
  rcases hpoly₂ with ⟨g, hgT₂, hgP₂⟩
  have hfg : f * g ∈ vanishingIdeal k n Y := by
    intro P hPY
    rw [evaluate_mul]
    by_cases hPZ₁ : P ∈ Z₁
    · have hfzero : evaluate k n f P = 0 := by
        have hPT₁ : P ∈ commonZeroSet k n T₁ := by
          rw [hT₁]
          exact hPZ₁
        exact hPT₁ f hfT₁
      rw [hfzero, zero_mul]
    · have hPZ₂ : P ∈ Z₂ := by
        exact (hcover hPY).resolve_left hPZ₁
      have hgzero : evaluate k n g P = 0 := by
        have hPT₂ : P ∈ commonZeroSet k n T₂ := by
          rw [hT₂]
          exact hPZ₂
        exact hPT₂ g hgT₂
      rw [hgzero, mul_zero]
  rcases (Ideal.isPrime_iff.mp hprime).2 hfg with hf | hg
  · exact hfP₁ (hf P₁ hP₁Y)
  · exact hgP₂ (hg P₂ hP₂Y)

/-- The vanishing ideal of an affine variety is radical. -/
theorem vanishingIdeal_radical_of_isAffineVariety
    {Y : Set (AffinePoint k n)} (hY : IsAffineVariety k n Y) :
    (vanishingIdeal k n Y).radical = vanishingIdeal k n Y :=
  (vanishingIdeal_isPrime_of_isAffineVariety k n hY).radical

end AffinePrime

end

end Hartshorne
