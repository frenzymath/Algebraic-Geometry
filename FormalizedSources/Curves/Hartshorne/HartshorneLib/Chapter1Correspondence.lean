/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1Closure
import HartshorneLib.Chapter1Prime

/-!
# Hartshorne I.1: the affine Nullstellensatz correspondence

The affine Nullstellensatz identifies algebraic point sets with radical ideals.
This file packages the two mutually inverse constructions and records their
order-reversing behavior.  The final theorem is the irreducibility/primeness
part of the same correspondence.
-/

namespace Hartshorne

noncomputable section

section AffineNullstellensatzCorrespondence

variable (k : Type*) [Field k] [IsAlgClosed k] (n : Nat)

/-- The subtype of algebraic subsets of affine `n`-space. -/
abbrev AffineAlgebraicSet :=
  {Y : Set (AffinePoint k n) // IsAlgebraicSet k n Y}

/-- The subtype of radical ideals in the affine polynomial ring. -/
abbrev AffineRadicalIdeal :=
  {I : Ideal (AffinePolynomial k n) // I.IsRadical}

/-- Send an algebraic set to its vanishing ideal. -/
def affineAlgebraicSetToRadicalIdeal :
    AffineAlgebraicSet k n → AffineRadicalIdeal k n := by
  intro Y
  refine ⟨vanishingIdeal k n Y, ?_⟩
  apply (Ideal.radical_eq_iff).mp
  calc
    (vanishingIdeal k n Y).radical =
        vanishingIdeal k n (commonZeroSet k n (vanishingIdeal k n Y)) := by
      symm
      exact vanishingIdeal_commonZeroSet_eq_radical k n _
    _ = vanishingIdeal k n Y := by
      rw [commonZeroSet_vanishingIdeal_eq_self k n Y.property]

/-- Send a radical ideal to its common zero set. -/
def affineRadicalIdealToAlgebraicSet :
    AffineRadicalIdeal k n → AffineAlgebraicSet k n := by
  intro I
  exact ⟨commonZeroSet k n (I : Ideal (AffinePolynomial k n)),
    ⟨(I : Ideal (AffinePolynomial k n)), rfl⟩⟩

theorem affineRadicalIdealToAlgebraicSet_leftInverse
    (Y : AffineAlgebraicSet k n) :
    affineRadicalIdealToAlgebraicSet k n
        (affineAlgebraicSetToRadicalIdeal k n Y) = Y := by
  apply Subtype.ext
  exact commonZeroSet_vanishingIdeal_eq_self k n Y.property

theorem affineAlgebraicSetToRadicalIdeal_rightInverse
    (I : AffineRadicalIdeal k n) :
    affineAlgebraicSetToRadicalIdeal k n
        (affineRadicalIdealToAlgebraicSet k n I) = I := by
  apply Subtype.ext
  change vanishingIdeal k n (commonZeroSet k n (I : Ideal (AffinePolynomial k n))) = I
  rw [vanishingIdeal_commonZeroSet_eq_radical]
  exact I.property.radical

/-- The affine Nullstellensatz equivalence between algebraic sets and radical ideals. -/
def affineNullstellensatzEquiv :
    AffineAlgebraicSet k n ≃ AffineRadicalIdeal k n where
  toFun := affineAlgebraicSetToRadicalIdeal k n
  invFun := affineRadicalIdealToAlgebraicSet k n
  left_inv := affineRadicalIdealToAlgebraicSet_leftInverse k n
  right_inv := affineAlgebraicSetToRadicalIdeal_rightInverse k n

theorem affineAlgebraicSetToRadicalIdeal_antitone
    {Y Z : AffineAlgebraicSet k n}
    (hYZ : (Y : Set (AffinePoint k n)) ⊆ Z) :
    affineAlgebraicSetToRadicalIdeal k n Z ≤
      affineAlgebraicSetToRadicalIdeal k n Y := by
  exact vanishingIdeal_mono k n hYZ

omit [IsAlgClosed k] in
theorem affineRadicalIdealToAlgebraicSet_antitone
    {I J : AffineRadicalIdeal k n}
    (hIJ : (I : Ideal (AffinePolynomial k n)) ≤ J) :
    (affineRadicalIdealToAlgebraicSet k n J : Set (AffinePoint k n)) ⊆
      affineRadicalIdealToAlgebraicSet k n I := by
  exact commonZeroSet_mono k n hIJ

end AffineNullstellensatzCorrespondence

section AffinePrimeCriterion

variable (k : Type*) [Field k] (n : Nat)

/-- An algebraic set is irreducible exactly when its vanishing ideal is prime. -/
theorem isAffineVariety_iff_vanishingIdeal_isPrime
    {Y : Set (AffinePoint k n)} (hY : IsAlgebraicSet k n Y) :
    IsAffineVariety k n Y ↔ (vanishingIdeal k n Y).IsPrime := by
  constructor
  · exact vanishingIdeal_isPrime_of_isAffineVariety k n
  · exact isAffineVariety_of_isAlgebraicSet_of_vanishingIdeal_isPrime k n hY

end AffinePrimeCriterion

end

end Hartshorne
