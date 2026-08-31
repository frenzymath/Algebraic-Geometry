/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1CoordinateRing

/-!
# Hartshorne I.1: coordinate polynomials

The affine point `Fin n -> k` presentation makes the coordinate functions
explicit.  These small lemmas let later constructions recover a point from its
polynomial evaluation map without unfolding the multivariate-polynomial API.
-/

namespace Hartshorne

noncomputable section

section AffineCoordinates

variable (k : Type*) [Field k] (n : Nat)

/-- The polynomial representing the `i`-th affine coordinate. -/
def coordinatePolynomial (i : Fin n) : AffinePolynomial k n :=
  MvPolynomial.X i

@[simp]
theorem evaluate_coordinatePolynomial (i : Fin n) (P : AffinePoint k n) :
    evaluate k n (coordinatePolynomial k n i) P = P i := by
  simp [coordinatePolynomial, evaluate]

/-- The constant polynomial with prescribed value in the ground field. -/
def constantPolynomial (a : k) : AffinePolynomial k n :=
  MvPolynomial.C a

@[simp]
theorem evaluate_constantPolynomial (a : k) (P : AffinePoint k n) :
    evaluate k n (constantPolynomial k n a) P = a := by
  simp [constantPolynomial, evaluate]

/-- Affine points are determined by the values of their coordinate polynomials. -/
theorem affinePoint_ext {P Q : AffinePoint k n}
    (h : ∀ i : Fin n,
      evaluate k n (coordinatePolynomial k n i) P =
        evaluate k n (coordinatePolynomial k n i) Q) :
    P = Q := by
  funext i
  simpa only [evaluate_coordinatePolynomial] using h i

theorem affinePoint_eq_iff {P Q : AffinePoint k n} :
    P = Q ↔ ∀ i : Fin n,
      evaluate k n (coordinatePolynomial k n i) P =
        evaluate k n (coordinatePolynomial k n i) Q := by
  constructor
  · intro h
    subst Q
    intro i
    rfl
  · exact affinePoint_ext k n

/-- Evaluation homomorphisms agree exactly when their points agree. -/
theorem evaluationAlgHom_eq_iff {P Q : AffinePoint k n} :
    evaluationAlgHom k n P = evaluationAlgHom k n Q ↔ P = Q := by
  constructor
  · intro h
    apply affinePoint_ext k n
    intro i
    have hi := congrArg
      (fun φ : AffinePolynomial k n →ₐ[k] k =>
        φ (coordinatePolynomial k n i)) h
    simpa only [evaluationAlgHom_apply, evaluate_coordinatePolynomial] using hi
  · intro h
    subst Q
    rfl

theorem evaluationAlgHom_injective :
    Function.Injective (evaluationAlgHom k n) := by
  intro P Q h
  exact (evaluationAlgHom_eq_iff k n).mp h

end AffineCoordinates

end

end Hartshorne
