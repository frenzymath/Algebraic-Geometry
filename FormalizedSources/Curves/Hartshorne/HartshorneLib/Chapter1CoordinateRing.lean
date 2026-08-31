/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1Variety
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Hartshorne I.1: affine coordinate rings and the Nullstellensatz

The affine definitions in `Chapter1` use evaluation in the ground field.  This
file identifies them with Mathlib's `MvPolynomial` zero-locus API, records the
radical form of the affine Nullstellensatz, and packages the quotient by a
vanishing ideal as the affine coordinate ring.
-/

namespace Hartshorne

noncomputable section

section AffineCoordinateRing

variable (k : Type*) [Field k] (n : Nat)

/-- Evaluation at a point, viewed as a `k`-algebra homomorphism. -/
def evaluationAlgHom (P : AffinePoint k n) : AffinePolynomial k n →ₐ[k] k :=
  MvPolynomial.aeval P

@[simp]
theorem evaluationAlgHom_apply (P : AffinePoint k n) (f : AffinePolynomial k n) :
    evaluationAlgHom k n P f = evaluate k n f P := by
  simp [evaluationAlgHom, evaluate, MvPolynomial.aeval_def]

/-- The ideal of a one-point set is the kernel of evaluation at that point. -/
theorem vanishingIdeal_eq_ker_evaluation (P : AffinePoint k n) :
    vanishingIdeal k n ({P} : Set (AffinePoint k n)) =
      RingHom.ker (evaluationAlgHom k n P).toRingHom := by
  ext f
  simp [vanishingIdeal, evaluationAlgHom, evaluate]

/-- The zero set of an ideal agrees with the common zero set of its elements. -/
theorem commonZeroSet_eq_zeroLocus (I : Ideal (AffinePolynomial k n)) :
    commonZeroSet k n (I : Set (AffinePolynomial k n)) =
      MvPolynomial.zeroLocus k I := by
  ext P
  simp [commonZeroSet, MvPolynomial.zeroLocus, evaluate, MvPolynomial.aeval_def]

/-- Hartshorne's vanishing ideal is Mathlib's `MvPolynomial` vanishing ideal. -/
theorem vanishingIdeal_eq_mvPolynomial (Y : Set (AffinePoint k n)) :
    vanishingIdeal k n Y = MvPolynomial.vanishingIdeal k Y := by
  ext f
  simp [vanishingIdeal, MvPolynomial.vanishingIdeal, evaluate, MvPolynomial.aeval_def]

/-- Replacing a family by the ideal it generates does not change its zero set. -/
theorem commonZeroSet_span (T : Set (AffinePolynomial k n)) :
    commonZeroSet k n (Ideal.span T : Set (AffinePolynomial k n)) =
      commonZeroSet k n T := by
  ext P
  constructor
  · intro h f hf
    exact h f (Ideal.subset_span hf)
  · intro h f hf
    have hle : Ideal.span T ≤ vanishingIdeal k n ({P} : Set (AffinePoint k n)) := by
      refine Ideal.span_le.2 ?_
      intro x hx Q hQ
      rw [Set.mem_singleton_iff.mp hQ]
      exact h x hx
    exact hle hf P rfl

/-- A polynomial family has a finite subfamily with the same common zero set. -/
theorem commonZeroSet_span_finite (T : Set (AffinePolynomial k n)) :
    ∃ S : Finset (AffinePolynomial k n), (↑S : Set (AffinePolynomial k n)) ⊆ T ∧
      commonZeroSet k n (Ideal.span (↑S : Set (AffinePolynomial k n))) =
        commonZeroSet k n T := by
  have hfg : (Ideal.span T).FG := Ideal.FG.of_isNoetherianRing _
  obtain ⟨S, hsub, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := AffinePolynomial k n) T).mp hfg
  have hspan' : Ideal.span T = Ideal.span (↑S : Set (AffinePolynomial k n)) := by
    exact hspan
  refine ⟨S, hsub, ?_⟩
  rw [← hspan']
  exact commonZeroSet_span k n T

/-- Zero sets are unchanged on passing from an ideal to its radical. -/
theorem commonZeroSet_radical (I : Ideal (AffinePolynomial k n)) :
    commonZeroSet k n (I.radical : Set (AffinePolynomial k n)) =
      commonZeroSet k n (I : Set (AffinePolynomial k n)) := by
  ext P
  constructor
  · intro h f hf
    exact h f (Ideal.le_radical hf)
  · intro h f hf
    rcases (Ideal.mem_radical_iff.mp hf) with ⟨m, hm⟩
    have hz : (evaluate k n f P) ^ m = 0 := by
      simpa [evaluate_pow] using h (f ^ m) hm
    exact eq_zero_of_pow_eq_zero hz

/-!
The affine Nullstellensatz.  Mathlib proves the theorem for its
`MvPolynomial.zeroLocus`; the preceding bridge makes the statement available
with the source-facing Hartshorne names.
-/
theorem vanishingIdeal_commonZeroSet_eq_radical [IsAlgClosed k]
    (I : Ideal (AffinePolynomial k n)) :
    vanishingIdeal k n (commonZeroSet k n (I : Set (AffinePolynomial k n))) = I.radical := by
  rw [commonZeroSet_eq_zeroLocus, vanishingIdeal_eq_mvPolynomial]
  exact MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I

/-! The radical equality above is equivalent to the power-membership form used
in Hartshorne's statement of the affine Nullstellensatz. -/

/-- Hilbert's Nullstellensatz: a polynomial vanishing on `V(I)` has a positive
power in `I`. -/
theorem hilbertNullstellensatz [IsAlgClosed k]
    (I : Ideal (AffinePolynomial k n)) (f : AffinePolynomial k n)
    (hf : ∀ P ∈ commonZeroSet k n (I : Set (AffinePolynomial k n)),
      evaluate k n f P = 0) :
    ∃ r : ℕ, 0 < r ∧ f ^ r ∈ I := by
  have hfvan : f ∈ vanishingIdeal k n
      (commonZeroSet k n (I : Set (AffinePolynomial k n))) := hf
  rw [vanishingIdeal_commonZeroSet_eq_radical] at hfvan
  rcases (Ideal.mem_radical_iff.mp hfvan) with ⟨m, hm⟩
  refine ⟨m + 1, Nat.zero_lt_succ m, ?_⟩
  simpa [pow_succ] using I.mul_mem_right f hm

/-- The affine coordinate ring of an algebraic set is the quotient by its
vanishing ideal. -/
abbrev AffineCoordinateRing (Y : Set (AffinePoint k n)) :=
  AffinePolynomial k n ⧸ vanishingIdeal k n Y

/-- The canonical quotient map to an affine coordinate ring. -/
def coordinateRingMk (Y : Set (AffinePoint k n)) :
    AffinePolynomial k n →ₐ[k] AffineCoordinateRing k n Y :=
  Ideal.Quotient.mkₐ k (vanishingIdeal k n Y)

@[simp]
theorem coordinateRingMk_apply (Y : Set (AffinePoint k n))
    (f : AffinePolynomial k n) :
    coordinateRingMk k n Y f = Ideal.Quotient.mk (vanishingIdeal k n Y) f := rfl

@[simp]
theorem coordinateRingMk_ker (Y : Set (AffinePoint k n)) :
    RingHom.ker (coordinateRingMk k n Y).toRingHom = vanishingIdeal k n Y := by
  exact Ideal.Quotient.mkₐ_ker k (vanishingIdeal k n Y)

/-- Evaluation at a point is surjective because constants are in its image. -/
def eval_surjective (P : AffinePoint k n) :
    Function.Surjective (evaluationAlgHom k n P) := by
  intro z
  exact ⟨MvPolynomial.C z, by simp [evaluationAlgHom]⟩

/-- The coordinate ring of a one-point algebraic set is the ground field. -/
def singletonCoordinateRingEquiv (P : AffinePoint k n) :
    AffineCoordinateRing k n ({P} : Set (AffinePoint k n)) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq (R₁ := k)
      (vanishingIdeal_eq_ker_evaluation k n P)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (eval_surjective k n P))

/-- The one-point coordinate-ring equivalence is surjective. -/
theorem singletonCoordinateRingEquiv_surjective (P : AffinePoint k n) :
    Function.Surjective (singletonCoordinateRingEquiv k n P) :=
  (singletonCoordinateRingEquiv k n P).surjective

@[simp]
theorem singletonCoordinateRingEquiv_mk (P : AffinePoint k n)
    (f : AffinePolynomial k n) :
    singletonCoordinateRingEquiv k n P
      (Ideal.Quotient.mk (vanishingIdeal k n ({P} : Set (AffinePoint k n))) f) =
        evaluate k n f P := by
  unfold singletonCoordinateRingEquiv
  rw [AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk k (vanishingIdeal_eq_ker_evaluation k n P) f]
  exact (Ideal.quotientKerAlgEquivOfSurjective_mk (eval_surjective k n P) f).trans
    (evaluationAlgHom_apply k n P f)

end AffineCoordinateRing

end

end Hartshorne
