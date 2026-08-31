/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4Curves

/-!
# Hartshorne IV.1: divisor dévissage

This file supplies the finite-support bookkeeping used to peel off one copy of
a non-generic point from a curve divisor.  The induction theorem is purely
algebraic: it is the integer-coefficient `Finsupp.induction` argument, with no
geometric existence assumptions beyond those already in `CurveDivisor`.
-/

set_option autoImplicit false

universe u v

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

namespace CurveDivisor

/-! ## One-point divisors and the dévissage step -/

/-- The divisor supported at one non-generic point with integer coefficient `n`. -/
noncomputable def single {x : X.left} (hx : x ≠ genericPoint X.left) (n : ℤ) :
    CurveDivisor k X :=
  Finsupp.single (⟨x, hx⟩ : {p : X.left // p ≠ genericPoint X.left}) n

/-- Remove one copy of a chosen non-generic point from a divisor. -/
noncomputable def devissageDivisor {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) : CurveDivisor k X :=
  D - single hx 1

@[simp]
theorem single_zero {x : X.left} (hx : x ≠ genericPoint X.left) :
    single hx 0 = (0 : CurveDivisor k X) := by
  change Finsupp.single (⟨x, hx⟩ : {p : X.left // p ≠ genericPoint X.left}) (0 : ℤ) = 0
  exact Finsupp.single_zero _

theorem single_add {x : X.left} (hx : x ≠ genericPoint X.left) (m n : ℤ) :
    single hx m + single hx n = single hx (m + n) := by
  change Finsupp.single (⟨x, hx⟩ : {p : X.left // p ≠ genericPoint X.left}) m +
      Finsupp.single ⟨x, hx⟩ n = Finsupp.single ⟨x, hx⟩ (m + n)
  exact (Finsupp.single_add _ _ _).symm

theorem nsmul_single_one {x : X.left} (hx : x ≠ genericPoint X.left) (n : ℕ) :
    n • single hx 1 = single hx (n : ℤ) := by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, single_zero]
  | succ n ih =>
    rw [succ_nsmul, ih, single_add, Nat.cast_add, Nat.cast_one]

@[simp]
theorem devissageDivisor_eq_sub {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    devissageDivisor hx D = D - single hx 1 :=
  rfl

theorem devissageDivisor_add_single {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    devissageDivisor hx D + single hx 1 = D := by
  rw [devissageDivisor_eq_sub]
  exact sub_add_cancel D (single hx 1)

/-! ## Integer-coefficient induction -/

/-- A single-unit bump suffices to prove a predicate on all integer-valued
finitely supported functions. -/
private theorem finsupp_induction_bump {α : Type u} {P : (α →₀ ℤ) → Prop}
    (zero : P 0)
    (bump : ∀ (a : α) (f : α →₀ ℤ), P (f + Finsupp.single a 1) ↔ P f)
    (f : α →₀ ℤ) : P f := by
  have hn : ∀ (n : ℤ), ∀ (a : α) (f : α →₀ ℤ),
      P (f + Finsupp.single a n) ↔ P f := by
    intro n
    induction n using Int.induction_on with
    | zero =>
        intro a f
        rw [Finsupp.single_zero, add_zero]
    | succ n ih =>
        intro a f
        have h1 : f + Finsupp.single a ((n : ℤ) + 1) =
            f + Finsupp.single a (n : ℤ) + Finsupp.single a 1 := by
          rw [Finsupp.single_add, add_assoc]
        rw [h1, bump a (f + Finsupp.single a (n : ℤ)), ih a f]
    | pred n ih =>
        intro a f
        have h1 : f + Finsupp.single a (-(n : ℤ) - 1) +
            Finsupp.single a 1 = f + Finsupp.single a (-(n : ℤ)) := by
          rw [add_assoc, ← Finsupp.single_add]
          norm_num
        rw [← ih a f, ← bump a (f + Finsupp.single a (-(n : ℤ) - 1)), h1]
  induction f using Finsupp.induction with
  | zero => exact zero
  | single_add a b f _ _ ih =>
      rw [show Finsupp.single a b + f = f + Finsupp.single a b from add_comm _ _]
      exact (hn b a f).mpr ih

/-- If a predicate holds at zero and is invariant in both directions under
the one-point dévissage step, it holds for every curve divisor. -/
theorem induction_devissage {P : CurveDivisor k X → Prop} (zero : P 0)
    (step : ∀ {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X),
      P D ↔ P (devissageDivisor hx D))
    (D : CurveDivisor k X) : P D := by
  refine finsupp_induction_bump (P := fun F : {p : X.left // p ≠ genericPoint X.left} →₀ ℤ => P F)
    zero (fun p F => ?_) D
  let F' : CurveDivisor k X := F
  have h := step p.2 (F' + single p.2 1)
  have h2 : P (devissageDivisor p.2 (F' + single p.2 1)) ↔ P F' := by
    have heq : devissageDivisor p.2 (F' + single p.2 1) = F' := by
      unfold devissageDivisor
      abel
    rw [heq]
  exact h.trans h2

/-! ## Finite-sum form of additive divisor maps -/

/-- An additive map out of divisors is determined by its values on one-point
divisors, with the finite support providing the sum. -/
theorem addHom_apply_eq_sum_single_smul
    {A : Type v} [AddCommGroup A] (φ : CurveDivisor k X →+ A)
    (D : CurveDivisor k X) :
    φ D = ∑ x ∈ (show PointDivisor X.left from D).support,
      ((show PointDivisor X.left from D).toFun x : ℤ) •
        φ (single x.2 1) := by
  change (({x : X.left // x ≠ genericPoint X.left} →₀ ℤ) →+ A) at φ
  change ({x : X.left // x ≠ genericPoint X.left} →₀ ℤ) at D
  change φ D = ∑ x ∈ D.support, (D x : ℤ) • φ (Finsupp.single x 1)
  calc
    φ D = φ (D.sum (fun x n => Finsupp.single x n)) := by
      rw [Finsupp.sum_single]
    _ = ∑ x ∈ D.support, φ (Finsupp.single x (D x)) := by
      simp only [Finsupp.sum]
      rw [map_sum]
    _ = ∑ x ∈ D.support, (D x : ℤ) • φ (Finsupp.single x 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finsupp.smul_single_one]
      rw [map_zsmul]

end CurveDivisor

end Hartshorne
