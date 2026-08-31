/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.ClosedPoint

/-!
# Weil divisors on a curve and their degree

For the curve bundle `X` over a field `K`, a Weil divisor is a finitely supported
`ℤ`-valued function on the closed points (identified with the non-generic points):

* `AlgebraicGeometry.Scheme.CurveDivisor`: the group of Weil divisors, `{x // x ≠ η} →₀ ℤ`,
  with its `Finsupp`-inherited `AddCommGroup` and pointwise partial order (independent of the
  base field).
* `AlgebraicGeometry.Scheme.CurveDivisor.deg`: the degree `∑ nₓ · [κ(x) : K]`, weighted by the
  residue degrees over the base field (the correct notion over a non-closed base field), with
  additivity `deg_add` and the single-point value `deg_single`.

The residue-degree weighting is essential over a non-closed field: for `X = ℙ¹_ℝ` and the
rational function `t² + 1`, the principal divisor is `x_{t²+1} − 2·∞`, whose *unweighted*
point count is `1 − 2 = −1 ≠ 0`, while the residue-weighted degree `1·[ℂ:ℝ] − 2·[ℝ:ℝ] = 0`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/-- A **Weil divisor** on the curve `X`: a finitely supported `ℤ`-valued function on the
closed points, identified with the non-generic points of the irreducible scheme.  Carries the
`Finsupp` `AddCommGroup` structure and the pointwise partial order.  Independent of the base
field. -/
def CurveDivisor (X : Scheme.{u}) [IsIntegral X] : Type u :=
  {x : X // x ≠ genericPoint X} →₀ ℤ

namespace CurveDivisor

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable instance : AddCommGroup X.CurveDivisor :=
  inferInstanceAs (AddCommGroup ({x : X // x ≠ genericPoint X} →₀ ℤ))

instance : PartialOrder X.CurveDivisor :=
  inferInstanceAs (PartialOrder ({x : X // x ≠ genericPoint X} →₀ ℤ))

section Degree

variable (K : Type u) [CommRing K] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] Scheme.residueFieldOverModule

/-- The **degree** of a Weil divisor, weighted by the residue degrees over the base field:
`deg D = ∑ₓ Dₓ · [κ(x) : K]`. -/
noncomputable def deg (D : X.CurveDivisor) : ℤ :=
  D.sum fun x n => n * (X.residueDeg K x.1 : ℤ)

@[simp]
theorem deg_zero : deg K (0 : X.CurveDivisor) = 0 := by
  simp only [deg]
  exact Finsupp.sum_zero_index

/-- Degree is additive. -/
theorem deg_add (D D' : X.CurveDivisor) : deg K (D + D') = deg K D + deg K D' := by
  simp only [deg]
  refine Finsupp.sum_add_index' (fun _ => ?_) (fun _ b₁ b₂ => ?_)
  · simp
  · ring

/-- The degree of a single-point divisor `n · x` is `n · [κ(x) : K]`. -/
theorem deg_single (x : {x : X // x ≠ genericPoint X}) (n : ℤ) :
    deg K (Finsupp.single x n : X.CurveDivisor) = n * (X.residueDeg K x.1 : ℤ) := by
  simp only [deg]
  refine Finsupp.sum_single_index ?_
  simp

/-- Degree of a negated divisor. -/
theorem deg_neg (D : X.CurveDivisor) : deg K (-D) = -deg K D := by
  have h := deg_add K D (-D)
  rw [add_neg_cancel, deg_zero] at h
  linarith

end Degree

end CurveDivisor

end Scheme

end AlgebraicGeometry
