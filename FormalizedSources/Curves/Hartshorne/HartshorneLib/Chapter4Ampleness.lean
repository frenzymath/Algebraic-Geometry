/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4LinearSystemCriteria

/-!
# Hartshorne IV.3.3: ample divisors on a curve

On a complete nonsingular curve, positivity of the divisor degree is the
numerical ampleness criterion.  The geometric definition of an ample
invertible sheaf is not yet part of this project API, so `AmpleCurveDivisor`
records the source criterion directly.  The main consequence is constructive:
an ample divisor has an explicitly bounded positive multiple whose numerical
linear system is very ample (and hence base-point-free in the corresponding
threshold sense).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-- Numerical ampleness for a divisor on a smooth proper integral curve. -/
def AmpleCurveDivisor (D : CurveDivisor k X) : Prop :=
  0 < CurveDivisor.degree D

/-- The curve ampleness predicate is exactly positivity of degree. -/
theorem ampleCurveDivisor_iff_degree_pos (D : CurveDivisor k X) :
    AmpleCurveDivisor D ↔ 0 < CurveDivisor.degree D :=
  Iff.rfl

private lemma one_le_degree_of_ample {D : CurveDivisor k X}
    (hD : AmpleCurveDivisor D) :
    (1 : ℤ) ≤ CurveDivisor.degree D := by
  dsimp [AmpleCurveDivisor] at hD
  omega

private lemma degree_threshold_le_nsmul_one (g : ℕ) {n : ℕ}
    (hn : 2 * g + 1 ≤ n) :
    (2 * (g : ℤ) + 1) ≤ n • (1 : ℤ) := by
  have hcast : (2 * (g : ℤ) + 1) ≤ (n : ℤ) := by
    exact_mod_cast hn
  simpa only [Nat.smul_one_eq_cast] using hcast

/-- Any multiple at least `2g+1` of an ample divisor is numerically very ample. -/
theorem veryAmpleLinearSystem_of_ample_nsmul
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X} {n : ℕ}
    (hD : AmpleCurveDivisor D)
    (hn : 2 * curveGenus (k := k) (X := X) + 1 ≤ n) :
    VeryAmpleLinearSystem (n • D) := by
  apply veryAmpleLinearSystem_of_degree_ge_two_mul_genus_plus_one
    (k := k) (X := X) sd
  rw [CurveDivisor.degree_nsmul]
  have hscale := nsmul_le_nsmul_right (one_le_degree_of_ample hD) n
  exact (degree_threshold_le_nsmul_one
    (curveGenus (k := k) (X := X)) hn).trans hscale

/-- Any multiple at least `2g+1` of an ample divisor is numerically
base-point-free. -/
theorem basePointFreeLinearSystem_of_ample_nsmul
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X} {n : ℕ}
    (hD : AmpleCurveDivisor D)
    (hn : 2 * curveGenus (k := k) (X := X) + 1 ≤ n) :
    BasePointFreeLinearSystem (n • D) := by
  apply basePointFreeLinearSystem_of_degree_ge_two_mul_genus
    (k := k) (X := X) sd
  rw [CurveDivisor.degree_nsmul]
  have hscale := nsmul_le_nsmul_right (one_le_degree_of_ample hD) n
  have hge := (degree_threshold_le_nsmul_one
    (curveGenus (k := k) (X := X)) hn).trans hscale
  exact (show (2 * (curveGenus (k := k) (X := X) : ℤ) : ℤ) ≤
      2 * (curveGenus (k := k) (X := X) : ℤ) + 1 by omega).trans hge

/-- A positive-degree divisor has a positive very-ample multiple. -/
theorem exists_veryAmple_nsmul_of_ample
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X} (hD : AmpleCurveDivisor D) :
    ∃ n : ℕ, 0 < n ∧ VeryAmpleLinearSystem (n • D) := by
  let n : ℕ := 2 * curveGenus (k := k) (X := X) + 1
  refine ⟨n, ?_, ?_⟩
  · dsimp [n]
    omega
  · exact veryAmpleLinearSystem_of_ample_nsmul (k := k) (X := X) sd hD le_rfl

/-- A positive-degree divisor has a positive base-point-free multiple. -/
theorem exists_basePointFree_nsmul_of_ample
    (sd : CurveSerreDualityData (k := k) (X := X))
    {D : CurveDivisor k X} (hD : AmpleCurveDivisor D) :
    ∃ n : ℕ, 0 < n ∧ BasePointFreeLinearSystem (n • D) := by
  let n : ℕ := 2 * curveGenus (k := k) (X := X) + 1
  refine ⟨n, ?_, ?_⟩
  · dsimp [n]
    omega
  · exact basePointFreeLinearSystem_of_ample_nsmul (k := k) (X := X) sd hD le_rfl

end
end Hartshorne
