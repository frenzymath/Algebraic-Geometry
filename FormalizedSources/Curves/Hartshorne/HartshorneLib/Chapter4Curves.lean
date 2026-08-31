/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Hartshorne IV.1: divisors on an integral curve

This file records the finite-formal-sum model of divisors used for curves.  The
degree is the unweighted sum of coefficients, matching Hartshorne's convention
over an algebraically closed base field.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

/-- A finite integer linear combination of the non-generic points of an
integral scheme. -/
def PointDivisor (X : Scheme.{u}) [IsIntegral X] : Type u :=
  {x : X // x ≠ genericPoint X} →₀ ℤ

/-- A divisor on a complete nonsingular integral curve over an algebraically
closed field. -/
def CurveDivisor (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] : Type u :=
  PointDivisor X.left

namespace CurveDivisor

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

noncomputable instance : AddCommGroup (CurveDivisor k X) :=
  inferInstanceAs (AddCommGroup ({x : X.left // x ≠ genericPoint X.left} →₀ ℤ))

instance : PartialOrder (CurveDivisor k X) :=
  inferInstanceAs (PartialOrder ({x : X.left // x ≠ genericPoint X.left} →₀ ℤ))

noncomputable instance : Lattice (CurveDivisor k X) :=
  inferInstanceAs (Lattice ({x : X.left // x ≠ genericPoint X.left} →₀ ℤ))

/-- The unweighted degree, appropriate over an algebraically closed base field. -/
noncomputable def degree (D : CurveDivisor k X) : ℤ :=
  D.sum fun _ n => n

/-- Degree as an additive homomorphism. -/
noncomputable def degreeHom : CurveDivisor k X →+ ℤ :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

/-! ### Coefficients and effectivity -/

/-- The coefficient of a divisor at a non-generic point. -/
def coeffAt {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) : ℤ :=
  (show PointDivisor X.left from D).toFun ⟨x, hx⟩

@[simp]
theorem coeffAt_zero {x : X.left} (hx : x ≠ genericPoint X.left) :
    coeffAt hx (0 : CurveDivisor k X) = 0 := by
  rfl

@[simp]
theorem coeffAt_add {x : X.left} (hx : x ≠ genericPoint X.left)
    (D E : CurveDivisor k X) :
    coeffAt hx (D + E) = coeffAt hx D + coeffAt hx E := by
  rfl

@[simp]
theorem coeffAt_neg {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    coeffAt hx (-D) = -coeffAt hx D := by
  rfl

@[simp]
theorem coeffAt_sub {x : X.left} (hx : x ≠ genericPoint X.left)
    (D E : CurveDivisor k X) :
    coeffAt hx (D - E) = coeffAt hx D - coeffAt hx E := by
  rfl

@[simp]
theorem coeffAt_inf {x : X.left} (hx : x ≠ genericPoint X.left)
    (D E : CurveDivisor k X) :
    coeffAt hx (D ⊓ E) = min (coeffAt hx D) (coeffAt hx E) := by
  rfl

@[simp]
theorem coeffAt_sup {x : X.left} (hx : x ≠ genericPoint X.left)
    (D E : CurveDivisor k X) :
    coeffAt hx (D ⊔ E) = max (coeffAt hx D) (coeffAt hx E) := by
  rfl

/-- Coefficients at all closed points determine a curve divisor. -/
theorem ext_coeffAt {D E : CurveDivisor k X}
    (h : ∀ (x : X.left) (hx : x ≠ genericPoint X.left),
      coeffAt hx D = coeffAt hx E) : D = E := by
  apply Finsupp.ext
  intro x
  exact h x.1 x.2

/-- Pointwise minimum plus maximum equals the sum of the two divisors. -/
theorem inf_add_sup (D E : CurveDivisor k X) :
    (D ⊓ E) + (D ⊔ E) = D + E := by
  apply ext_coeffAt
  intro x hx
  rw [coeffAt_add, coeffAt_add, coeffAt_inf, coeffAt_sup]
  exact min_add_max _ _

/-- The divisor order is the pointwise coefficient order. -/
theorem le_iff_coeffAt {D E : CurveDivisor k X} :
    D ≤ E ↔ ∀ (x : X.left) (hx : x ≠ genericPoint X.left),
      coeffAt hx D ≤ coeffAt hx E := by
  constructor
  · intro h x hx
    exact Finsupp.le_def.mp h ⟨x, hx⟩
  · intro h
    change ∀ x, _
    intro x
    exact h x.1 x.2

/-! ### Degree and effective divisors -/

/-- An effective divisor has nonnegative degree. -/
theorem degree_nonneg {D : CurveDivisor k X} (hD : 0 ≤ D) :
    0 ≤ degree D := by
  exact Finsupp.sum_nonneg fun x _ => Finsupp.le_def.mp hD x

/-- An effective divisor of degree zero is the zero divisor. -/
theorem eq_zero_of_nonneg_of_degree_eq_zero {D : CurveDivisor k X}
    (hD : 0 ≤ D) (hdegree : degree D = 0) : D = 0 := by
  apply Finsupp.ext
  intro x
  change (show PointDivisor X.left from D).toFun x = 0
  have hxnonneg : 0 ≤ (show PointDivisor X.left from D).toFun x := by
    exact Finsupp.le_def.mp hD x
  by_contra hne
  have hxpos : 0 < (show PointDivisor X.left from D).toFun x := by
    omega
  have hmem : x ∈ (show PointDivisor X.left from D).support :=
    Finsupp.mem_support_iff.mpr hne
  have hterms : ∀ y ∈ (show PointDivisor X.left from D).support,
      0 ≤ (show PointDivisor X.left from D).toFun y := by
    intro y hy
    exact Finsupp.le_def.mp hD y
  have hsumpos : 0 < degree D := by
    exact Finsupp.sum_pos' hterms ⟨x, hmem, hxpos⟩
  omega

/-- A nonzero effective divisor has positive degree. -/
theorem degree_pos_of_nonneg_of_ne_zero {D : CurveDivisor k X}
    (hD : 0 ≤ D) (hne : D ≠ 0) : 0 < degree D := by
  have hnonneg := degree_nonneg hD
  have hdegree : degree D ≠ 0 := fun h =>
    hne (eq_zero_of_nonneg_of_degree_eq_zero hD h)
  omega

@[simp]
theorem degreeHom_apply (D : CurveDivisor k X) : degreeHom D = degree D :=
  Finsupp.liftAddHom_apply
    (α := {x : X.left // x ≠ genericPoint X.left}) (M := ℤ) (N := ℤ)
    (fun _ => AddMonoidHom.id ℤ) D

@[simp]
theorem degree_zero : degree (0 : CurveDivisor k X) = 0 := by
  rw [← degreeHom_apply]
  exact map_zero degreeHom

theorem degree_eq_zero_iff_of_nonneg {D : CurveDivisor k X} (hD : 0 ≤ D) :
    degree D = 0 ↔ D = 0 := by
  constructor
  · exact eq_zero_of_nonneg_of_degree_eq_zero hD
  · intro h
    rw [h, degree_zero]

theorem degree_add (D E : CurveDivisor k X) :
    degree (D + E) = degree D + degree E := by
  rw [← degreeHom_apply, ← degreeHom_apply, ← degreeHom_apply]
  exact map_add degreeHom D E

@[simp]
theorem degree_neg (D : CurveDivisor k X) : degree (-D) = -degree D := by
  rw [← degreeHom_apply, ← degreeHom_apply]
  exact map_neg degreeHom D

theorem degree_sub (D E : CurveDivisor k X) :
    degree (D - E) = degree D - degree E := by
  rw [← degreeHom_apply, ← degreeHom_apply, ← degreeHom_apply]
  exact map_sub degreeHom D E

@[simp]
theorem degree_nsmul (n : ℕ) (D : CurveDivisor k X) :
    degree (n • D) = n • degree D := by
  rw [← degreeHom_apply, ← degreeHom_apply]
  exact map_nsmul (degreeHom (k := k) (X := X)) n D

theorem degree_zsmul (n : ℤ) (D : CurveDivisor k X) :
    degree (n • D) = n • degree D := by
  rw [← degreeHom_apply, ← degreeHom_apply]
  exact map_zsmul (degreeHom (k := k) (X := X)) n D

/-- Degree is monotone for the pointwise divisor order. -/
theorem degree_mono {D E : CurveDivisor k X} (hDE : D ≤ E) :
    degree D ≤ degree E := by
  have hdiff : 0 ≤ E - D := by
    rw [le_iff_coeffAt]
    intro x hx
    rw [coeffAt_sub, coeffAt_zero]
    exact sub_nonneg.mpr (le_iff_coeffAt.mp hDE x hx)
  have hdegree := degree_nonneg hdiff
  rw [degree_sub] at hdegree
  omega

/-- The degrees of the infimum and supremum balance those of the two divisors. -/
theorem degree_inf_add_degree_sup (D E : CurveDivisor k X) :
    degree (D ⊓ E) + degree (D ⊔ E) = degree D + degree E := by
  rw [← degree_add, inf_add_sup, degree_add]

@[simp]
theorem degree_single (x : {x : X.left // x ≠ genericPoint X.left}) (n : ℤ) :
    degree (Finsupp.single x n : CurveDivisor k X) = n := by
  simp [degree]

/-- The support of an effective divisor has at most as many points as its degree. -/
theorem support_card_le_degree {D : CurveDivisor k X} (hD : 0 ≤ D) :
    ((show PointDivisor X.left from D).support.card : ℤ) ≤ degree D := by
  rw [degree]
  calc
    ((show PointDivisor X.left from D).support.card : ℤ) =
        ∑ x ∈ (show PointDivisor X.left from D).support, (1 : ℤ) := by
      simp
    _ ≤ ∑ x ∈ (show PointDivisor X.left from D).support,
        (show PointDivisor X.left from D).toFun x := by
      gcongr with x hx
      have hxnonneg : 0 ≤ (show PointDivisor X.left from D).toFun x :=
        Finsupp.le_def.mp hD x
      have hxne : (show PointDivisor X.left from D).toFun x ≠ 0 :=
        Finsupp.mem_support_iff.mp hx
      omega
    _ = (show PointDivisor X.left from D).sum (fun _ n => n) := rfl

end CurveDivisor

end Hartshorne
