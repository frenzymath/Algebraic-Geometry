/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ProjectiveSpaceAffineChart
import AlgebraicJacobian.Picard.RigidPushforwardP1ChartRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Fintype.BigOperators

/-!
# The standard projective chart ring

For a finite coordinate type `n`, this file identifies the degree-zero
homogeneous localization of `R[X_none, X_i]` at `X_none` with the polynomial
ring `R[X_i]`. This is the algebraic half of the standard-chart identification
between `ProjectiveSpace.affineChart n S` and affine space over `S`.
-/

set_option autoImplicit false

open MvPolynomial HomogeneousLocalization

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.AffineChartRing

section

variable (R : Type u) [CommRing R]
variable (n : Type u)

/-- Every homogeneous coordinate, including the homogenizing coordinate, has
degree one. -/
theorem X_mem_deg_one (i : Option n) :
    (X i : MvPolynomial (Option n) R) ∈ homogeneousSubmodule (Option n) R 1 :=
  isHomogeneous_X _ _

/-- The degree-zero part of the homogeneous coordinate ring consists of the
constants. -/
theorem exists_algebraMap_eq_gradeZero
    (c : homogeneousSubmodule (Option n) R 0) :
    ∃ r : R, algebraMap R (homogeneousSubmodule (Option n) R 0) r = c := by
  have hc : (c : MvPolynomial (Option n) R) ∈
      (1 : Submodule R (MvPolynomial (Option n) R)) := by
    rw [← homogeneousSubmodule_zero (σ := Option n) (R := R)]
    exact c.2
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
  exact ⟨r, Subtype.ext (by simpa using hr)⟩

/-- The homogeneous coordinate ring is generated over its degree-zero part by
its variables. -/
theorem adjoin_gradeZero_range_X :
    Algebra.adjoin (homogeneousSubmodule (Option n) R 0)
      (Set.range (X : Option n → MvPolynomial (Option n) R)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  have hp : p ∈ Algebra.adjoin R
      (Set.range (X : Option n → MvPolynomial (Option n) R)) := by
    rw [MvPolynomial.adjoin_range_X]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem q hq => exact Algebra.subset_adjoin hq
  | algebraMap r =>
      exact Subalgebra.algebraMap_mem _
        (⟨algebraMap R (MvPolynomial (Option n) R) r, by
          rw [MvPolynomial.algebraMap_eq]
          exact isHomogeneous_C _ r⟩ : homogeneousSubmodule (Option n) R 0)
  | add q₁ q₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
  | mul q₁ q₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂

variable [GradedAlgebra (homogeneousSubmodule (Option n) R)]

/-- The normalized affine coordinate `X_j / X_none`. -/
def chartCoord (j : n) :
    Away (homogeneousSubmodule (Option n) R) (X none) :=
  Away.mk (homogeneousSubmodule (Option n) R) (X_mem_deg_one R n none) 1 (X (some j))
    (by simpa using X_mem_deg_one R n (some j))

/-- Dehomogenization sends `X_none` to one and every `X_j` to the
corresponding affine variable. -/
def dehomogenize : MvPolynomial (Option n) R →ₐ[R] MvPolynomial n R :=
  MvPolynomial.aeval fun o => o.elim 1 (fun j => X j)

omit [GradedAlgebra (homogeneousSubmodule (Option n) R)] in
@[simp]
theorem dehomogenize_X_none : dehomogenize R n (X none) = 1 := by
  simp [dehomogenize]

omit [GradedAlgebra (homogeneousSubmodule (Option n) R)] in
@[simp]
theorem dehomogenize_X_some (j : n) : dehomogenize R n (X (some j)) = X j := by
  simp [dehomogenize]

omit [GradedAlgebra (homogeneousSubmodule (Option n) R)] in
private theorem isUnit_dehomogenize_X_none :
    IsUnit ((dehomogenize R n).toRingHom (X none)) := by
  have h : (dehomogenize R n).toRingHom (X none) = 1 := by
    change dehomogenize R n (X none) = 1
    exact dehomogenize_X_none R n
  rw [h]
  exact isUnit_one

/-- The map from affine polynomials to the standard chart ring. -/
def polyToAway : MvPolynomial n R →ₐ[R]
    Away (homogeneousSubmodule (Option n) R) (X none) :=
  MvPolynomial.aeval (chartCoord R n)

@[simp]
theorem polyToAway_X (j : n) : polyToAway R n (X j) = chartCoord R n j :=
  MvPolynomial.aeval_X _ _

/-- Dehomogenization descends from the ordinary localization to its
degree-zero subring. -/
def awayToPoly : Away (homogeneousSubmodule (Option n) R) (X none) →ₐ[R]
    MvPolynomial n R where
  toRingHom :=
    (Localization.awayLift (dehomogenize R n).toRingHom (X none)
      (isUnit_dehomogenize_X_none R n)).comp
      (algebraMap (Away (homogeneousSubmodule (Option n) R) (X none))
        (Localization.Away (X none : MvPolynomial (Option n) R)))
  commutes' r := by
    change (Localization.awayLift (dehomogenize R n).toRingHom (X none)
        (isUnit_dehomogenize_X_none R n))
        ((algebraMap R (Away (homogeneousSubmodule (Option n) R) (X none)) r).val) =
      algebraMap R (MvPolynomial n R) r
    rw [HomogeneousLocalization.algebraMap_val, IsLocalization.Away.lift_eq]
    exact (dehomogenize R n).commutes r

/-- Evaluation of `awayToPoly` on a homogeneous fraction. -/
theorem awayToPoly_mk (a : ℕ) (p : MvPolynomial (Option n) R)
    (hp : p ∈ homogeneousSubmodule (Option n) R (a • 1)) :
    awayToPoly R n
        (Away.mk (homogeneousSubmodule (Option n) R) (X_mem_deg_one R n none) a p hp) =
      dehomogenize R n p := by
  have h1 : (dehomogenize R n).toRingHom (X none) * 1 = 1 := by
    rw [mul_one]
    change dehomogenize R n (X none) = 1
    exact dehomogenize_X_none R n
  have h := Localization.awayLift_mk (A := MvPolynomial n R)
    ((dehomogenize R n).toRingHom) (X none) p 1 h1 a
  exact h.trans (by rw [one_pow, mul_one]; rfl)

@[simp]
theorem awayToPoly_chartCoord (j : n) :
    awayToPoly R n (chartCoord R n j) = X j :=
  (awayToPoly_mk R n 1 (X (some j))
    (by simpa using X_mem_deg_one R n (some j))).trans
      (dehomogenize_X_some R n j)

/-- Dehomogenization is a left inverse to the affine-coordinate map. -/
theorem awayToPoly_comp_polyToAway :
    (awayToPoly R n).comp (polyToAway R n) =
      AlgHom.id R (MvPolynomial n R) := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [AlgHom.comp_apply, polyToAway_X, awayToPoly_chartCoord, AlgHom.id_apply]

/-! ### Surjectivity of the affine-coordinate map -/

variable [Finite n]
local instance : Fintype n := Fintype.ofFinite n

/-- Reading the total degree off an exponent vector indexed by `Option n`. -/
private theorem degree_eq {e : Option n → ℕ} {a : ℕ}
    (hae : ∑ l, e l • (1 : ℕ) = a • (1 : ℕ)) :
    e none + ∑ j, e (some j) = a := by
  simpa [Fintype.sum_option] using hae

omit [Finite n] in
/-- The value of a normalized affine coordinate in the ordinary localization. -/
theorem val_chartCoord (j : n) :
    (chartCoord R n j).val = Localization.mk (X (some j))
      (⟨X none ^ 1, 1, rfl⟩ :
        Submonoid.powers (X none : MvPolynomial (Option n) R)) :=
  rfl

/-- A spanning homogeneous monomial is the corresponding monomial in the
normalized affine coordinates. -/
private theorem away_mk_prod_eq (a : ℕ) (e : Option n → ℕ)
    (hae : e none + ∑ j, e (some j) = a)
    (H : (∏ l, (X l : MvPolynomial (Option n) R) ^ e l) ∈
      homogeneousSubmodule (Option n) R (a • 1)) :
    Away.mk (homogeneousSubmodule (Option n) R) (X_mem_deg_one R n none) a
        (∏ l, X l ^ e l) H =
      ∏ j, chartCoord R n j ^ e (some j) := by
  apply (show Function.Injective (algebraMap
      (Away (homogeneousSubmodule (Option n) R) (X none))
      (Localization.Away (X none : MvPolynomial (Option n) R))) from
    HomogeneousLocalization.val_injective _)
  simp only [map_prod, map_pow, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, chartCoord, Localization.mk_pow, Localization.mk_prod]
  rw [Fintype.prod_option, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  push_cast
  rw [Finset.prod_pow_eq_pow_sum, ← hae, pow_add]
  ring

/-- Every element of the standard chart ring is a polynomial in the normalized
affine coordinates. -/
theorem polyToAway_surjective : Function.Surjective (polyToAway R n) := by
  intro z
  have hz : z ∈
      (⊤ : Submodule (homogeneousSubmodule (Option n) R 0)
        (Away (homogeneousSubmodule (Option n) R) (X none))) := trivial
  rw [← Away.span_mk_prod_pow_eq_top (X_mem_deg_one R n none) X
    (adjoin_gradeZero_range_X R n) (fun _ => 1) (fun l => X_mem_deg_one R n l)] at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨a, e, hae, rfl⟩ := hw
      refine ⟨∏ j, X j ^ e (some j), ?_⟩
      rw [map_prod]
      simp_rw [map_pow, polyToAway_X]
      exact (away_mk_prod_eq R n a e (degree_eq n hae) _).symm
  | zero => exact ⟨0, map_zero _⟩
  | add u v _ _ hu hv =>
      obtain ⟨p, rfl⟩ := hu
      obtain ⟨q, rfl⟩ := hv
      exact ⟨p + q, map_add _ _ _⟩
  | smul c w _ hw =>
      obtain ⟨p, rfl⟩ := hw
      obtain ⟨r, rfl⟩ := exists_algebraMap_eq_gradeZero R n c
      exact ⟨r • p, by rw [map_smul, IsScalarTower.algebraMap_smul]⟩

omit [Finite n] in
theorem awayToPoly_polyToAway_apply (p : MvPolynomial n R) :
    awayToPoly R n (polyToAway R n p) = p :=
  AlgHom.congr_fun (awayToPoly_comp_polyToAway R n) p

/-- The affine-coordinate map is also a left inverse to dehomogenization. -/
theorem polyToAway_comp_awayToPoly :
    (polyToAway R n).comp (awayToPoly R n) =
      AlgHom.id R (Away (homogeneousSubmodule (Option n) R) (X none)) := by
  refine AlgHom.ext fun z => ?_
  obtain ⟨p, rfl⟩ := polyToAway_surjective R n z
  rw [AlgHom.comp_apply, AlgHom.id_apply, awayToPoly_polyToAway_apply]

/-- The standard projective chart ring is the polynomial ring on the remaining
homogeneous coordinates. -/
def awayAlgEquiv :
    Away (homogeneousSubmodule (Option n) R) (X none) ≃ₐ[R] MvPolynomial n R :=
  AlgEquiv.ofAlgHom (awayToPoly R n) (polyToAway R n)
    (awayToPoly_comp_polyToAway R n) (polyToAway_comp_awayToPoly R n)

@[simp]
theorem awayAlgEquiv_chartCoord (j : n) :
    awayAlgEquiv R n (chartCoord R n j) = X j :=
  awayToPoly_chartCoord R n j

@[simp]
theorem awayAlgEquiv_symm_X (j : n) :
    (awayAlgEquiv R n).symm (X j) = chartCoord R n j :=
  (awayAlgEquiv R n).symm_apply_eq.mpr (awayAlgEquiv_chartCoord R n j).symm

end

end AlgebraicGeometry.ProjectiveSpace.AffineChartRing
