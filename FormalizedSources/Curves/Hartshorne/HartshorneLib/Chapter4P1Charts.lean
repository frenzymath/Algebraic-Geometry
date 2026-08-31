/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import Mathlib

/-!
# The projective line and its standard affine charts

This file provides the standard `Proj` model of the projective line over a field,
together with its two basic affine opens and the canonical affine chart maps.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry
open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HomogeneousLocalization

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (x : Submonoid A)

lemma val_fromZeroRingHom (c : 𝒜 0) :
    (fromZeroRingHom 𝒜 x c).val = algebraMap A (Localization x) (c : A) := by
  have h : fromZeroRingHom 𝒜 x c = HomogeneousLocalization.mk ⟨0, c, 1, one_mem x⟩ := rfl
  rw [h, val_mk, ← Localization.mk_one_eq_algebraMap]
  congr 1

noncomputable instance : Algebra R (HomogeneousLocalization 𝒜 x) where
  toSMul := inferInstanceAs (SMul R (HomogeneousLocalization 𝒜 x))
  algebraMap := (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0))
  commutes' _ _ := mul_comm _ _
  smul_def' r z := by
    apply val_injective
    change (r • z).val = ((fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0)) r * z).val
    rw [val_mul, val_smul x r z, RingHom.comp_apply, val_fromZeroRingHom,
      SetLike.GradeZero.coe_algebraMap]
    induction z.val using Localization.induction_on with
    | H w =>
      rw [Localization.smul_mk, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
        Algebra.smul_def]
      exact congrArg (Localization.mk _) (Subtype.ext (one_mul _).symm)

lemma algebraMap_eq' :
    algebraMap R (HomogeneousLocalization 𝒜 x) =
      (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0)) := rfl

instance : IsScalarTower R (𝒜 0) (HomogeneousLocalization 𝒜 x) :=
  .of_algebraMap_eq' rfl

@[simp] lemma algebraMap_val (r : R) :
    (algebraMap R (HomogeneousLocalization 𝒜 x) r).val =
      algebraMap A (Localization x) (algebraMap R A r) := by
  rw [algebraMap_eq', RingHom.comp_apply, val_fromZeroRingHom,
    SetLike.GradeZero.coe_algebraMap]

end HomogeneousLocalization

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) k

/-- The projective line over `k`, as `Proj` of the standard graded polynomial ring. -/
noncomputable def P1 : Scheme.{u} :=
  Proj 𝒜

namespace P1

theorem fin_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

theorem fin_one_ne_zero : (1 : Fin 2) ≠ 0 := by decide

/-- The variables are homogeneous of degree one. -/
theorem X_mem (i : Fin 2) : MvPolynomial.X i ∈ 𝒜 1 := by
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_X k i)

theorem X_mul_X_mem :
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1 ∈ 𝒜 2 := by
  exact SetLike.mul_mem_graded (X_mem k 0) (X_mem k 1)

/-- The standard chart `D₊(Xᵢ)` of the projective line. -/
noncomputable def chartOpen (i : Fin 2) : (P1 k).Opens :=
  Proj.basicOpen 𝒜 (MvPolynomial.X i)

theorem isAffineOpen_chartOpen (i : Fin 2) : IsAffineOpen (chartOpen k i) := by
  exact Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X i) (X_mem k i) one_pos

theorem adjoin_gradeZero_range_X :
    Algebra.adjoin (𝒜 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  have hp : p ∈ Algebra.adjoin k
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)) := by
    rw [MvPolynomial.adjoin_range_X]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem q hq => exact Algebra.subset_adjoin hq
  | algebraMap r =>
      exact Subalgebra.algebraMap_mem _
        (⟨algebraMap k (MvPolynomial (Fin 2) k) r, by
          rw [MvPolynomial.algebraMap_eq]
          exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
            (MvPolynomial.isHomogeneous_C _ r)⟩ : 𝒜 0)
  | add q₁ q₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
  | mul q₁ q₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂

/-- The two standard charts cover the projective line. -/
theorem chartOpen_sup : chartOpen k 0 ⊔ chartOpen k 1 = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top' 𝒜
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)
      (fun i => ⟨1, X_mem k i⟩) (adjoin_gradeZero_range_X k)
  refine le_antisymm le_top (h.ge.trans (iSup_le fun i => ?_))
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- The overlap is the basic open of `X₀ X₁`. -/
theorem chartOpen_inf : chartOpen k 0 ⊓ chartOpen k 1 =
    Proj.basicOpen 𝒜 (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  exact (Proj.basicOpen_mul 𝒜 (MvPolynomial.X 0) (MvPolynomial.X 1)).symm

/-- The canonical open immersion from the affine model of a chart. -/
noncomputable def chartι (i : Fin 2) :
    Spec (.of (Away 𝒜 (MvPolynomial.X i))) ⟶ P1 k :=
  Proj.awayι 𝒜 (MvPolynomial.X i) (X_mem k i) one_pos

instance (i : Fin 2) : IsOpenImmersion (chartι k i) := by
  exact inferInstanceAs (IsOpenImmersion (Proj.awayι _ _ _ _))

theorem opensRange_chartι (i : Fin 2) :
    (chartι k i).opensRange = chartOpen k i := by
  exact Proj.opensRange_awayι 𝒜 (MvPolynomial.X i) (X_mem k i) one_pos

/-- The affine coordinate `Xⱼ/Xᵢ` on the chart `D₊(Xᵢ)`. -/
noncomputable def chartCoord (i j : Fin 2) : Away 𝒜 (MvPolynomial.X i) :=
  Away.mk 𝒜 (X_mem k i) 1 (MvPolynomial.X j) (by simpa using X_mem k j)

theorem val_chartCoord (i j : Fin 2) :
    (chartCoord k i j).val = Localization.mk (MvPolynomial.X j)
      (⟨MvPolynomial.X i ^ 1, 1, rfl⟩ :
        Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k)) := rfl

@[simp] theorem chartCoord_eq (i j : Fin 2) :
    chartCoord k i j =
      Away.mk 𝒜 (X_mem k i) 1 (MvPolynomial.X j) (by simpa using X_mem k j) := rfl

/-- Dehomogenization at `Xᵢ`, sending `Xᵢ` to `1`. -/
noncomputable def dehomogenize (i : Fin 2) :
    MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval (Function.update (fun _ => Polynomial.X) i 1)

@[simp] theorem dehomogenize_X_self (i : Fin 2) :
    dehomogenize k i (MvPolynomial.X i) = 1 := by
  rw [dehomogenize, MvPolynomial.aeval_X, Function.update_self]

theorem dehomogenize_X_of_ne {i j : Fin 2} (hij : i ≠ j) :
    dehomogenize k i (MvPolynomial.X j) = Polynomial.X := by
  rw [dehomogenize, MvPolynomial.aeval_X, Function.update_of_ne hij.symm]

noncomputable def polyToAway (i j : Fin 2) : Polynomial k →ₐ[k] Away 𝒜 (MvPolynomial.X i) :=
  Polynomial.aeval (chartCoord k i j)

@[simp] theorem polyToAway_X (i j : Fin 2) :
    polyToAway k i j Polynomial.X = chartCoord k i j := Polynomial.aeval_X _

theorem isUnit_dehomogenize_X_self (i : Fin 2) :
    IsUnit ((dehomogenize k i).toRingHom (MvPolynomial.X i)) := by
  change IsUnit (dehomogenize k i (MvPolynomial.X i))
  rw [dehomogenize_X_self k i]
  exact isUnit_one

noncomputable def awayToPoly (i : Fin 2) : Away 𝒜 (MvPolynomial.X i) →ₐ[k] Polynomial k where
  toRingHom :=
    (Localization.awayLift (dehomogenize k i).toRingHom (MvPolynomial.X i)
      (isUnit_dehomogenize_X_self k i)).comp
      (algebraMap (Away 𝒜 (MvPolynomial.X i))
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin 2) k)))
  commutes' r := by
    change (Localization.awayLift (dehomogenize k i).toRingHom (MvPolynomial.X i)
        (isUnit_dehomogenize_X_self k i))
        ((algebraMap k (Away 𝒜 (MvPolynomial.X i)) r).val) = algebraMap k (Polynomial k) r
    rw [HomogeneousLocalization.algebraMap_val, IsLocalization.Away.lift_eq]
    exact (dehomogenize k i).commutes r

theorem awayToPoly_mk (i : Fin 2) (n : ℕ) (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ 𝒜 (n • 1)) :
    awayToPoly k i (Away.mk 𝒜 (X_mem k i) n a ha) = dehomogenize k i a := by
  have h1 : (dehomogenize k i).toRingHom (MvPolynomial.X i) * 1 = 1 := by
    rw [mul_one]
    exact dehomogenize_X_self k i
  have h := Localization.awayLift_mk (A := Polynomial k)
    ((dehomogenize k i).toRingHom) (MvPolynomial.X i) a 1 h1 n
  exact h.trans (by rw [one_pow, mul_one]; rfl)

theorem awayToPoly_chartCoord {i j : Fin 2} (hij : i ≠ j) :
    awayToPoly k i (chartCoord k i j) = Polynomial.X := by
  exact (awayToPoly_mk k i 1 (MvPolynomial.X j)
    (by simpa using X_mem k j)).trans (dehomogenize_X_of_ne k hij)

theorem awayToPoly_comp_polyToAway {i j : Fin 2} (hij : i ≠ j) :
    (awayToPoly k i).comp (polyToAway k i j) = AlgHom.id k (Polynomial k) := by
  apply Polynomial.algHom_ext
  rw [AlgHom.comp_apply, polyToAway_X, awayToPoly_chartCoord k hij, AlgHom.id_apply]

noncomputable def gradeZeroAlgEquiv : k ≃ₐ[k] (𝒜 0) := by
  refine AlgEquiv.ofBijective (Algebra.ofId k (𝒜 0)) ⟨?_, ?_⟩
  · intro a b hab
    have h : (MvPolynomial.C a : MvPolynomial (Fin 2) k) = MvPolynomial.C b := by
      have h' := congrArg Subtype.val hab
      simpa [Algebra.ofId_apply, MvPolynomial.algebraMap_eq] using h'
    exact MvPolynomial.C_injective _ _ h
  · intro c
    have hc : (c : MvPolynomial (Fin 2) k) ∈ (1 : Submodule k (MvPolynomial (Fin 2) k)) := by
      rw [← homogeneousSubmodule_zero (σ := Fin 2) (R := k)]
      exact c.2
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
    exact ⟨r, Subtype.ext (by simpa [Algebra.ofId_apply] using hr)⟩

theorem prod_X_pow_eq {i j : Fin 2} (hij : i ≠ j) (e : Fin 2 → ℕ) :
    (∏ l, (MvPolynomial.X l : MvPolynomial (Fin 2) k) ^ e l) =
      MvPolynomial.X i ^ e i * MvPolynomial.X j ^ e j := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.prod_univ_two, mul_comm]

theorem sum_fin_two_eq {i j : Fin 2} (hij : i ≠ j) (e : Fin 2 → ℕ) :
    e i + e j = e 0 + e 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [add_comm]

theorem chartCoord_pow (i j : Fin 2) (m : ℕ) :
    chartCoord k i j ^ m =
      Away.mk 𝒜 (X_mem k i) m (MvPolynomial.X j ^ m)
        (by simpa using SetLike.pow_mem_graded m (X_mem k j)) := by
  rw [ext_iff_val, val_pow, val_chartCoord, Away.val_mk, Localization.mk_pow,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

theorem away_mk_prod_eq {i j : Fin 2} (hij : i ≠ j) (a : ℕ) (e : Fin 2 → ℕ)
    (hae : e 0 + e 1 = a)
    (H : (∏ l, MvPolynomial.X l ^ e l) ∈ 𝒜 (a • 1)) :
    Away.mk 𝒜 (X_mem k i) a (∏ l, MvPolynomial.X l ^ e l) H =
      chartCoord k i j ^ e j := by
  have hij' : e i + e j = a := (sum_fin_two_eq hij e).trans hae
  rw [chartCoord_pow, ext_iff_val, Away.val_mk, Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  push_cast
  rw [prod_X_pow_eq k hij e, ← hij']
  ring

theorem polyToAway_surjective {i j : Fin 2} (hij : i ≠ j) :
    Function.Surjective (polyToAway k i j) := by
  intro z
  have hz : z ∈ (⊤ : Submodule (𝒜 0) (Away 𝒜 (MvPolynomial.X i))) := trivial
  rw [← Away.span_mk_prod_pow_eq_top (X_mem k i)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)
    (adjoin_gradeZero_range_X k) (fun _ => 1) (fun l => X_mem k l)] at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, e, hae, rfl⟩ := hw
    refine ⟨Polynomial.X ^ e j, ?_⟩
    rw [map_pow, polyToAway_X]
    exact (away_mk_prod_eq k hij a e (by simpa using hae) _).symm
  | zero => exact ⟨0, map_zero _⟩
  | add u v _ _ hu hv =>
    obtain ⟨p, rfl⟩ := hu
    obtain ⟨q, rfl⟩ := hv
    exact ⟨p + q, map_add _ _ _⟩
  | smul c w _ hw =>
    obtain ⟨p, rfl⟩ := hw
    obtain ⟨r, rfl⟩ := (gradeZeroAlgEquiv k).surjective c
    refine ⟨r • p, ?_⟩
    rw [map_smul]
    change r • polyToAway k i j p = (algebraMap k (𝒜 0) r) • polyToAway k i j p
    exact (IsScalarTower.algebraMap_smul (𝒜 0) r
      (polyToAway k i j p)).symm

theorem polyToAway_comp_awayToPoly {i j : Fin 2} (hij : i ≠ j) :
    (polyToAway k i j).comp (awayToPoly k i) = AlgHom.id k (Away 𝒜 (MvPolynomial.X i)) := by
  refine AlgHom.ext fun z => ?_
  obtain ⟨p, rfl⟩ := polyToAway_surjective k hij z
  have h := AlgHom.congr_fun (awayToPoly_comp_polyToAway k hij) p
  exact congrArg (polyToAway k i j) h

noncomputable def awayAlgEquiv {i j : Fin 2} (hij : i ≠ j) :
    Away 𝒜 (MvPolynomial.X i) ≃ₐ[k] Polynomial k :=
  AlgEquiv.ofAlgHom (awayToPoly k i) (polyToAway k i j)
    (awayToPoly_comp_polyToAway k hij) (polyToAway_comp_awayToPoly k hij)

@[simp] theorem awayAlgEquiv_chartCoord {i j : Fin 2} (hij : i ≠ j) :
    awayAlgEquiv k hij (chartCoord k i j) = Polynomial.X :=
  awayToPoly_chartCoord k hij

end P1
end AlgebraicGeometry
