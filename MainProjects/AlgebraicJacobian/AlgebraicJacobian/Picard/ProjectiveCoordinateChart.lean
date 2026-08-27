/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ProjectiveSpace
import Mathlib.Data.Fintype.BigOperators

/-!
# Projective coordinate charts

This file gives the coordinate-level API for constructing morphisms from an
affine scheme to the integral model of projective space. A coordinate family
with one coordinate equal to `1` defines a morphism through the corresponding
standard chart. Two such morphisms agree when their coordinate families differ
by multiplication by a unit.

The construction is deliberately independent of curves. It is the reusable
gluing substrate for globalizing affine embeddings over the two standard
charts of the projective line.
-/

open CategoryTheory MvPolynomial HomogeneousLocalization

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Coordinates

variable {J : Type u}
variable {B B' : Type u} [CommRing B] [CommRing B']

/-- Evaluation of the integral homogeneous coordinate ring at a family of
elements of a ring. -/
def eval (c : J → B) : MvPolynomial J (ULift.{u} ℤ) →+* B :=
  eval₂Hom ((Int.castRingHom B).comp
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom) c

@[simp]
theorem eval_X (c : J → B) (i : J) : eval c (X i) = c i := by
  simp [eval]

@[simp]
theorem eval_monomial (c : J → B) (d : J →₀ ℕ) (a : ULift.{u} ℤ) :
    eval c (monomial d a) = (a.down : B) * d.prod (fun i e ↦ c i ^ e) := by
  simp [eval, ULift.ringEquiv]

/-- A homogeneous polynomial of degree `m` scales by `lambda ^ m` when all
projective coordinates are scaled by `lambda`. -/
theorem eval_smul_of_isHomogeneous [Finite J] (lambda : B) (c : J → B)
    {p : MvPolynomial J (ULift.{u} ℤ)} {m : ℕ} (hp : p.IsHomogeneous m) :
    eval (fun i ↦ lambda * c i) p = lambda ^ m * eval c p := by
  classical
  letI := Fintype.ofFinite J
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdeg : Finsupp.degree d = m := by
    by_contra hne
    exact (mem_support_iff.mp hd) (hp.coeff_eq_zero hne)
  rw [eval_monomial, eval_monomial]
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul]
  have hpow : d.prod (fun _ e ↦ lambda ^ e) = lambda ^ m := by
    rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum, hdeg]
  rw [hpow]
  ring

/-- The lift of a homogeneous-coordinate evaluation to the degree-zero
localization at a homogeneous element whose image is a unit. -/
def awayLift (f : MvPolynomial J (ULift.{u} ℤ))
    (psi : MvPolynomial J (ULift.{u} ℤ) →+* B) (hu : IsUnit (psi f)) :
    Away (homogeneousSubmodule J (ULift.{u} ℤ)) f →+* B :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hu).comp
    (algebraMap (Away (homogeneousSubmodule J (ULift.{u} ℤ)) f)
      (Localization.Away f))

/-- Normal form for `awayLift`: the value of `a / f ^ n`, multiplied by
the evaluated denominator, is the value of `a`. -/
theorem awayLift_mul_eq {f : MvPolynomial J (ULift.{u} ℤ)} {e : ℕ}
    (hf : f ∈ homogeneousSubmodule J (ULift.{u} ℤ) e)
    (psi : MvPolynomial J (ULift.{u} ℤ) →+* B)
    (hu : IsUnit (psi f)) (n : ℕ) (a : MvPolynomial J (ULift.{u} ℤ))
    (ha : a ∈ homogeneousSubmodule J (ULift.{u} ℤ) (n • e)) :
    awayLift f psi hu
        (Away.mk (homogeneousSubmodule J (ULift.{u} ℤ)) hf n a ha) *
      psi f ^ n = psi a := by
  have hspec :
      Localization.mk a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) *
          algebraMap _ (Localization.Away f) (f ^ n) =
        algebraMap _ (Localization.Away f) a := by
    rw [Localization.mk_eq_mk'_apply]
    exact IsLocalization.mk'_spec _ _ _
  have hlift := congrArg (IsLocalization.Away.lift
    (S := Localization.Away f) f hu) hspec
  rw [map_mul, IsLocalization.Away.lift_eq,
    IsLocalization.Away.lift_eq] at hlift
  calc
    awayLift f psi hu
        (Away.mk (homogeneousSubmodule J (ULift.{u} ℤ)) hf n a ha) *
      psi f ^ n =
        IsLocalization.Away.lift (S := Localization.Away f) f hu
            (Localization.mk a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) *
          psi (f ^ n) := by
      rw [awayLift, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
        HomogeneousLocalization.Away.val_mk, map_pow]
    _ = psi a := hlift

/-- `awayLift` only depends on the underlying evaluation map. -/
theorem awayLift_congr {f : MvPolynomial J (ULift.{u} ℤ)}
    {psi₁ psi₂ : MvPolynomial J (ULift.{u} ℤ) →+* B} (h : psi₁ = psi₂)
    (hu : IsUnit (psi₁ f)) :
    awayLift f psi₁ hu = awayLift f psi₂ (h ▸ hu) := by
  subst h
  rfl

/-- Post-composition commutes with evaluation. -/
theorem comp_eval (r : B →+* B') (c : J → B) :
    r.comp (eval c) = eval (fun i ↦ r (c i)) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [eval]
  · intro i
    simp

/-- Post-composition commutes with `awayLift`. -/
theorem comp_awayLift {f : MvPolynomial J (ULift.{u} ℤ)} {e : ℕ}
    (hf : f ∈ homogeneousSubmodule J (ULift.{u} ℤ) e) (r : B →+* B')
    (psi : MvPolynomial J (ULift.{u} ℤ) →+* B) (hu : IsUnit (psi f)) :
    r.comp (awayLift f psi hu) =
      awayLift f (r.comp psi) (by simpa using hu.map r) := by
  apply RingHom.ext
  intro w
  obtain ⟨n, a, ha, rfl⟩ :=
    Away.mk_surjective (homogeneousSubmodule J (ULift.{u} ℤ)) hf w
  have h₁ := congrArg r (awayLift_mul_eq hf psi hu n a ha)
  rw [map_mul, map_pow] at h₁
  have h₂ := awayLift_mul_eq hf (r.comp psi)
    (by simpa using hu.map r) n a ha
  simp only [RingHom.comp_apply] at h₂ ⊢
  exact ((hu.map r).pow n).mul_right_cancel (h₁.trans h₂.symm)

/-- Every homogeneous coordinate has degree one. -/
theorem X_mem_deg_one (i : J) :
    (X i : MvPolynomial J (ULift.{u} ℤ)) ∈
      homogeneousSubmodule J (ULift.{u} ℤ) 1 :=
  isHomogeneous_X _ _

/-- A coordinate family with its `i`-th coordinate equal to one defines a
ring map from the `i`-th standard projective chart. -/
def chartHom (i : J) (c : J → B) (hi : c i = 1) :
    Away (homogeneousSubmodule J (ULift.{u} ℤ)) (X i) →+* B :=
  awayLift (X i) (eval c) (by rw [eval_X, hi]; exact isUnit_one)

/-- The normalized coordinate `X_j / X_i` on the `i`-th projective chart. -/
def chartCoord (i j : J) :
    Away (homogeneousSubmodule J (ULift.{u} ℤ)) (X i) :=
  Away.mk (homogeneousSubmodule J (ULift.{u} ℤ)) (X_mem_deg_one i) 1 (X j)
    (by simpa using X_mem_deg_one j)

/-- The localization element attached to `X_j` is the normalized coordinate
`X_j / X_i`. -/
theorem isLocalizationElem_eq_chartCoord (i j : J) :
    Away.isLocalizationElem (X_mem_deg_one i) (X_mem_deg_one j) =
      chartCoord i j := by
  apply HomogeneousLocalization.val_injective
  simp [chartCoord]

/-- Post-composition commutes with a standard-chart classifying map. -/
theorem comp_chartHom (r : B →+* B') (i : J) (c : J → B) (hi : c i = 1) :
    r.comp (chartHom i c hi) =
      chartHom i (fun j ↦ r (c j)) (by rw [hi, map_one]) := by
  rw [chartHom, chartHom]
  exact (comp_awayLift (X_mem_deg_one i) r (eval c)
    (by rw [eval_X, hi]; exact isUnit_one)).trans
      (awayLift_congr (comp_eval r c) _)

theorem chartHom_mk (i : J) (c : J → B) (hi : c i = 1)
    {e : ℕ} (hf : (X i : MvPolynomial J (ULift.{u} ℤ)) ∈
      homogeneousSubmodule J (ULift.{u} ℤ) e)
    (n : ℕ) (a : MvPolynomial J (ULift.{u} ℤ))
    (ha : a ∈ homogeneousSubmodule J (ULift.{u} ℤ) (n • e)) :
    chartHom i c hi
      (Away.mk (homogeneousSubmodule J (ULift.{u} ℤ)) hf n a ha) = eval c a := by
  have h := awayLift_mul_eq hf (eval c)
    (by rw [eval_X, hi]; exact isUnit_one) n a ha
  simpa [chartHom, hi] using h

@[simp]
theorem chartHom_chartCoord (i j : J) (c : J → B) (hi : c i = 1) :
    chartHom i c hi (chartCoord i j) = c j := by
  rw [chartCoord, chartHom_mk]
  exact eval_X c j

/-- The affine morphism into the `i`-th standard chart classified by a
coordinate family whose `i`-th coordinate is one. -/
def fromSpec (i : J) (c : J → B) (hi : c i = 1) :
    Spec (.of B) ⟶ Proj (homogeneousSubmodule J (ULift.{u} ℤ)) :=
  Spec.map (CommRingCat.ofHom (chartHom i c hi)) ≫
    Proj.awayι (homogeneousSubmodule J (ULift.{u} ℤ))
      (X i) (X_mem_deg_one i) Nat.zero_lt_one

/-- The inverse image of `D_+(X_j)` under a normalized coordinate map is the
ordinary principal open where the coordinate `c_j` is nonzero. -/
theorem fromSpec_preimage_basicOpen (i j : J) (c : J → B) (hi : c i = 1) :
    fromSpec i c hi ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule J (ULift.{u} ℤ)) (X j) =
      PrimeSpectrum.basicOpen (c j) := by
  rw [fromSpec, Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen (homogeneousSubmodule J (ULift.{u} ℤ))
    (X_mem_deg_one i) Nat.one_pos (X_mem_deg_one j) Nat.one_pos]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  change chartHom i c hi
      (Away.isLocalizationElem (X_mem_deg_one i) (X_mem_deg_one j)) = c j
  rw [isLocalizationElem_eq_chartCoord, chartHom_chartCoord]

/-- A normalized coordinate family on an open subscheme defines a morphism
from that open to the integral model of projective space. -/
def fromOpen {Z : Scheme.{u}} (U : Z.Opens) (i : J)
    (c : J → Γ(Z, U)) (hi : c i = 1) :
    U.toScheme ⟶ Proj (homogeneousSubmodule J (ULift.{u} ℤ)) :=
  U.toSpecΓ ≫ fromSpec i c hi

/-- On an open source, the inverse image of `D_+(X_j)` is the restriction of
the principal open where the section `c_j` is nonzero. -/
theorem fromOpen_preimage_basicOpen {Z : Scheme.{u}} (U : Z.Opens)
    (i j : J) (c : J → Γ(Z, U)) (hi : c i = 1) :
    fromOpen U i c hi ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule J (ULift.{u} ℤ)) (X j) =
      U.ι ⁻¹ᵁ Z.basicOpen (c j) := by
  rw [fromOpen, Scheme.Hom.comp_preimage, fromSpec_preimage_basicOpen,
    Scheme.Opens.toSpecΓ_preimage_basicOpen]

/-- `fromSpec` is natural in the affine coordinate ring. -/
theorem SpecMap_fromSpec (r : B →+* B') (i : J) (c : J → B)
    (hi : c i = 1) :
    Spec.map (CommRingCat.ofHom r) ≫ fromSpec i c hi =
      fromSpec i (fun j ↦ r (c j)) (by rw [hi, map_one]) := by
  rw [fromSpec, fromSpec, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext w
  exact DFunLike.congr_fun (comp_chartHom r i c hi) w

/-- Coordinate morphisms from open subschemes commute with restriction. -/
theorem homOfLE_fromOpen {Z : Scheme.{u}} {U V : Z.Opens} (h : V ≤ U)
    (i : J) (c : J → Γ(Z, U)) (hi : c i = 1) :
    Z.homOfLE h ≫ fromOpen U i c hi =
      fromOpen V i
        (fun j ↦ (Z.presheaf.map (homOfLE h).op).hom (c j))
        (by rw [hi, map_one]) := by
  rw [fromOpen, fromOpen,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc V U h]
  congr 1
  exact SpecMap_fromSpec (Z.presheaf.map (homOfLE h).op).hom i c hi

/-- The product of two degree-one coordinates has degree two. -/
theorem X_mul_X_mem_deg_two (i j : J) :
    (X i * X j : MvPolynomial J (ULift.{u} ℤ)) ∈
      homogeneousSubmodule J (ULift.{u} ℤ) 2 := by
  simpa using SetLike.mul_mem_graded (X_mem_deg_one i) (X_mem_deg_one j)

/-- Coordinate maps through two standard charts agree when their coordinate
families differ by multiplication by a unit. -/
theorem fromSpec_eq_of_unit_smul [Finite J] (i₀ i₁ : J) (c₀ c₁ : J → B)
    (hi₀ : c₀ i₀ = 1) (hi₁ : c₁ i₁ = 1) (lambda : B)
    (hlambda : IsUnit lambda) (hc : ∀ j, c₀ j = lambda * c₁ j) :
    fromSpec i₀ c₀ hi₀ = fromSpec i₁ c₁ hi₁ := by
  classical
  letI := Fintype.ofFinite J
  have hc₀i₁ : c₀ i₁ = lambda := by rw [hc i₁, hi₁, mul_one]
  have hunit₀ : IsUnit (c₀ i₁) := by simpa [hc₀i₁] using hlambda
  have hlambda_mul : lambda * c₁ i₀ = 1 := by rw [← hc i₀, hi₀]
  have hunit₁ : IsUnit (c₁ i₀) :=
    IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at hlambda_mul)
  have hu₀ : IsUnit (eval c₀ (X i₀ * X i₁)) := by
    rw [map_mul, eval_X, eval_X, hi₀, one_mul]
    exact hunit₀
  have hu₁ : IsUnit (eval c₁ (X i₀ * X i₁)) := by
    rw [map_mul, eval_X, eval_X, hi₁, mul_one]
    exact hunit₁
  let overlap₀ :
      Away (homogeneousSubmodule J (ULift.{u} ℤ)) (X i₀ * X i₁) →+* B :=
    awayLift (X i₀ * X i₁) (eval c₀) hu₀
  let overlap₁ :
      Away (homogeneousSubmodule J (ULift.{u} ℤ)) (X i₀ * X i₁) →+* B :=
    awayLift (X i₀ * X i₁) (eval c₁) hu₁
  have hoverlap : overlap₀ = overlap₁ := by
    apply RingHom.ext
    intro w
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective
      (homogeneousSubmodule J (ULift.{u} ℤ))
      (X_mul_X_mem_deg_two i₀ i₁) w
    have h₀ := awayLift_mul_eq (X_mul_X_mem_deg_two i₀ i₁)
      (eval c₀) hu₀ n a ha
    have h₁ := awayLift_mul_eq (X_mul_X_mem_deg_two i₀ i₁)
      (eval c₁) hu₁ n a ha
    have hscale := eval_smul_of_isHomogeneous lambda c₁
      ((mem_homogeneousSubmodule _ _).mp ha)
    have hcoords : c₀ = fun j ↦ lambda * c₁ j := funext hc
    rw [← hcoords] at hscale
    have hexp : n • (2 : ℕ) = 2 * n := by
      rw [Nat.nsmul_eq_mul, Nat.mul_comm]
    rw [hexp] at hscale
    have hden : eval c₀ (X i₀ * X i₁) =
        lambda ^ 2 * eval c₁ (X i₀ * X i₁) := by
      rw [map_mul, map_mul, eval_X, eval_X, eval_X, eval_X, hc i₀, hc i₁]
      ring
    have hcommon : IsUnit
        (lambda ^ (2 * n) * eval c₁ (X i₀ * X i₁) ^ n) :=
      (hlambda.pow (2 * n)).mul (hu₁.pow n)
    apply hcommon.mul_right_cancel
    calc
      overlap₀
            (Away.mk (homogeneousSubmodule J (ULift.{u} ℤ))
              (X_mul_X_mem_deg_two i₀ i₁) n a ha) *
          (lambda ^ (2 * n) * eval c₁ (X i₀ * X i₁) ^ n) =
          overlap₀
              (Away.mk (homogeneousSubmodule J (ULift.{u} ℤ))
                (X_mul_X_mem_deg_two i₀ i₁) n a ha) *
            eval c₀ (X i₀ * X i₁) ^ n := by
              rw [hden, mul_pow, pow_mul]
      _ = eval c₀ a := h₀
      _ = lambda ^ (2 * n) * eval c₁ a := hscale
      _ = lambda ^ (2 * n) *
          (overlap₁
              (Away.mk (homogeneousSubmodule J (ULift.{u} ℤ))
                (X_mul_X_mem_deg_two i₀ i₁) n a ha) *
            eval c₁ (X i₀ * X i₁) ^ n) := by rw [h₁]
      _ = overlap₁
            (Away.mk (homogeneousSubmodule J (ULift.{u} ℤ))
              (X_mul_X_mem_deg_two i₀ i₁) n a ha) *
          (lambda ^ (2 * n) * eval c₁ (X i₀ * X i₁) ^ n) := by ring
  have hfac₀ : overlap₀.comp
        (awayMap (homogeneousSubmodule J (ULift.{u} ℤ))
          (X_mem_deg_one i₁) rfl) = chartHom i₀ c₀ hi₀ := by
    apply RingHom.ext
    intro w
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective
      (homogeneousSubmodule J (ULift.{u} ℤ)) (X_mem_deg_one i₀) w
    rw [RingHom.comp_apply, awayMap_mk, chartHom_mk]
    have hmem : a * X i₁ ^ n ∈
        homogeneousSubmodule J (ULift.{u} ℤ) (n • (1 + 1)) := by
      have h := SetLike.mul_mem_graded ha
        (SetLike.pow_mem_graded n (X_mem_deg_one i₁))
      rwa [← smul_add] at h
    have h := awayLift_mul_eq (X_mul_X_mem_deg_two i₀ i₁)
      (eval c₀) hu₀ n (a * X i₁ ^ n) (by simpa using hmem)
    simp only [map_mul, map_pow, eval_X, hi₀, one_mul] at h
    exact (hunit₀.pow n).mul_right_cancel h
  have hfac₁ : overlap₁.comp
        (awayMap (homogeneousSubmodule J (ULift.{u} ℤ))
          (X_mem_deg_one i₀) (mul_comm (X i₀) (X i₁))) =
      chartHom i₁ c₁ hi₁ := by
    apply RingHom.ext
    intro w
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective
      (homogeneousSubmodule J (ULift.{u} ℤ)) (X_mem_deg_one i₁) w
    rw [RingHom.comp_apply, awayMap_mk, chartHom_mk]
    have hmem : a * X i₀ ^ n ∈
        homogeneousSubmodule J (ULift.{u} ℤ) (n • (1 + 1)) := by
      have h := SetLike.mul_mem_graded ha
        (SetLike.pow_mem_graded n (X_mem_deg_one i₀))
      rwa [← smul_add] at h
    have h := awayLift_mul_eq (X_mul_X_mem_deg_two i₀ i₁)
      (eval c₁) hu₁ n (a * X i₀ ^ n) (by simpa using hmem)
    simp only [map_mul, map_pow, eval_X, hi₁, mul_one] at h
    exact (hunit₁.pow n).mul_right_cancel h
  rw [fromSpec, fromSpec, ← hfac₀, ← hfac₁,
    CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι, hoverlap]

end AlgebraicGeometry.ProjectiveSpace.Coordinates
