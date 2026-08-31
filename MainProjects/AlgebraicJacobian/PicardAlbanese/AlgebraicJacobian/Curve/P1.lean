/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# The projective line over a field, with usable charts

We define `AlgebraicGeometry.P1 k` as `Proj` of the standard graded polynomial ring
`k[X₀, X₁]` (`MvPolynomial (Fin 2) k` with the degree grading), together with:

* `P1.structureMap : P1 k ⟶ Spec (.of k)`, and the instance `IsProper (P1.structureMap k)`
  (inherited from mathlib's properness of `Proj`);
* the two standard affine charts `D₊(X₀)`, `D₊(X₁)` (`P1.chartOpen`), which cover `P1 k`
  (`P1.chartOpen_sup`), together with the open immersions `P1.chartι i` from the affine
  models `Spec (k[X₀,X₁]_(Xᵢ))₀`;
* identifications of the chart section rings with polynomial rings:
  `P1.awayAlgEquiv : (k[X₀,X₁]_(Xᵢ))₀ ≃ₐ[k] k[t]` (the coordinate is `t = Xⱼ/Xᵢ`).

The identification of the chart *overlap* with Laurent polynomials, the section-level
versions, and the bundled chart package `AlgebraicGeometry.LaurentChartPair` are in the
continuation file `AlgebraicJacobian.Curve.P1Charts`.

The generic instance `Algebra R (HomogeneousLocalization 𝒜 x)` (for a graded `R`-algebra) and
the lemma `LaurentPolynomial.exists_toLaurent_add_aeval` (*Laurent span*: every Laurent
polynomial is the sum of a polynomial in `T` and a polynomial in `T⁻¹`) are general-purpose
and live in their natural namespaces.

## Implementation notes

We install `MvPolynomial.gradedAlgebra` as a (project-global) instance: everywhere in this
project, `MvPolynomial` carries the standard degree grading. Mathlib leaves this to the user
because other gradings exist; this project only ever uses the standard one.
-/

set_option autoImplicit false

universe u

open CategoryTheory

attribute [instance] MvPolynomial.gradedAlgebra

section GenericLemmas

/-! ### Generic support lemmas -/

namespace MvPolynomial

theorem X_mem_homogeneousSubmodule_one {σ : Type*} (R : Type*) [CommSemiring R] (i : σ) :
    X i ∈ homogeneousSubmodule σ R 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)

end MvPolynomial

namespace LaurentPolynomial

/-- **Laurent span**: every Laurent polynomial is the sum of a polynomial in `T` and a
polynomial in `T⁻¹`. -/
theorem exists_toLaurent_add_aeval {R : Type*} [CommSemiring R] (f : R[T;T⁻¹]) :
    ∃ p q : Polynomial R, f = p.toLaurent + Polynomial.aeval (T (-1) : R[T;T⁻¹]) q := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p₁, q₁, rfl⟩ := hp
    obtain ⟨p₂, q₂, rfl⟩ := hq
    exact ⟨p₁ + p₂, q₁ + q₂, by simp only [map_add]; ring⟩
  | C_mul_T n a =>
    rcases le_or_gt 0 n with hn | hn
    · refine ⟨Polynomial.C a * Polynomial.X ^ n.toNat, 0, ?_⟩
      rw [map_zero, add_zero, Polynomial.toLaurent_C_mul_X_pow, Int.toNat_of_nonneg hn]
    · refine ⟨0, Polynomial.C a * Polynomial.X ^ (-n).toNat, ?_⟩
      rw [map_zero, zero_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        T_pow, ← C_eq_algebraMap]
      congr 2
      omega

end LaurentPolynomial

namespace HomogeneousLocalization

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (x : Submonoid A)

lemma val_fromZeroRingHom (c : 𝒜 0) :
    (fromZeroRingHom 𝒜 x c).val = algebraMap A (Localization x) (c : A) := by
  have h : fromZeroRingHom 𝒜 x c = HomogeneousLocalization.mk ⟨0, c, 1, one_mem x⟩ := rfl
  rw [h, val_mk, ← Localization.mk_one_eq_algebraMap]
  congr 1

/-- If `A` is a graded `R`-algebra, then any homogeneous localization of `A` is an
`R`-algebra, via `R → 𝒜 0 → HomogeneousLocalization 𝒜 x`. The scalar action is the
existing pointwise one. -/
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
      (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0)) :=
  rfl

instance : IsScalarTower R (𝒜 0) (HomogeneousLocalization 𝒜 x) :=
  .of_algebraMap_eq' rfl

@[simp]
lemma algebraMap_val (r : R) :
    (algebraMap R (HomogeneousLocalization 𝒜 x) r).val =
      algebraMap A (Localization x) (algebraMap R A r) := by
  rw [algebraMap_eq', RingHom.comp_apply, val_fromZeroRingHom,
    SetLike.GradeZero.coe_algebraMap]

end HomogeneousLocalization

end GenericLemmas

namespace AlgebraicGeometry

open MvPolynomial HomogeneousLocalization

/-- The projective line over `k`, as `Proj` of the standard graded ring `k[X₀, X₁]`. -/
noncomputable def P1 (k : Type u) [Field k] : Scheme.{u} :=
  Proj (homogeneousSubmodule (Fin 2) k)

namespace P1

variable (k : Type u) [Field k]

/-- The standard grading of `k[X₀, X₁]`, the graded ring underlying `P1 k`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) k

theorem fin_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

theorem fin_one_ne_zero : (1 : Fin 2) ≠ 0 := by decide

/-! ### The structure morphism and properness -/

/-- The degree-zero part of `k[X₀,X₁]` is a trivial field extension of `k`. -/
noncomputable def gradeZeroAlgEquiv : k ≃ₐ[k] (𝒜 0) := by
  refine AlgEquiv.ofBijective (Algebra.ofId k (𝒜 0)) ⟨fun a b hab => ?_, fun c => ?_⟩
  · have h : (MvPolynomial.C a : MvPolynomial (Fin 2) k) = MvPolynomial.C b := by
      have h' := congrArg Subtype.val hab
      simpa [Algebra.ofId_apply, MvPolynomial.algebraMap_eq] using h'
    exact MvPolynomial.C_injective _ _ h
  · have hc : (c : MvPolynomial (Fin 2) k) ∈ (1 : Submodule k (MvPolynomial (Fin 2) k)) := by
      rw [← homogeneousSubmodule_zero (σ := Fin 2) (R := k)]
      exact c.2
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
    exact ⟨r, Subtype.ext (by simpa [Algebra.ofId_apply] using hr)⟩

instance : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin 2) k) :=
  have : IsScalarTower k (𝒜 0) (MvPolynomial (Fin 2) k) :=
    IsScalarTower.of_algebraMap_eq fun r => (SetLike.GradeZero.coe_algebraMap 𝒜 r).symm
  Algebra.FiniteType.of_restrictScalars_finiteType k (𝒜 0) (MvPolynomial (Fin 2) k)

/-- The structure morphism of the projective line over `k`. -/
noncomputable def structureMap : P1 k ⟶ Spec (.of k) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))

instance : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))) := by
  have : IsIso (CommRingCat.ofHom (algebraMap k (𝒜 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (gradeZeroAlgEquiv k).bijective
  infer_instance

instance isProper_structureMap : IsProper (structureMap k) := by
  have h1 : IsProper (Proj.toSpecZero 𝒜) := inferInstance
  have h2 : IsProper (Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))) := inferInstance
  exact IsProper.comp_iff.mpr h1

/-- `P1 k` as an object over `Spec k`. -/
noncomputable def asOver : Over (Spec (.of k)) := Over.mk (structureMap k)

instance : IsProper (asOver k).hom :=
  inferInstanceAs (IsProper (structureMap k))

/-! ### The standard affine charts -/

/-- The variables of `k[X₀,X₁]` are homogeneous of degree one. -/
theorem X_mem (i : Fin 2) : X i ∈ 𝒜 1 :=
  X_mem_homogeneousSubmodule_one k i

/-- The product of the two variables is homogeneous of degree two. -/
theorem X_mul_X_mem : (X 0 : MvPolynomial (Fin 2) k) * X 1 ∈ 𝒜 2 :=
  SetLike.mul_mem_graded (X_mem k 0) (X_mem k 1)

/-- The chart `D₊(Xᵢ)` of the projective line. -/
noncomputable def chartOpen (i : Fin 2) : (P1 k).Opens :=
  Proj.basicOpen 𝒜 (X i)

theorem isAffineOpen_chartOpen (i : Fin 2) : IsAffineOpen (chartOpen k i) :=
  Proj.isAffineOpen_basicOpen 𝒜 (X i) (X_mem k i) one_pos

theorem adjoin_gradeZero_range_X :
    Algebra.adjoin (𝒜 0) (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  have hp : p ∈ Algebra.adjoin k (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) := by
    rw [MvPolynomial.adjoin_range_X]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem q hq => exact Algebra.subset_adjoin hq
  | algebraMap r =>
    exact Subalgebra.algebraMap_mem _
      (⟨algebraMap k (MvPolynomial (Fin 2) k) r, by
        rw [MvPolynomial.algebraMap_eq]
        exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ r)⟩ : 𝒜 0)
  | add q₁ q₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
  | mul q₁ q₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂

/-- The two standard charts cover the projective line. -/
theorem chartOpen_sup : chartOpen k 0 ⊔ chartOpen k 1 = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top' 𝒜 (X : Fin 2 → MvPolynomial (Fin 2) k)
    (fun i => ⟨1, X_mem k i⟩) (adjoin_gradeZero_range_X k)
  refine le_antisymm le_top (h.ge.trans (iSup_le fun i => ?_))
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- The overlap of the two standard charts is the basic open of `X₀X₁`. -/
theorem chartOpen_inf : chartOpen k 0 ⊓ chartOpen k 1 = Proj.basicOpen 𝒜 (X 0 * X 1) :=
  (Proj.basicOpen_mul 𝒜 (X 0) (X 1)).symm

/-- The open immersion from the affine model `Spec (k[X₀,X₁]_(Xᵢ))₀` onto the chart
`D₊(Xᵢ)` of the projective line. -/
noncomputable def chartι (i : Fin 2) :
    Spec (.of (Away 𝒜 (X i))) ⟶ P1 k :=
  Proj.awayι 𝒜 (X i) (X_mem k i) one_pos

instance (i : Fin 2) : IsOpenImmersion (chartι k i) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι _ _ _ _))

theorem opensRange_chartι (i : Fin 2) : (chartι k i).opensRange = chartOpen k i :=
  Proj.opensRange_awayι 𝒜 (X i) (X_mem k i) one_pos

/-- The chart inclusions are morphisms over `Spec k`. -/
theorem chartι_structureMap (i : Fin 2) :
    chartι k i ≫ structureMap k =
      Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 (X i)))) := by
  change Proj.awayι 𝒜 (X i) (X_mem k i) one_pos ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))) = _
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-! ### The chart coordinate and the identification with the polynomial ring

Throughout, `i j : Fin 2` are the two distinct indices; the chart coordinate on `D₊(Xᵢ)`
is `t = Xⱼ/Xᵢ`. -/

/-- The chart coordinate `t = Xⱼ/Xᵢ` in the section ring of the chart `D₊(Xᵢ)`. -/
noncomputable def chartCoord (i j : Fin 2) : Away 𝒜 (X i) :=
  Away.mk 𝒜 (X_mem k i) 1 (X j) (by simpa using X_mem k j)

theorem chartCoord_eq (i j : Fin 2) :
    chartCoord k i j = Away.mk 𝒜 (X_mem k i) 1 (X j) (by simpa using X_mem k j) :=
  rfl

theorem val_chartCoord (i j : Fin 2) :
    (chartCoord k i j).val = Localization.mk (X j)
      (⟨X i ^ 1, 1, rfl⟩ : Submonoid.powers (X i : MvPolynomial (Fin 2) k)) :=
  rfl

/-- Dehomogenization at `Xᵢ`: the `k`-algebra map `k[X₀,X₁] → k[t]` with `Xᵢ ↦ 1`,
`Xⱼ ↦ t`. -/
noncomputable def dehomogenize (i : Fin 2) :
    MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval (Function.update (fun _ => Polynomial.X) i 1)

@[simp]
theorem dehomogenize_X_self (i : Fin 2) : dehomogenize k i (X i) = 1 := by
  rw [dehomogenize, MvPolynomial.aeval_X, Function.update_self]

theorem dehomogenize_X_of_ne {i j : Fin 2} (hij : i ≠ j) :
    dehomogenize k i (X j) = Polynomial.X := by
  rw [dehomogenize, MvPolynomial.aeval_X, Function.update_of_ne hij.symm]

/-- `k[t] → (k[X₀,X₁]_(Xᵢ))₀`, `t ↦ Xⱼ/Xᵢ`. Bijective for `i ≠ j`; see `P1.awayAlgEquiv`. -/
noncomputable def polyToAway (i j : Fin 2) : Polynomial k →ₐ[k] Away 𝒜 (X i) :=
  Polynomial.aeval (chartCoord k i j)

@[simp]
theorem polyToAway_X (i j : Fin 2) :
    polyToAway k i j Polynomial.X = chartCoord k i j :=
  Polynomial.aeval_X _

theorem polyToAway_monomial (i j : Fin 2) (n : ℕ) (a : k) :
    polyToAway k i j (Polynomial.monomial n a) =
      algebraMap k (Away 𝒜 (X i)) a * chartCoord k i j ^ n := by
  change Polynomial.aeval (chartCoord k i j) (Polynomial.monomial n a) = _
  exact Polynomial.aeval_monomial _

theorem isUnit_dehomogenize_X_self (i : Fin 2) :
    IsUnit ((dehomogenize k i).toRingHom (X i)) := by
  have h : (dehomogenize k i).toRingHom (X i) = 1 := dehomogenize_X_self k i
  rw [h]
  exact isUnit_one

/-- `(k[X₀,X₁]_(Xᵢ))₀ → k[t]`, induced by dehomogenization at `Xᵢ`.
Inverse of `P1.polyToAway`; see `P1.awayAlgEquiv`. -/
noncomputable def awayToPoly (i : Fin 2) : Away 𝒜 (X i) →ₐ[k] Polynomial k where
  toRingHom :=
    (Localization.awayLift (dehomogenize k i).toRingHom (X i)
      (isUnit_dehomogenize_X_self k i)).comp
      (algebraMap (Away 𝒜 (X i)) (Localization.Away (X i : MvPolynomial (Fin 2) k)))
  commutes' r := by
    change (Localization.awayLift (dehomogenize k i).toRingHom (X i)
        (isUnit_dehomogenize_X_self k i))
        ((algebraMap k (Away 𝒜 (X i)) r).val) = algebraMap k (Polynomial k) r
    rw [HomogeneousLocalization.algebraMap_val, IsLocalization.Away.lift_eq]
    exact (dehomogenize k i).commutes r

/-- The workhorse: `awayToPoly` sends `a/Xᵢⁿ` to the dehomogenization of `a`. -/
theorem awayToPoly_mk (i : Fin 2) (n : ℕ) (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ 𝒜 (n • 1)) :
    awayToPoly k i (Away.mk 𝒜 (X_mem k i) n a ha) = dehomogenize k i a := by
  have h1 : (dehomogenize k i).toRingHom (X i) * 1 = 1 := by
    rw [mul_one]
    exact dehomogenize_X_self k i
  have h := Localization.awayLift_mk (A := Polynomial k)
    ((dehomogenize k i).toRingHom) (X i) a 1 h1 n
  exact h.trans (by rw [one_pow, mul_one]; rfl)

@[simp]
theorem awayToPoly_chartCoord {i j : Fin 2} (hij : i ≠ j) :
    awayToPoly k i (chartCoord k i j) = Polynomial.X :=
  (awayToPoly_mk k i 1 (X j) (by simpa using X_mem k j)).trans (dehomogenize_X_of_ne k hij)

theorem awayToPoly_comp_polyToAway {i j : Fin 2} (hij : i ≠ j) :
    (awayToPoly k i).comp (polyToAway k i j) = AlgHom.id k (Polynomial k) := by
  apply Polynomial.algHom_ext
  rw [AlgHom.comp_apply, polyToAway_X, awayToPoly_chartCoord k hij, AlgHom.id_apply]

theorem awayToPoly_polyToAway_apply {i j : Fin 2} (hij : i ≠ j) (p : Polynomial k) :
    awayToPoly k i (polyToAway k i j p) = p :=
  AlgHom.congr_fun (awayToPoly_comp_polyToAway k hij) p

section Surjectivity

theorem prod_X_pow_eq {i j : Fin 2} (hij : i ≠ j) (e : Fin 2 → ℕ) :
    (∏ l, (X l : MvPolynomial (Fin 2) k) ^ e l) = X i ^ e i * X j ^ e j := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.prod_univ_two, mul_comm]

theorem sum_fin_two_eq {i j : Fin 2} (hij : i ≠ j) (e : Fin 2 → ℕ) :
    e i + e j = e 0 + e 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [add_comm]

theorem chartCoord_pow (i j : Fin 2) (m : ℕ) :
    chartCoord k i j ^ m =
      Away.mk 𝒜 (X_mem k i) m (X j ^ m)
        (by simpa using SetLike.pow_mem_graded m (X_mem k j)) := by
  rw [ext_iff_val, val_pow, val_chartCoord, Away.val_mk, Localization.mk_pow,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

theorem away_mk_prod_eq {i j : Fin 2} (hij : i ≠ j) (a : ℕ) (e : Fin 2 → ℕ)
    (hae : e 0 + e 1 = a)
    (H : (∏ l, (X l : MvPolynomial (Fin 2) k) ^ e l) ∈ 𝒜 (a • 1)) :
    Away.mk 𝒜 (X_mem k i) a (∏ l, X l ^ e l) H = chartCoord k i j ^ e j := by
  have hij' : e i + e j = a := (sum_fin_two_eq hij e).trans hae
  rw [chartCoord_pow, ext_iff_val, Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  push_cast
  rw [prod_X_pow_eq k hij e, ← hij']
  ring

theorem polyToAway_surjective {i j : Fin 2} (hij : i ≠ j) :
    Function.Surjective (polyToAway k i j) := by
  intro z
  have hz : z ∈ (⊤ : Submodule (𝒜 0) (Away 𝒜 (X i))) := trivial
  rw [← Away.span_mk_prod_pow_eq_top (X_mem k i) X (adjoin_gradeZero_range_X k)
    (fun _ => 1) (fun l => X_mem k l)] at hz
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
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

end Surjectivity

theorem polyToAway_comp_awayToPoly {i j : Fin 2} (hij : i ≠ j) :
    (polyToAway k i j).comp (awayToPoly k i) = AlgHom.id k (Away 𝒜 (X i)) := by
  refine AlgHom.ext fun z => ?_
  obtain ⟨p, rfl⟩ := polyToAway_surjective k hij z
  rw [AlgHom.comp_apply, AlgHom.id_apply, awayToPoly_polyToAway_apply k hij]

/-- The chart identification: the section ring `(k[X₀,X₁]_(Xᵢ))₀` of the chart `D₊(Xᵢ)` is a
polynomial ring over `k`, with variable the chart coordinate `t = Xⱼ/Xᵢ`. -/
noncomputable def awayAlgEquiv {i j : Fin 2} (hij : i ≠ j) :
    Away 𝒜 (X i) ≃ₐ[k] Polynomial k :=
  AlgEquiv.ofAlgHom (awayToPoly k i) (polyToAway k i j)
    (awayToPoly_comp_polyToAway k hij) (polyToAway_comp_awayToPoly k hij)

@[simp]
theorem awayAlgEquiv_chartCoord {i j : Fin 2} (hij : i ≠ j) :
    awayAlgEquiv k hij (chartCoord k i j) = Polynomial.X :=
  awayToPoly_chartCoord k hij

@[simp]
theorem awayAlgEquiv_symm_X {i j : Fin 2} (hij : i ≠ j) :
    (awayAlgEquiv k hij).symm Polynomial.X = chartCoord k i j :=
  (awayAlgEquiv k hij).symm_apply_eq.mpr (awayAlgEquiv_chartCoord k hij).symm

theorem awayAlgEquiv_polyToAway {i j : Fin 2} (hij : i ≠ j) (p : Polynomial k) :
    awayAlgEquiv k hij (polyToAway k i j p) = p :=
  AlgHom.congr_fun (awayToPoly_comp_polyToAway k hij) p

end P1

end AlgebraicGeometry
