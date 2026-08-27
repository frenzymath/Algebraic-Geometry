/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.P1ChartData

/-!
# The `ℙ¹` chart ring is a polynomial ring (over an arbitrary base ring)

For a commutative ring `R` and two *distinct* homogeneous coordinates `i ≠ j` of the
two-element index type `ULift (Fin 2)`, the degree-zero away ring

`(R[X₀, X₁]_{Xᵢ})₀ = HomogeneousLocalization.Away (homogeneousSubmodule (ULift (Fin 2)) R) (Xᵢ)`

— the section ring of the standard affine chart `D₊(Xᵢ)` of `Proj R[X₀, X₁] = ℙ¹_R` — is a
*free* `R`-algebra on one generator, namely the chart coordinate `t = Xⱼ/Xᵢ`:

`AlgebraicGeometry.Adelic.p1AwayAlgEquiv : Away 𝒜 (X i) ≃ₐ[R] Polynomial R`.

This is strictly stronger than the spanning statement `Adelic.span_p1CoordAway_pow_top` of
`AlgebraicJacobian.RiemannRoch.Adelic.P1ChartData` (which only says that the powers of `Xⱼ/Xᵢ`
*generate* the chart ring as an `𝒜 0`-module): here the powers are also independent, so the
chart ring is a polynomial ring, and in particular a domain when `R` is
(`instIsDomainAwayP1`).  Freeness — not just spanning — is what the rigid-pushforward chart
computations of `AlgebraicJacobian.Picard.RigidPushforward*` need: over a rank-one free module
there is no room for the correction terms a merely spanning family would allow, and a
polynomial ring over a field is a PID, which is what makes the fibre-chart classification of
line bundles on `ℙ¹` available.

## Main results

* `AlgebraicGeometry.Adelic.p1ChartCoord` — the chart coordinate `Xⱼ/Xᵢ` over a general base;
* `AlgebraicGeometry.Adelic.p1Dehomogenize` — dehomogenisation `R[X₀, X₁] → R[t]`, `Xᵢ ↦ 1`;
* `AlgebraicGeometry.Adelic.p1AwayAlgEquiv` — the chart identification `Away 𝒜 (X i) ≃ₐ[R] R[t]`;
* `AlgebraicGeometry.Adelic.p1AwayAlgEquiv_p1CoordAway` — its value on the coordinate fraction
  `Adelic.p1CoordAway` of `P1ChartData.lean` (the integral model, `R = ULift ℤ`);
* `AlgebraicGeometry.Adelic.instIsDomainAwayP1` — the chart ring is a domain over a domain.

## Implementation notes

The standard grading of `R[X₀, X₁]` is *not* installed as a global instance here (Mathlib
deliberately leaves `MvPolynomial.gradedAlgebra` unregistered, and `Picard/ProjectiveSpace.lean`
registers it only for the integral base `ULift ℤ`); it is taken as an instance *hypothesis*
`[GradedAlgebra (homogeneousSubmodule (ULift (Fin 2)) R)]`, which at `R = ULift ℤ` is discharged
by the project-wide instance, so the results specialise to the integral model with no
instance-mismatch bookkeeping.  For the same reason the grading is spelled out in full
throughout instead of being abbreviated by a local notation (a notation cannot carry the
universe annotation `ULift.{u}`).

The `R`-algebra structure on a homogeneous localization of a graded `R`-algebra (through
`R → 𝒜 0 → 𝒜_(f)`) is missing from Mathlib and is supplied here in its natural namespace.

No step of the argument uses invertibility of nonzero scalars: `R` is an arbitrary commutative
ring throughout (over a field this is `AlgebraicJacobian.Curve.P1.awayAlgEquiv` of the sibling
project `Algebraic-Jacobian-Challenge-Rebuild`).
-/

set_option autoImplicit false

universe u

open MvPolynomial HomogeneousLocalization

namespace HomogeneousLocalization

/-! ## The base-ring algebra structure on a homogeneous localization -/

section BaseAlgebra

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (x : Submonoid A)

/-- The value of the degree-zero fraction `c / 1` in the localization is the image of `c`. -/
lemma val_fromZeroRingHom (c : 𝒜 0) :
    (fromZeroRingHom 𝒜 x c).val = algebraMap A (Localization x) (c : A) := by
  have h : fromZeroRingHom 𝒜 x c = HomogeneousLocalization.mk ⟨0, c, 1, one_mem x⟩ := rfl
  rw [h, val_mk, ← Localization.mk_one_eq_algebraMap]
  congr 1

/-- If `A` is a graded `R`-algebra, then any homogeneous localization of `A` is an `R`-algebra,
via `R → 𝒜 0 → HomogeneousLocalization 𝒜 x`.  The scalar action is the existing pointwise
one. -/
noncomputable instance instAlgebraBase : Algebra R (HomogeneousLocalization 𝒜 x) where
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

/-- The structure map of `HomogeneousLocalization.instAlgebraBase` factors through `𝒜 0`. -/
lemma algebraMap_eq_comp :
    algebraMap R (HomogeneousLocalization 𝒜 x) =
      (fromZeroRingHom 𝒜 x).comp (algebraMap R (𝒜 0)) :=
  rfl

instance : IsScalarTower R (𝒜 0) (HomogeneousLocalization 𝒜 x) :=
  .of_algebraMap_eq' rfl

@[simp]
lemma algebraMap_val (r : R) :
    (algebraMap R (HomogeneousLocalization 𝒜 x) r).val =
      algebraMap A (Localization x) (algebraMap R A r) := by
  rw [algebraMap_eq_comp, RingHom.comp_apply, val_fromZeroRingHom,
    SetLike.GradeZero.coe_algebraMap]

end BaseAlgebra

end HomogeneousLocalization

namespace AlgebraicGeometry.Adelic

/-! ## The chart ring of `ℙ¹` over a general commutative ring -/

section ChartRing

variable (R : Type u) [CommRing R]

/-! ### Generalities on the two-element index type -/

/-- Two distinct homogeneous coordinates exhaust the index type. -/
private theorem univ_eq_pair {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    (Finset.univ : Finset (ULift.{u} (Fin 2))) = {i, j} :=
  (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hij]; simp)).symm

/-- Reading the total degree off a `Away.span_mk_prod_pow_eq_top` exponent vector. -/
private theorem add_eq_of_sum_smul_one {i j : ULift.{u} (Fin 2)} (hij : i ≠ j)
    {e : ULift.{u} (Fin 2) → ℕ} {a : ℕ} (hae : ∑ l, e l • (1 : ℕ) = a • (1 : ℕ)) :
    e i + e j = a := by
  rw [univ_eq_pair hij, Finset.sum_pair hij] at hae
  simpa using hae

/-- The two-element index type has, for each `i`, an index distinct from `i`. -/
private theorem exists_ne_index (i : ULift.{u} (Fin 2)) : ∃ j : ULift.{u} (Fin 2), i ≠ j :=
  ⟨⟨i.down + 1⟩, fun h => by simpa using congrArg (fun l : ULift.{u} (Fin 2) => l.down) h⟩

/-- A product over the two homogeneous coordinates, in the order given by `i ≠ j`. -/
private theorem prod_X_pow_eq {i j : ULift.{u} (Fin 2)} (hij : i ≠ j)
    (e : ULift.{u} (Fin 2) → ℕ) :
    (∏ l, (X l : MvPolynomial (ULift.{u} (Fin 2)) R) ^ e l) = X i ^ e i * X j ^ e j := by
  rw [univ_eq_pair hij, Finset.prod_pair hij]

/-- The variable `Xᵢ` of `R[X₀, X₁]` is homogeneous of degree one. -/
theorem p1X_mem_deg_one (i : ULift.{u} (Fin 2)) :
    (X i : MvPolynomial (ULift.{u} (Fin 2)) R) ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) R 1 :=
  isHomogeneous_X _ _

/-! ### Dehomogenisation -/

/-- Dehomogenisation at `Xᵢ`: the `R`-algebra map `R[X₀, X₁] → R[t]` with `Xᵢ ↦ 1`,
`Xⱼ ↦ t`. -/
noncomputable def p1Dehomogenize (i : ULift.{u} (Fin 2)) :
    MvPolynomial (ULift.{u} (Fin 2)) R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval (Function.update (fun _ => Polynomial.X) i 1)

@[simp]
theorem p1Dehomogenize_X_self (i : ULift.{u} (Fin 2)) : p1Dehomogenize R i (X i) = 1 := by
  rw [p1Dehomogenize, MvPolynomial.aeval_X, Function.update_self]

theorem p1Dehomogenize_X_of_ne {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    p1Dehomogenize R i (X j) = Polynomial.X := by
  rw [p1Dehomogenize, MvPolynomial.aeval_X, Function.update_of_ne hij.symm]

private theorem isUnit_p1Dehomogenize_X_self (i : ULift.{u} (Fin 2)) :
    IsUnit ((p1Dehomogenize R i).toRingHom (X i)) := by
  have h : (p1Dehomogenize R i).toRingHom (X i) = 1 := p1Dehomogenize_X_self R i
  rw [h]
  exact isUnit_one

/-! ### The degree-zero part -/

/-- The degree-zero part of `R[X₀, X₁]` consists of the constants: every element of `𝒜 0` is
the image of a scalar.  (Over a field this is the bijectivity half of
`AlgebraicJacobian.Curve.P1.gradeZeroAlgEquiv`; over `ULift ℤ` it is
`AlgebraicGeometry.ProjectiveSpace.bijective_algebraMap_gradeZero`.) -/
theorem exists_algebraMap_eq_gradeZero (c : homogeneousSubmodule (ULift.{u} (Fin 2)) R 0) :
    ∃ r : R, algebraMap R (homogeneousSubmodule (ULift.{u} (Fin 2)) R 0) r = c := by
  have hc : (c : MvPolynomial (ULift.{u} (Fin 2)) R) ∈
      (1 : Submodule R (MvPolynomial (ULift.{u} (Fin 2)) R)) := by
    rw [← homogeneousSubmodule_zero (σ := ULift.{u} (Fin 2)) (R := R)]
    exact c.2
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
  exact ⟨r, Subtype.ext (by simpa using hr)⟩

/-- The homogeneous coordinate ring is generated over its degree-zero part by the variables. -/
theorem adjoin_gradeZero_range_X :
    Algebra.adjoin (homogeneousSubmodule (ULift.{u} (Fin 2)) R 0)
      (Set.range (X : ULift.{u} (Fin 2) → MvPolynomial (ULift.{u} (Fin 2)) R)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  have hp : p ∈ Algebra.adjoin R
      (Set.range (X : ULift.{u} (Fin 2) → MvPolynomial (ULift.{u} (Fin 2)) R)) := by
    rw [MvPolynomial.adjoin_range_X]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem q hq => exact Algebra.subset_adjoin hq
  | algebraMap r =>
    exact Subalgebra.algebraMap_mem _
      (⟨algebraMap R (MvPolynomial (ULift.{u} (Fin 2)) R) r, by
        rw [MvPolynomial.algebraMap_eq]
        exact isHomogeneous_C _ r⟩ : homogeneousSubmodule (ULift.{u} (Fin 2)) R 0)
  | add q₁ q₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
  | mul q₁ q₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂

variable [GradedAlgebra (homogeneousSubmodule (ULift.{u} (Fin 2)) R)]

/-! ### The chart coordinate -/

/-- The chart coordinate `t = Xⱼ/Xᵢ` in the section ring of the chart `D₊(Xᵢ)` of `ℙ¹_R`.
At `R = ULift ℤ` this is `AlgebraicGeometry.Adelic.p1CoordAway`. -/
noncomputable def p1ChartCoord (i j : ULift.{u} (Fin 2)) :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (X i) :=
  Away.mk _ (p1X_mem_deg_one R i) 1 (X j) (by simpa using p1X_mem_deg_one R j)

theorem val_p1ChartCoord (i j : ULift.{u} (Fin 2)) :
    (p1ChartCoord R i j).val = Localization.mk (X j)
      (⟨X i ^ 1, 1, rfl⟩ : Submonoid.powers (X i : MvPolynomial (ULift.{u} (Fin 2)) R)) :=
  rfl

theorem p1ChartCoord_pow (i j : ULift.{u} (Fin 2)) (m : ℕ) :
    p1ChartCoord R i j ^ m =
      Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (p1X_mem_deg_one R i) m (X j ^ m)
        (by simpa using SetLike.pow_mem_graded m (p1X_mem_deg_one R j)) := by
  rw [ext_iff_val, val_pow, val_p1ChartCoord, Away.val_mk, Localization.mk_pow,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

/-! ### The two `R`-algebra maps between the chart ring and the polynomial ring -/

/-- `R[t] → (R[X₀, X₁]_{Xᵢ})₀`, `t ↦ Xⱼ/Xᵢ`.  Bijective for `i ≠ j`; see `p1AwayAlgEquiv`. -/
noncomputable def p1PolyToAway (i j : ULift.{u} (Fin 2)) :
    Polynomial R →ₐ[R] Away (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (X i) :=
  Polynomial.aeval (p1ChartCoord R i j)

@[simp]
theorem p1PolyToAway_X (i j : ULift.{u} (Fin 2)) :
    p1PolyToAway R i j Polynomial.X = p1ChartCoord R i j :=
  Polynomial.aeval_X _

/-- `(R[X₀, X₁]_{Xᵢ})₀ → R[t]`, induced by dehomogenisation at `Xᵢ`.  Inverse of
`p1PolyToAway`; see `p1AwayAlgEquiv`. -/
noncomputable def p1AwayToPoly (i : ULift.{u} (Fin 2)) :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (X i) →ₐ[R] Polynomial R where
  toRingHom :=
    (Localization.awayLift (p1Dehomogenize R i).toRingHom (X i)
      (isUnit_p1Dehomogenize_X_self R i)).comp
      (algebraMap (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (X i))
        (Localization.Away (X i : MvPolynomial (ULift.{u} (Fin 2)) R)))
  commutes' r := by
    change (Localization.awayLift (p1Dehomogenize R i).toRingHom (X i)
        (isUnit_p1Dehomogenize_X_self R i))
        ((algebraMap R (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (X i)) r).val)
      = algebraMap R (Polynomial R) r
    rw [HomogeneousLocalization.algebraMap_val, IsLocalization.Away.lift_eq]
    exact (p1Dehomogenize R i).commutes r

/-- The workhorse: `p1AwayToPoly` sends `a/Xᵢⁿ` to the dehomogenisation of `a`. -/
theorem p1AwayToPoly_mk (i : ULift.{u} (Fin 2)) (n : ℕ)
    (a : MvPolynomial (ULift.{u} (Fin 2)) R)
    (ha : a ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) R (n • 1)) :
    p1AwayToPoly R i
        (Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (p1X_mem_deg_one R i) n a ha)
      = p1Dehomogenize R i a := by
  have h1 : (p1Dehomogenize R i).toRingHom (X i) * 1 = 1 := by
    rw [mul_one]
    exact p1Dehomogenize_X_self R i
  have h := Localization.awayLift_mk (A := Polynomial R)
    ((p1Dehomogenize R i).toRingHom) (X i) a 1 h1 n
  exact h.trans (by rw [one_pow, mul_one]; rfl)

@[simp]
theorem p1AwayToPoly_p1ChartCoord {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    p1AwayToPoly R i (p1ChartCoord R i j) = Polynomial.X :=
  (p1AwayToPoly_mk R i 1 (X j) (by simpa using p1X_mem_deg_one R j)).trans
    (p1Dehomogenize_X_of_ne R hij)

theorem p1AwayToPoly_comp_p1PolyToAway {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    (p1AwayToPoly R i).comp (p1PolyToAway R i j) = AlgHom.id R (Polynomial R) := by
  apply Polynomial.algHom_ext
  rw [AlgHom.comp_apply, p1PolyToAway_X, p1AwayToPoly_p1ChartCoord R hij, AlgHom.id_apply]

theorem p1AwayToPoly_p1PolyToAway_apply {i j : ULift.{u} (Fin 2)} (hij : i ≠ j)
    (p : Polynomial R) : p1AwayToPoly R i (p1PolyToAway R i j p) = p :=
  AlgHom.congr_fun (p1AwayToPoly_comp_p1PolyToAway R hij) p

/-! ### Surjectivity of `p1PolyToAway` -/

private theorem away_mk_prod_eq {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) (a : ℕ)
    (e : ULift.{u} (Fin 2) → ℕ) (hae : e i + e j = a)
    (H : (∏ l, (X l : MvPolynomial (ULift.{u} (Fin 2)) R) ^ e l) ∈
      homogeneousSubmodule (ULift.{u} (Fin 2)) R (a • 1)) :
    Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (p1X_mem_deg_one R i) a
        (∏ l, X l ^ e l) H
      = p1ChartCoord R i j ^ e j := by
  rw [p1ChartCoord_pow, ext_iff_val, Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  push_cast
  rw [prod_X_pow_eq R hij e, ← hae]
  ring

theorem p1PolyToAway_surjective {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    Function.Surjective (p1PolyToAway R i j) := by
  intro z
  have hz : z ∈ (⊤ : Submodule (homogeneousSubmodule (ULift.{u} (Fin 2)) R 0)
      (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (X i))) := trivial
  rw [← Away.span_mk_prod_pow_eq_top (p1X_mem_deg_one R i) X (adjoin_gradeZero_range_X R)
    (fun _ => 1) (fun l => p1X_mem_deg_one R l)] at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, e, hae, rfl⟩ := hw
    refine ⟨Polynomial.X ^ e j, ?_⟩
    rw [map_pow, p1PolyToAway_X]
    exact (away_mk_prod_eq R hij a e (add_eq_of_sum_smul_one hij hae) _).symm
  | zero => exact ⟨0, map_zero _⟩
  | add u v _ _ hu hv =>
    obtain ⟨p, rfl⟩ := hu
    obtain ⟨q, rfl⟩ := hv
    exact ⟨p + q, map_add _ _ _⟩
  | smul c w _ hw =>
    obtain ⟨p, rfl⟩ := hw
    obtain ⟨r, rfl⟩ := exists_algebraMap_eq_gradeZero R c
    exact ⟨r • p, by rw [map_smul, IsScalarTower.algebraMap_smul]⟩

theorem p1PolyToAway_comp_p1AwayToPoly {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    (p1PolyToAway R i j).comp (p1AwayToPoly R i)
      = AlgHom.id R (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (X i)) := by
  refine AlgHom.ext fun z => ?_
  obtain ⟨p, rfl⟩ := p1PolyToAway_surjective R hij z
  rw [AlgHom.comp_apply, AlgHom.id_apply, p1AwayToPoly_p1PolyToAway_apply R hij]

/-! ### The chart identification -/

/-- **The chart ring of `ℙ¹` is free.**  The section ring `(R[X₀, X₁]_{Xᵢ})₀` of the standard
chart `D₊(Xᵢ)` of `ℙ¹_R` is a polynomial ring over `R`, on the chart coordinate
`t = Xⱼ/Xᵢ` (`p1ChartCoord`). -/
noncomputable def p1AwayAlgEquiv {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (X i) ≃ₐ[R] Polynomial R :=
  AlgEquiv.ofAlgHom (p1AwayToPoly R i) (p1PolyToAway R i j)
    (p1AwayToPoly_comp_p1PolyToAway R hij) (p1PolyToAway_comp_p1AwayToPoly R hij)

@[simp]
theorem p1AwayAlgEquiv_p1ChartCoord {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    p1AwayAlgEquiv R hij (p1ChartCoord R i j) = Polynomial.X :=
  p1AwayToPoly_p1ChartCoord R hij

@[simp]
theorem p1AwayAlgEquiv_symm_X {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    (p1AwayAlgEquiv R hij).symm Polynomial.X = p1ChartCoord R i j :=
  (p1AwayAlgEquiv R hij).symm_apply_eq.mpr (p1AwayAlgEquiv_p1ChartCoord R hij).symm

theorem p1AwayAlgEquiv_p1PolyToAway {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) (p : Polynomial R) :
    p1AwayAlgEquiv R hij (p1PolyToAway R i j p) = p :=
  p1AwayToPoly_p1PolyToAway_apply R hij p

/-- **The chart ring of `ℙ¹` over a domain is a domain**, being a polynomial ring. -/
instance instIsDomainAwayP1 [IsDomain R] (i : ULift.{u} (Fin 2)) :
    IsDomain (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) R) (X i)) := by
  obtain ⟨j, hij⟩ := exists_ne_index i
  exact Function.Injective.isDomain (p1AwayAlgEquiv R hij).toRingEquiv.toRingHom
    (p1AwayAlgEquiv R hij).injective

end ChartRing

/-! ## The integral model `R = ULift ℤ`

The base of the integral model of `ℙ¹` used throughout `AlgebraicJacobian` (the grading
`𝒫[n] = homogeneousSubmodule n (ULift ℤ)` of `Picard/ProjectiveSpace.lean`).  Here the general
chart coordinate is *definitionally* the coordinate fraction `Adelic.p1CoordAway` of
`RiemannRoch/Adelic/P1ChartData.lean`. -/

section IntegralModel

/-- `ULift ℤ` is a domain (not available by unification from the instance for `ℤ`). -/
instance instIsDomainULiftInt : IsDomain (ULift.{u} ℤ) :=
  Function.Injective.isDomain (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom
    ULift.ringEquiv.injective

/-- Over the integral base, the chart coordinate is `Adelic.p1CoordAway`. -/
theorem p1ChartCoord_eq_p1CoordAway (i j : ULift.{u} (Fin 2)) :
    p1ChartCoord (ULift.{u} ℤ) i j = p1CoordAway (ULift.{u} (Fin 2)) i j :=
  rfl

/-- **The chart identification sends the coordinate fraction `Xⱼ/Xᵢ` to the variable.**  This is
the interface to the existing chart data of `RiemannRoch/Adelic/P1ChartData.lean`. -/
@[simp]
theorem p1AwayAlgEquiv_p1CoordAway {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    p1AwayAlgEquiv (ULift.{u} ℤ) hij (p1CoordAway (ULift.{u} (Fin 2)) i j) = Polynomial.X := by
  rw [← p1ChartCoord_eq_p1CoordAway]
  exact p1AwayAlgEquiv_p1ChartCoord _ hij

/-- The chart ring of the integral model of `ℙ¹` is a domain. -/
example (i : ULift.{u} (Fin 2)) :
    IsDomain (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)) :=
  inferInstance

end IntegralModel

end AlgebraicGeometry.Adelic
