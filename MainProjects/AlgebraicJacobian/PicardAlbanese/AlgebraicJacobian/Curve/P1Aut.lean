/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.P1
import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Automorphisms of the projective line: the `GL₂`-twist

Work in progress.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace MvPolynomial

section LinearSubstitution

variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]

/-- The linear form `∑ⱼ Mᵢⱼ Xⱼ`, the image of `Xᵢ` under the substitution attached to a
square matrix `M`. -/
noncomputable def matrixLinearForm (M : Matrix σ σ R) (i : σ) : MvPolynomial σ R :=
  ∑ j, M i j • X j

/-- The linear forms attached to a matrix are homogeneous of degree one. -/
theorem matrixLinearForm_mem (M : Matrix σ σ R) (i : σ) :
    matrixLinearForm M i ∈ homogeneousSubmodule σ R 1 :=
  Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (X_mem_homogeneousSubmodule_one R j)

/-- The `R`-algebra endomorphism of `R[Xᵢ]` given by the linear substitution
`Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ`. -/
noncomputable def substAlgHom (M : Matrix σ σ R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (matrixLinearForm M)

@[simp]
theorem substAlgHom_X (M : Matrix σ σ R) (i : σ) :
    substAlgHom M (X i) = matrixLinearForm M i :=
  aeval_X _ _

/-- A linear substitution preserves the degree of a homogeneous polynomial. -/
theorem substAlgHom_mem (M : Matrix σ σ R) {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ homogeneousSubmodule σ R d) :
    substAlgHom M p ∈ homogeneousSubmodule σ R d := by
  rw [mem_homogeneousSubmodule] at hp ⊢
  have h := hp.aeval (matrixLinearForm M)
    (fun i => (mem_homogeneousSubmodule _ _).mp (matrixLinearForm_mem M i))
  rwa [one_mul] at h

/-- The linear substitution attached to a matrix, as a *graded* ring endomorphism of
`R[Xᵢ]` for the standard degree grading. -/
noncomputable def substGradedHom (M : Matrix σ σ R) :
    homogeneousSubmodule σ R →+*ᵍ homogeneousSubmodule σ R where
  __ := (substAlgHom M).toRingHom
  map_mem := substAlgHom_mem M

@[simp]
theorem substGradedHom_apply (M : Matrix σ σ R) (p : MvPolynomial σ R) :
    substGradedHom M p = substAlgHom M p :=
  rfl

/-- The substitution attached to a product of matrices is the composite of the substitutions,
in the *reverse* order: `subst (M * N) = subst N ∘ subst M`. -/
theorem substAlgHom_mul (M N : Matrix σ σ R) :
    substAlgHom (M * N) = (substAlgHom N).comp (substAlgHom M) := by
  refine algHom_ext fun i => ?_
  rw [substAlgHom_X, AlgHom.comp_apply, substAlgHom_X, matrixLinearForm, matrixLinearForm,
    map_sum]
  simp_rw [map_smul, substAlgHom_X, matrixLinearForm, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- A linear substitution is the identity in degree zero: it is an `R`-algebra map, and the
degree-zero part of `R[Xᵢ]` consists of the constants. -/
theorem substAlgHom_of_mem_zero (M : Matrix σ σ R) {p : MvPolynomial σ R}
    (hp : p ∈ homogeneousSubmodule σ R 0) : substAlgHom M p = p := by
  rw [homogeneousSubmodule_zero] at hp
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hp
  exact (substAlgHom M).commutes r

/-- The degree-zero component of a linear substitution is the identity. -/
theorem substGradedHom_gradedZeroRingHom (M : Matrix σ σ R) :
    (substGradedHom M).gradedZeroRingHom = RingHom.id (homogeneousSubmodule σ R 0) :=
  RingHom.ext fun c => Subtype.ext (substAlgHom_of_mem_zero M c.2)

/-- The substitution attached to a product of matrices, as graded ring homs. -/
theorem substGradedHom_mul (M N : Matrix σ σ R) :
    substGradedHom (M * N) = (substGradedHom N).comp (substGradedHom M) :=
  GradedRingHom.ext fun p => DFunLike.congr_fun (substAlgHom_mul M N) p

section DecEq

variable [DecidableEq σ]

/-- The identity matrix induces the identity substitution. -/
@[simp]
theorem substAlgHom_one : substAlgHom (1 : Matrix σ σ R) = AlgHom.id R (MvPolynomial σ R) := by
  refine algHom_ext fun i => ?_
  rw [substAlgHom_X, AlgHom.id_apply, matrixLinearForm]
  simp [Matrix.one_apply, ite_smul]

/-- The identity matrix induces the identity graded ring hom. -/
@[simp]
theorem substGradedHom_one :
    substGradedHom (1 : Matrix σ σ R) = GradedRingHom.id (homogeneousSubmodule σ R) :=
  GradedRingHom.ext fun p => DFunLike.congr_fun (substAlgHom_one (σ := σ) (R := R)) p

end DecEq

end LinearSubstitution

end MvPolynomial

namespace AlgebraicGeometry

open HomogeneousIdeal MvPolynomial Graded

section IrrelevantLe

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A graded ring hom admitting a graded set-theoretic section satisfies the hypothesis
`ℬ₊ ≤ 𝒜₊.map f` needed to form `Proj.map f`. Indeed a positive-degree element `x` of `ℬ`
is `f (g x)`, and `g x` is again of positive degree, hence irrelevant. -/
theorem irrelevant_le_map_of_rightInverse (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (h : ∀ x, f (g x) = x) : ℬ₊ ≤ 𝒜₊.map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  have hgx : g x ∈ 𝒜₊ := HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi (map_mem g hx)
  have hmem : f (g x) ∈ (𝒜₊.map f).toIdeal :=
    Ideal.mem_map_of_mem (f : A →+* B) hgx
  rw [h x] at hmem
  exact hmem

end IrrelevantLe

section MapCongr

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- `Proj.map` only depends on the graded ring hom, not on the proof of its hypothesis. -/
theorem Proj.map_congr {f g : 𝒜 →+*ᵍ ℬ} (h : f = g) (hf : ℬ₊ ≤ 𝒜₊.map f)
    (hg : ℬ₊ ≤ 𝒜₊.map g) : Proj.map f hf = Proj.map g hg := by
  subst h; rfl

end MapCongr

section ToSpecZero

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The degree-zero part is natural for the localization maps: mapping `c/1` along a graded
ring hom `f` gives `f c / 1`. -/
theorem HomogeneousLocalization.Away.map_comp_fromZeroRingHom (f : 𝒜 →+*ᵍ ℬ) (x : A) :
    (HomogeneousLocalization.Away.map f x).comp
        (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers x)) =
      (HomogeneousLocalization.fromZeroRingHom ℬ (Submonoid.powers (f x))).comp
        f.gradedZeroRingHom := by
  have hle : Submonoid.powers x ≤ (Submonoid.powers (f x)).comap f := by
    rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩
  have hmap : HomogeneousLocalization.Away.map f x = HomogeneousLocalization.map f hle := rfl
  refine RingHom.ext fun c => ?_
  have h1 : HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers x) c =
      HomogeneousLocalization.mk ⟨0, c, 1, Submonoid.one_mem _⟩ := rfl
  have h2 : HomogeneousLocalization.fromZeroRingHom ℬ (Submonoid.powers (f x))
        (f.gradedZeroRingHom c) =
      HomogeneousLocalization.mk ⟨0, f.gradedZeroRingHom c, 1, Submonoid.one_mem _⟩ := rfl
  rw [RingHom.comp_apply, RingHom.comp_apply, h1, h2, hmap, HomogeneousLocalization.map_mk]
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `Proj A ⟶ Spec A₀` in the graded ring `A`. -/
theorem Proj.map_comp_toSpecZero (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s => ?_
  obtain ⟨n, x, hx⟩ := s
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [Proj.awayι_comp_map_assoc f hf n.2 x hx, Proj.awayι_toSpecZero,
    Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    HomogeneousLocalization.Away.map_comp_fromZeroRingHom]

end ToSpecZero

namespace P1

variable (k : Type u) [Field k]

open scoped LinearAlgebra.Projectivization

local notation "𝒜" => homogeneousSubmodule (Fin 2) k

/-- Notation-free shorthand for the coefficient matrix of `M ∈ GL₂(k)`. -/
local notation "mat" M => ((M : Matrix.GeneralLinearGroup (Fin 2) k) :
  Matrix (Fin 2) (Fin 2) k)

/-- The substitution attached to an invertible matrix satisfies the hypothesis of `Proj.map`:
its inverse substitution is a two-sided inverse. -/
theorem irrelevant_le_map_substGradedHom (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    𝒜₊ ≤ 𝒜₊.map (substGradedHom (mat M)) := by
  refine irrelevant_le_map_of_rightInverse _ (substGradedHom (mat M⁻¹)) fun x => ?_
  have h : substGradedHom ((mat M⁻¹) * (mat M)) =
      (substGradedHom (mat M)).comp (substGradedHom (mat M⁻¹)) := substGradedHom_mul _ _
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, substGradedHom_one] at h
  exact DFunLike.congr_fun h.symm x

/-- **The `GL₂(k)`-twist of the projective line.** The linear substitution
`Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` attached to `M ∈ GL₂(k)` induces, via functoriality of `Proj`, an
automorphism of `P¹_k`. -/
noncomputable def autOfMatrix (M : Matrix.GeneralLinearGroup (Fin 2) k) : P1 k ⟶ P1 k :=
  Proj.map (substGradedHom (mat M)) (irrelevant_le_map_substGradedHom k M)

@[simp]
theorem autOfMatrix_one : autOfMatrix k 1 = 𝟙 (P1 k) := by
  refine Eq.trans (Proj.map_congr (g := GradedRingHom.id 𝒜) ?_ _ (by simp)) Proj.map_id
  rw [Units.val_one, substGradedHom_one]

/-- Functoriality. `Proj.map` is contravariant, so `M ↦ autOfMatrix M` is an
**anti**-homomorphism for composition of morphisms: `γ_{MN} = γ_N ≫ γ_M`.
(Equivalently, it *is* a homomorphism into `Aut (P1 k)`, whose multiplication is
`(f * g).hom = g.hom ≫ f.hom`; see `P1.autMonoidHom`.) -/
theorem autOfMatrix_mul (M N : Matrix.GeneralLinearGroup (Fin 2) k) :
    autOfMatrix k (M * N) = autOfMatrix k N ≫ autOfMatrix k M := by
  have h := Proj.map_comp (substGradedHom (mat M)) (substGradedHom (mat N))
    (irrelevant_le_map_substGradedHom k M) (irrelevant_le_map_substGradedHom k N)
  refine Eq.trans (Proj.map_congr ?_ _ _) h
  rw [Units.val_mul, substGradedHom_mul]

/-- The `GL₂(k)`-twist as an isomorphism of schemes, with inverse the twist by `M⁻¹`. -/
@[simps]
noncomputable def autIsoOfMatrix (M : Matrix.GeneralLinearGroup (Fin 2) k) : P1 k ≅ P1 k where
  hom := autOfMatrix k M
  inv := autOfMatrix k M⁻¹
  hom_inv_id := by rw [← autOfMatrix_mul, inv_mul_cancel, autOfMatrix_one]
  inv_hom_id := by rw [← autOfMatrix_mul, mul_inv_cancel, autOfMatrix_one]

instance isIso_autOfMatrix (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    IsIso (autOfMatrix k M) :=
  (autIsoOfMatrix k M).isIso_hom

/-- The action of `GL₂(k)` on `P¹_k` by scheme automorphisms, as a group homomorphism
`GL₂(k) →* Aut (P¹_k)`. -/
@[simps]
noncomputable def autMonoidHom : Matrix.GeneralLinearGroup (Fin 2) k →* Aut (P1 k) where
  toFun := autIsoOfMatrix k
  map_one' := Iso.ext (autOfMatrix_one k)
  map_mul' M N := Iso.ext (autOfMatrix_mul k M N)

/-! ### The twist lies over `Spec k`

This is what makes `γ ≫ π` still satisfy the DD-R compatibility `hpi`: a linear substitution
is `k`-linear, hence the identity in degree zero, so it commutes with `Proj 𝒜 ⟶ Spec (𝒜 0)`. -/

theorem autOfMatrix_comp_toSpecZero (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    autOfMatrix k M ≫ Proj.toSpecZero 𝒜 = Proj.toSpecZero 𝒜 := by
  have h := Proj.map_comp_toSpecZero (substGradedHom (mat M))
    (irrelevant_le_map_substGradedHom k M)
  rw [substGradedHom_gradedZeroRingHom] at h
  simp only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] at h
  exact h

/-- **The twist is a morphism over `Spec k`.** -/
theorem autOfMatrix_comp_structureMap (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    autOfMatrix k M ≫ structureMap k = structureMap k := by
  change autOfMatrix k M ≫ Proj.toSpecZero 𝒜 ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0))) = _
  rw [← Category.assoc, autOfMatrix_comp_toSpecZero]
  rfl

/-! ### The twisted charts

The twist `γ = autOfMatrix M` pulls the standard chart `D₊(Xᵢ)` back to the basic open of the
linear form `ℓᵢ = ∑ⱼ Mᵢⱼ Xⱼ` — the `i`-th row of `M`. These twisted charts are again affine and
again cover `P¹_k`. -/

/-- The `i`-th twisted coordinate `ℓᵢ = ∑ⱼ Mᵢⱼ Xⱼ`. -/
noncomputable def twistedCoord (M : Matrix.GeneralLinearGroup (Fin 2) k) (i : Fin 2) :
    MvPolynomial (Fin 2) k :=
  matrixLinearForm (mat M) i

theorem twistedCoord_mem (M : Matrix.GeneralLinearGroup (Fin 2) k) (i : Fin 2) :
    twistedCoord k M i ∈ 𝒜 1 :=
  matrixLinearForm_mem _ i

/-- **The twisted chart.** `γ⁻¹(D₊(Xᵢ)) = D₊(ℓᵢ)`, where `ℓᵢ` is the `i`-th row form of `M`.
This is free: `Proj.map_preimage_basicOpen` holds by `rfl`. -/
theorem autOfMatrix_preimage_chartOpen (M : Matrix.GeneralLinearGroup (Fin 2) k) (i : Fin 2) :
    autOfMatrix k M ⁻¹ᵁ chartOpen k i = Proj.basicOpen 𝒜 (twistedCoord k M i) := by
  have h : autOfMatrix k M ⁻¹ᵁ chartOpen k i =
      Proj.basicOpen 𝒜 (substGradedHom (mat M) (X i)) := rfl
  rw [h, substGradedHom_apply, substAlgHom_X]
  rfl

/-- Each twisted chart is an affine open, directly from `Proj.isAffineOpen_basicOpen`
applied to the degree-one form `ℓᵢ`. -/
theorem isAffineOpen_preimage_chartOpen (M : Matrix.GeneralLinearGroup (Fin 2) k) (i : Fin 2) :
    IsAffineOpen (autOfMatrix k M ⁻¹ᵁ chartOpen k i) := by
  rw [autOfMatrix_preimage_chartOpen]
  exact Proj.isAffineOpen_basicOpen 𝒜 (twistedCoord k M i) (twistedCoord_mem k M i) one_pos

/-- The two twisted charts still cover `P¹_k`: preimage preserves `⊔` and `⊤`. -/
theorem autOfMatrix_preimage_chartOpen_sup (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    (autOfMatrix k M ⁻¹ᵁ chartOpen k 0) ⊔ (autOfMatrix k M ⁻¹ᵁ chartOpen k 1) = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, chartOpen_sup, Scheme.Hom.preimage_top]

/-! ### Two-transitivity on rational points -/

/-- The type of `k`-rational points of the projective line, in homogeneous coordinates. -/
abbrev RationalPoint := ℙ k (Fin 2 → k)

/-- **Two-transitivity of `GL₂(k)` on `P¹(k)`.** Any ordered pair of distinct rational
points can be carried to any other ordered pair by one invertible matrix. The matrix action here
is the homogeneous-coordinate action underlying `autOfMatrix`. -/
theorem exists_matrix_smul_pair {p₀ p₁ q₀ q₁ : RationalPoint k}
    (hp : p₀ ≠ p₁) (hq : q₀ ≠ q₁) :
    ∃ M : Matrix.GeneralLinearGroup (Fin 2) k,
      Matrix.GeneralLinearGroup.toLin M • p₀ = q₀ ∧
      Matrix.GeneralLinearGroup.toLin M • p₁ = q₁ := by
  have htrans : MulAction.IsMultiplyPretransitive
      (LinearMap.GeneralLinearGroup k (Fin 2 → k)) (RationalPoint k) 2 :=
    inferInstance
  obtain ⟨g, hg₀, hg₁⟩ := (MulAction.is_two_pretransitive_iff.mp htrans) hp hq
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm g, ?_, ?_⟩
  · simpa using hg₀
  · simpa using hg₁

/-! ### Avoiding a finite set with two twisted charts -/

/-- The scalars whose affine linear form `X₁ - aX₀` vanishes at a point of `P¹`. -/
noncomputable def badScalars (x : P1 k) : Set k :=
  {a | X 1 - C a * X 0 ∈ x.asHomogeneousIdeal}

/-- At a projective point, at most one form in the pencil `X₁ - aX₀` vanishes. -/
theorem badScalars_subsingleton (x : P1 k) : (badScalars k x).Subsingleton := by
  intro a ha b hb
  change X 1 - C a * X 0 ∈ x.asHomogeneousIdeal at ha
  change X 1 - C b * X 0 ∈ x.asHomogeneousIdeal at hb
  by_contra hab
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hd : C (b - a) * (X 0 : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal := by
    rw [show C (b - a) * (X 0 : MvPolynomial (Fin 2) k) =
      (X 1 - C a * X 0) - (X 1 - C b * X 0) by rw [C_sub]; ring]
    exact x.asHomogeneousIdeal.sub_mem ha hb
  have hx0 : (X 0 : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal := by
    have hmul := x.asHomogeneousIdeal.toIdeal.mul_mem_left (C (b - a)⁻¹) hd
    rw [show C (b - a)⁻¹ * (C (b - a) * (X 0 : MvPolynomial (Fin 2) k)) = X 0 by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hba, C_1, one_mul]] at hmul
    exact hmul
  have hx1 : (X 1 : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal := by
    rw [show (X 1 : MvPolynomial (Fin 2) k) =
      (X 1 - C a * X 0) + C a * X 0 by ring]
    exact x.asHomogeneousIdeal.add_mem ha
      (x.asHomogeneousIdeal.toIdeal.mul_mem_left (C a) hx0)
  have hxcover : x ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
    rw [chartOpen_sup]
    trivial
  change x ∈ chartOpen k 0 ∨ x ∈ chartOpen k 1 at hxcover
  rcases hxcover with hxcover | hxcover
  · change (X 0 : MvPolynomial (Fin 2) k) ∉ x.asHomogeneousIdeal at hxcover
    exact hxcover hx0
  · change (X 1 : MvPolynomial (Fin 2) k) ∉ x.asHomogeneousIdeal at hxcover
    exact hxcover hx1

/-- The union of the bad scalar sets of a finite subset of `P¹` has cardinality at most the
cardinality of that subset. -/
theorem badScalars_biUnion_ncard_le (S : Set (P1 k)) (hS : S.Finite) :
    (⋃ x ∈ S, badScalars k x).ncard ≤ S.ncard := by
  classical
  let s : Finset (P1 k) := hS.toFinset
  have hEq : (⋃ x ∈ S, badScalars k x) = ⋃ x ∈ s, badScalars k x := by
    ext a
    simp [s]
  rw [hEq]
  calc
    (⋃ x ∈ s, badScalars k x).ncard
        ≤ ∑ x ∈ s, (badScalars k x).ncard :=
      Finset.set_ncard_biUnion_le s (badScalars k)
    _ ≤ ∑ x ∈ s, 1 := Finset.sum_le_sum fun x _ =>
      (Set.ncard_le_one (badScalars_subsingleton k x).finite).mpr
        (badScalars_subsingleton k x)
    _ = s.card := by simp
    _ = S.ncard := (Set.ncard_eq_toFinset_card S hS).symm

/-- Two distinct members of the pencil `X₁ - aX₀` are the rows of an invertible matrix. -/
theorem exists_matrix_twistedCoord_eq (a b : k) (hab : a ≠ b) :
    ∃ M : Matrix.GeneralLinearGroup (Fin 2) k,
      twistedCoord k M 0 = X 1 - C a * X 0 ∧
      twistedCoord k M 1 = X 1 - C b * X 0 := by
  let A : Matrix (Fin 2) (Fin 2) k := !![-a, 1; -b, 1]
  have hdet : Matrix.det A ≠ 0 := by
    rw [show Matrix.det A = b - a by
      simp [A, Matrix.det_fin_two_of, sub_eq_add_neg, add_comm]]
    exact sub_ne_zero.mpr (Ne.symm hab)
  let M : Matrix.GeneralLinearGroup (Fin 2) k :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet
  refine ⟨M, ?_, ?_⟩
  · simp [twistedCoord, MvPolynomial.matrixLinearForm, M, A, Fin.sum_univ_two,
      MvPolynomial.smul_eq_C_mul, sub_eq_add_neg, add_comm]
  · simp [twistedCoord, MvPolynomial.matrixLinearForm, M, A, Fin.sum_univ_two,
      MvPolynomial.smul_eq_C_mul, sub_eq_add_neg, add_comm]

/-- Over a finite field with at least two more elements than `S`, one coordinate twist puts
the finite subset `S` inside the intersection of the two twisted standard charts. -/
theorem exists_matrix_finite_subset_chartInter_of_ncard_add_two_le [Fintype k]
    (S : Set (P1 k)) (hS : S.Finite) (hcard : S.ncard + 2 ≤ Fintype.card k) :
    ∃ M : Matrix.GeneralLinearGroup (Fin 2) k,
      S ⊆ ((autOfMatrix k M ⁻¹ᵁ chartOpen k 0 : (P1 k).Opens) : Set (P1 k)) ∩
        ((autOfMatrix k M ⁻¹ᵁ chartOpen k 1 : (P1 k).Opens) : Set (P1 k)) := by
  classical
  let B : Set k := ⋃ x ∈ S, badScalars k x
  have hB : B.Finite := by
    dsimp [B]
    exact hS.biUnion fun x _ => (badScalars_subsingleton k x).finite
  have hBncard : B.ncard ≤ S.ncard := by
    dsimp [B]
    exact badScalars_biUnion_ncard_le k S hS
  let s : Finset k := hB.toFinset
  have hs : 1 < sᶜ.card := by
    rw [Finset.card_compl]
    have hscard : s.card = B.ncard := (Set.ncard_eq_toFinset_card B hB).symm
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hs
  have haB : a ∉ B := by simpa [s] using ha
  have hbB : b ∉ B := by simpa [s] using hb
  obtain ⟨M, hM0, hM1⟩ := exists_matrix_twistedCoord_eq k a b hab
  refine ⟨M, fun x hx => ?_⟩
  constructor
  · rw [autOfMatrix_preimage_chartOpen]
    change twistedCoord k M 0 ∉ x.asHomogeneousIdeal
    rw [hM0]
    intro hbad
    apply haB
    exact Set.mem_iUnion_of_mem x (Set.mem_iUnion_of_mem hx hbad)
  · rw [autOfMatrix_preimage_chartOpen]
    change twistedCoord k M 1 ∉ x.asHomogeneousIdeal
    rw [hM1]
    intro hbad
    apply hbB
    exact Set.mem_iUnion_of_mem x (Set.mem_iUnion_of_mem hx hbad)

/-- Over an infinite field, one coordinate twist puts any finite subset of `P¹` inside the
intersection of the two twisted standard charts. -/
theorem exists_matrix_finite_subset_chartInter [Infinite k]
    (S : Set (P1 k)) (hS : S.Finite) :
    ∃ M : Matrix.GeneralLinearGroup (Fin 2) k,
      S ⊆ ((autOfMatrix k M ⁻¹ᵁ chartOpen k 0 : (P1 k).Opens) : Set (P1 k)) ∩
        ((autOfMatrix k M ⁻¹ᵁ chartOpen k 1 : (P1 k).Opens) : Set (P1 k)) := by
  let B : Set k := ⋃ x ∈ S, badScalars k x
  have hB : B.Finite := by
    dsimp [B]
    exact hS.biUnion fun x _ => (badScalars_subsingleton k x).finite
  obtain ⟨a, ha⟩ := hB.exists_notMem
  have hBa : (B ∪ {a}).Finite := hB.union (Set.finite_singleton a)
  obtain ⟨b, hb⟩ := hBa.exists_notMem
  have hbB : b ∉ B := fun h => hb (Set.mem_union_left _ h)
  have hab : a ≠ b := by
    intro hab
    apply hb
    exact Set.mem_union_right B (by simp [hab])
  obtain ⟨M, hM0, hM1⟩ := exists_matrix_twistedCoord_eq k a b hab
  refine ⟨M, fun x hx => ?_⟩
  constructor
  · rw [autOfMatrix_preimage_chartOpen]
    change twistedCoord k M 0 ∉ x.asHomogeneousIdeal
    rw [hM0]
    intro hbad
    apply ha
    exact Set.mem_iUnion_of_mem x (Set.mem_iUnion_of_mem hx hbad)
  · rw [autOfMatrix_preimage_chartOpen]
    change twistedCoord k M 1 ∉ x.asHomogeneousIdeal
    rw [hM1]
    intro hbad
    apply hbB
    exact Set.mem_iUnion_of_mem x (Set.mem_iUnion_of_mem hx hbad)

end P1

end AlgebraicGeometry
