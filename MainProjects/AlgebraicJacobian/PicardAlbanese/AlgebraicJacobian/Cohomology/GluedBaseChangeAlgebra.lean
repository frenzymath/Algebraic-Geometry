/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# DAT-1 (1d-ii) — base-change-in-stages and localization transports (pure algebra)

The three module-algebra tools the on-the-nose base-change clauses of the m-chart glued
constructor fire (`informal/spec-dat-1.md`, stage (1d-ii)); no schemes appear.

* `IsBaseChange.tensorProduct_mk_one` — **base change in stages**: if the algebra map
  `A → A'` realizes `A'` as the base change of `A` along `R → R'`, then for every
  `A`-module `M` the map `m ↦ 1 ⊗ₜ m` realizes `A' ⊗[A] M` as the base change of `M`
  along `R → R'` (so `R' ⊗[R] M ≃ₗ[R'] A' ⊗[A] M`). Proved by the universal property
  (`IsBaseChange.of_lift_unique`): an `R`-linear map `φ : M → Q` into an `R'`-module
  extends through `a' ⊗ m ↦ (hA.lift (a ↦ φ (a • m))) a'`, uniquely since
  `(algebraMap A A' a) ⊗ₜ m = 1 ⊗ₜ (a • m)`.
* `isLocalizedModule_restrictScalars_powers` — an `A'`-linear localization at the
  powers of `algebraMap A A' a` restricts to an `A`-linear localization at the powers
  of `a`.
* `IsLocalizedModule.bijective_of_comp_eq` — a linear map intertwining two
  localizations of the same module at the same submonoid is bijective (uniqueness of
  localizations, in the form the span-locality argument consumes).
-/

set_option autoImplicit false

universe u

open TensorProduct

/-! ## Base change in stages -/

section Stage

variable {R R' A A' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable [CommRing A] [CommRing A'] [Algebra R A]
variable [Algebra R' A'] [Algebra A A'] [Algebra R A']
variable [IsScalarTower R R' A'] [IsScalarTower R A A']
variable {M : Type u} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]

/-- **Base change in stages**: if `A'` is the base change of `A` along `R → R'`
(through the algebra map `A → A'`), then for every `A`-module `M` the canonical map
`m ↦ 1 ⊗ₜ m` exhibits `A' ⊗[A] M` as the base change of `M` along `R → R'`. -/
theorem IsBaseChange.tensorProduct_mk_one
    (hA : IsBaseChange R' ((IsScalarTower.toAlgHom R A A').toLinearMap)) :
    IsBaseChange R' (((TensorProduct.mk A A' M) 1).restrictScalars R) := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ φ
  -- the lift on the first factor: `a' ↦ φ (a • m)` extended through `hA`
  let L : M → A' →ₗ[R'] Q := fun m => hA.lift
    { toFun := fun a => φ (a • m)
      map_add' := fun a b => by rw [add_smul, map_add]
      map_smul' := fun r a => by rw [RingHom.id_apply, smul_assoc, map_smul] }
  have hL : ∀ (m : M) (a : A), L m (algebraMap A A' a) = φ (a • m) := fun m a =>
    hA.lift_eq _ a
  -- additivity in `m`
  have hLadd : ∀ m m' : M, L (m + m') = L m + L m' := by
    intro m m'
    refine hA.algHom_ext _ _ fun a => ?_
    rw [LinearMap.add_apply]
    change L (m + m') (algebraMap A A' a) =
      L m (algebraMap A A' a) + L m' (algebraMap A A' a)
    rw [hL, hL, hL, smul_add, map_add]
  have hLzero : L 0 = 0 := by
    refine hA.algHom_ext _ _ fun a => ?_
    change L 0 (algebraMap A A' a) = (0 : A' →ₗ[R'] Q) (algebraMap A A' a)
    rw [hL, smul_zero, map_zero, LinearMap.zero_apply]
  -- `A`-balancedness in `m`
  have hLbal : ∀ (a₀ : A) (m : M),
      (L m).comp (LinearMap.mulLeft R' (algebraMap A A' a₀)) = L (a₀ • m) := by
    intro a₀ m
    refine hA.algHom_ext _ _ fun a => ?_
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    change L m (algebraMap A A' a₀ * algebraMap A A' a) = L (a₀ • m) (algebraMap A A' a)
    rw [← map_mul, hL, hL, mul_comm a₀ a, mul_smul]
  -- the balanced biadditive map and its lift to the tensor product
  let F : A' →+ M →+ Q :=
    { toFun := fun a' =>
        { toFun := fun m => L m a'
          map_zero' := by rw [hLzero, LinearMap.zero_apply]
          map_add' := fun m m' => by rw [hLadd, LinearMap.add_apply] }
      map_zero' := by
        ext m
        exact map_zero (L m)
      map_add' := fun a' a'' => by
        ext m
        exact map_add (L m) a' a'' }
  have hFbal : ∀ (a₀ : A) (a' : A') (m : M), F (a₀ • a') m = F a' (a₀ • m) := by
    intro a₀ a' m
    change L m (a₀ • a') = L (a₀ • m) a'
    rw [Algebra.smul_def, ← hLbal a₀ m, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  let ℓ₀ : A' ⊗[A] M →+ Q := TensorProduct.liftAddHom F hFbal
  have hℓ₀ : ∀ (a' : A') (m : M), ℓ₀ (a' ⊗ₜ m) = L m a' := fun a' m => rfl
  -- upgrade to `R'`-linearity
  let ℓ : A' ⊗[A] M →ₗ[R'] Q :=
    { toFun := ℓ₀
      map_add' := ℓ₀.map_add
      map_smul' := by
        intro r' x
        rw [RingHom.id_apply]
        induction x with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | tmul a' m =>
          rw [TensorProduct.smul_tmul', hℓ₀, hℓ₀, map_smul]
        | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add] }
  refine ⟨ℓ, ?_, ?_⟩
  · -- the triangle
    refine LinearMap.ext fun m => ?_
    change ℓ₀ ((1 : A') ⊗ₜ m) = φ m
    have h1 : (1 : A') = algebraMap A A' 1 := (map_one _).symm
    rw [hℓ₀, h1, hL, one_smul]
  · -- uniqueness
    rintro ℓ' hℓ'
    have htri : ∀ m : M, ℓ' ((1 : A') ⊗ₜ m) = φ m := fun m =>
      DFunLike.congr_fun hℓ' m
    refine LinearMap.ext fun x => ?_
    induction x with
    | zero => rw [map_zero, map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul a' m =>
      have hmk : ∀ m : M, ℓ ((1 : A') ⊗ₜ m) = φ m := fun m => by
        change ℓ₀ ((1 : A') ⊗ₜ m) = φ m
        have h1 : (1 : A') = algebraMap A A' 1 := (map_one _).symm
        rw [hℓ₀, h1, hL, one_smul]
      induction a' using hA.inductionOn with
      | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
      | tmul a =>
        have ha' : (IsScalarTower.toAlgHom R A A').toLinearMap a ⊗ₜ[A] m =
            (1 : A') ⊗ₜ[A] (a • m) := by
          change (algebraMap A A' a) ⊗ₜ[A] m = (1 : A') ⊗ₜ[A] (a • m)
          rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
        rw [ha', htri, hmk]
      | smul r' a'' ih =>
        rw [← TensorProduct.smul_tmul', map_smul, map_smul, ih]
      | add a'' a''' ih ih' =>
        rw [TensorProduct.add_tmul, map_add, map_add, ih, ih']

end Stage

/-! ## Localization at powers, restricted along an algebra map -/

section Powers

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
variable {P Q : Type u} [AddCommGroup P] [Module A' P] [AddCommGroup Q] [Module A' Q]
variable [Module A P] [Module A Q] [IsScalarTower A A' P] [IsScalarTower A A' Q]

/-- **Restriction of a powers-localization along an algebra map**: an `A'`-linear map
exhibiting `Q` as the localization of `P` at the powers of `algebraMap A A' a` also
exhibits it, `A`-linearly, as the localization at the powers of `a`. -/
theorem isLocalizedModule_restrictScalars_powers (a : A) (ℓ : P →ₗ[A'] Q)
    [IsLocalizedModule (Submonoid.powers (algebraMap A A' a)) ℓ] :
    IsLocalizedModule (Submonoid.powers a) (ℓ.restrictScalars A) := by
  constructor
  · rintro ⟨x, n, rfl⟩
    have hu := IsLocalizedModule.map_units (S := Submonoid.powers (algebraMap A A' a))
      ℓ ⟨(algebraMap A A' a) ^ n, n, rfl⟩
    rw [Module.End.isUnit_iff] at hu ⊢
    have hfun : ⇑(algebraMap A (Module.End A Q) (a ^ n)) =
        ⇑(algebraMap A' (Module.End A' Q) ((algebraMap A A' a) ^ n)) := by
      funext q
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← map_pow,
        algebraMap_smul]
    rw [hfun]
    exact hu
  · intro q
    obtain ⟨⟨p, s⟩, hs⟩ := IsLocalizedModule.surj
      (S := Submonoid.powers (algebraMap A A' a)) ℓ q
    obtain ⟨n, hn⟩ := s.2
    refine ⟨⟨p, ⟨a ^ n, n, rfl⟩⟩, ?_⟩
    change (a ^ n) • q = ℓ p
    have hn' : (algebraMap A A' a) ^ n = (s : A') := hn
    rw [← algebraMap_smul A' (a ^ n) q, map_pow, hn']
    exact hs
  · intro p p' hpp
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers (algebraMap A A' a)) (f := ℓ) hpp
    obtain ⟨n, hn⟩ := s.2
    refine ⟨⟨a ^ n, n, rfl⟩, ?_⟩
    change (a ^ n) • p = (a ^ n) • p'
    have hn' : (algebraMap A A' a) ^ n = (s : A') := hn
    rw [← algebraMap_smul A' (a ^ n) p, ← algebraMap_smul A' (a ^ n) p', map_pow, hn']
    exact hs

end Powers

/-! ## Uniqueness of localizations, in bijectivity form -/

section Unique

variable {R : Type u} [CommRing R] (S : Submonoid R)
variable {M P Q : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
variable [AddCommGroup Q] [Module R Q]

/-- **A map intertwining two localizations is bijective**: if `p : M → P` and
`q : M → Q` are both localizations at `S` and `T ∘ p = q`, then `T` is bijective —
the uniqueness of localizations, in the form consumed by the span-locality
bijectivity argument. -/
theorem IsLocalizedModule.bijective_of_comp_eq (p : M →ₗ[R] P) (q : M →ₗ[R] Q)
    [IsLocalizedModule S p] [IsLocalizedModule S q] (T : P →ₗ[R] Q)
    (h : T ∘ₗ p = q) : Function.Bijective T := by
  -- the inverse, by the universal property of `q`
  set T' : Q →ₗ[R] P := IsLocalizedModule.lift S q p (IsLocalizedModule.map_units p)
    with hT'
  have hT'q : T' ∘ₗ q = p := IsLocalizedModule.lift_comp S q p _
  have h₁ : (T' ∘ₗ T) ∘ₗ p = LinearMap.id (R := R) (M := P) ∘ₗ p := by
    rw [LinearMap.comp_assoc, h, hT'q, LinearMap.id_comp]
  have h₂ : (T ∘ₗ T') ∘ₗ q = LinearMap.id (R := R) (M := Q) ∘ₗ q := by
    rw [LinearMap.comp_assoc, hT'q, h, LinearMap.id_comp]
  have hleft : T' ∘ₗ T = LinearMap.id :=
    IsLocalizedModule.linearMap_ext S p p h₁
  have hright : T ∘ₗ T' = LinearMap.id :=
    IsLocalizedModule.linearMap_ext S q q h₂
  exact Function.bijective_iff_has_inverse.mpr
    ⟨T', fun x => DFunLike.congr_fun hleft x, fun x => DFunLike.congr_fun hright x⟩

end Unique
