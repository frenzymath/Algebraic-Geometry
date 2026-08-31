/-
Copyright (c) 2026 The StacksPart03Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart03Lib Contributors
-/

import StacksPart03Lib.PeriodicLength

/-!
# Morphisms and componentwise short exact sequences of periodic complexes

The Chow chapter treats two-periodic complexes as an abelian category.  This
file records the componentwise API needed for that viewpoint.  The final
additivity theorem is stated for complexes whose *ambient* modules have finite
length; this is the finite-length case used in the periodic-length arguments.
-/

namespace StacksPart03

namespace TwoPeriodicComplex

variable {R : Type*} [Semiring R]
  {M₁ N₁ M₂ N₂ M₃ N₃ : Type*}
  [AddCommMonoid M₁] [AddCommMonoid N₁]
  [AddCommMonoid M₂] [AddCommMonoid N₂]
  [AddCommMonoid M₃] [AddCommMonoid N₃]
  [Module R M₁] [Module R N₁]
  [Module R M₂] [Module R N₂]
  [Module R M₃] [Module R N₃]

/-! ## Componentwise morphisms -/

/-- A morphism of two-periodic complexes, given by its two components. -/
structure Hom (C : TwoPeriodicComplex R M₁ N₁)
    (D : TwoPeriodicComplex R M₂ N₂) where
  f₀ : M₁ →ₗ[R] M₂
  f₁ : N₁ →ₗ[R] N₂
  comm₀ : D.d₀.comp f₀ = f₁.comp C.d₀
  comm₁ : D.d₁.comp f₁ = f₀.comp C.d₁

namespace Hom

@[ext]
theorem ext {C : TwoPeriodicComplex R M₁ N₁}
    {D : TwoPeriodicComplex R M₂ N₂} {f g : C.Hom D}
    (h₀ : f.f₀ = g.f₀) (h₁ : f.f₁ = g.f₁) : f = g := by
  cases f
  cases g
  simp_all

/-- The identity morphism of a two-periodic complex. -/
def id (C : TwoPeriodicComplex R M₁ N₁) : C.Hom C where
  f₀ := LinearMap.id
  f₁ := LinearMap.id
  comm₀ := by simp
  comm₁ := by simp

/-- Composition of componentwise morphisms. -/
def comp {C : TwoPeriodicComplex R M₁ N₁}
    {D : TwoPeriodicComplex R M₂ N₂}
    {E : TwoPeriodicComplex R M₃ N₃}
    (g : D.Hom E) (f : C.Hom D) : C.Hom E where
  f₀ := g.f₀.comp f.f₀
  f₁ := g.f₁.comp f.f₁
  comm₀ := by
    calc
      E.d₀.comp (g.f₀.comp f.f₀) = (E.d₀.comp g.f₀).comp f.f₀ :=
        (LinearMap.comp_assoc f.f₀ g.f₀ E.d₀).symm
      _ = (g.f₁.comp D.d₀).comp f.f₀ := by rw [g.comm₀]
      _ = g.f₁.comp (D.d₀.comp f.f₀) := LinearMap.comp_assoc f.f₀ D.d₀ g.f₁
      _ = g.f₁.comp (f.f₁.comp C.d₀) := by rw [f.comm₀]
      _ = (g.f₁.comp f.f₁).comp C.d₀ :=
        (LinearMap.comp_assoc C.d₀ f.f₁ g.f₁).symm
  comm₁ := by
    calc
      E.d₁.comp (g.f₁.comp f.f₁) = (E.d₁.comp g.f₁).comp f.f₁ :=
        (LinearMap.comp_assoc f.f₁ g.f₁ E.d₁).symm
      _ = (g.f₀.comp D.d₁).comp f.f₁ := by rw [g.comm₁]
      _ = g.f₀.comp (D.d₁.comp f.f₁) := LinearMap.comp_assoc f.f₁ D.d₁ g.f₀
      _ = g.f₀.comp (f.f₀.comp C.d₁) := by rw [f.comm₁]
      _ = (g.f₀.comp f.f₀).comp C.d₁ :=
        (LinearMap.comp_assoc C.d₁ f.f₀ g.f₀).symm

@[simp]
theorem id_f₀ (C : TwoPeriodicComplex R M₁ N₁) : (Hom.id C).f₀ = LinearMap.id := rfl

@[simp]
theorem id_f₁ (C : TwoPeriodicComplex R M₁ N₁) : (Hom.id C).f₁ = LinearMap.id := rfl

@[simp]
theorem comp_f₀ {C : TwoPeriodicComplex R M₁ N₁}
    {D : TwoPeriodicComplex R M₂ N₂}
    {E : TwoPeriodicComplex R M₃ N₃}
    (g : D.Hom E) (f : C.Hom D) : (g.comp f).f₀ = g.f₀.comp f.f₀ := rfl

@[simp]
theorem comp_f₁ {C : TwoPeriodicComplex R M₁ N₁}
    {D : TwoPeriodicComplex R M₂ N₂}
    {E : TwoPeriodicComplex R M₃ N₃}
    (g : D.Hom E) (f : C.Hom D) : (g.comp f).f₁ = g.f₁.comp f.f₁ := rfl

end Hom

/-! ## Componentwise short exact sequences -/

/-- A componentwise short exact sequence of two-periodic complexes.

The two component sequences are required to be injective, surjective, and
exact.  The morphism fields ensure that the component maps commute with both
periodic differentials.
-/
structure ShortExact (A : TwoPeriodicComplex R M₁ N₁)
    (B : TwoPeriodicComplex R M₂ N₂)
    (C : TwoPeriodicComplex R M₃ N₃) where
  i : A.Hom B
  p : B.Hom C
  injective₀ : Function.Injective i.f₀
  surjective₀ : Function.Surjective p.f₀
  exact₀ : Function.Exact i.f₀ p.f₀
  injective₁ : Function.Injective i.f₁
  surjective₁ : Function.Surjective p.f₁
  exact₁ : Function.Exact i.f₁ p.f₁

namespace ShortExact

variable {A : TwoPeriodicComplex R M₁ N₁}
  {B : TwoPeriodicComplex R M₂ N₂}
  {C : TwoPeriodicComplex R M₃ N₃}

@[simp]
theorem comp_zero₀ (h : A.ShortExact B C) : h.p.f₀.comp h.i.f₀ = 0 := by
  rw [LinearMap.ext_iff]
  intro x
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, Function.comp_apply, Pi.zero_apply] using
    congrFun h.exact₀.comp_eq_zero x

@[simp]
theorem comp_zero₁ (h : A.ShortExact B C) : h.p.f₁.comp h.i.f₁ = 0 := by
  rw [LinearMap.ext_iff]
  intro x
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, Function.comp_apply, Pi.zero_apply] using
    congrFun h.exact₁.comp_eq_zero x

end ShortExact

/-! ## Finite ambient length and multiplicity -/

section FiniteLength

variable {R : Type*} [Ring R]
  {M₁ N₁ M₂ N₂ M₃ N₃ : Type*}
  [AddCommGroup M₁] [AddCommGroup N₁]
  [AddCommGroup M₂] [AddCommGroup N₂]
  [AddCommGroup M₃] [AddCommGroup N₃]
  [Module R M₁] [Module R N₁]
  [Module R M₂] [Module R N₂]
  [Module R M₃] [Module R N₃]

/-- Both ambient modules of a periodic complex have finite length. -/
abbrev HasFiniteAmbientLength (_C : TwoPeriodicComplex R M₁ N₁) : Prop :=
  IsFiniteLength R M₁ ∧ IsFiniteLength R N₁

theorem HasFiniteAmbientLength.to_cohomology
    (C : TwoPeriodicComplex R M₁ N₁) (hC : C.HasFiniteAmbientLength) :
    C.HasFiniteLength :=
  C.hasFiniteLength_of_finite_ambient hC.1 hC.2

theorem ShortExact.hasFiniteAmbientLength_middle
    {A : TwoPeriodicComplex R M₁ N₁}
    {B : TwoPeriodicComplex R M₂ N₂}
    {C : TwoPeriodicComplex R M₃ N₃}
    (h : A.ShortExact B C)
    (hA : A.HasFiniteAmbientLength) (hC : C.HasFiniteAmbientLength) :
    B.HasFiniteAmbientLength := by
  have hA_noeth : IsNoetherian R M₁ :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA.1).1
  have hA_art : IsArtinian R M₁ :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA.1).2
  have hC_noeth : IsNoetherian R M₃ :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hC.1).1
  have hC_art : IsArtinian R M₃ :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hC.1).2
  have hB_noeth : IsNoetherian R M₂ := by
    letI : IsNoetherian R M₁ := hA_noeth
    letI : IsNoetherian R M₃ := hC_noeth
    exact isNoetherian_of_range_eq_ker h.i.f₀ h.p.f₀
      (LinearMap.exact_iff.mp h.exact₀).symm
  have hB_art : IsArtinian R M₂ := by
    letI : IsArtinian R M₁ := hA_art
    letI : IsArtinian R M₃ := hC_art
    exact isArtinian_of_range_eq_ker h.i.f₀ h.p.f₀
      (LinearMap.exact_iff.mp h.exact₀).symm
  have hA_noeth' : IsNoetherian R N₁ :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA.2).1
  have hA_art' : IsArtinian R N₁ :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA.2).2
  have hC_noeth' : IsNoetherian R N₃ :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hC.2).1
  have hC_art' : IsArtinian R N₃ :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hC.2).2
  have hB_noeth' : IsNoetherian R N₂ := by
    letI : IsNoetherian R N₁ := hA_noeth'
    letI : IsNoetherian R N₃ := hC_noeth'
    exact isNoetherian_of_range_eq_ker h.i.f₁ h.p.f₁
      (LinearMap.exact_iff.mp h.exact₁).symm
  have hB_art' : IsArtinian R N₂ := by
    letI : IsArtinian R N₁ := hA_art'
    letI : IsArtinian R N₃ := hC_art'
    exact isArtinian_of_range_eq_ker h.i.f₁ h.p.f₁
      (LinearMap.exact_iff.mp h.exact₁).symm
  exact ⟨isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨hB_noeth, hB_art⟩,
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨hB_noeth', hB_art'⟩⟩

theorem ShortExact.multiplicity_eq_add
    {A : TwoPeriodicComplex R M₁ N₁}
    {B : TwoPeriodicComplex R M₂ N₂}
    {C : TwoPeriodicComplex R M₃ N₃}
    (h : A.ShortExact B C)
    (hA : A.HasFiniteAmbientLength)
    (hC : C.HasFiniteAmbientLength) :
    B.multiplicity (HasFiniteAmbientLength.to_cohomology B
      (h.hasFiniteAmbientLength_middle hA hC)) =
      A.multiplicity (HasFiniteAmbientLength.to_cohomology A hA) +
        C.multiplicity (HasFiniteAmbientLength.to_cohomology C hC) := by
  let hB : B.HasFiniteAmbientLength := h.hasFiniteAmbientLength_middle hA hC
  let hAh : A.HasFiniteLength := hA.to_cohomology
  let hBh : B.HasFiniteLength := hB.to_cohomology
  let hCh : C.HasFiniteLength := hC.to_cohomology
  have hM : finiteLengthInt R M₂ hB.1 =
      finiteLengthInt R M₁ hA.1 + finiteLengthInt R M₃ hC.1 :=
    finiteLengthInt_eq_add_of_exact h.i.f₀ h.p.f₀
      h.injective₀ h.surjective₀ h.exact₀ hA.1 hB.1 hC.1
  have hN : finiteLengthInt R N₂ hB.2 =
      finiteLengthInt R N₁ hA.2 + finiteLengthInt R N₃ hC.2 :=
    finiteLengthInt_eq_add_of_exact h.i.f₁ h.p.f₁
      h.injective₁ h.surjective₁ h.exact₁ hA.2 hB.2 hC.2
  rw [B.multiplicity_eq_ambient_length_sub hB.1 hB.2,
    A.multiplicity_eq_ambient_length_sub hA.1 hA.2,
    C.multiplicity_eq_ambient_length_sub hC.1 hC.2]
  linarith [hM, hN]

end FiniteLength

end TwoPeriodicComplex

end StacksPart03
