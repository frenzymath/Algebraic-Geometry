/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2ModuleKSheaf
import Mathlib

/-!
# Module-valued sheaf cohomology

The χ-ledger uses `Ext` in the category of sheaves of modules.  This file
provides the cohomology carrier and the degree-zero identification with global
sections, together with the functoriality needed by later divisor-sheaf units.
-/

set_option autoImplicit false

universe u v w

open CategoryTheory Limits Opposite TopologicalSpace

namespace CategoryTheory

namespace Abelian.Ext

variable {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]

/-- Vanishing criterion for `Ext¹`: if `A` admits a monomorphism into an injective
object and every map from `L` to its cokernel lifts, then `Ext¹(L, A)` is
subsingleton. -/
theorem subsingleton_one_of_injective_of_surjective {A I : C} (ι : A ⟶ I) [Mono ι]
    [Injective I] (L : C)
    (hsurj : ∀ φ : L ⟶ cokernel ι, ∃ ψ : L ⟶ I, ψ ≫ cokernel.π ι = φ) :
    Subsingleton (Abelian.Ext L A 1) := by
  suffices h : ∀ z : Abelian.Ext L A 1, z = 0 from ⟨fun x y ↦ (h x).trans (h y).symm⟩
  intro z
  have hS : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι) }
  have h1 : z.comp (mk₀ ι) (add_zero 1) = 0 := eq_zero_of_injective _
  obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ L hS z h1 (zero_add 1)
  obtain ⟨ψ, hψ⟩ := hsurj (homEquiv₀ x₃)
  have hx₃' : mk₀ (ψ ≫ cokernel.π ι) = x₃ := by
    rw [hψ, mk₀_homEquiv₀_apply]
  calc
    z = x₃.comp hS.extClass (zero_add 1) := hx₃.symm
    _ = ((mk₀ ψ).comp (mk₀ (cokernel.π ι)) (zero_add 0)).comp hS.extClass
        (zero_add 1) := by rw [mk₀_comp_mk₀, hx₃']
    _ = (mk₀ ψ).comp ((mk₀ (cokernel.π ι)).comp hS.extClass (zero_add 1))
        (zero_add 1) := comp_assoc _ _ _ rfl rfl rfl
    _ = 0 := by rw [hS.comp_extClass]; simp

end Abelian.Ext

namespace Sheaf

variable {C : Type u} [SmallCategory C]

noncomputable def constModuleSheaf (J : GrothendieckTopology C) (R : Type u)
    [CommRing R] [HasSheafify J (ModuleCat.{u} R)] :
    Sheaf J (ModuleCat.{u} R) :=
  (constantSheaf J (ModuleCat.{u} R)).obj (ModuleCat.of R R)

noncomputable abbrev HModule (J : GrothendieckTopology C) (R : Type u) [CommRing R]
    [HasSheafify J (ModuleCat.{u} R)]
    (F : Sheaf J (ModuleCat.{u} R)) (n : ℕ) : Type u :=
  Abelian.Ext (constModuleSheaf J R) F n

namespace HModule

variable {J : GrothendieckTopology C} {R : Type u} [CommRing R]
  [HasSheafify J (ModuleCat.{u} R)]
variable {F G G' : Sheaf J (ModuleCat.{u} R)}

noncomputable def map (f : F ⟶ G) (n : ℕ) : HModule J R F n →ₗ[R] HModule J R G n :=
  (Abelian.Ext.mk₀ f).postcompOfLinear R (constModuleSheaf J R) (add_zero n)

lemma map_apply (f : F ⟶ G) {n : ℕ} (x : HModule J R F n) :
    map f n x = x.comp (Abelian.Ext.mk₀ f) (add_zero n) := rfl

@[simp] lemma map_id_apply {n : ℕ} (x : HModule J R F n) : map (𝟙 F) n x = x := by
  simp [map_apply]

lemma map_comp_apply (f : F ⟶ G) (g : G ⟶ G') {n : ℕ} (x : HModule J R F n) :
    map (f ≫ g) n x = map g n (map f n x) := by
  simp [map_apply]

instance [Injective F] (n : ℕ) : Subsingleton (HModule J R F (n + 1)) :=
  subsingleton_of_forall_eq 0 fun x ↦ x.eq_zero_of_injective

end HModule

section DegreeZero

variable {J : GrothendieckTopology C} {R : Type u} [CommRing R]
  [HasSheafify J (ModuleCat.{u} R)] {T : C} (hT : IsTerminal T)

noncomputable def constantSheafAdjHomLinearEquiv (M : ModuleCat.{u} R)
    (F : Sheaf J (ModuleCat.{u} R)) :
    ((constantSheaf J (ModuleCat.{u} R)).obj M ⟶ F) ≃ₗ[R]
      (M ⟶ F.obj.obj (op T)) := by
  refine {
    toFun := (constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv M F
    invFun := ((constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv M F).symm
    left_inv := ((constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv M F).left_inv
    right_inv := ((constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv M F).right_inv
    map_add' := fun f g ↦ by simp only [Adjunction.homEquiv_apply]; ext v; rfl
    map_smul' := fun r f ↦ by simp only [Adjunction.homEquiv_apply]; ext v; rfl }

omit [HasSheafify J (ModuleCat.{u} R)] in
lemma constantSheafAdjHomLinearEquiv_apply (M : ModuleCat.{u} R)
    {F : Sheaf J (ModuleCat.{u} R)} (φ : (constantSheaf J (ModuleCat.{u} R)).obj M ⟶ F) :
    constantSheafAdjHomLinearEquiv hT M F φ =
      (constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv M F φ := rfl

omit [HasSheafify J (ModuleCat.{u} R)] in
lemma constantSheafAdjHomLinearEquiv_naturality (M : ModuleCat.{u} R)
    {F G : Sheaf J (ModuleCat.{u} R)}
    (φ : (constantSheaf J (ModuleCat.{u} R)).obj M ⟶ F) (f : F ⟶ G) :
    constantSheafAdjHomLinearEquiv hT M G (φ ≫ f) =
      constantSheafAdjHomLinearEquiv hT M F φ ≫ f.hom.app (op T) := by
  simp only [constantSheafAdjHomLinearEquiv_apply]
  exact (constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv_naturality_right φ f

noncomputable def constModuleSheafHomEquiv (F : Sheaf J (ModuleCat.{u} R)) :
    (constModuleSheaf J R ⟶ F) ≃ₗ[R] F.obj.obj (op T) :=
  (constantSheafAdjHomLinearEquiv hT (ModuleCat.of R R) F).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R _))

lemma constModuleSheafHomEquiv_naturality {F G : Sheaf J (ModuleCat.{u} R)}
    (φ : constModuleSheaf J R ⟶ F) (f : F ⟶ G) :
    constModuleSheafHomEquiv hT G (φ ≫ f) =
      f.hom.app (op T) (constModuleSheafHomEquiv hT F φ) := by
  simp only [constModuleSheafHomEquiv]
  rfl

noncomputable def HModule.linearEquiv₀ (F : Sheaf J (ModuleCat.{u} R)) :
    HModule J R F 0 ≃ₗ[R] F.obj.obj (op T) :=
  (Abelian.Ext.linearEquiv₀ (R := R)).trans (constModuleSheafHomEquiv hT F)

lemma HModule.linearEquiv₀_map {F G : Sheaf J (ModuleCat.{u} R)}
    (f : F ⟶ G) (x : HModule J R F 0) :
    Abelian.Ext.linearEquiv₀ (R := R) (HModule.map f 0 x) =
      Abelian.Ext.linearEquiv₀ (R := R) x ≫ f := by
  apply (Abelian.Ext.mk₀_bijective (constModuleSheaf J R) G).injective
  simp only [Abelian.Ext.mk₀_linearEquiv₀_apply, ← Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_linearEquiv₀_apply]
  exact HModule.map_apply f x

theorem HModule.linearEquiv₀_naturality {F G : Sheaf J (ModuleCat.{u} R)}
    (f : F ⟶ G) (x : HModule J R F 0) :
    f.hom.app (op T) (HModule.linearEquiv₀ hT F x) =
      HModule.linearEquiv₀ hT G (HModule.map f 0 x) := by
  simp only [HModule.linearEquiv₀, LinearEquiv.trans_apply, HModule.linearEquiv₀_map f x]
  exact (constModuleSheafHomEquiv_naturality hT (Abelian.Ext.linearEquiv₀ x) f).symm

theorem HModule.linearEquiv₀_symm_naturality {F G : Sheaf J (ModuleCat.{u} R)}
    (f : F ⟶ G) (s : F.obj.obj (op T)) :
    HModule.map f 0 ((HModule.linearEquiv₀ hT F).symm s) =
      (HModule.linearEquiv₀ hT G).symm (f.hom.app (op T) s) := by
  apply (HModule.linearEquiv₀ hT G).injective
  simp [← HModule.linearEquiv₀_naturality]

end DegreeZero

end Sheaf
end CategoryTheory
