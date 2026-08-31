/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Diagonal normalization of invertible descent cocycles

An invertible overlap morphism satisfying the triple cocycle is automatically
the identity after restriction to the diagonal.
-/

set_option autoImplicit false

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Limits LocallyDiscreteOpToCat

variable {C₀ : Type u} [Category.{v} C₀]
  {F₀ : Pseudofunctor (LocallyDiscrete C₀ᵒᵖ) Cat.{v', u'}}

/-- Pulling an isomorphism along a pseudofunctor map produces an isomorphism. -/
noncomputable instance LocallyDiscreteOpToCat.pullHom_isIso
    {X₁ X₂ : C₀} {M₁ : F₀.obj (.mk (op X₁))} {M₂ : F₀.obj (.mk (op X₂))}
    {Y : C₀} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F₀.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F₀.map f₂.op.toLoc).toFunctor.obj M₂)
    [IsIso φ] {Y' : C₀} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    IsIso (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) := by
  let a := (F₀.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₁])).hom.toNatTrans.app M₁
  let b := (F₀.map g.op.toLoc).toFunctor.map φ
  let c := (F₀.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₂])).inv.toNatTrans.app M₂
  have ha : IsIso a := by dsimp only [a]; infer_instance
  have hb : IsIso b := by dsimp only [b]; infer_instance
  have hc : IsIso c := by dsimp only [c]; infer_instance
  have hbc : IsIso (b ≫ c) := @IsIso.comp_isIso _ _ _ _ _ b c hb hc
  have habc : IsIso (a ≫ b ≫ c) :=
    @IsIso.comp_isIso _ _ _ _ _ a (b ≫ c) ha hbc
  have h : pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = a ≫ b ≫ c := by rfl
  exact h ▸ habc

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

open DescentData'

/-- An invertible overlap morphism satisfying the triple cocycle restricts to
the identity on every diagonal. -/
lemma pullHom'_hom_self_of_comp
    {obj : ∀ i, F.obj (.mk (op (X i)))}
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (homIso : ∀ i j, IsIso (hom i j))
    (hom_comp : ∀ i₁ i₂ i₃,
      pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
      pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃) :
    ∀ i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _ := by
  intro i
  let d := pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i))
  have hd : d ≫ d = d := by
    dsimp only [d]
    exact comp_pullHom'' hom hom_comp (f i)
      (𝟙 (X i)) (𝟙 (X i)) (𝟙 (X i))
      (by simp) (by simp) (by simp)
  letI := homIso i i
  haveI : IsIso d := by
    dsimp only [d, pullHom']
    infer_instance
  apply (cancel_mono d).1
  rw [hd]
  simp

/-- An invertible chosen-pullback cocycle before diagonal normalization. -/
structure DescentCocycle' where
  obj : ∀ i, F.obj (.mk (op (X i)))
  hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)
  homIso : ∀ i j, IsIso (hom i j)
  pullHom'_hom_comp : ∀ i₁ i₂ i₃,
    DescentData'.pullHom' hom (sq₃ i₁ i₂ i₃).p
        (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
      DescentData'.pullHom' hom (sq₃ i₁ i₂ i₃).p
        (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      DescentData'.pullHom' hom (sq₃ i₁ i₂ i₃).p
        (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃

namespace DescentCocycle'

variable {F sq sq₃}

/-- Normalize the diagonal of an invertible cocycle and package it as descent
data. -/
noncomputable def toDescentData (D : F.DescentCocycle' sq sq₃) :
    F.DescentData' sq sq₃ :=
  { obj := D.obj
    hom := D.hom
    pullHom'_hom_self :=
      pullHom'_hom_self_of_comp F sq sq₃ D.hom D.homIso D.pullHom'_hom_comp
    pullHom'_hom_comp := D.pullHom'_hom_comp }

@[simp]
lemma toDescentData_obj (D : F.DescentCocycle' sq sq₃) (i : ι) :
    D.toDescentData.obj i = D.obj i := rfl

lemma toDescentData_hom_heq (D : F.DescentCocycle' sq sq₃) (i j : ι) :
    HEq (D.toDescentData.hom i j) (D.hom i j) := by
  rfl

@[simp]
lemma toDescentData_hom_transport (D : F.DescentCocycle' sq sq₃) (i j : ι) :
    eqToHom (congrArg
        (fun M => (F.map (sq i j).p₁.op.toLoc).toFunctor.obj M)
        (D.toDescentData_obj i)).symm ≫
      D.toDescentData.hom i j ≫
      eqToHom (congrArg
        (fun M => (F.map (sq i j).p₂.op.toLoc).toFunctor.obj M)
        (D.toDescentData_obj j)) =
      D.hom i j := by
  simp [toDescentData]

attribute [irreducible] toDescentData

end DescentCocycle'

end CategoryTheory.Pseudofunctor
