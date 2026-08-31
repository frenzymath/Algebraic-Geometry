/-
Copyright (c) 2026 The StacksPart07Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart07Lib Contributors
-/

import StacksPart07Lib.RepresentableMorphisms

/-!
# Products of representable transformations

The product lemma in the first algebraic-stacks chapter (Stacks, Tag `02ZU`)
is formal: a product transformation is a composite of two base changes of the
original transformations.  This file records that argument in the presheaf
model used by the Part 07 representability interface.
-/

namespace StacksPart07Lib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe v u v' u'

/-! The pullback of a map along the second product projection. -/

lemma isPullback_prod_snd_with_id {C : Type u} [Category.{v} C]
    {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct X A]
    [HasBinaryProduct X B] :
    IsPullback (prod.snd : X ⨯ A ⟶ A) (prod.map (𝟙 X) f) f
      (prod.snd : X ⨯ B ⟶ B) := by
  let c : PullbackCone f (prod.snd : X ⨯ B ⟶ B) :=
    PullbackCone.mk (prod.snd : X ⨯ A ⟶ A) (prod.map (𝟙 X) f)
      (by rw [prod.map_snd])
  apply IsPullback.of_isLimit (c := c)
  exact PullbackCone.IsLimit.mk (by
      rw [prod.map_snd])
    (fun s => prod.lift (s.snd ≫ prod.fst) s.fst)
    (fun s => by
      rw [prod.lift_snd])
    (fun s => by
      apply prod.hom_ext
      · rw [Category.assoc, prod.map_fst, prod.lift_fst_assoc, Category.comp_id]
      · rw [Category.assoc, prod.map_snd, prod.lift_snd_assoc]
        exact s.condition)
    (fun s m h₁ h₂ => by
      apply prod.hom_ext
      · rw [← h₂, Category.assoc, prod.map_fst, prod.lift_fst, Category.comp_id]
      · rw [← h₁, prod.lift_snd])

/-! ### Products of pullback squares -/

/-- The product of two pullback squares is a pullback square.

The universal property is checked componentwise in the two factor
categories. -/
lemma isPullback_prod_category
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {P X Y Z : C} {P' X' Y' Z' : D}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f' g') :
    IsPullback (Prod.mkHom fst fst') (Prod.mkHom snd snd')
      (Prod.mkHom f f') (Prod.mkHom g g') := by
  let c : PullbackCone (Prod.mkHom f f') (Prod.mkHom g g') :=
    PullbackCone.mk (Prod.mkHom fst fst') (Prod.mkHom snd snd')
      (by
        apply Prod.hom_ext
        · exact h.w
        · exact h'.w)
  apply IsPullback.of_isLimit (c := c)
  exact PullbackCone.IsLimit.mk c.condition
    (fun s => Prod.mkHom
      (h.lift s.fst.1 s.snd.1 (by
        exact congrArg Prod.fst s.condition))
      (h'.lift s.fst.2 s.snd.2 (by
        exact congrArg Prod.snd s.condition)))
    (fun s => by
      apply Prod.hom_ext
      · change
          h.lift s.fst.1 s.snd.1 (congrArg Prod.fst s.condition) ≫ fst = s.fst.1
        exact h.lift_fst _ _ _
      · change
          h'.lift s.fst.2 s.snd.2 (congrArg Prod.snd s.condition) ≫ fst' = s.fst.2
        exact h'.lift_fst _ _ _)
    (fun s => by
      apply Prod.hom_ext
      · change
          h.lift s.fst.1 s.snd.1 (congrArg Prod.fst s.condition) ≫ snd = s.snd.1
        exact h.lift_snd _ _ _
      · change
          h'.lift s.fst.2 s.snd.2 (congrArg Prod.snd s.condition) ≫ snd' = s.snd.2
        exact h'.lift_snd _ _ _)
    (fun s m hm₁ hm₂ => by
      apply Prod.hom_ext
      · apply h.hom_ext
        · have hm₁' : m.1 ≫ fst = s.fst.1 := by
            simpa [c] using congrArg Prod.fst hm₁
          have hl₁' :
              (h.lift s.fst.1 s.snd.1 (congrArg Prod.fst s.condition)) ≫ fst = s.fst.1 := by
            exact h.lift_fst _ _ _
          exact hm₁'.trans hl₁'.symm
        · have hm₂' : m.1 ≫ snd = s.snd.1 := by
            simpa [c] using congrArg Prod.fst hm₂
          have hl₂' :
              (h.lift s.fst.1 s.snd.1 (congrArg Prod.fst s.condition)) ≫ snd = s.snd.1 := by
            exact h.lift_snd _ _ _
          exact hm₂'.trans hl₂'.symm
      · apply h'.hom_ext
        · have hm₁' : m.2 ≫ fst' = s.fst.2 := by
            simpa [c] using congrArg Prod.snd hm₁
          have hl₁' :
              (h'.lift s.fst.2 s.snd.2 (congrArg Prod.snd s.condition)) ≫ fst' = s.fst.2 := by
            exact h'.lift_fst _ _ _
          exact hm₁'.trans hl₁'.symm
        · have hm₂' : m.2 ≫ snd' = s.snd.2 := by
            simpa [c] using congrArg Prod.snd hm₂
          have hl₂' :
              (h'.lift s.fst.2 s.snd.2 (congrArg Prod.snd s.condition)) ≫ snd' = s.snd.2 := by
            exact h'.lift_snd _ _ _
          exact hm₂'.trans hl₂'.symm)

/-!
### Product representability

The products here are the categorical products in the presheaf category. -/

theorem representableTransformation_prod {C : Type u} [Category.{v} C]
    {F₁ G₁ F₂ G₂ : Presheaf C}
    (f₁ : F₁ ⟶ G₁) (f₂ : F₂ ⟶ G₂)
    (h₁ : RepresentableTransformation C f₁)
    (h₂ : RepresentableTransformation C f₂) :
    RepresentableTransformation C (prod.map f₁ f₂) := by
  have hleft : RepresentableTransformation C (prod.map f₁ (𝟙 F₂)) :=
    representableTransformation_baseChange
      (IsPullback.of_prod_fst_with_id f₁ F₂) h₁
  have hright : RepresentableTransformation C (prod.map (𝟙 G₁) f₂) :=
    representableTransformation_baseChange
      (isPullback_prod_snd_with_id f₂ G₁) h₂
  have hcomp : RepresentableTransformation C
      (prod.map f₁ (𝟙 F₂) ≫ prod.map (𝟙 G₁) f₂) :=
    representableTransformation_comp _ _ hleft hright
  rw [prod.map_map] at hcomp
  simpa using hcomp

end StacksPart07Lib
