/-
Copyright (c) 2026 The StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import StacksPart04Lib.Representability
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Products.Basic

/-!
# StacksPart04Lib.Products

Generic categorical product and pullback facts used by the limits and groupoid
chapters of the algebraic-spaces blueprint.
-/

namespace StacksPart04Lib

open CategoryTheory
open CategoryTheory.Limits

universe u v u' v'

section ProductPullbacks

variable {C : Type u} [Category.{v} C]

/-- Pulling a morphism back along the first projection is represented by a
product with the identity on the second factor. -/
lemma isPullback_prod_fst_with_id {A B : C} (f : A ⟶ B) (X : C)
    [HasBinaryProduct A X] [HasBinaryProduct B X] :
    IsPullback (prod.fst : A ⨯ X ⟶ A) (prod.map f (𝟙 X)) f
      (prod.fst : B ⨯ X ⟶ B) := by
  exact IsPullback.of_prod_fst_with_id f X

/-- Pulling a morphism back along the second projection is represented by a
product with the identity on the first factor. -/
lemma isPullback_prod_snd_with_id {A B : C} (f : A ⟶ B) (X : C)
    [HasBinaryProduct X A] [HasBinaryProduct X B] :
    IsPullback (prod.snd : X ⨯ A ⟶ A) (prod.map (𝟙 X) f) f
      (prod.snd : X ⨯ B ⟶ B) := by
  let c : PullbackCone f (prod.snd : X ⨯ B ⟶ B) :=
    PullbackCone.mk (prod.snd : X ⨯ A ⟶ A) (prod.map (𝟙 X) f)
      (by rw [prod.map_snd])
  apply IsPullback.of_isLimit (c := c)
  exact PullbackCone.IsLimit.mk (by
      rw [prod.map_snd])
    (fun s => prod.lift (s.snd ≫ prod.fst) s.fst)
    (fun s => by rw [prod.lift_snd])
    (fun s => by
      apply prod.hom_ext
      · rw [Category.assoc, prod.map_fst, prod.lift_fst_assoc, Category.comp_id]
      · rw [Category.assoc, prod.map_snd, prod.lift_snd_assoc]
        exact s.condition)
    (fun s m h₁ h₂ => by
      apply prod.hom_ext
      · rw [← h₂, Category.assoc, prod.map_fst, prod.lift_fst, Category.comp_id]
      · rw [← h₁, prod.lift_snd])

end ProductPullbacks

section ProductCategories

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/-- The product of two Cartesian squares is Cartesian.  The universal property
is checked componentwise in the two factor categories. -/
lemma isPullback_prod_category
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

end ProductCategories

section PresheafProducts

variable {C : Type u} [Category.{v} C]

/-- A product of representable transformations is representable.  It is the
composition of the two canonical base changes along product projections. -/
theorem representableTransformation_prod
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

end PresheafProducts

section GroupoidProducts

variable {C : Type u} {D : Type u'}

/-- In a product of groupoids, inversion is computed componentwise. -/
@[simp]
theorem groupoid_prod_inv
    [Groupoid.{v} C] [Groupoid.{v'} D]
    {X Y : C} {X' Y' : D} (f : (X, X') ⟶ (Y, Y')) :
    Groupoid.inv f = Prod.mkHom (Groupoid.inv f.1) (Groupoid.inv f.2) := by
  rfl

/-- The first component of an inverse in a product groupoid. -/
@[simp]
theorem groupoid_prod_inv_fst
    [Groupoid.{v} C] [Groupoid.{v'} D]
    {X Y : C} {X' Y' : D} (f : (X, X') ⟶ (Y, Y')) :
    (Groupoid.inv f).1 = Groupoid.inv f.1 := by
  rfl

/-- The second component of an inverse in a product groupoid. -/
@[simp]
theorem groupoid_prod_inv_snd
    [Groupoid.{v} C] [Groupoid.{v'} D]
    {X Y : C} {X' Y' : D} (f : (X, X') ⟶ (Y, Y')) :
    (Groupoid.inv f).2 = Groupoid.inv f.2 := by
  rfl

end GroupoidProducts

end StacksPart04Lib
