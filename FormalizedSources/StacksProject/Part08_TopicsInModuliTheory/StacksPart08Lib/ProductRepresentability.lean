/-
Copyright (c) 2026 The StacksPart08Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart08Lib Contributors
-/

import StacksPart08Lib.Representability

/-!
# Products of representable transformations

The product lemma in the moduli-stack chapter (Stacks, Tag `02ZU`) is formal:
a product transformation is a composite of two base changes of the original
transformations. This file records that argument in the presheaf model used by
the Part 08 representability interface.
-/

namespace StacksPart08

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
    (fun s m h1 h2 => by
      apply prod.hom_ext
      · rw [← h2, Category.assoc, prod.map_fst, prod.lift_fst, Category.comp_id]
      · rw [← h1, prod.lift_snd])

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
    (fun s m hm1 hm2 => by
      apply Prod.hom_ext
      · apply h.hom_ext
        · have hm1' : m.1 ≫ fst = s.fst.1 := by
            simpa [c] using congrArg Prod.fst hm1
          have hl1' :
              (h.lift s.fst.1 s.snd.1 (congrArg Prod.fst s.condition)) ≫ fst = s.fst.1 := by
            exact h.lift_fst _ _ _
          exact hm1'.trans hl1'.symm
        · have hm2' : m.1 ≫ snd = s.snd.1 := by
            simpa [c] using congrArg Prod.fst hm2
          have hl2' :
              (h.lift s.fst.1 s.snd.1 (congrArg Prod.fst s.condition)) ≫ snd = s.snd.1 := by
            exact h.lift_snd _ _ _
          exact hm2'.trans hl2'.symm
      · apply h'.hom_ext
        · have hm1' : m.2 ≫ fst' = s.fst.2 := by
            simpa [c] using congrArg Prod.snd hm1
          have hl1' :
              (h'.lift s.fst.2 s.snd.2 (congrArg Prod.snd s.condition)) ≫ fst' = s.fst.2 := by
            exact h'.lift_fst _ _ _
          exact hm1'.trans hl1'.symm
        · have hm2' : m.2 ≫ snd' = s.snd.2 := by
            simpa [c] using congrArg Prod.snd hm2
          have hl2' :
              (h'.lift s.fst.2 s.snd.2 (congrArg Prod.snd s.condition)) ≫ snd' = s.snd.2 := by
            exact h'.lift_snd _ _ _
          exact hm2'.trans hl2'.symm)

/-!
### Product representability

The products here are the categorical products in the presheaf category.
-/

/-- Products of representable transformations remain representable. -/
theorem representableTransformation_prod {C : Type u} [Category.{v} C]
    {F1 G1 F2 G2 : Presheaf C}
    (f1 : F1 ⟶ G1) (f2 : F2 ⟶ G2)
    (h1 : RepresentableTransformation C f1)
    (h2 : RepresentableTransformation C f2) :
    RepresentableTransformation C (prod.map f1 f2) := by
  have hleft : RepresentableTransformation C (prod.map f1 (𝟙 F2)) :=
    representableTransformation_baseChange
      (IsPullback.of_prod_fst_with_id f1 F2) h1
  have hright : RepresentableTransformation C (prod.map (𝟙 G1) f2) :=
    representableTransformation_baseChange
      (isPullback_prod_snd_with_id f2 G1) h2
  have hcomp : RepresentableTransformation C
      (prod.map f1 (𝟙 F2) ≫ prod.map (𝟙 G1) f2) :=
    representableTransformation_comp _ _ hleft hright
  rw [prod.map_map] at hcomp
  simpa using hcomp

end StacksPart08
