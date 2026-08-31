/-
Copyright (c) 2026 The StacksPart07Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart07Lib Contributors
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Endomorphism

/-!
# StacksPart07Lib.Groupoids

Elementary categorical facts for the groupoid constructions used throughout
the algebraic-stacks chapters.  These statements are entirely axiom-free and
depend only on Mathlib's category and groupoid interfaces.
-/

universe u v u' v'

namespace StacksPart07Lib

open CategoryTheory

/-! An arrow is invertible exactly when it has a two-sided inverse. -/
theorem isIso_iff_exists_inverse {C : Type u} [Category.{v} C] {X Y : C}
    (f : X ⟶ Y) :
    IsIso f ↔ ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y := by
  constructor
  · intro hf
    letI : IsIso f := hf
    exact ⟨inv f, IsIso.hom_inv_id f, IsIso.inv_hom_id f⟩
  · rintro ⟨g, hfg, hgf⟩
    exact IsIso.mk ⟨g, hfg, hgf⟩

/-! A two-sided inverse is unique. -/
theorem inverse_unique {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}
    {g h : Y ⟶ X}
    (hg : f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y)
    (hh : f ≫ h = 𝟙 X ∧ h ≫ f = 𝟙 Y) :
    g = h := by
  calc
    g = 𝟙 Y ≫ g := by simp
    _ = (h ≫ f) ≫ g := by rw [hh.2]
    _ = h ≫ (f ≫ g) := by simp only [Category.assoc]
    _ = h ≫ 𝟙 X := by rw [hg.1]
    _ = h := by simp

/-! A category is a groupoid exactly when every arrow is invertible. -/
theorem isGroupoid_iff_all_isIso {C : Type u} [Category.{v} C] :
    IsGroupoid C ↔ ∀ {X Y : C} (f : X ⟶ Y), IsIso f := by
  constructor
  · intro h X Y f
    letI : IsGroupoid C := h
    exact IsGroupoid.all_isIso f
  · intro h
    exact IsGroupoid.mk h

/-! In a groupoid, inversion is an involution. -/
@[simp]
theorem groupoid_inv_inv {C : Type u} [Groupoid.{v} C] {X Y : C}
    (f : X ⟶ Y) :
    Groupoid.inv (Groupoid.inv f) = f := by
  simp

/-! Products of groupoids are groupoids. -/
theorem isGroupoid_prod {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D] [IsGroupoid C] [IsGroupoid D] :
    IsGroupoid (C × D) := by
  infer_instance

/-! Dependent products of groupoids are groupoids. -/
theorem isGroupoid_pi {I : Type u} {C : I → Type u'}
    [∀ i, Category.{v'} (C i)] [∀ i, IsGroupoid (C i)] :
    IsGroupoid (∀ i, C i) := by
  infer_instance

/-! A product morphism is invertible exactly componentwise. -/
theorem isIso_prod_iff {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    {P Q : C} {S T : D} (f : (P, S) ⟶ (Q, T)) :
    IsIso f ↔ IsIso f.1 ∧ IsIso f.2 := by
  exact CategoryTheory.isIso_prod_iff C D

/-! Endomorphisms of an object in a groupoid form a group. -/
instance endGroup (C : Type u) [Groupoid.{v} C] (X : C) : Group (End X) :=
  inferInstance

end StacksPart07Lib
