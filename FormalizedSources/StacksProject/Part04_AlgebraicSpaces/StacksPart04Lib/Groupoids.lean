/-
Copyright (c) 2026 StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Endomorphism

/-!
# StacksPart04Lib.Groupoids

Small categorical foundations for the groupoid chapters of the algebraic
spaces blueprint.  The algebraic-space statements in Chapter 14 are
pointwise statements about groupoid categories; this file records the generic
categorical facts used by that pointwise interpretation.  In particular, no
geometric structure or project-local assumption is hidden here.
-/

universe u v u' v'

namespace StacksPart04Lib

open CategoryTheory

/-!
An arrow is invertible exactly when it has a two-sided inverse.  This is the
categorical core of the groupoid conventions used in Chapter 14 (compare
Stacks tag 043W and the preceding groupoid-scheme discussion).
-/
theorem isIso_iff_exists_inverse {C : Type u} [Category.{v} C] {X Y : C}
    (f : X ⟶ Y) :
    IsIso f ↔ ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y := by
  constructor
  · intro hf
    letI : IsIso f := hf
    exact ⟨inv f, IsIso.hom_inv_id f, IsIso.inv_hom_id f⟩
  · rintro ⟨g, hfg, hgf⟩
    exact IsIso.mk ⟨g, hfg, hgf⟩

/-!
The inverse appearing above is unique (Stacks tag 0017).
-/
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

/-!
A category is a groupoid exactly when every arrow is invertible.  The
propositional `IsGroupoid` form is convenient when the category structure is
already supplied (Stacks tag 043W, pointwise in a test scheme).
-/
theorem isGroupoid_iff_all_isIso {C : Type u} [Category.{v} C] :
    IsGroupoid C ↔ ∀ {X Y : C} (f : X ⟶ Y), IsIso f := by
  constructor
  · intro h X Y f
    letI : IsGroupoid C := h
    exact IsGroupoid.all_isIso f
  · intro h
    exact IsGroupoid.mk h

/-!
In a groupoid, inversion is an involution.  This is the categorical shadow of
the inverse morphism in the septuple `(U, R, s, t, c, e, i)` of Chapter 14.
-/
@[simp]
theorem groupoid_inv_inv {C : Type u} [Groupoid.{v} C] {X Y : C}
    (f : X ⟶ Y) :
    Groupoid.inv (Groupoid.inv f) = f := by
  simp

/-!
Products of groupoids are groupoids.  Mathlib supplies the instance; this
named theorem makes the closure used by products of pointwise groupoids
available to downstream Part 04 files (compare the product constructions in
Chapters 14 and 15).
-/
theorem isGroupoid_prod {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D] [IsGroupoid C] [IsGroupoid D] :
    IsGroupoid (C × D) := by
  infer_instance

/-!
Dependent products of groupoids are groupoids as well.  This is useful for
families of test categories and for pointwise constructions.
-/
theorem isGroupoid_pi {I : Type u} {C : I → Type u'}
    [∀ i, Category.{v'} (C i)] [∀ i, IsGroupoid (C i)] :
    IsGroupoid (∀ i, C i) := by
  infer_instance

/-!
The morphism-level product criterion exposes the componentwise form of the
preceding closure theorem.
-/
theorem isIso_prod_iff {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    {P Q : C} {S T : D} (f : (P, S) ⟶ (Q, T)) :
    IsIso f ↔ IsIso f.1 ∧ IsIso f.2 := by
  exact CategoryTheory.isIso_prod_iff C D

/-!
For each object of a groupoid, its endomorphisms form a group.  This is the
categorical model for stabilizer/vertex groups appearing in the groupoid
sections of Chapters 14 and 15.
-/
instance endGroup (C : Type u) [Groupoid.{v} C] (X : C) : Group (End X) :=
  inferInstance

end StacksPart04Lib
