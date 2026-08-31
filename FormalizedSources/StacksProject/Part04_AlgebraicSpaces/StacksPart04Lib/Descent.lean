/-
Copyright (c) 2026 The StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Types.Basic

/-!
# StacksPart04Lib.Descent

Pointwise descent data for a groupoid presentation.  A compatible family of
sections is the elementary categorical core of descent: transport along every
arrow identifies the values on its source and target.  The construction is
deliberately independent of schemes, quotients, and morphism properties, so it
can be reused by the groupoid chapters of the algebraic-spaces blueprint.
-/

namespace StacksPart04Lib

open CategoryTheory

universe u v w

/-! ### Compatible families -/

/-- A section of a diagram of types whose values are compatible with every
morphism in the indexing category. -/
structure DescentSection {C : Type u} [Category.{v} C] (F : C ⥤ Type w) where
  value : ∀ X : C, F.obj X
  compatible : ∀ {X Y : C} (f : X ⟶ Y), F.map f (value X) = value Y

namespace DescentSection

variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w}

@[simp]
theorem map_id (s : DescentSection F) (X : C) :
    F.map (𝟙 X) (s.value X) = s.value X := by
  exact s.compatible (𝟙 X)

theorem compatible_comp (s : DescentSection F)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) (s.value X) = s.value Z := by
  rw [F.map_comp]
  change F.map g (F.map f (s.value X)) = s.value Z
  rw [s.compatible f, s.compatible g]

/-- Compatible sections are determined by their values objectwise. -/
theorem ext {s t : DescentSection F} (h : ∀ X : C, s.value X = t.value X) : s = t := by
  cases s with
  | mk sv sc =>
    cases t with
    | mk tv tc =>
      simp only [DescentSection.mk.injEq]
      funext X
      exact h X

/-- On a presentation connected from a chosen object, a compatible section is
determined by its value at that object. -/
theorem ext_of_component {X₀ : C}
    (reachable : ∀ X : C, Nonempty (X₀ ⟶ X))
    {s t : DescentSection F} (h₀ : s.value X₀ = t.value X₀) : s = t := by
  apply ext
  intro X
  obtain ⟨f⟩ := reachable X
  calc
    s.value X = F.map f (s.value X₀) := (s.compatible f).symm
    _ = F.map f (t.value X₀) := congrArg (fun z => F.map f z) h₀
    _ = t.value X := t.compatible f

/-! ### Groupoid transport -/

/-- Compatibility in the reverse direction is automatic for a groupoid: use
the inverse arrow.  This is the pointwise form of the cocycle symmetry used
in groupoid presentations. -/
theorem compatible_inv [IsGroupoid C] (s : DescentSection F)
    {X Y : C} (f : X ⟶ Y) :
    F.map (inv f) (s.value Y) = s.value X := by
  rw [← s.compatible f]
  calc
    F.map (inv f) (F.map f (s.value X)) =
        F.map (f ≫ inv f) (s.value X) :=
      ConcreteCategory.congr_hom (F.map_comp f (inv f)).symm _
    _ = s.value X := by simp

/-! ### Pullback and transport -/

/-- Pull a compatible section back along a functor of indexing categories. -/
def pullback {D : Type u} [Category.{v} D] (G : D ⥤ C)
    (s : DescentSection F) : DescentSection (G ⋙ F) where
  value X := s.value (G.obj X)
  compatible f := s.compatible (G.map f)

@[simp]
theorem pullback_value {D : Type u} [Category.{v} D] (G : D ⥤ C)
    (s : DescentSection F) (X : D) :
    (pullback G s).value X = s.value (G.obj X) := rfl

theorem pullback_id (s : DescentSection F) :
    pullback (𝟭 C) s = s := by
  apply ext
  intro X
  rfl

theorem pullback_comp {D E : Type u} [Category.{v} D] [Category.{v} E]
    (G : D ⥤ C) (H : E ⥤ D) (s : DescentSection F) :
    pullback H (pullback G s) = pullback (H ⋙ G) s := by
  apply ext
  intro X
  rfl

/-- A natural transformation transports a compatible section pointwise. -/
def map {F' : C ⥤ Type w} (α : F ⟶ F')
    (s : DescentSection F) : DescentSection F' where
  value X := α.app X (s.value X)
  compatible {X Y} f := by
    rw [← s.compatible f]
    exact ConcreteCategory.congr_hom (α.naturality f).symm (s.value X)

@[simp]
theorem map_value {F' : C ⥤ Type w} (α : F ⟶ F')
    (s : DescentSection F) (X : C) :
    (map α s).value X = α.app X (s.value X) := rfl

end DescentSection

end StacksPart04Lib
