/-
Copyright (c) 2026 StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The action groupoid of a group action

For a group `G` acting on a type `X`, the action groupoid has the points of
`X` as objects and an arrow `x ⟶ y` for every `g : G` carrying `x` to `y`.
The group is kept as an explicit parameter of `actionGroupoid`: it cannot be
inferred from the object type `X`, and a global category instance would
therefore have unsynthesizable parameters.
-/

universe u v

namespace StacksPart04Lib

open CategoryTheory

/-! An arrow in the action groupoid, with its source and target equation. -/
def ActionHom (G : Type u) (X : Type v) [Group G] [MulAction G X]
    (x y : X) : Type u := {g : G // g • x = y}

namespace ActionGroupoid

variable (G : Type u) (X : Type v) [Group G] [MulAction G X]

/-! The canonical identity arrow. -/
def id (x : X) : ActionHom G X x x := ⟨1, by simp⟩

/-! Composition of arrows (the categorical composite is `g * f`). -/
def comp {x y z : X} (f : ActionHom G X x y) (g : ActionHom G X y z) :
    ActionHom G X x z :=
  ⟨g.1 * f.1, by
    rw [mul_smul, f.2, g.2]⟩

/-! The inverse arrow. -/
def inv {x y : X} (f : ActionHom G X x y) : ActionHom G X y x :=
  ⟨f.1⁻¹, by
    calc
      f.1⁻¹ • y = f.1⁻¹ • (f.1 • x) := congrArg (fun t : X => f.1⁻¹ • t) f.2.symm
      _ = x := inv_smul_smul f.1 x⟩

/-! The category-theoretic groupoid attached to the action. -/
@[reducible]
def groupoid : Groupoid.{u} X where
  Hom x y := ActionHom G X x y
  id := id G X
  comp := @comp G X _ _
  inv := @inv G X _ _
  id_comp := by
    intro x y f
    exact Subtype.ext (by simp [comp, id])
  comp_id := by
    intro x y f
    exact Subtype.ext (by simp [comp, id])
  assoc := by
    intro w x y z f g h
    exact Subtype.ext (by simp [comp, mul_assoc])
  inv_comp := by
    intro x y f
    exact Subtype.ext (by simp [comp, inv, id])
  comp_inv := by
    intro x y f
    exact Subtype.ext (by simp [comp, inv, id])

@[simp]
theorem id_val (x : X) : (id G X x).1 = 1 := rfl

@[simp]
theorem comp_val {x y z : X} (f : ActionHom G X x y) (g : ActionHom G X y z) :
    (comp G X f g).1 = g.1 * f.1 := rfl

@[simp]
theorem inv_val {x y : X} (f : ActionHom G X x y) : (inv G X f).1 = f.1⁻¹ := rfl

theorem id_comp_hom {x y : X} (f : ActionHom G X x y) :
    comp G X (id G X x) f = f := by
  exact Subtype.ext (by simp [comp, id])

theorem comp_id_hom {x y : X} (f : ActionHom G X x y) :
    comp G X f (id G X y) = f := by
  exact Subtype.ext (by simp [comp, id])

theorem comp_inv_hom {x y : X} (f : ActionHom G X x y) :
    comp G X f (inv G X f) = id G X x := by
  exact Subtype.ext (by simp [comp, inv, id])

theorem inv_comp_hom {x y : X} (f : ActionHom G X x y) :
    comp G X (inv G X f) f = id G X y := by
  exact Subtype.ext (by simp [comp, inv, id])

@[simp]
theorem inv_inv_hom {x y : X} (f : ActionHom G X x y) :
    inv G X (inv G X f) = f := by
  exact Subtype.ext (by simp [inv])

theorem hom_nonempty_iff {x y : X} :
    Nonempty (ActionHom G X x y) ↔ ∃ g : G, g • x = y := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f.1, f.2⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨g, hg⟩⟩

theorem hom_exists_iff {x y : X} :
    Nonempty (ActionHom G X x y) ↔ y ∈ Set.range (fun g : G => g • x) := by
  rw [hom_nonempty_iff]
  rfl

/-! The stabilizer (or isotropy group) at a point. -/
def Stabilizer (x : X) : Subgroup G where
  carrier := {g | g • x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (g * h) • x = x at *
    rw [mul_smul, hh, hg]
  inv_mem' := by
    intro g hg
    change g⁻¹ • x = x at *
    calc
      g⁻¹ • x = g⁻¹ • (g • x) := congrArg (fun t : X => g⁻¹ • t) hg.symm
      _ = x := inv_smul_smul g x

theorem mem_stabilizer_iff {x : X} {g : G} :
    g ∈ Stabilizer G X x ↔ g • x = x := Iff.rfl

theorem isotropy_nonempty (x : X) :
    Nonempty (ActionHom G X x x) :=
  (hom_nonempty_iff G X).2 ⟨1, by simp⟩

theorem isotropy_iff_stabilizer {x : X} {g : G} :
    g ∈ Stabilizer G X x ↔ ∃ f : ActionHom G X x x, f.1 = g := by
  constructor
  · intro hg
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    exact f.2

end ActionGroupoid

end StacksPart04Lib
