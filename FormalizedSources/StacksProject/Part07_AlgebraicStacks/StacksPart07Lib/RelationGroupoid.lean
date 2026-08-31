/-
Copyright (c) 2026 StacksPart07Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart07Lib Contributors
-/

import Mathlib.CategoryTheory.Groupoid

/-!
# The groupoid attached to a setoid

An equivalence relation can be viewed as a thin groupoid: its objects are the
points and there is one arrow precisely when two points are related.  The
type synonym below keeps the relation-specific category instance separate
from any category structure on the underlying type.
-/

universe u

namespace StacksPart07Lib

open CategoryTheory

variable {α : Type u}

/-! `RelationCategory r` is a type synonym for the objects of `r`. -/
@[nolint unusedArguments]
def RelationCategory (_r : Setoid α) : Type u := α

/-! The (lifted) proposition-valued hom type used by the category. -/
def RelationHom (r : Setoid α) (x y : α) : Type u :=
  ULift (PLift (r.r x y))

namespace RelationCategory

variable (r : Setoid α)

theorem hom_ext {x y : α} (f g : RelationHom r x y) : f = g := by
  apply ULift.ext
  apply Subsingleton.elim

instance groupoid : SmallGroupoid (RelationCategory r) where
  Hom x y := RelationHom r x y
  id x := ULift.up (PLift.up (r.refl x))
  comp f g :=
    ULift.up (PLift.up (r.trans f.down.down g.down.down))
  inv f :=
    ULift.up (PLift.up (r.symm f.down.down))
  id_comp := by
    intro X Y f
    exact hom_ext r _ _
  comp_id := by
    intro X Y f
    exact hom_ext r _ _
  assoc := by
    intro W X Y Z f g h
    exact hom_ext r _ _
  inv_comp := by
    intro X Y f
    exact hom_ext r _ _
  comp_inv := by
    intro X Y f
    exact hom_ext r _ _

instance homSubsingleton (x y : RelationCategory r) :
    Subsingleton (x ⟶ y) := by
  change Subsingleton (RelationHom r x y)
  exact ⟨fun f g => hom_ext r f g⟩

/-! Construct and forget arrows without exposing the lift wrappers. -/
def homOfRel {x y : RelationCategory r} (h : r.r x y) : x ⟶ y :=
  ULift.up (PLift.up h)

def relOfHom {x y : RelationCategory r} (f : x ⟶ y) : r.r x y := by
  change RelationHom r x y at f
  exact f.down.down

theorem relOfHom_homOfRel {x y : RelationCategory r} (h : r.r x y) :
    relOfHom r (homOfRel r h) = h := by
  rfl

theorem homOfRel_relOfHom {x y : RelationCategory r} (f : x ⟶ y) :
    homOfRel r (relOfHom r f) = f := by
  exact hom_ext r _ _

/-! A hom exists exactly when the corresponding points are related. -/
theorem hom_nonempty_iff {x y : RelationCategory r} :
    Nonempty (x ⟶ y) ↔ r.r x y := by
  constructor
  · rintro ⟨f⟩
    exact relOfHom r f
  · intro h
    exact ⟨homOfRel r h⟩

theorem nonempty_hom_iff {x y : RelationCategory r} :
    Nonempty (x ⟶ y) ↔ r.r x y :=
  hom_nonempty_iff r

/-! Inversion acts on the relation by symmetry. -/
theorem inv_homOfRel {x y : RelationCategory r} (h : r.r x y) :
    Groupoid.inv (homOfRel r h) = homOfRel r (r.symm h) := by
  exact hom_ext r _ _

theorem relOfInv {x y : RelationCategory r} (f : x ⟶ y) :
    relOfHom r (Groupoid.inv f) = r.symm (relOfHom r f) := by
  rfl

@[simp]
theorem inv_inv {x y : RelationCategory r} (f : x ⟶ y) :
    Groupoid.inv (Groupoid.inv f) = f := by
  apply Subsingleton.elim

@[simp]
theorem comp_inv {x y : RelationCategory r} (f : x ⟶ y) :
    f ≫ Groupoid.inv f = 𝟙 x := by
  exact Groupoid.comp_inv f

@[simp]
theorem inv_comp {x y : RelationCategory r} (f : x ⟶ y) :
    Groupoid.inv f ≫ f = 𝟙 y := by
  exact Groupoid.inv_comp f

end RelationCategory

end StacksPart07Lib
