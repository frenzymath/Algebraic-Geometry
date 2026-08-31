/-
Copyright (c) 2026 The StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import StacksPart04Lib.Groupoids

/-!
# Functors and groupoid inverses

The structure maps in a groupoid presentation are functorial.  The basic
identity below records that a functor between groupoids carries the chosen
inverse to the chosen inverse in the target; it is the categorical form of
the inversion compatibility used in the groupoid chapters.
-/

namespace StacksPart04Lib

open CategoryTheory

universe u v u' v'

/-- A functor between groupoids preserves inversion. -/
theorem functor_map_inv {C : Type u} {D : Type u'}
    [Groupoid.{v} C] [Groupoid.{v'} D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    F.map (Groupoid.inv f) = Groupoid.inv (F.map f) := by
  apply inverse_unique
    (⟨?_, ?_⟩)
    (⟨Groupoid.comp_inv _, Groupoid.inv_comp _⟩)
  · rw [← F.map_comp, Groupoid.comp_inv, F.map_id]
  · rw [← F.map_comp, Groupoid.inv_comp, F.map_id]

end StacksPart04Lib
