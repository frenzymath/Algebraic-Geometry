/-
Copyright (c) 2026 The StacksPart05Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart05Lib Contributors
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# StacksPart05Lib.Monomorphisms

The composition property for monomorphisms of formal algebraic spaces
(Stacks, Tag 0GHT), in the general categorical form supplied by Mathlib.
-/

namespace StacksPart05Lib

open CategoryTheory
open CategoryTheory.Limits

/-- The composite of two monomorphisms is a monomorphism.

This is the categorical form of the composition statement for formal
algebraic spaces in Stacks, Tag 0GHT.
-/
theorem composition_monomorphism {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] : Mono (f ≫ g) := by
  exact CategoryTheory.mono_comp f g

/-- Pulling back a monomorphism along any morphism gives a monomorphism.

This is the categorical form of the base-change statement in Stacks,
Tag 0GHU.
-/
theorem base_change_monomorphism {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [Mono f] :
    Mono (pullback.snd f g) := by
  infer_instance

/-- The symmetric pullback leg is useful when the base-change map is presented
with the other projection. -/
theorem base_change_monomorphism_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [Mono g] :
    Mono (pullback.fst f g) := by
  infer_instance

end StacksPart05Lib
