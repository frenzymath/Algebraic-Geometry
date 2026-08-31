/-
Copyright (c) 2026 StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import StacksPart04Lib.FiberedGroupoids
import Mathlib.CategoryTheory.Groupoid.Basic

/-!
# Fibred categories in setoids

For a fibred category in groupoids, having setoid fibres means precisely that
the fibre categories are thin. This file records the corresponding
characterizations and uniqueness lemmas.
-/

namespace CategoryTheory.Functor

open CategoryTheory
open CategoryTheory.IsHomLift

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} {𝒳 : Type u₂}
variable [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- A fibred category in groupoids whose fibres are setoids (thin groupoids). -/
class IsFiberedInSetoids (p : 𝒳 ⥤ 𝒮) : Prop extends IsFiberedInGroupoids p where
  fiber_isThin (S : 𝒮) : Quiver.IsThin (Fiber p S)

attribute [instance] IsFiberedInSetoids.fiber_isThin

/-- Unpack the groupoid and thinness components of the setoid condition. -/
theorem isFiberedInSetoids_iff (p : 𝒳 ⥤ 𝒮) :
    IsFiberedInSetoids p ↔
      IsFiberedInGroupoids p ∧ ∀ S : 𝒮, Quiver.IsThin (Fiber p S) := by
  constructor
  · intro h
    letI : IsFiberedInSetoids p := h
    exact ⟨h.toIsFiberedInGroupoids, fun S => inferInstance⟩
  · rintro ⟨hp, ht⟩
    exact { toIsFiberedInGroupoids := hp, fiber_isThin := ht }

/-- Arrows in a fibre are unique. -/
theorem fiber_hom_eq (p : 𝒳 ⥤ 𝒮) [IsFiberedInSetoids p]
    {S : 𝒮} {a b : Fiber p S} (f g : a ⟶ b) : f = g := by
  exact Subsingleton.elim _ _

/-- The corresponding uniqueness statement after including a fibre in the total category. -/
theorem fiber_inclusion_hom_eq (p : 𝒳 ⥤ 𝒮) [IsFiberedInSetoids p]
    {S : 𝒮} {a b : Fiber p S} (f g : a ⟶ b) :
    (Fiber.fiberInclusion : Fiber p S ⥤ 𝒳).map f =
      (Fiber.fiberInclusion : Fiber p S ⥤ 𝒳).map g := by
  exact congrArg (fun q => (Fiber.fiberInclusion : Fiber p S ⥤ 𝒳).map q)
    (fiber_hom_eq p f g)

/-- Thinness is equivalent to uniqueness of arrows in every standard fibre. -/
theorem isFiberedInSetoids_iff_vertical_hom_eq (p : 𝒳 ⥤ 𝒮)
    [IsFiberedInGroupoids p] :
    IsFiberedInSetoids p ↔
      ∀ (S : 𝒮) (a b : Fiber p S) (f g : a ⟶ b), f = g := by
  constructor
  · intro h
    letI : IsFiberedInSetoids p := h
    intro S a b f g
    exact fiber_hom_eq p f g
  · intro h
    exact {
      toIsFiberedInGroupoids := inferInstance
      fiber_isThin := fun S a b => ⟨fun f g => h S a b f g⟩
    }

end CategoryTheory.Functor
