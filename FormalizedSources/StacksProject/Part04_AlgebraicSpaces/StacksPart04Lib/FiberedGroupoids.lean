/-
Copyright (c) 2026 StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import Mathlib.CategoryTheory.FiberedCategory.HasFibers
import Mathlib.CategoryTheory.Groupoid

/-!
# StacksPart04Lib.FiberedGroupoids

The elementary categorical package for a category fibred in groupoids. A
projection is required to be fibred, and each ordinary fibre category is
required to be a groupoid. The total category itself need not be a groupoid.
-/

namespace CategoryTheory.Functor

open CategoryTheory
open CategoryTheory.IsHomLift

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} {𝒳 : Type u₂}
variable [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- A functor whose fibres are groupoids and which has cartesian lifts. -/
class IsFiberedInGroupoids (p : 𝒳 ⥤ 𝒮) : Prop extends p.IsFibered where
  fiber_isGroupoid (S : 𝒮) : IsGroupoid (Fiber p S)

attribute [instance] IsFiberedInGroupoids.fiber_isGroupoid

/-- Unpack the two components of the fibred-in-groupoids condition. -/
theorem isFiberedInGroupoids_iff (p : 𝒳 ⥤ 𝒮) :
    IsFiberedInGroupoids p ↔ p.IsFibered ∧ ∀ S : 𝒮, IsGroupoid (Fiber p S) := by
  constructor
  · intro h
    letI : IsFiberedInGroupoids p := h
    exact ⟨inferInstance, fun S => by infer_instance⟩
  · rintro ⟨hp, hf⟩
    exact { toIsFibered := hp, fiber_isGroupoid := hf }

/-- Build the package from a fibred structure and groupoid fibres. -/
theorem isFiberedInGroupoids_of_fibers (p : 𝒳 ⥤ 𝒮)
    (hp : p.IsFibered) (hf : ∀ S : 𝒮, IsGroupoid (Fiber p S)) :
    IsFiberedInGroupoids p := by
  exact { toIsFibered := hp, fiber_isGroupoid := hf }

/-- Every arrow in an ordinary fibre is an isomorphism. -/
theorem fiber_hom_isIso (p : 𝒳 ⥤ 𝒮) [IsFiberedInGroupoids p]
    {S : 𝒮} {a b : Fiber p S} (f : a ⟶ b) : IsIso f := by
  infer_instance

/-- A vertical arrow in the total category is an isomorphism. -/
theorem vertical_isIso (p : 𝒳 ⥤ 𝒮) [IsFiberedInGroupoids p]
    {S : 𝒮} {a b : 𝒳} (f : a ⟶ b) [IsHomLift p (𝟙 S) f] : IsIso f := by
  let φ : Fiber p S := Fiber.mk (domain_eq p (𝟙 S) f)
  let ψ : Fiber p S := Fiber.mk (codomain_eq p (𝟙 S) f)
  let q : φ ⟶ ψ := Fiber.homMk p S f
  haveI : IsIso q := by infer_instance
  haveI : IsIso ((Fiber.fiberInclusion : Fiber p S ⥤ 𝒳).map q) :=
    Functor.map_isIso (Fiber.fiberInclusion : Fiber p S ⥤ 𝒳) q
  simpa [q, φ, ψ] using
    (inferInstance : IsIso ((Fiber.fiberInclusion : Fiber p S ⥤ 𝒳).map q))

end CategoryTheory.Functor
