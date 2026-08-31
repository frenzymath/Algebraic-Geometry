/-
Copyright (c) 2026 The StacksPart08Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart08Lib Contributors
-/

import Mathlib.Data.Nat.Basic

/-!
# Abstract quotient descent for stack-like invariants

Objects in a moduli problem are often identified up to an isomorphism
relation.  This file records the elementary quotient step independently of
any geometric representability assumptions: an invariant descends exactly
when it is constant on equivalent objects.
-/

namespace StacksPart08

universe u v

/-- A function is invariant under the equivalence relation on `α`. -/
def QuotientDescent {α : Type u} {β : Type v} [Setoid α]
    (f : α → β) : Prop :=
  ∀ ⦃a b : α⦄, a ≈ b → f a = f b

/-- Invariant maps compose: postcomposing a quotient-invariant map with any
function preserves invariance on the source quotient. -/
theorem quotientDescent_comp {α : Type u} {β : Type v} {γ : Type*}
    [Setoid α] (f : α → β) (g : β → γ)
    (hf : QuotientDescent f) :
    QuotientDescent (g ∘ f) := by
  intro a b hab
  exact congrArg g (hf hab)

/-- The descended function on equivalence classes. -/
def quotientDescend {α : Type u} {β : Type v} [Setoid α]
    (f : α → β) (hf : QuotientDescent f) :
    Quotient (inferInstance : Setoid α) → β :=
  Quotient.lift f (fun _ _ hab => hf hab)

@[simp]
theorem quotientDescend_mk {α : Type u} {β : Type v} [Setoid α]
    (f : α → β) (hf : QuotientDescent f) (a : α) :
    quotientDescend f hf (Quotient.mk' a) = f a :=
  rfl

/-- An invariant descends to the quotient iff a function on classes realizes it. -/
theorem quotientDescent_iff_exists {α : Type u} {β : Type v} [Setoid α]
    (f : α → β) :
      QuotientDescent f ↔
      ∃ g : Quotient (inferInstance : Setoid α) → β,
        ∀ a, g (Quotient.mk' a) = f a := by
  constructor
  · intro hf
    exact ⟨quotientDescend f hf, fun a => quotientDescend_mk f hf a⟩
  · rintro ⟨g, hg⟩ a b hab
    rw [← hg a, ← hg b]
    exact congrArg g (Quotient.sound hab)

/-- A descended function on classes is uniquely determined by its values on representatives. -/
theorem quotientDescent_unique {α : Type u} {β : Type v} [Setoid α]
    (f : α → β)
    {g₁ g₂ : Quotient (inferInstance : Setoid α) → β}
    (h₁ : ∀ a, g₁ (Quotient.mk' a) = f a)
    (h₂ : ∀ a, g₂ (Quotient.mk' a) = f a) :
    g₁ = g₂ := by
  funext q
  induction q using Quotient.inductionOn with
  | _ a =>
    change g₁ (Quotient.mk' a) = g₂ (Quotient.mk' a)
    exact (h₁ a).trans (h₂ a).symm

end StacksPart08
