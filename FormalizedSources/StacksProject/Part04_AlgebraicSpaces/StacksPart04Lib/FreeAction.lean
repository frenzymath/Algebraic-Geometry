/-
Copyright (c) 2026 StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import StacksPart04Lib.ActionGroupoid

/-!
# Free actions and action-groupoid thinness

The pointwise form of a free action in the algebraic-spaces blueprint is the
injectivity of `(g, x) |-> (g • x, x)` (Stacks tag 06P9).  At the set level,
this is equivalent to saying that the associated action groupoid has at most
one arrow between any two objects.
-/

namespace StacksPart04Lib.ActionGroupoid

universe u v

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

/-- Pointwise freeness of a group action. -/
def IsFree : Prop :=
  ∀ ⦃g h : G⦄ (x : X), g • x = h • x → g = h

/-- The map whose algebraic-space analogue occurs in the free-action criterion. -/
def actionPair : G × X → X × X :=
  fun p => (p.1 • p.2, p.2)

/-- A group action is free exactly when `(g, x) |-> (g • x, x)` is injective.

This is the pointwise/set-level content of Stacks, Lemma 06P9.
-/
theorem isFree_iff_actionPair_injective :
    IsFree (G := G) (X := X) ↔ Function.Injective (actionPair (G := G) (X := X)) := by
  constructor
  · intro h p q hpq
    have hxy : p.2 = q.2 := congrArg (fun z : X × X => z.2) hpq
    have hsmul : p.1 • p.2 = q.1 • p.2 := by
      calc
        p.1 • p.2 = (actionPair (G := G) (X := X) p).1 := rfl
        _ = (actionPair (G := G) (X := X) q).1 :=
          congrArg (fun z : X × X => z.1) hpq
        _ = q.1 • q.2 := rfl
        _ = q.1 • p.2 := by rw [hxy]
    have hgh : p.1 = q.1 := h p.2 hsmul
    exact Prod.ext hgh hxy
  · intro h g g' x hxx
    have hpq : actionPair (G := G) (X := X) (g, x) =
        actionPair (G := G) (X := X) (g', x) := by
      apply Prod.ext
      · exact hxx
      · rfl
    have hpair : (g, x) = (g', x) := h hpq
    exact congrArg (fun z : G × X => z.1) hpair

/-- Freeness is equivalent to thinness of the associated action groupoid. -/
theorem isFree_iff_hom_subsingleton :
    IsFree (G := G) (X := X) ↔
      ∀ (x y : X), Subsingleton (ActionHom G X x y) := by
  constructor
  · intro h x y
    constructor
    intro f g
    apply Subtype.ext
    exact h x (f.2.trans g.2.symm)
  · intro h g g' x hxx
    let f : ActionHom G X x (g • x) := ⟨g, rfl⟩
    let f' : ActionHom G X x (g • x) := ⟨g', hxx.symm⟩
    have hfg : f = f' := Subsingleton.elim f f'
    exact congrArg Subtype.val hfg

end StacksPart04Lib.ActionGroupoid
