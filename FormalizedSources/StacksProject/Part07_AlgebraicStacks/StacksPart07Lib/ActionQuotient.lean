/-
Copyright (c) 2026 StacksPart07Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart07Lib Contributors
-/

import StacksPart07Lib.ActionGroupoid
import StacksPart07Lib.RelationGroupoid
import StacksPart07Lib.QuotientFoundations

/-!
# Orbit relations and the action-groupoid quotient

The orbit relation of a group action is an equivalence relation.  The action
groupoid therefore maps canonically to the associated thin relation groupoid;
this records the quotient shadow of an action without assuming that a
geometric quotient exists.
-/

namespace StacksPart07Lib

open CategoryTheory

universe u v

namespace ActionQuotient

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

/-! ### The orbit relation -/

/-- Two points are related when one is carried to the other by the action. -/
def orbitRel (G : Type u) (X : Type v) [Group G] [MulAction G X]
    (x y : X) : Prop :=
  ∃ g : G, g • x = y

/-- The orbit relation of a group action is an equivalence relation. -/
def orbitSetoid (G : Type u) (X : Type v) [Group G] [MulAction G X] : Setoid X where
  r := orbitRel G X
  iseqv := {
    refl := fun x => ⟨1, by simp⟩
    symm := by
      rintro x y ⟨g, h⟩
      exact ⟨g⁻¹, by rw [← h, inv_smul_smul]⟩
    trans := by
      rintro x y z ⟨g, h⟩ ⟨k, hk⟩
      exact ⟨k * g, by rw [mul_smul, h, hk]⟩ }

theorem orbitRel_iff {x y : X} :
    orbitRel G X x y ↔ ∃ g : G, g • x = y :=
  Iff.rfl

theorem orbitRel_refl (x : X) : orbitRel G X x x :=
  (orbitSetoid G X).refl x

theorem orbitRel_symm {x y : X} (h : orbitRel G X x y) :
    orbitRel G X y x :=
  (orbitSetoid G X).symm h

theorem orbitRel_trans {x y z : X} (hxy : orbitRel G X x y)
    (hyz : orbitRel G X y z) : orbitRel G X x z :=
  (orbitSetoid G X).trans hxy hyz

/-! ### The action category and its thin quotient shadow -/

@[nolint unusedArguments]
def ActionCategory (_G : Type u) (X : Type v) : Type v := X

namespace ActionCategory

@[nolint unusedArguments]
instance groupoid (G : Type u) (X : Type v) [Group G] [MulAction G X] :
    Groupoid (ActionCategory G X) :=
  ActionGroupoid.groupoid G X

end ActionCategory

/-- The canonical functor from the action groupoid to the thin groupoid of
orbits.  Distinct group elements inducing the same arrow are identified. -/
def toRelation :
    ActionCategory G X ⥤ RelationCategory (orbitSetoid G X) where
  obj := id
  map {x y} f :=
    RelationCategory.homOfRel (orbitSetoid G X) ⟨f.1, f.2⟩
  map_id := by
    intro x
    exact RelationCategory.hom_ext _ _ _
  map_comp := by
    intro x y z f g
    exact RelationCategory.hom_ext _ _ _

@[simp]
theorem toRelation_obj (x : ActionCategory G X) :
    (toRelation (G := G) (X := X)).obj x = x :=
  rfl

theorem action_hom_nonempty_iff_orbitRel {x y : ActionCategory G X} :
    Nonempty (x ⟶ y) ↔ orbitRel G X x y := by
  exact ActionGroupoid.hom_nonempty_iff G X

/-! ### Factorization through the orbit quotient -/

/-- The canonical projection to the set of orbit classes. -/
def orbitQuotientMk (x : X) : Quotient (orbitSetoid G X) :=
  Quotient.mk (orbitSetoid G X) x

@[simp]
theorem orbitQuotientMk_eq_iff {x y : X} :
    orbitQuotientMk (G := G) (X := X) x = orbitQuotientMk y ↔
      orbitRel G X x y := by
  change Quotient.mk (orbitSetoid G X) x = Quotient.mk (orbitSetoid G X) y ↔ _
  rw [Quotient.eq]
  rfl

/-- An invariant map descends uniquely to the orbit quotient. -/
def invariantLift {Y : Type*} (f : X → Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    Quotient (orbitSetoid G X) → Y :=
  Quotient.lift f (by
    intro x y h
    obtain ⟨g, hg⟩ := h
    rw [← hg]
    exact (hf g x).symm)

@[simp]
theorem invariantLift_mk {Y : Type*} (f : X → Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) (x : X) :
    invariantLift (G := G) (X := X) f hf (orbitQuotientMk x) = f x :=
  rfl

theorem invariantLift_comp_mk {Y : Type*} (f : X → Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    invariantLift (G := G) (X := X) f hf ∘ orbitQuotientMk = f := by
  funext x
  rfl

theorem invariantLift_unique {Y : Type*} (f : X → Y)
    (hf : ∀ (g : G) (x : X), f (g • x) = f x)
    {q : Quotient (orbitSetoid G X) → Y}
    (hq : q ∘ orbitQuotientMk = f) :
    q = invariantLift (G := G) (X := X) f hf := by
  change q ∘ Quotient.mk (orbitSetoid G X) = f at hq
  apply quotient_factorization_unique (orbitSetoid G X) f
  · simpa [Function.comp_def] using hq
  · exact invariantLift_comp_mk f hf

end ActionQuotient

end StacksPart07Lib
