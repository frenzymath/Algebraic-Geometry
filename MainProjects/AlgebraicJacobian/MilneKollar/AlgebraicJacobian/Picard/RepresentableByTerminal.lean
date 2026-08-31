/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# A presheaf with unique values is represented by the terminal object

This file supplies the categorical bridge that was missing between "a presheaf
`F : Cᵒᵖ ⥤ Type v` has exactly one element at every test object" and
"`F` is representable by the terminal object of `C`".

Mathlib `v4.31` has `CategoryTheory.Limits.hasTerminal_of_unique` (a `C`-object
`X` with `Unique (Y ⟶ X)` for every `Y` is terminal) and
`CategoryTheory.Limits.IsTerminal.ofUnique`, but **not** the presheaf-side
statement: from `Nonempty (F.obj T)` and `Subsingleton (F.obj T)` at every `T`,
build the natural bijection `(X ⟶ Y) ≃ F.obj (op X)` that
`Functor.RepresentableBy` is. Both sides of that bijection are singletons —
the left because `Y` is terminal, the right by hypothesis — so the bijection
and its naturality are `Subsingleton.elim`. Verified absent by search over
mathlib and both projects; the nearest hits (`hasTerminal_of_unique`,
`isTerminalEquivUnique`) are about representing objects, not represented
presheaves.

## Why it is worth a named declaration

`Functor.RepresentableBy` is *data* (a chosen `Equiv` per object, plus a
naturality equation), not a `Prop`. So even when a presheaf is manifestly a
subterminal-and-inhabited functor, producing the `RepresentableBy` witness
still requires building that `Equiv` by hand at every use site. This file does
it once, at full categorical generality, so a consumer that has proved
`Nonempty` and `Subsingleton` pointwise gets the representability witness by a
single application — no `Equiv` plumbing.

## The intended consumer

`Picard/DivFamilyZero.lean` proves `Nonempty ((DivFunctorDeg π 0).obj (op T))`
for every `π` and test `T` (`DivFunctorDeg.instNonemptyObjZero`, the empty
divisor). If a lane proves the matching
`Subsingleton ((DivFunctorDeg π 0).obj (op T))` — that the empty divisor is the
*only* relative effective divisor of degree `0` — then
`representableByTerminal` yields
`(DivFunctorDeg π 0).RepresentableBy (Over.mk (𝟙 S))` immediately, the first
genuine `RepresentableBy` producer on the AJC divisor side. That `Subsingleton`
is real content (a fact about `fiberDeg`, a `finrank` with a junk value at
infinite dimension), and it is **not** discharged here; this file supplies only
the categorical interface it plugs into.

Everything here is about an arbitrary category and carries no algebraic-geometry
hypothesis; nothing closes any `sorry`.
-/

universe w v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

/-- **A presheaf that is pointwise nonempty and subsingleton is represented by
any terminal object.**

The representing map `(X ⟶ Y) ≃ F.obj (op X)` sends every morphism to the
unique element of `F.obj (op X)` and back to the unique morphism `X ⟶ Y` (which
exists because `Y` is terminal). Both round trips, and the naturality square,
are forced by the two `Subsingleton`s.

This is the presheaf-side companion of `Limits.hasTerminal_of_unique`, which is
absent from mathlib `v4.31`. -/
noncomputable def representableByTerminal (F : Cᵒᵖ ⥤ Type w) {Y : C}
    (hY : Limits.IsTerminal Y)
    (hne : ∀ T : Cᵒᵖ, Nonempty (F.obj T)) (hss : ∀ T : Cᵒᵖ, Subsingleton (F.obj T)) :
    F.RepresentableBy Y where
  homEquiv {X} := by
    haveI := hne (Opposite.op X)
    haveI := hss (Opposite.op X)
    exact
      { toFun := fun _ => Classical.arbitrary _
        invFun := fun _ => hY.from X
        left_inv := fun _ => hY.hom_ext _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  homEquiv_comp {X X'} f g := by
    haveI := hss (Opposite.op X)
    exact Subsingleton.elim _ _

/-- **The `Unique`-packaged form of `representableByTerminal`.** When the values
of `F` are literally `Unique` (a single default plus subsingleton), the same
terminal object represents it. -/
noncomputable def representableByTerminal_of_unique (F : Cᵒᵖ ⥤ Type w) {Y : C}
    (hY : Limits.IsTerminal Y) (h : ∀ T : Cᵒᵖ, Unique (F.obj T)) :
    F.RepresentableBy Y :=
  representableByTerminal F hY (fun T => ⟨(h T).default⟩) (fun T => (h T).instSubsingleton)

/-- **Existence corollary**: a pointwise nonempty-and-subsingleton presheaf is
representable (forgets the chosen terminal object). -/
theorem isRepresentable_of_terminal (F : Cᵒᵖ ⥤ Type w) {Y : C}
    (hY : Limits.IsTerminal Y)
    (hne : ∀ T : Cᵒᵖ, Nonempty (F.obj T)) (hss : ∀ T : Cᵒᵖ, Subsingleton (F.obj T)) :
    F.IsRepresentable :=
  (representableByTerminal F hY hne hss).isRepresentable

end CategoryTheory.Functor
