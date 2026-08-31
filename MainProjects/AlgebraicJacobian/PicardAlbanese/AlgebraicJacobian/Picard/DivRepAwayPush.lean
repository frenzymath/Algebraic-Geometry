/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAwaySpanGlue

/-!
# Pushing an away cover forward along an algebra map

The `pull_naturality` field of `DivRepAffinePullback` compares the forward map at `A` with
the forward map at `B` along a `k`-algebra map `φ : A →ₐ[k] B`.  The forward map is built
from an atlas factorization over a spanning family `f : Fin m → A`, so naturality needs the
*pushed* family `φ ∘ f : Fin m → B` and the induced comparison of carriers.

This file supplies that transport, at the canonical carriers, over `k`:

* `AlgebraicGeometry.DivFamZar.awayPush` — the induced `k`-algebra map
  `Localization.Away a →ₐ[k] Localization.Away (φ a)`, i.e. mathlib's
  `Localization.awayMap` upgraded over the base field.  Characterized by
  `awayPush_algebraMap`.
* `AlgebraicGeometry.DivFamZar.awayPush_comp_toAlgHom` — the square with the two structure
  maps: pushing forward after restricting to `Localization.Away a` is restricting to
  `Localization.Away (φ a)` after `φ`.  This is the identity that turns naturality of the
  forward map into a statement about the pushed cover.
* `AlgebraicGeometry.DivFamZar.span_range_map_eq_top` — the pushed family still spans, so
  it is again an admissible cover.

Nothing here mentions divisors: it is the localization bookkeeping the naturality field
needs, isolated so that the naturality proof itself reads as a comparison of glued values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace DivFamZar

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-! ## The pushed carrier

**This is mathlib's map, not ours.**  `Localization.awayMapₐ`
(`Mathlib/RingTheory/Localization/Away/Basic.lean`) already gives
`Localization.Away a →ₐ[R] Localization.Away (f a)` for `f : A →ₐ[R] B` over an arbitrary
base ring `R`, which is exactly the transport this lane needs at `R := k`.  An earlier draft
of this file re-derived it from the `RingHom`-level `Localization.awayMap` by supplying
`commutes'` by hand; a fresh-context review caught the duplication.  What remains here is the
naturality square, which mathlib does not state in the `IsScalarTower.toAlgHom` spelling the
`DivFamZar` statements use. -/

/-- **The characterizing property of the pushed carrier map**: on the image of `A`,
`Localization.awayMapₐ φ a` is `φ` followed by the structure map of the pushed carrier. -/
@[simp]
theorem awayMapₐ_algebraMap (φ : A →ₐ[k] B) (a : A) (x : A) :
    Localization.awayMapₐ φ a (algebraMap A (Localization.Away a) x)
      = algebraMap B (Localization.Away (φ a)) (φ x) := by
  simp [Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- **The naturality square of the away carriers**: restricting to `Localization.Away a` and
then pushing forward along `φ` is the same as applying `φ` and then restricting to
`Localization.Away (φ a)`.  This is the identity that converts `pull_naturality` into a
comparison over the pushed cover, and it is the one thing here that mathlib does not already
state — its `awayMapₐ` lemmas are in the `algebraMap A (Localization.Away a)` spelling, while
the `DivFamZar.mapAlgHom` statements consume `IsScalarTower.toAlgHom`. -/
theorem awayMapₐ_comp_toAlgHom (φ : A →ₐ[k] B) (a : A) :
    (Localization.awayMapₐ φ a).comp (IsScalarTower.toAlgHom k A (Localization.Away a))
      = (IsScalarTower.toAlgHom k B (Localization.Away (φ a))).comp φ :=
  AlgHom.ext fun x => awayMapₐ_algebraMap φ a x

/-! ## The pushed cover is a cover -/

/-- **The pushed family still spans**: the image of a spanning family under a ring
homomorphism spans the unit ideal of the target, so an away cover pushes forward to an away
cover. -/
theorem span_range_map_eq_top {ι : Type} (φ : A →ₐ[k] B) (f : ι → A)
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Ideal.span (Set.range fun t => φ (f t)) = ⊤ := by
  have himg : Ideal.map φ.toRingHom (Ideal.span (Set.range f))
      = Ideal.span (Set.range fun t => φ (f t)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [← himg, hspan, Ideal.map_top]

end DivFamZar

end AlgebraicGeometry
