/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffMap
import AlgebraicJacobian.Picard.DivisorFamilyZarFunctor

/-!
# The chart-typed divisor functor maps into the WIDENED one (R2)

`divFamZarToAffVehicle` (`…AffVehicle.lean`) carries a chart-typed vehicle section to a widened
one at each affine open of a test.  Now that both sides are functors —`divFunctor`
(`DivisorFamilyZarFunctor.lean`) and `divFunctorAff` (`…AffMap.lean`) — the comparison can be
stated where a consumer actually uses it: as a **natural transformation** of presheaves on the
slice over `Spec k`.

## Why this is the shape that matters

A consumer holding a chart-typed section over a general test `T` does not want to know that the
two carriers agree affine-open by affine-open; it wants to substitute the widened functor for the
chart-typed one and keep its restriction maps.  That is exactly naturality, and it is the
statement `DivRepGlobalData`-style clauses (which are equations between *restrictions*) can
consume.

The proof is one application of the widened uniqueness `divFamZarAff.mapVal_eq_of`: the
componentwise image of the chart-typed glued value already has the widened pullback property,
because `DivFamZar.toAff_mapAlgHom` turns each clause of the chart-typed `mapVal_spec` into the
corresponding widened clause.  No gluing is redone.

## The direction, and it is not an omission

Old → new only.  A widened certificate cover is an arbitrary family of affine opens, and by
`informal/spec-dd-r.md` ADDENDUM 3 §2 / ADDENDUM 4 §4.3 there is a straddling divisor at every
genus `≥ 2` that no fixed pair of `P¹` charts can confine — so no natural transformation back can
exist.  That failure is the content of R2 (protection I-0492), not a gap in this file.

## Main declarations

* `AlgebraicGeometry.divFamZarToAffVehicle_map` — the comparison commutes with restriction along
  an arbitrary morphism of test objects.
* `AlgebraicGeometry.divFunctorToAff` — the natural transformation `divFunctor ⟶ divFunctorAff`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}

noncomputable section

/-- **The vehicle comparison commutes with restriction along an arbitrary test morphism.**

Both sides are widened sections over `T'`; by the widened uniqueness of glued values it is enough
that the left-hand one has the widened pullback property, and each of its clauses is the
`toAff`-image of a clause of the chart-typed `divFamZar.mapVal_spec`
(`DivFamZar.toAff_mapAlgHom`). -/
theorem divFamZarToAffVehicle_map {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (s : divFamZar C π n T) :
    divFamZarToAffVehicle C n π (divFamZar.map C π n f s)
      = divFamZarAff.map C n f (divFamZarToAffVehicle C n π s) := by
  refine divFamZarAff.ext fun W => ?_
  rw [divFamZarToAffVehicle_val, divFamZarAff.map_val]
  refine (divFamZarAff.mapVal_eq_of C n f (divFamZarToAffVehicle C n π s) ?_).symm
  intro W₀ hW₀ V hV
  -- `divFamZarToAffVehicle_val` must fire FIRST: the widened value at `V` is only `rfl`-equal to
  -- `(s.1 V).toAff`, and until it is spelled that way the backward rewrite has no `toAff` to
  -- match on the right-hand side.
  rw [divFamZarToAffVehicle_val, ← DivFamZar.toAff_mapAlgHom, ← DivFamZar.toAff_mapAlgHom,
    divFamZar.map_val]
  exact congrArg DivFamZar.toAff (divFamZar.mapVal_spec C π n f s W W₀ hW₀ V hV)

variable (C π n) in
/-- **The comparison of divisor functors**: the chart-typed locally certified divisor functor maps
naturally into the widened one of R2.

This is the form a consumer substitutes: it may replace `divFunctor` by `divFunctorAff` and keep
every restriction equation it had, without re-deriving anything over the widened cover. -/
def divFunctorToAff : divFunctor C π n ⟶ divFunctorAff C n where
  app T := ↾divFamZarToAffVehicle C n π
  naturality {T T'} g := by
    ext s
    exact divFamZarToAffVehicle_map g.unop s

@[simp]
lemma divFunctorToAff_app (T : (Over (Spec (.of k)))ᵒᵖ) (s : divFamZar C π n T.unop) :
    (divFunctorToAff C π n).app T s = divFamZarToAffVehicle C n π s :=
  rfl

end

end AlgebraicGeometry
