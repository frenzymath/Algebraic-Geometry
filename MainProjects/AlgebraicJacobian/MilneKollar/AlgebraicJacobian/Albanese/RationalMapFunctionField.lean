/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.Birational.Dominant
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
# Function-field pullback of a rational map

For a rational map `f : X ⤏ Y` out of an integral scheme `X`, Mathlib's
`AlgebraicGeometry.Scheme.RationalMap.fromFunctionField` gives a morphism
`Spec K(X) ⟶ Y` (the restriction of `f` to the generic point). Composing it with
`AlgebraicGeometry.Scheme.stalkClosedPointTo` produces the pullback of germs
`𝒪_{Y, f(η_X)} ⟶ K(X)` at the image of the generic point of `X`.

When `f` is **dominant** and `Y` is irreducible, that image point is the generic
point of `Y`, so the germ pullback becomes a field homomorphism
`K(Y) ⟶ K(X)` — the function-field functoriality `K(Y) → K(X)` that Milne's
rational-map extension leg (`Albanese/CodimOneExtension.lean`) and the
Weil-divisor obstruction (`thm:weil_divisor_obstruction`) both require.

## Main definitions

* `Scheme.RationalMap.stalkPullback` — the germ pullback
  `𝒪_{Y, f(η_X)} ⟶ K(X)` (no dominance needed).
* `Scheme.RationalMap.fromFunctionField_base_eq_genericPoint` — for a dominant
  rational map into an irreducible target, `f(η_X) = η_Y`.
* `Scheme.RationalMap.functionFieldPullback` — the induced field homomorphism
  `K(Y) ⟶ K(X)` for a dominant rational map.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

variable {X Y : Scheme.{u}}

/-- **Germ pullback along a rational map.** For a rational map `f : X ⤏ Y` out of
an integral scheme `X`, the associated morphism `f.fromFunctionField : Spec K(X) ⟶ Y`
induces, by `Scheme.stalkClosedPointTo`, a local ring homomorphism from the germ
of `Y` at the image `f(η_X)` of the generic point of `X` into the function field
`K(X)`. -/
noncomputable def stalkPullback [IsIntegral X] (f : X.RationalMap Y) :
    Y.presheaf.stalk (f.fromFunctionField (closedPoint X.functionField)) ⟶ X.functionField :=
  Scheme.stalkClosedPointTo f.fromFunctionField

/-!
## Dominant refinement

When `f` is **dominant** and `Y` is irreducible, the base point
`f.fromFunctionField (closedPoint K(X))` equals `genericPoint Y`, so `stalkPullback`
becomes a field homomorphism `K(Y) ⟶ K(X)`.
-/

/-- **For a dominant rational map into an irreducible target, the function-field
morphism sends the closed point of `Spec K(X)` to the generic point of `Y`.**

Reducing to a representative partial map `g`, the morphism
`g.fromFunctionField = g.domain.fromSpecStalkOfMem (η_X) ≫ g.hom` sends the closed
point of `Spec 𝒪_{X, η_X} = Spec K(X)` to `g.hom (η_{g.domain})`. The inner point
is the generic point of the domain (checked after applying the open immersion
`g.domain.ι`, using `Opens.fromSpecStalkOfMem_ι` and `fromSpecStalk_closedPoint`),
and a dominant morphism sends the generic point of its (irreducible) source to the
generic point of `Y` (image of a generic point is generic on the dense range, and
generic points are unique in the T₀ space `Y`). -/
theorem fromFunctionField_base_eq_genericPoint [IsIntegral X] [IrreducibleSpace Y]
    (f : X.RationalMap Y) [f.IsDominant] :
    f.fromFunctionField (closedPoint X.functionField) = genericPoint Y := by
  obtain ⟨g, rfl⟩ := f.exists_rep
  haveI : IsDominant g.hom := (PartialMap.isDominant_toRationalMap_iff g).mp ‹_›
  have hη : genericPoint X ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  haveI : Nonempty (g.domain : Type _) := ⟨⟨genericPoint X, hη⟩⟩
  haveI : IsIntegral g.domain.toScheme := inferInstance
  haveI : IrreducibleSpace g.domain.toScheme := inferInstance
  -- reduce the rational-map `fromFunctionField` to the partial-map one, then to the
  -- composite `g.domain.fromSpecStalkOfMem (η_X) hη ≫ g.hom`
  rw [RationalMap.fromFunctionField_toRationalMap]
  have hcomp : PartialMap.fromFunctionField g
      = g.domain.fromSpecStalkOfMem (genericPoint X) hη ≫ g.hom := rfl
  rw [hcomp, Scheme.Hom.comp_apply]
  -- the inner point is the generic point of the domain
  have hp : (g.domain.fromSpecStalkOfMem (genericPoint X) hη) (closedPoint X.functionField)
      = genericPoint g.domain.toScheme := by
    apply (Scheme.Opens.ι g.domain).isOpenEmbedding.injective
    rw [genericPoint_eq_of_isOpenImmersion (Scheme.Opens.ι g.domain),
      ← Scheme.Hom.comp_apply, Opens.fromSpecStalkOfMem_ι]
    exact Scheme.fromSpecStalk_closedPoint
  rw [hp]
  -- a dominant morphism sends the generic point of an irreducible source to `genericPoint Y`
  have himg := (genericPoint_spec g.domain.toScheme).image g.hom.continuous
  rw [Set.image_univ, g.hom.denseRange.closure_range] at himg
  exact himg.eq (genericPoint_spec Y)

/-- **The induced field homomorphism `K(Y) ⟶ K(X)` of a dominant rational map.**

Since `f.fromFunctionField (closedPoint K(X)) = genericPoint Y`
(`fromFunctionField_base_eq_genericPoint`), the germ pullback `stalkPullback` has
source `𝒪_{Y, η_Y} = K(Y)` up to the canonical stalk isomorphism, giving the
function-field functoriality `K(Y) → K(X)` required by the rational-map extension
leg of Milne's Albanese argument. -/
noncomputable def functionFieldPullback [IsIntegral X] [IrreducibleSpace Y]
    (f : X.RationalMap Y) [f.IsDominant] :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr
    (Inseparable.of_eq (fromFunctionField_base_eq_genericPoint f).symm)).hom ≫ f.stalkPullback

end RationalMap

end Scheme

end AlgebraicGeometry
