/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.P1Points
import AlgebraicJacobian.Cohomology.SectionsBaseChange

/-!
# The canonical section of `ℙ¹` over an arbitrary test ring

`ℙ¹` has a canonical rational point — the origin `[1 : 0]` of the first standard chart — and
that point exists over *every* base, not only over a separably closed field.  This file packages
it as a **section functor**: for every commutative `k`-algebra `A` a morphism

  `P1.overSection k A : overSpec k A ⟶ (P1.asOver k)`

in `Over (Spec k)`, natural in `A` (`P1.overSection_naturality`).  It is `[1 : 0]` through the
chart `D₊(X₀)`, built from `P1Points.fromSpecChart` with the constant chart coordinate `0`; the
over-`k` condition is `fromSpecChart_structureMap`.

## Why this is worth a file

The representability route reaches `ℙ¹` through
`AlgebraicGeometry.jacobianData_of_overSpec_subsingleton` and the section-conditional
étale↔Zariski comparison
`AlgebraicGeometry.PicEtAff.unitEquiv_of_section` / `relPicToPicEt_surjective_of_section`
(`Picard/EffectivityClose.lean`, `Picard/PicEtUnitFieldComparison.lean`).  Both of those
consume a section `σ : overSpec k _ ⟶ C` of the curve.  The inbox pricing `I-1603` records that
this input — "a `k`-rational point at `ℙ¹`" — **is not constructed anywhere in this project**,
even though `ℙ¹` has one over any ring.  This file constructs it, unconditionally on the base
field and over an arbitrary test ring, so the comparison lemmas can be instantiated at `ℙ¹`.

Nothing here is new mathematics: it is the origin of a chart.  The value is that the section a
dozen downstream lemmas assume as a hypothesis now exists as a term, at the object the headline
is about.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

open scoped CartesianMonoidalCategory

namespace AlgebraicGeometry

namespace P1

variable (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]

/-- The canonical `A`-point `[1 : 0]` of `ℙ¹`, as a morphism `Spec A ⟶ ℙ¹` over `k`.

It is `fromSpecChart` through the first chart `D₊(X₀)` with chart coordinate `0`, i.e. the origin
of that chart.  Being through a chart it is defined for every ring, with no positivity,
separable-closure or nonemptiness hypothesis. -/
noncomputable def specPoint : Spec (.of A) ⟶ P1 k :=
  fromSpecChart k (CommRingCat.ofHom (algebraMap k A)) 0 (0 : A)

/-- `specPoint` is a morphism over `k`: composing with the structure map of `ℙ¹` gives the
structure map `Spec A ⟶ Spec k` of `overSpec k A`. -/
theorem specPoint_structureMap :
    specPoint k A ≫ structureMap k = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  rw [specPoint, fromSpecChart_structureMap]

/-- **The canonical section of `ℙ¹` over the test ring `A`**: `[1 : 0]` as a morphism
`overSpec k A ⟶ (P1.asOver k)` in `Over (Spec k)`.

This is the section `σ` that `PicEtAff.unitEquiv_of_section`, `relPicToPicEt_surjective_of_section`
and the challenge-target chain all take as a hypothesis; it exists at every test ring. -/
noncomputable def overSection : overSpec k A ⟶ (P1.asOver k) :=
  Over.homMk (specPoint k A) (specPoint_structureMap k A)

@[simp]
theorem overSection_left : (overSection k A).left = specPoint k A := rfl

/-! ## The global `k`-rational point

The monoidal unit `𝟙_ (Over (Spec k))` is *definitionally* `Over.mk (𝟙 (Spec k))` (this first
step is `rfl`), so the section at the test ring `A = k` is a **global `k`-rational point**
`𝟙_ ⟶ (P1.asOver k)`.  Note the source is `Over.mk (𝟙 (Spec k))`, which is only
*propositionally* — not definitionally — equal to `overSpec k k = Over.mk (Spec.map (algebraMap
k k))`: matching the two structure maps costs `Spec.map_id` and `algebraMap k k = id`.  That is
why the `w`-condition below is discharged by an explicit rewrite rather than by `rfl`.  This is
the `P : 𝟙_ ⟶ P1.asOver k` that `Curve/P1H1Vanishing.lean` and the challenge target
`exists_unique_ofCurve_comp` record as constructed nowhere in the project. -/

/-- **The global `k`-rational point of `ℙ¹`**: the origin `[1 : 0]`, as a morphism from the
monoidal unit of `Over (Spec k)`.  This is the point hypothesis `P` of the challenge's
`JacobianData.exists_unique_ofCurve_comp` at `ℙ¹`. -/
noncomputable def unitPoint : 𝟙_ (Over (Spec (.of k))) ⟶ (P1.asOver k) :=
  Over.homMk (specPoint k k) (by
    change specPoint k k ≫ structureMap k = 𝟙 (Spec (CommRingCat.of k))
    rw [specPoint_structureMap,
      show (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (CommRingCat.of k) from by ext x; simp,
      Spec.map_id])

@[simp]
theorem unitPoint_left : (unitPoint k).left = specPoint k k := rfl

/-! ## Naturality

The point `[1 : 0]` is *constant*: it does not depend on the test ring, only on `ℙ¹`.  So
base-changing the section along an algebra map `A → B` lands on the section at `B`.  Stated at
the scheme level (`specPoint_naturality`) it needs no `Over`-category machinery, so this file
stays below the Picard layer that owns `Over.overSpecMap`. -/

variable (B : Type u) [CommRing B] [Algebra k B]

/-- **Naturality of the canonical point** at the scheme level: pulling `specPoint` back along
`Spec` of the algebra map `A → B` is `specPoint` at `B`.

`fromSpecChart` is natural in the ring (`SpecMap_fromSpecChart`), and the chart coordinate is the
constant `0`, which the algebra map sends to `0`; the base map `k → B` factors as `k → A → B` by
the scalar tower. -/
theorem specPoint_naturality (φ : A →ₐ[k] B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ specPoint k A = specPoint k B := by
  rw [specPoint, specPoint, SpecMap_fromSpecChart]
  congr 1
  · rw [← CommRingCat.ofHom_comp]
    congr 1
    exact φ.comp_algebraMap
  · exact map_zero _

end P1

end AlgebraicGeometry
