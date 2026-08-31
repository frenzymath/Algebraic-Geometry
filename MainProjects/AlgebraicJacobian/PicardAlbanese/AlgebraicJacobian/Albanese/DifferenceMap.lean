/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.RationalMapPrecomp
import AlgebraicJacobian.Albanese.RationalMapProd

/-!
# Milne's difference rational map `Φ = (x, y) ↦ f(x) · f(y)⁻¹`

This file assembles **Sub-step 1** of Milne's Lemma 3.3
(`indeterminacy_pure_codim_one_into_grpScheme`, `Albanese/CodimOneExtension.lean`):
from a rational map `f : X ⤏ G` into a group variety over an algebraically closed
field `k̄`, build the *difference rational map*

  `Φ : X ×_{k̄} X ⤏ G`,   `Φ(x, y) = f(x) · f(y)⁻¹`,

which is the vehicle for reducing the indeterminacy of `f` to a pole-divisor
computation on the nonsingular surface `X ×_{k̄} X`.

The construction glues the two rational-map bricks already in the project:

* `Scheme.RationalMap.precomp` (`Albanese/RationalMapPrecomp.lean`) — precompose
  `f` with the two projections `prᵢ : X ×_{k̄} X ⟶ X`, which are open because
  `X.hom` is smooth (hence its base change `prᵢ` is smooth, flat, locally of finite
  presentation, universally open, an open map);
* `Scheme.RationalMap.prod` (`Albanese/RationalMapProd.lean`) — pair
  `f ∘ pr₁` and `f ∘ pr₂` into `X ×_{k̄} X ⤏ G ×_{k̄} G`;

and then composes on the right with the **group-object difference morphism**
`GrpObj.diff G = (g, h) ↦ g · h⁻¹ : G ⊗ G ⟶ G`, whose underlying scheme morphism
`(GrpObj.diff G).left : G ×_{k̄} G ⟶ G` is the honest group law `m ∘ (id × inv)`.

The pairing `prod` requires the source `X ×_{k̄} X` to be integral; this is passed
as the hypothesis `[IsIntegral (pullback X.hom X.hom)]`. The caller supplies it via
the project lemma `isReduced_of_smooth_of_isAlgClosed` (self-product is smooth over
`k̄`, hence reduced) together with `GeometricallyIrreducible.irreducibleSpace` — the
`isIntegral_pullback_self` recipe is spelled out in the module note below and lives
in `CodimOneExtension.lean`'s cone (it depends on the standard-smooth chart machinery
there, so it is not restated here to keep this file a Mathlib-only leaf).

## Main definitions

* `CategoryTheory.GrpObj.diff` — the division morphism `G ⊗ G ⟶ G` of a group
  object in any cartesian-monoidal category.
* `AlgebraicGeometry.grpObjDiffLeft` — its underlying scheme morphism, typed as
  `pullback G.hom G.hom ⟶ G.left`.
* `AlgebraicGeometry.Scheme.RationalMap.differenceRationalMap` — Milne's
  `Φ : X ×_{k̄} X ⤏ G`.

## Main results

* `AlgebraicGeometry.isOpenMap_pullback_fst_self` / `..._snd_self` — the two
  projections of the self-product are open maps.
* `AlgebraicGeometry.Scheme.RationalMap.differenceRationalMap_compHom_over` — the
  difference map is a `k̄`-rational map (`Φ.compHom G.hom = (pr₁ ≫ X.hom).toRat`).

Sub-steps 2 (`(x, x) ∈ Dom Φ ↔ x ∈ Dom f`) and 4b (diagonal codim-1 Krull bound)
remain; they consume `differenceRationalMap` built here.
-/

set_option autoImplicit false

universe u

open CategoryTheory CartesianMonoidalCategory MonoidalCategory Limits TopologicalSpace
open scoped CategoryTheory.MonObj

namespace CategoryTheory.GrpObj

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

/-- **Difference / division morphism of a group object.** For a group object `G`
in a cartesian-monoidal category, `GrpObj.diff G = fst / snd : G ⊗ G ⟶ G` is the
morphism `(g, h) ↦ g · h⁻¹`, i.e. the group law composed with inversion on the
second factor. There is no ready-made such morphism in mathlib (`GrpObj.conj` and
`GrpObj.commutator` are the only prebuilt `G ⊗ G ⟶ G` maps), so we build it from
the hom-set group structure `CategoryTheory.MonObj.Hom.group`. -/
noncomputable def diff (G : C) [GrpObj G] : G ⊗ G ⟶ G :=
  fst G G / snd G G

/-- **Reconstruction identity `(a · b⁻¹) · b = a` for `T`-points of a group object.**
Pairing `a` and `b` into `G ⊗ G`, applying the difference `diff G = fst / snd`
(which sends `(a, b) ↦ a · b⁻¹`), pairing the result again with `b`, and multiplying
recovers `a`. This is the group-theoretic heart of Milne Lemma 3.3 Sub-step 2, the
formula `f(x) = Φ(x, u) · f(u)`: with `a = f(x)`, `b = f(u)`, the difference map value
`Φ = a · b⁻¹` recombines with `b` to give `a`. -/
lemma lift_diff_lift_mul {T : C} (G : C) [GrpObj G] (a b : T ⟶ G) :
    lift (lift a b ≫ diff G) b ≫ μ = a := by
  rw [diff, GrpObj.comp_div, lift_fst, lift_snd]
  exact div_mul_cancel a b

end CategoryTheory.GrpObj

namespace AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

/-- The underlying scheme morphism `(GrpObj.diff G).left : G ×_{k̄} G ⟶ G` of the
group-object difference morphism, typed directly against `pullback G.hom G.hom`
(definitionally `(G ⊗ G).left` via `Over.tensorObj_left`). This coercion avoids the
`(G ⊗ G).left` vs `pullback G.hom G.hom` transparency wall when right-composing a
rational map with target `pullback G.hom G.hom`. -/
noncomputable def grpObjDiffLeft (G : Over (Spec (.of kbar))) [GrpObj G] :
    pullback G.hom G.hom ⟶ G.left :=
  (GrpObj.diff G).left

/-- The difference morphism sits over `Spec k̄`: `grpObjDiffLeft G ≫ G.hom =
pr₁ ≫ G.hom`. This is the reduction that turns `Φ.compHom G.hom` into the structure
morphism of `X ×_{k̄} X`; it is `Over.w` of `GrpObj.diff G`. -/
lemma grpObjDiffLeft_comp_hom (G : Over (Spec (.of kbar))) [GrpObj G] :
    grpObjDiffLeft G ≫ G.hom = pullback.fst G.hom G.hom ≫ G.hom :=
  Over.w (GrpObj.diff G)

/-- The underlying scheme morphism `μ.left : G ×_{k̄} G ⟶ G` of the group law of `G`,
typed against `pullback G.hom G.hom` (definitionally `(G ⊗ G).left`), mirroring
`grpObjDiffLeft`. -/
noncomputable def grpObjMulLeft (G : Over (Spec (.of kbar))) [GrpObj G] :
    pullback G.hom G.hom ⟶ G.left :=
  (μ : G ⊗ G ⟶ G).left

/-- **Scheme-level reconstruction identity.** For two `k̄`-morphisms `A, B : T ⟶ G`
sharing the structure map `t` (`A ≫ G.hom = B ≫ G.hom = t`), pairing them, applying
the group difference `A · B⁻¹`, re-pairing with `B` and multiplying recovers `A`:
`m ∘ ⟨(A · B⁻¹), B⟩ = A`. This is `CategoryTheory.GrpObj.lift_diff_lift_mul`
transported through `Over.forget` (`(-).left` is a functor sending
`CartesianMonoidalCategory.lift`/`fst` to `pullback.lift`/`pullback.fst`); it is the
scheme incarnation of Milne's `f(x) = Φ(x, u) · f(u)`. -/
lemma pullback_lift_diff_lift_mul (G : Over (Spec (.of kbar))) [GrpObj G]
    {T : Scheme.{u}} (t : T ⟶ Spec (.of kbar)) (A B : T ⟶ G.left)
    (hA : A ≫ G.hom = t) (hB : B ≫ G.hom = t) :
    pullback.lift (pullback.lift A B (hA.trans hB.symm) ≫ grpObjDiffLeft G) B
        (by rw [Category.assoc, grpObjDiffLeft_comp_hom, ← Category.assoc,
          pullback.lift_fst, hA, hB]) ≫ grpObjMulLeft G
      = A := by
  have key := congrArg (fun m : Over.mk t ⟶ G => m.left)
    (GrpObj.lift_diff_lift_mul G (Over.homMk A hA) (Over.homMk B hB))
  simp only [Over.comp_left, Over.lift_left, Over.homMk_left] at key
  exact key

/-- The first projection `X ×_{k̄} X ⟶ X` is an open map (it is smooth, being a
base change of the smooth structure morphism, hence universally open). -/
theorem isOpenMap_pullback_fst_self (X : Over (Spec (.of kbar))) [Smooth X.hom] :
    IsOpenMap (pullback.fst X.hom X.hom).base :=
  (pullback.fst X.hom X.hom).isOpenMap

/-- The second projection `X ×_{k̄} X ⟶ X` is an open map. -/
theorem isOpenMap_pullback_snd_self (X : Over (Spec (.of kbar))) [Smooth X.hom] :
    IsOpenMap (pullback.snd X.hom X.hom).base :=
  (pullback.snd X.hom X.hom).isOpenMap

namespace Scheme.RationalMap

/-- **Right-composition with a morphism only enlarges the domain of definition.**
For a rational map `F : X ⤏ Y` and a morphism `g : Y ⟶ Z`, every point at which
`F` is defined is also a point at which `F.compHom g` is defined: a partial-map
representative `F₀` of `F` yields the representative `F₀.compHom g` of
`F.compHom g` with the *same* domain (post-composing with a total morphism never
destroys definedness). This is Milne Lemma 3.3, Sub-step 1: the difference map
`Φ = (prod ⋯).compHom (diff_G)` is defined wherever the pairing `prod ⋯` is. -/
theorem le_domain_compHom {X Y Z : Scheme.{u}} (F : X.RationalMap Y) (g : Y ⟶ Z) :
    F.domain ≤ (F.compHom g).domain := by
  intro x hx
  rw [RationalMap.mem_domain] at hx ⊢
  obtain ⟨F₀, hxF₀, hF₀⟩ := hx
  exact ⟨F₀.compHom g, hxF₀, by rw [RationalMap.compHom_toRationalMap, hF₀]⟩

variable {X G : Over (Spec (.of kbar))}
  [Smooth X.hom]
  [GrpObj G] [LocallyOfFiniteType G.hom]

/-- **Milne's difference rational map** `Φ = (x, y) ↦ f(x) · f(y)⁻¹`.

For a rational map `f : X ⤏ G` into a group variety over `k̄`, with `f` defined
over `k̄` (`f.compHom G.hom = X.hom.toRationalMap`), the difference map
`Φ : X ×_{k̄} X ⤏ G` is `((f ∘ pr₁) ×_{k̄} (f ∘ pr₂)) ∘ (g, h ↦ g · h⁻¹)`.

The self-product must be integral for the pairing `prod` to be well-defined; this
is the hypothesis `[IsIntegral (pullback X.hom X.hom)]`. -/
noncomputable def differenceRationalMap
    (f : X.left.RationalMap G.left)
    (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] :
    (pullback X.hom X.hom).RationalMap G.left :=
  (RationalMap.prod (pullback.fst X.hom X.hom ≫ X.hom) G.hom G.hom
      (f.precomp (pullback.fst X.hom X.hom) (isOpenMap_pullback_fst_self X))
      (f.precomp (pullback.snd X.hom X.hom) (isOpenMap_pullback_snd_self X))
      (by rw [RationalMap.precomp_compHom, hover, RationalMap.precomp_hom_toRationalMap])
      (by rw [RationalMap.precomp_compHom, hover, RationalMap.precomp_hom_toRationalMap,
        pullback.condition])).compHom (grpObjDiffLeft G)

/-- **The difference map is a `k̄`-rational map.** Right-composing `Φ` with the
structure morphism `G.hom` recovers the structure morphism `pr₁ ≫ X.hom` of
`X ×_{k̄} X`. -/
theorem differenceRationalMap_compHom_over
    (f : X.left.RationalMap G.left)
    (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] :
    (differenceRationalMap f hover).compHom G.hom
      = (pullback.fst X.hom X.hom ≫ X.hom).toRationalMap := by
  simp only [differenceRationalMap]
  rw [RationalMap.compHom_compHom, grpObjDiffLeft_comp_hom]
  exact RationalMap.prod_compHom_over _ _ _ _ _ _ _

/-- The explicit pairing partial map `U ×_{k̄} U → G ×_{k̄} G` of Milne's
construction (`(x, y) ↦ (φ_U(x), φ_U(y))`), built from the maximal representative
`φ_U = f.toPartialMap` of `f` over the common domain `Dom(f∘pr₁) ⊓ Dom(f∘pr₂)`. It
is the partial-map witness that `prod` is defined on `Dom(f) ×_{k̄} Dom(f)`. -/
noncomputable def precompDiffPairing
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsReduced X.left] [G.left.IsSeparated] :
    (pullback X.hom X.hom).PartialMap (pullback G.hom G.hom) where
  domain := (f.toPartialMap.precomp (pullback.fst X.hom X.hom)
      (isOpenMap_pullback_fst_self X)).domain
    ⊓ (f.toPartialMap.precomp (pullback.snd X.hom X.hom)
      (isOpenMap_pullback_snd_self X)).domain
  dense_domain := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact (f.toPartialMap.precomp (pullback.fst X.hom X.hom)
        (isOpenMap_pullback_fst_self X)).dense_domain.inter_of_isOpen_left
      (f.toPartialMap.precomp (pullback.snd X.hom X.hom)
        (isOpenMap_pullback_snd_self X)).dense_domain
      (f.toPartialMap.precomp (pullback.fst X.hom X.hom)
        (isOpenMap_pullback_fst_self X)).domain.isOpen
  hom := pullback.lift
    ((pullback X.hom X.hom).homOfLE inf_le_left
      ≫ (f.toPartialMap.precomp (pullback.fst X.hom X.hom)
        (isOpenMap_pullback_fst_self X)).hom)
    ((pullback X.hom X.hom).homOfLE inf_le_right
      ≫ (f.toPartialMap.precomp (pullback.snd X.hom X.hom)
        (isOpenMap_pullback_snd_self X)).hom)
    (by
      -- Over-`Spec k̄` structure making *both* projections `S`-morphisms (they agree
      -- after `X.hom` by `pullback.condition`), so the precomposed legs inherit
      -- over-ness from `f.toPartialMap` without ever unfolding `precomp`.
      letI : X.left.Over (Spec (.of kbar)) := ⟨X.hom⟩
      letI : G.left.Over (Spec (.of kbar)) := ⟨G.hom⟩
      letI : (pullback X.hom X.hom).Over (Spec (.of kbar)) :=
        ⟨pullback.fst X.hom X.hom ≫ X.hom⟩
      haveI : f.IsOver (Spec (.of kbar)) := RationalMap.isOver_iff.mpr hover
      haveI : (pullback.fst X.hom X.hom).IsOver (Spec (.of kbar)) := ⟨rfl⟩
      haveI : (pullback.snd X.hom X.hom).IsOver (Spec (.of kbar)) := ⟨pullback.condition.symm⟩
      have e₁ : (f.toPartialMap.precomp (pullback.fst X.hom X.hom)
            (isOpenMap_pullback_fst_self X)).hom ≫ G.hom
          = (f.toPartialMap.precomp (pullback.fst X.hom X.hom)
            (isOpenMap_pullback_fst_self X)).domain.ι ≫ (pullback.fst X.hom X.hom ≫ X.hom) :=
        (PartialMap.isOver_iff (S := Spec (.of kbar))).mp inferInstance
      have e₂ : (f.toPartialMap.precomp (pullback.snd X.hom X.hom)
            (isOpenMap_pullback_snd_self X)).hom ≫ G.hom
          = (f.toPartialMap.precomp (pullback.snd X.hom X.hom)
            (isOpenMap_pullback_snd_self X)).domain.ι ≫ (pullback.fst X.hom X.hom ≫ X.hom) :=
        (PartialMap.isOver_iff (S := Spec (.of kbar))).mp inferInstance
      rw [Category.assoc, Category.assoc, e₁, e₂]
      simp only [← Category.assoc, Scheme.homOfLE_ι])

omit [GrpObj G] in
/-- The explicit pairing partial map represents Milne's `prod (f∘pr₁, f∘pr₂)`. Both
are `k̄`-rational maps out of the integral scheme `X ×_{k̄} X`, so it suffices to
match their induced morphisms `Spec K(X × X) ⟶ G ×_{k̄} G`: on each `pullback`
factor the pairing's generic-point morphism restricts to `(f ∘ prᵢ)`'s. -/
theorem precompDiffPairing_toRationalMap
    (f : X.left.RationalMap G.left)
    (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] [IsReduced X.left] [G.left.IsSeparated] :
    (precompDiffPairing f hover).toRationalMap
      = RationalMap.prod (pullback.fst X.hom X.hom ≫ X.hom) G.hom G.hom
        (f.precomp (pullback.fst X.hom X.hom) (isOpenMap_pullback_fst_self X))
        (f.precomp (pullback.snd X.hom X.hom) (isOpenMap_pullback_snd_self X))
        (by rw [RationalMap.precomp_compHom, hover, RationalMap.precomp_hom_toRationalMap])
        (by rw [RationalMap.precomp_compHom, hover, RationalMap.precomp_hom_toRationalMap,
          pullback.condition]) := by
  refine RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [RationalMap.fromFunctionField_toRationalMap, prod_fromFunctionField]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    have hrhs : (f.precomp (pullback.fst X.hom X.hom)
          (isOpenMap_pullback_fst_self X)).fromFunctionField
        = (f.toPartialMap.precomp (pullback.fst X.hom X.hom)
          (isOpenMap_pullback_fst_self X)).fromFunctionField := by
      rw [← RationalMap.fromFunctionField_toRationalMap, RationalMap.precomp_toRationalMap,
        f.toRationalMap_toPartialMap]
    rw [hrhs, ← PartialMap.fromFunctionField_restrict
      (f.toPartialMap.precomp (pullback.fst X.hom X.hom) (isOpenMap_pullback_fst_self X))
      (precompDiffPairing f hover).dense_domain inf_le_left]
    simp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem,
      PartialMap.restrict_hom, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _
  · rw [pullback.lift_snd]
    have hrhs : (f.precomp (pullback.snd X.hom X.hom)
          (isOpenMap_pullback_snd_self X)).fromFunctionField
        = (f.toPartialMap.precomp (pullback.snd X.hom X.hom)
          (isOpenMap_pullback_snd_self X)).fromFunctionField := by
      rw [← RationalMap.fromFunctionField_toRationalMap, RationalMap.precomp_toRationalMap,
        f.toRationalMap_toPartialMap]
    rw [hrhs, ← PartialMap.fromFunctionField_restrict
      (f.toPartialMap.precomp (pullback.snd X.hom X.hom) (isOpenMap_pullback_snd_self X))
      (precompDiffPairing f hover).dense_domain inf_le_right]
    simp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem,
      PartialMap.restrict_hom, Category.assoc]
    congr 1
    exact pullback.lift_snd _ _ _

/-- **Milne Lemma 3.3, Sub-step 1 (domain lower bound / Sub-step 2 easy direction).**
The difference rational map `Φ` is defined on `Dom(f) ×_{k̄} Dom(f)`: every point
`p` of `X ×_{k̄} X` projecting into `Dom(f)` under both projections lies in
`Dom(Φ)`. This is Milne's "clearly `Φ` is defined at `(x, x)` if `f` is defined at
`x`" — indeed at every `(x, y)` with `x, y ∈ Dom(f)` — made precise: a maximal
representative `(U, φ_U)` of `f` (`f.toPartialMap`) supplies the honest morphism
`U ×_{k̄} U → G` of Milne's construction, which represents `Φ`. -/
theorem le_domain_differenceRationalMap
    (f : X.left.RationalMap G.left)
    (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] [IsReduced X.left] [G.left.IsSeparated] :
    (pullback.fst X.hom X.hom ⁻¹ᵁ f.domain) ⊓ (pullback.snd X.hom X.hom ⁻¹ᵁ f.domain)
      ≤ (differenceRationalMap f hover).domain := by
  -- Right-composition with `diff_G` only enlarges the domain, reducing to `prod`;
  -- the explicit pairing `precompDiffPairing` is a representative defined on all of
  -- `Dom(f) ×_{k̄} Dom(f)`.
  refine le_trans ?_ (le_domain_compHom _ (grpObjDiffLeft G))
  intro p hp
  rw [RationalMap.mem_domain]
  exact ⟨precompDiffPairing f hover, hp, precompDiffPairing_toRationalMap f hover⟩

/-- **Milne Lemma 3.3, Sub-step 2 reconstruction identity.** `f ∘ pr₁ = m ∘ ⟨Φ, f ∘ pr₂⟩`:
the difference map `Φ = f(x)·f(y)⁻¹` recombined with the second factor `f ∘ pr₂` via the
group law `m` recovers the first factor `f ∘ pr₁`. This is Milne's formula
`f(x) = Φ(x, u) · f(u)`, made a rational-map identity on `X ×_{k̄} X` via the
function-field group law (`pullback_lift_diff_lift_mul`). -/
theorem reconstruct_precomp_fst
    (f : X.left.RationalMap G.left)
    (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] :
    (RationalMap.prod (pullback.fst X.hom X.hom ≫ X.hom) G.hom G.hom
        (differenceRationalMap f hover)
        (f.precomp (pullback.snd X.hom X.hom) (isOpenMap_pullback_snd_self X))
        (differenceRationalMap_compHom_over f hover)
        (by rw [RationalMap.precomp_compHom, hover, RationalMap.precomp_hom_toRationalMap,
          pullback.condition])).compHom (grpObjMulLeft G)
      = f.precomp (pullback.fst X.hom X.hom) (isOpenMap_pullback_fst_self X) := by
  refine RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [RationalMap.fromFunctionField_compHom, RationalMap.prod_fromFunctionField]
  simp only [differenceRationalMap, RationalMap.fromFunctionField_compHom,
    RationalMap.prod_fromFunctionField]
  exact pullback_lift_diff_lift_mul G _
    ((f.precomp (pullback.fst X.hom X.hom) (isOpenMap_pullback_fst_self X)).fromFunctionField)
    ((f.precomp (pullback.snd X.hom X.hom) (isOpenMap_pullback_snd_self X)).fromFunctionField)
    (RationalMap.fromFunctionField_comp_structure _ (pullback.fst X.hom X.hom ≫ X.hom) G.hom
      (by rw [RationalMap.precomp_compHom, hover, RationalMap.precomp_hom_toRationalMap]))
    (RationalMap.fromFunctionField_comp_structure _ (pullback.fst X.hom X.hom ≫ X.hom) G.hom
      (by rw [RationalMap.precomp_compHom, hover, RationalMap.precomp_hom_toRationalMap,
        pullback.condition]))

/-- **Milne Lemma 3.3, Sub-step 2 (hard direction, algebraic content).** `f ∘ pr₁` is
defined wherever `Φ` is defined *and* `f ∘ pr₂` is defined: at a point `p` with
`Φ` defined and `pr₂ p ∈ Dom(f)`, the reconstruction `f(x) = Φ(x, u) · f(u)` exhibits
`f ∘ pr₁` as regular. Concretely `Dom(Φ) ⊓ pr₂⁻¹(Dom f) ≤ Dom(f ∘ pr₁)`.

This is the group-theoretic half of Milne's converse (`(x, x) ∈ Dom Φ ⟹ x ∈ Dom f`);
it remains to combine it with the topological input — openness of `Dom(Φ)` and
irreducibility of the fibre `X_{κ(x)}` (geometric irreducibility) to produce a suitable
`u`, plus the smooth-descent reflection `Dom(f ∘ pr₁) ⊆ pr₁⁻¹(Dom f)`. -/
theorem le_domain_precomp_fst_of_difference
    (f : X.left.RationalMap G.left)
    (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] [IsReduced X.left] [G.left.IsSeparated] :
    (differenceRationalMap f hover).domain ⊓ (pullback.snd X.hom X.hom ⁻¹ᵁ f.domain)
      ≤ (f.precomp (pullback.fst X.hom X.hom) (isOpenMap_pullback_fst_self X)).domain := by
  rw [← reconstruct_precomp_fst f hover]
  refine le_trans ?_ (le_domain_compHom _ (grpObjMulLeft G))
  refine le_trans (inf_le_inf_left _ (RationalMap.le_domain_precomp f
    (pullback.snd X.hom X.hom) (isOpenMap_pullback_snd_self X))) ?_
  exact RationalMap.le_domain_prod _ _ _ _ _ _ _

end Scheme.RationalMap

end AlgebraicGeometry
