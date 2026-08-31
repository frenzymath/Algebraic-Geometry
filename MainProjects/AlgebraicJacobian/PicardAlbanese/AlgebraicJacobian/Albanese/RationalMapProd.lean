/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Pairing of two rational maps into a fibre product

Mathlib's `AlgebraicGeometry.Scheme.RationalMap` API provides `compHom`
(right-composition with a morphism) but no way to *pair* two rational maps out of
a common source into a fibre product. For Milne's difference-map construction
`Φ = m ∘ (f × f) : X × X ⤏ G` (Milne, *Abelian Varieties*, Lemma 3.3) one needs
exactly this pairing: given `f ∘ pr₁` and `f ∘ pr₂ : X × X ⤏ G`, assemble the map
`X × X ⤏ G ×_{k̄} G` whose two projections recover the factors, so that it can be
right-composed with the group law `G ×_{k̄} G → G`.

The naive `PartialMap`-level pairing via `pullback.lift` does **not** descend to
rational maps through `Quotient.map₂`: `RationalMap.IsOver S` guarantees only *one*
over-`S` representative, not that an arbitrary pair of representatives is
simultaneously over `S`, so the compatibility hypothesis fails. Instead we use the
function-field correspondence: over an integral source `X`, a rational map
`X ⤏ Y` over `S` is the same datum as an `S`-morphism `Spec K(X) ⟶ Y`
(`AlgebraicGeometry.Scheme.RationalMap.ofFunctionField` /
`equivFunctionField`), and morphisms out of the single scheme `Spec K(X)` pair
freely by `pullback.lift`.

To stay clear of `Over`-typeclass diamonds on the pullback target we work with
explicit structure morphisms `sX : X ⟶ S`, `sY : Y ⟶ S`, `sZ : Z ⟶ S` (matching
mathlib's `equivFunctionField`), and phrase the over-`S` datum as the equation
`a.compHom sY = sX.toRationalMap`. In Milne's setting `S = Spec k̄`,
`sX = X.hom`, `sY = sZ = G.hom`, and the target `pullback G.hom G.hom` is
definitionally `(G ⊗ G).left` (`CategoryTheory.Over.tensorObj_left`), so the group
law `(GrpObj.mul).left : (G ⊗ G).left ⟶ G.left` composes on the right directly.

## Main definitions

* `Scheme.RationalMap.prod` — the pairing `X ⤏ pullback sY sZ` of `a : X ⤏ Y` and
  `b : X ⤏ Z`, both over `S`.

## Main results

* `Scheme.RationalMap.fromFunctionField_compHom` — the function-field morphism of a
  right-composition is the composite of function-field morphisms.
* `Scheme.RationalMap.prod_compHom_fst` / `prod_compHom_snd` — the two projections of
  the pairing recover the original rational maps.
* `Scheme.RationalMap.prod_compHom_over` — the pairing is again over `S`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

variable {T X Y Z S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **Associativity of right-composition.** Composing on the right by `g` and then `h`
is composing by `g ≫ h`. -/
@[simp]
lemma compHom_compHom (f : X ⤏ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (f.compHom g).compHom h = f.compHom (g ≫ h) := by
  obtain ⟨f, rfl⟩ := f.exists_rep
  simp only [← compHom_toRationalMap]
  refine congrArg PartialMap.toRationalMap (PartialMap.ext _ _ rfl ?_)
  simp only [PartialMap.compHom_hom, Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp,
    Category.assoc]

/-- **Function-field functoriality of right-composition.** For a rational map
`f : X ⤏ Y` out of an irreducible scheme and a morphism `g : Y ⟶ Z`, the associated
morphism `Spec K(X) ⟶ Z` of `f.compHom g` is `f.fromFunctionField ≫ g`. -/
@[simp]
lemma fromFunctionField_compHom [IrreducibleSpace X] (f : X ⤏ Y) (g : Y ⟶ Z) :
    (f.compHom g).fromFunctionField = f.fromFunctionField ≫ g := by
  obtain ⟨f, rfl⟩ := f.exists_rep
  rw [← compHom_toRationalMap, fromFunctionField_toRationalMap, fromFunctionField_toRationalMap]
  exact PartialMap.fromSpecStalkOfMem_compHom f g _ _

/-- The function-field morphism of an over-`S` rational map factors the structure
morphism: if `a.compHom sY = sX.toRationalMap`, then
`a.fromFunctionField ≫ sY = X.fromSpecStalk η ≫ sX`. -/
lemma fromFunctionField_comp_structure [IsIntegral X] (a : X ⤏ Y) (sX : X ⟶ S)
    (sY : Y ⟶ S) (ha : a.compHom sY = sX.toRationalMap) :
    a.fromFunctionField ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX := by
  rw [← fromFunctionField_compHom, ha]
  exact PartialMap.fromSpecStalkOfMem_toPartialMap sX _

/-- **Pairing of two rational maps into a fibre product.** For rational maps
`a : X ⤏ Y` and `b : X ⤏ Z` out of an integral scheme `X`, both defined over `S`
(encoded as `a.compHom sY = sX.toRationalMap`, resp. for `b`), the pairing
`a.prod b : X ⤏ pullback sY sZ` is the rational map whose function-field morphism is
`pullback.lift a.fromFunctionField b.fromFunctionField`.

Milne's difference map is `(f.precomp pr₁).prod (f.precomp pr₂)` followed by
right-composition with the group law of `G`. -/
noncomputable def prod (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
    (a : X ⤏ Y) (b : X ⤏ Z)
    (ha : a.compHom sY = sX.toRationalMap) (hb : b.compHom sZ = sX.toRationalMap) :
    X ⤏ pullback sY sZ :=
  haveI : LocallyOfFiniteType (pullback.fst sY sZ ≫ sY) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  ofFunctionField sX (pullback.fst sY sZ ≫ sY)
    (pullback.lift a.fromFunctionField b.fromFunctionField
      ((fromFunctionField_comp_structure a sX sY ha).trans
        (fromFunctionField_comp_structure b sX sZ hb).symm))
    (by rw [pullback.lift_fst_assoc]; exact fromFunctionField_comp_structure a sX sY ha)

/-- The function-field morphism of the pairing is the `pullback.lift` of the factors'
function-field morphisms. -/
@[simp]
lemma prod_fromFunctionField (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
    (a : X ⤏ Y) (b : X ⤏ Z)
    (ha : a.compHom sY = sX.toRationalMap) (hb : b.compHom sZ = sX.toRationalMap) :
    (prod sX sY sZ a b ha hb).fromFunctionField
      = pullback.lift a.fromFunctionField b.fromFunctionField
        ((fromFunctionField_comp_structure a sX sY ha).trans
          (fromFunctionField_comp_structure b sX sZ hb).symm) := by
  haveI : LocallyOfFiniteType (pullback.fst sY sZ ≫ sY) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  exact fromFunctionField_ofFunctionField _ _ _ _

/-- **First projection of the pairing.** Right-composing the pairing with
`pullback.fst` recovers `a`. -/
lemma prod_compHom_fst (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
    (a : X ⤏ Y) (b : X ⤏ Z)
    (ha : a.compHom sY = sX.toRationalMap) (hb : b.compHom sZ = sX.toRationalMap) :
    (prod sX sY sZ a b ha hb).compHom (pullback.fst sY sZ) = a :=
  eq_of_fromFunctionField_eq _ _ (by
    rw [fromFunctionField_compHom, prod_fromFunctionField, pullback.lift_fst])

/-- **Second projection of the pairing.** Right-composing the pairing with
`pullback.snd` recovers `b`. -/
lemma prod_compHom_snd (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
    (a : X ⤏ Y) (b : X ⤏ Z)
    (ha : a.compHom sY = sX.toRationalMap) (hb : b.compHom sZ = sX.toRationalMap) :
    (prod sX sY sZ a b ha hb).compHom (pullback.snd sY sZ) = b :=
  eq_of_fromFunctionField_eq _ _ (by
    rw [fromFunctionField_compHom, prod_fromFunctionField, pullback.lift_snd])

/-- **The pairing is over `S`.** Right-composing with the structure morphism
`pullback.fst sY sZ ≫ sY` of the fibre product recovers `sX.toRationalMap`. -/
lemma prod_compHom_over (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
    (a : X ⤏ Y) (b : X ⤏ Z)
    (ha : a.compHom sY = sX.toRationalMap) (hb : b.compHom sZ = sX.toRationalMap) :
    (prod sX sY sZ a b ha hb).compHom (pullback.fst sY sZ ≫ sY) = sX.toRationalMap := by
  rw [← compHom_compHom, prod_compHom_fst, ha]

/-- **Explicit pairing partial map on the common domain.** The maximal representatives
`a.toPartialMap`, `b.toPartialMap` (defined on `a.domain`, `b.domain`) are both
`S`-morphisms, hence pair via `pullback.lift` into a partial map
`X ⤏ pullback sY sZ` defined on all of `a.domain ⊓ b.domain`. This is the honest
representative witnessing that `prod` is defined wherever *both* factors are. -/
noncomputable def pairPartialMap (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
    [IsReduced X] [Y.IsSeparated] [Z.IsSeparated] [S.IsSeparated]
    (a : X ⤏ Y) (b : X ⤏ Z)
    (ha : a.compHom sY = sX.toRationalMap) (hb : b.compHom sZ = sX.toRationalMap) :
    X.PartialMap (pullback sY sZ) where
  domain := a.toPartialMap.domain ⊓ b.toPartialMap.domain
  dense_domain := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact a.toPartialMap.dense_domain.inter_of_isOpen_left b.toPartialMap.dense_domain
      a.toPartialMap.domain.isOpen
  hom := by
    letI : X.Over S := ⟨sX⟩
    letI : Y.Over S := ⟨sY⟩
    letI : Z.Over S := ⟨sZ⟩
    haveI : a.IsOver S := RationalMap.isOver_iff.mpr ha
    haveI : b.IsOver S := RationalMap.isOver_iff.mpr hb
    have ea : a.toPartialMap.hom ≫ sY = a.toPartialMap.domain.ι ≫ sX :=
      (PartialMap.isOver_iff (S := S)).mp inferInstance
    have eb : b.toPartialMap.hom ≫ sZ = b.toPartialMap.domain.ι ≫ sX :=
      (PartialMap.isOver_iff (S := S)).mp inferInstance
    exact pullback.lift
      (X.homOfLE inf_le_left ≫ a.toPartialMap.hom)
      (X.homOfLE inf_le_right ≫ b.toPartialMap.hom)
      (by
        rw [Category.assoc, Category.assoc, ea, eb, ← Category.assoc, ← Category.assoc,
          Scheme.homOfLE_ι, Scheme.homOfLE_ι])

/-- The explicit pairing partial map represents `prod`. Both are `S`-rational maps out
of the integral `X`, so it suffices to match their function-field morphisms
`Spec K(X) ⟶ pullback sY sZ`: on each `pullback` factor the pairing's generic-point
morphism restricts to `a.fromFunctionField`, resp. `b.fromFunctionField`. -/
lemma pairPartialMap_toRationalMap (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
    [IsReduced X] [Y.IsSeparated] [Z.IsSeparated] [S.IsSeparated]
    (a : X ⤏ Y) (b : X ⤏ Z)
    (ha : a.compHom sY = sX.toRationalMap) (hb : b.compHom sZ = sX.toRationalMap) :
    (pairPartialMap sX sY sZ a b ha hb).toRationalMap = prod sX sY sZ a b ha hb := by
  refine eq_of_fromFunctionField_eq _ _ ?_
  rw [fromFunctionField_toRationalMap, prod_fromFunctionField]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    have hfst : (pairPartialMap sX sY sZ a b ha hb).fromFunctionField ≫ pullback.fst sY sZ
        = a.fromFunctionField := by
      rw [show a.fromFunctionField
          = (a.toPartialMap.restrict _ (pairPartialMap sX sY sZ a b ha hb).dense_domain
              inf_le_left).fromFunctionField from ?_]
      · simp only [pairPartialMap, PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem,
          PartialMap.restrict_hom, Category.assoc]
        congr 1
        exact pullback.lift_fst _ _ _
      · rw [PartialMap.fromFunctionField_restrict,
          ← RationalMap.fromFunctionField_toRationalMap, a.toRationalMap_toPartialMap]
    exact hfst
  · rw [pullback.lift_snd]
    have hsnd : (pairPartialMap sX sY sZ a b ha hb).fromFunctionField ≫ pullback.snd sY sZ
        = b.fromFunctionField := by
      rw [show b.fromFunctionField
          = (b.toPartialMap.restrict _ (pairPartialMap sX sY sZ a b ha hb).dense_domain
              inf_le_right).fromFunctionField from ?_]
      · simp only [pairPartialMap, PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem,
          PartialMap.restrict_hom, Category.assoc]
        congr 1
        exact pullback.lift_snd _ _ _
      · rw [PartialMap.fromFunctionField_restrict,
          ← RationalMap.fromFunctionField_toRationalMap, b.toRationalMap_toPartialMap]
    exact hsnd

/-- **`prod` is defined wherever both factors are.** The pairing `a.prod b` of two
`S`-rational maps out of an integral, reduced source is defined on the intersection
`a.domain ⊓ b.domain` of the two domains of definition. This is the domain lower
bound that Milne Lemma 3.3 needs for the pairing step (it feeds the reconstruction
`f ∘ pr₁ = m ∘ ⟨Φ, f ∘ pr₂⟩`). -/
theorem le_domain_prod (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
    [IsReduced X] [Y.IsSeparated] [Z.IsSeparated] [S.IsSeparated]
    (a : X ⤏ Y) (b : X ⤏ Z)
    (ha : a.compHom sY = sX.toRationalMap) (hb : b.compHom sZ = sX.toRationalMap) :
    a.domain ⊓ b.domain ≤ (prod sX sY sZ a b ha hb).domain := by
  rw [← pairPartialMap_toRationalMap sX sY sZ a b ha hb]
  exact (pairPartialMap sX sY sZ a b ha hb).le_domain_toRationalMap

end RationalMap

end Scheme

end AlgebraicGeometry
