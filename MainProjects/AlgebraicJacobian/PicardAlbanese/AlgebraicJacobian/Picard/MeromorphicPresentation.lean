/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorClass
import AlgebraicJacobian.RiemannRoch.DivisorSheafZero

/-!
# Meromorphic presentations of Čech Picard classes

On an integral scheme `X`, every nonempty open contains the generic point `η`, and
sections embed into the function field `K(X)` by taking germs at `η`. This file exploits
this to present every Čech Picard class (`AlgebraicJacobian.Picard.Pic`) *meromorphically*:
by a pointed cover, a unit cocycle on it, and rational functions `f x ∈ K(X)ˣ`, one per
member, whose ratios `f x / f y` are the germs at `η` of the cocycle values. All cochain
comparisons downstream then happen inside `K(X)ˣ`, where gluing is literal equality of
field elements.

## Main declarations

* `AlgebraicGeometry.Scheme.germGenericUnits`: the embedding `Γ(X, U)ˣ →* K(X)ˣ` of unit
  sections over an open containing `η` into the units of the function field, with its
  restriction-invariance (`germGenericUnits_unitsRestrict`) and injectivity
  (`germGenericUnits_injective`, on an integral scheme).
* `AlgebraicGeometry.Scheme.PointedCover.genericPoint_mem_opens`: on an irreducible
  scheme every member of a pointed cover contains the generic point.
* `AlgebraicGeometry.Scheme.MeromorphicPresentation`: the presentation structure — a
  pointed cover, a unit cocycle, and elements `elem x ∈ K(X)ˣ` with
  `elem x / elem y = germ_η (cocycle x y)` — and its Picard class
  `MeromorphicPresentation.picClass`.
* `AlgebraicGeometry.Scheme.MeromorphicPresentation.ofCocycle`: the base-index
  construction presenting any unit cocycle: `elem x := germ_η (cocycle x η)`, using the
  generic point itself as the (canonical) base index.
* `AlgebraicGeometry.Scheme.exists_meromorphicPresentation`: every Čech Picard class of
  an integral scheme admits a meromorphic presentation (the W1 keystone).
* `AlgebraicGeometry.Scheme.LocalEquations.presentation`: the meromorphic presentation of
  a local-equation system — the germs at `η` of its regular equations — with the same
  Picard class (`LocalEquations.presentation_picClass`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X]

/-! ## Unit sections as units of the function field -/

/-- The embedding of unit sections over an open containing the generic point into the
units of the function field: the germ-at-`η` map on units. -/
noncomputable def germGenericUnits {U : X.Opens} (hηU : genericPoint X ∈ U) :
    Γ(X, U)ˣ →* X.functionFieldˣ :=
  Units.map (X.presheaf.germ U (genericPoint X) hηU).hom

/-- The underlying rational function of an embedded unit section is the germ at `η` of
its underlying section. -/
@[simp]
lemma germGenericUnits_val {U : X.Opens} (hηU : genericPoint X ∈ U) (u : Γ(X, U)ˣ) :
    (germGenericUnits hηU u : X.functionField)
      = (X.presheaf.germ U (genericPoint X) hηU).hom (u : Γ(X, U)) :=
  rfl

/-- Embedding a restricted unit section gives the embedding of the original unit
section: germs at `η` are restriction-invariant. -/
lemma germGenericUnits_unitsRestrict {U W : X.Opens} (h : W ≤ U)
    (hηW : genericPoint X ∈ W) (u : Γ(X, U)ˣ) :
    germGenericUnits hηW (X.unitsRestrict h u) = germGenericUnits (h hηW) u := by
  refine Units.ext ?_
  rw [germGenericUnits_val, germGenericUnits_val, Units.coe_map, MonoidHom.coe_coe]
  exact X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) hηW (u : Γ(X, U))

/-- On an integral scheme the embedding of unit sections into `K(X)ˣ` is injective:
sections are determined by their germs at the generic point. -/
lemma germGenericUnits_injective {U : X.Opens}
    (hηU : genericPoint X ∈ U) :
    Function.Injective (germGenericUnits (X := X) hηU) := by
  intro u v huv
  refine Units.ext (germ_injective_of_isIntegral X (genericPoint X) hηU ?_)
  exact congrArg Units.val huv

/-! ## Pointed covers and the generic point -/

namespace PointedCover

variable (𝒰 : X.PointedCover)

/-- On an irreducible scheme, every member of a pointed cover contains the generic
point: it contains its point, so it is nonempty. -/
lemma genericPoint_mem_opens (x : X) : genericPoint X ∈ 𝒰.opens x :=
  genericPoint_mem_of_nonempty ⟨x, 𝒰.mem_opens x⟩

/-- On an irreducible scheme, every pairwise overlap of a pointed cover contains the
generic point. -/
lemma genericPoint_mem_inf (x y : X) : genericPoint X ∈ 𝒰.opens x ⊓ 𝒰.opens y :=
  ⟨𝒰.genericPoint_mem_opens x, 𝒰.genericPoint_mem_opens y⟩

end PointedCover

omit [IsIntegral X] in
/-- Restriction of a unit Čech `H¹` class along a refinement, on a cocycle
representative: the class of the restricted cocycle. -/
lemma unitsRes_class {𝒰 𝒲 : X.PointedCover} (h : 𝒲 ≤ 𝒰) (γ : X.unitsCocycle 𝒰) :
    unitsRes h γ.class = (γ.res fun x ↦ homOfLE (h x)).class :=
  rfl

/-! ## Meromorphic presentations -/

/-- A **meromorphic presentation** of a Čech Picard class on an integral scheme: a
pointed cover, a unit cocycle on it, and rational functions `elem x ∈ K(X)ˣ`, one per
member, whose ratios are the germs at `η` of the cocycle values:
`elem x / elem y = germ_η (cocycle x y)`.

The elements `elem` are a meromorphic trivialization of the class `picClass` of the
cocycle; their zero/pole orders cut out its divisor
(`AlgebraicJacobian.Picard.PresentationDivisor`). -/
structure MeromorphicPresentation (X : Scheme.{u}) [IsIntegral X] : Type u where
  /-- The pointed cover carrying the presented cocycle. -/
  cover : X.PointedCover
  /-- The presented unit Čech 1-cocycle. -/
  cocycle : X.unitsCocycle cover
  /-- The meromorphic trivialization: one unit of the function field per member. -/
  elem : X → X.functionFieldˣ
  /-- The ratio property: on each pair, the ratio of the trivializing elements is the
  germ at `η` of the cocycle value. -/
  ratio : ∀ x y : X, elem x * (elem y)⁻¹
    = germGenericUnits (cover.genericPoint_mem_inf x y) (unitsEvInf cocycle x y)

namespace MeromorphicPresentation

/-- The Čech Picard class presented by a meromorphic presentation. -/
def picClass (P : X.MeromorphicPresentation) : X.CechPic :=
  CechPic.mk P.cover P.cocycle.class

/-- The base-index construction: any unit cocycle `γ` on a pointed cover is presented
meromorphically by `elem x := germ_η (γ x η)`, taking the generic point itself as the
canonical base index (all overlaps contain `η`, so the cocycle identity for the triple
`(x, y, η)` becomes the ratio property in `K(X)ˣ`). -/
noncomputable def ofCocycle (𝒰 : X.PointedCover) (γ : X.unitsCocycle 𝒰) :
    X.MeromorphicPresentation where
  cover := 𝒰
  cocycle := γ
  elem x := germGenericUnits (𝒰.genericPoint_mem_inf x (genericPoint X))
    (unitsEvInf γ x (genericPoint X))
  ratio x y := by
    have hηT : genericPoint X
        ∈ 𝒰.opens x ⊓ 𝒰.opens y ⊓ 𝒰.opens (genericPoint X) :=
      ⟨𝒰.genericPoint_mem_inf x y, 𝒰.genericPoint_mem_opens (genericPoint X)⟩
    have key := congrArg (germGenericUnits hηT)
      (unitsEvInf_trans γ x y (genericPoint X))
    rw [map_mul, germGenericUnits_unitsRestrict, germGenericUnits_unitsRestrict,
      germGenericUnits_unitsRestrict] at key
    rw [mul_inv_eq_iff_eq_mul]
    exact key.symm

@[simp]
lemma ofCocycle_picClass (𝒰 : X.PointedCover) (γ : X.unitsCocycle 𝒰) :
    (ofCocycle 𝒰 γ).picClass = CechPic.mk 𝒰 γ.class :=
  rfl

end MeromorphicPresentation

/-- **Existence of meromorphic presentations** (the W1 keystone): every Čech Picard
class of an integral scheme is the class of a meromorphic presentation. -/
theorem exists_meromorphicPresentation (L : X.CechPic) :
    ∃ P : X.MeromorphicPresentation, P.picClass = L := by
  induction L using CechPic.ind with | _ 𝒰 a =>
  induction a using Quot.ind with | _ γ =>
  exact ⟨MeromorphicPresentation.ofCocycle 𝒰 γ, rfl⟩

/-! ## The presentation of a local-equation system -/

namespace LocalEquations

variable (E : X.LocalEquations)

/-- The germ at `η` of a local equation is a nonzero rational function: the equation is
regular, so its germ at the generic point is a nonzerodivisor of the field `K(X)`. -/
lemma germGeneric_eqn_ne_zero (x : X) :
    (X.presheaf.germ (E.cover.opens x) (genericPoint X)
        (E.cover.genericPoint_mem_opens x)).hom (E.eqn x) ≠ (0 : X.functionField) := by
  have h : (X.presheaf.germ (E.cover.opens x) (genericPoint X)
        (E.cover.genericPoint_mem_opens x)).hom (E.eqn x)
      ∈ nonZeroDivisors X.functionField :=
    E.regular x (genericPoint X) (E.cover.genericPoint_mem_opens x)
  exact mem_nonZeroDivisors_iff_ne_zero.mp h

/-- The meromorphic presentation of a local-equation system: the trivializing elements
are the germs at `η` of the regular equations, and the presented cocycle is the cocycle
of transition units. The ratio property is the defining equation `eqn x = g x y · eqn y`
pushed to the generic point. -/
noncomputable def presentation : X.MeromorphicPresentation where
  cover := E.cover
  cocycle := E.unitsCocycle
  elem x := Units.mk0 _ (E.germGeneric_eqn_ne_zero x)
  ratio x y := by
    refine Units.ext ?_
    have key := congrArg
      (X.presheaf.germ (E.cover.opens x ⊓ E.cover.opens y) (genericPoint X)
        (E.cover.genericPoint_mem_inf x y)).hom (E.eqn_restrict_eq x y)
    rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply] at key
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0,
      unitsCocycle_evInf, germGenericUnits_val,
      mul_inv_eq_iff_eq_mul₀ (E.germGeneric_eqn_ne_zero y)]
    exact key

/-- The presentation of a local-equation system presents its Picard class. -/
@[simp]
lemma presentation_picClass : E.presentation.picClass = E.picClass :=
  rfl

@[simp]
lemma presentation_cover : E.presentation.cover = E.cover :=
  rfl

@[simp]
lemma presentation_cocycle : E.presentation.cocycle = E.unitsCocycle :=
  rfl

/-- The trivializing element of the presentation of a local-equation system is the germ
at `η` of its equation. -/
lemma presentation_elem_val (x : X) :
    (E.presentation.elem x : X.functionField)
      = (X.presheaf.germ (E.cover.opens x) (genericPoint X)
          (E.cover.genericPoint_mem_opens x)).hom (E.eqn x) :=
  rfl

end LocalEquations

end Scheme

end AlgebraicGeometry
