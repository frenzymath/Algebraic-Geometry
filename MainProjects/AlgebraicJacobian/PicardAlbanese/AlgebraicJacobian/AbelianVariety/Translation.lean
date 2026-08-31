/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianData

/-!
# Translation isomorphisms and transport of point-local properties (Wave-5 X2)

Group schemes are homogeneous: right translation by a point is an automorphism, so any
point-local property that holds at one rational point spreads to every rational point.
This file provides the translation isomorphisms and the transport lemmas that the
Wave-5 smoothness lane consumes — S1 (spreading geometric reducedness from the
identity section, recon route α1) and S3 (uniformizing the fibre dimension across the
smooth locus) — plus the `JacobianData` corollaries for `d.J`.

Mathlib's `AlgebraicGeometry/Group/Smooth.lean` performs the same homogeneity dance,
but INLINE inside the `private` lemma `smooth_of_grpObj_of_isAlgClosed` (there are no
reusable standalone lemmas there — checked against the pinned checkout).  Per the
worksheet mandate we therefore re-prove the minimal general forms here instead of
copying the private proof wholesale.

## Contents

* Categorical layer (any cartesian monoidal category, Hom-group calculus):
  `GrpObj.comp_mulRight_hom` / `comp_mulRight_inv` — composing with a right
  translation is Hom-group multiplication; `GrpObj.pointTranslation x y : G ≅ G` — the
  translation `(· ⋅ x⁻¹ y)` carrying the point `x` to the point `y`
  (`comp_pointTranslation_hom`).
* Scheme layer: `pointTranslationIso G x y : G.left ≅ G.left` — the same translation
  as an isomorphism of the underlying scheme of a group scheme `G : Over S`, with its
  structure-morphism compatibility (`pointTranslationIso_hom_comp`) and its action on
  the underlying points (`pointTranslationIso_hom_apply`).
* Transport of point-local properties along automorphisms/open immersions —
  `mem_smoothLocus_iff_of_comp_eq` (membership in the smooth locus),
  `isReduced_stalk_iff_of_isOpenImmersion` (reducedness of the stalk),
  `isIrreducible_preimage_iff_of_isIso` (irreducibility of subsets, in particular of
  open neighbourhoods).
* `JacobianData` corollaries closing the file: `d.pointTranslation`,
  `d.pointTranslationIso`, and the three transport statements specialized to `d.J`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe v₁ u₁ u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.GrpObj

section Categorical

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G] {X : C}

/-- Composing with a right translation is Hom-group multiplication:
`f ≫ (mulRight g).hom = f ⋅ (toUnit X ≫ g)` in the group `X ⟶ G`. -/
theorem comp_mulRight_hom (f : X ⟶ G) (g : 𝟙_ C ⟶ G) :
    f ≫ (mulRight g).hom = f * (toUnit X ≫ g) := by
  rw [mulRight_hom, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, Hom.mul_def]

/-- Composing with the inverse of a right translation divides in the Hom-group:
`f ≫ (mulRight g).inv = f ⋅ (toUnit X ≫ g)⁻¹` in the group `X ⟶ G`. -/
theorem comp_mulRight_inv (f : X ⟶ G) (g : 𝟙_ C ⟶ G) :
    f ≫ (mulRight g).inv = f * (toUnit X ≫ g)⁻¹ := by
  rw [mulRight_inv, comp_lift_assoc, Category.comp_id, ← Category.assoc, comp_toUnit,
    Hom.mul_def, Hom.inv_def, Category.assoc]

variable (G) in
/-- **The translation carrying the point `x` to the point `y`**: the automorphism
`(· ⋅ x⁻¹ y)` of a group object, `mulRight x ⁻¹ ≪≫ mulRight y`.  This is the
homogeneity automorphism mathlib uses inline in `Group/Smooth.lean`, packaged. -/
def pointTranslation (x y : 𝟙_ C ⟶ G) : G ≅ G :=
  (mulRight x).symm ≪≫ mulRight y

/-- The translation `pointTranslation x y` does carry `x` to `y`. -/
@[reassoc (attr := simp)]
theorem comp_pointTranslation_hom (x y : 𝟙_ C ⟶ G) :
    x ≫ (pointTranslation G x y).hom = y := by
  rw [pointTranslation, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, comp_mulRight_inv,
    comp_mulRight_hom, toUnit_unit, Category.id_comp, Category.id_comp, mul_inv_cancel,
    _root_.one_mul]

end Categorical

section Scheme

open AlgebraicGeometry

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- The translation carrying the section `x` to the section `y`, as an isomorphism of
the underlying scheme of the group scheme `G : Over S`. -/
noncomputable def pointTranslationIso (x y : 𝟙_ (Over S) ⟶ G) : G.left ≅ G.left :=
  (Over.forget S).mapIso (pointTranslation G x y)

@[simp]
theorem pointTranslationIso_hom (x y : 𝟙_ (Over S) ⟶ G) :
    (pointTranslationIso G x y).hom = (pointTranslation G x y).hom.left :=
  rfl

@[simp]
theorem pointTranslationIso_inv (x y : 𝟙_ (Over S) ⟶ G) :
    (pointTranslationIso G x y).inv = (pointTranslation G x y).inv.left :=
  rfl

/-- Translations commute with the structure morphism: `pointTranslationIso` is an
automorphism of `G.left` over `S`. -/
@[reassoc (attr := simp)]
theorem pointTranslationIso_hom_comp (x y : 𝟙_ (Over S) ⟶ G) :
    (pointTranslationIso G x y).hom ≫ G.hom = G.hom :=
  Over.w _

/-- The action of `pointTranslationIso G x y` on underlying points: it carries the
points of the section `x` to the points of the section `y`. -/
theorem pointTranslationIso_hom_apply (x y : 𝟙_ (Over S) ⟶ G) (s : S) :
    (pointTranslationIso G x y).hom (x.left s) = y.left s := by
  rw [pointTranslationIso_hom, ← Scheme.Hom.comp_apply, ← Over.comp_left,
    comp_pointTranslation_hom]

end Scheme

end CategoryTheory.GrpObj

namespace AlgebraicGeometry

/-! ## Transport of point-local properties

The three point-local properties the Wave-5 smoothness lane transports along
translations: membership in the smooth locus, reducedness of the stalk, and
irreducibility of (open neighbourhood) subsets.  Stated for general scheme
morphisms/automorphisms — the translation isomorphisms above are the intended
instantiation. -/

section Transport

/-- Membership in the smooth locus of `f` is invariant under any automorphism
commuting with the structure morphism `f` (e.g. a translation of a group scheme). -/
theorem mem_smoothLocus_iff_of_comp_eq {X S : Scheme.{u}} (e : X ⟶ X) [IsOpenImmersion e]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (he : e ≫ f = f) (z : X) :
    e z ∈ f.smoothLocus ↔ z ∈ f.smoothLocus := by
  conv_lhs => rw [← Scheme.Hom.mem_preimage]
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  simp only [he]

/-- Reducedness of the stalk is invariant under (the underlying map of) an open
immersion — in particular under any isomorphism of schemes. -/
theorem isReduced_stalk_iff_of_isOpenImmersion {X Y : Scheme.{u}} (e : X ⟶ Y)
    [IsOpenImmersion e] (z : X) :
    _root_.IsReduced (X.presheaf.stalk z) ↔ _root_.IsReduced (Y.presheaf.stalk (e z)) := by
  constructor
  · intro h
    exact isReduced_of_injective (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv
      (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv.injective
  · intro h
    exact isReduced_of_injective (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv.symm
      (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv.symm.injective

/-- Irreducibility of subsets — in particular of irreducible open neighbourhoods — is
invariant under isomorphisms of schemes (preimage form; combine with
`Scheme.Hom.coe_preimage`/`Scheme.Hom.mem_preimage` for the `Opens` spelling). -/
theorem isIrreducible_preimage_iff_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    (t : Set Y) : IsIrreducible (e ⁻¹' t) ↔ IsIrreducible t := by
  have hcoe : ⇑(Scheme.homeoOfIso (asIso e)) = ⇑e := by
    rw [Scheme.coe_homeoOfIso, asIso_hom]
  constructor
  · intro hi
    have hsurj : Function.Surjective ⇑e := by
      rw [← hcoe]
      exact (Scheme.homeoOfIso (asIso e)).surjective
    have h2 := hi.image ⇑e e.continuous.continuousOn
    rwa [Set.image_preimage_eq t hsurj] at h2
  · intro ht
    refine ht.preimage ?_ ?_
    · rw [← hcoe]
      exact (Scheme.homeoOfIso (asIso e)).isOpenEmbedding
    · have hr : Set.range ⇑e = Set.univ := by
        rw [← hcoe]
        exact (Scheme.homeoOfIso (asIso e)).surjective.range_eq
      rw [hr, Set.inter_univ]
      exact ht.nonempty

end Transport

/-! ## Datum corollaries for `d.J`

The instantiations at the Jacobian datum, closing the Wave-5 X2 brick.  Consumers:
S1 spreads reducedness from the identity section along `d.pointTranslationIso`; S3
uniformizes the fibre dimension across the smooth locus. -/

namespace JacobianData

open CategoryTheory.GrpObj

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- Translation of the Jacobian datum's representing object carrying the `k`-point `x`
to the `k`-point `y`, as an isomorphism in `Over (Spec k)`. -/
noncomputable def pointTranslation (d : JacobianData C)
    (x y : 𝟙_ (Over (Spec (.of k))) ⟶ d.J) : d.J ≅ d.J :=
  letI := d.grpObj
  GrpObj.pointTranslation d.J x y

/-- `d.pointTranslation x y` carries `x` to `y`. -/
@[reassoc (attr := simp)]
theorem comp_pointTranslation_hom (d : JacobianData C)
    (x y : 𝟙_ (Over (Spec (.of k))) ⟶ d.J) :
    x ≫ (d.pointTranslation x y).hom = y :=
  letI := d.grpObj
  GrpObj.comp_pointTranslation_hom x y

/-- Translation of the Jacobian datum's representing object, as an isomorphism of the
underlying scheme `d.J.left`. -/
noncomputable def pointTranslationIso (d : JacobianData C)
    (x y : 𝟙_ (Over (Spec (.of k))) ⟶ d.J) : d.J.left ≅ d.J.left :=
  letI := d.grpObj
  GrpObj.pointTranslationIso d.J x y

/-- Translations of `d.J.left` commute with the structure morphism. -/
@[reassoc (attr := simp)]
theorem pointTranslationIso_hom_comp (d : JacobianData C)
    (x y : 𝟙_ (Over (Spec (.of k))) ⟶ d.J) :
    (d.pointTranslationIso x y).hom ≫ d.J.hom = d.J.hom :=
  letI := d.grpObj
  GrpObj.pointTranslationIso_hom_comp d.J x y

/-- The action of `d.pointTranslationIso x y` on underlying points: it carries the
point of `x` to the point of `y`. -/
theorem pointTranslationIso_hom_apply (d : JacobianData C)
    (x y : 𝟙_ (Over (Spec (.of k))) ⟶ d.J) (s : Spec (.of k)) :
    (d.pointTranslationIso x y).hom (x.left s) = y.left s :=
  letI := d.grpObj
  GrpObj.pointTranslationIso_hom_apply d.J x y s

/-- Membership in the smooth locus of `d.J.hom` is translation-invariant (S3
consumer).  The `LocallyOfFinitePresentation` hypothesis is available from
`letI := d.locallyOfFiniteType` (mathlib upgrades lft to lfp over the Noetherian base
`Spec k`). -/
theorem pointTranslationIso_mem_smoothLocus_iff (d : JacobianData C)
    (x y : 𝟙_ (Over (Spec (.of k))) ⟶ d.J) [LocallyOfFinitePresentation d.J.hom]
    (z : d.J.left) :
    (d.pointTranslationIso x y).hom z ∈ d.J.hom.smoothLocus ↔ z ∈ d.J.hom.smoothLocus :=
  mem_smoothLocus_iff_of_comp_eq _ d.J.hom (d.pointTranslationIso_hom_comp x y) z

/-- Reducedness of the stalks of `d.J` is translation-invariant (S1 consumer). -/
theorem isReduced_stalk_pointTranslationIso_iff (d : JacobianData C)
    (x y : 𝟙_ (Over (Spec (.of k))) ⟶ d.J) (z : d.J.left) :
    _root_.IsReduced (d.J.left.presheaf.stalk z) ↔
      _root_.IsReduced (d.J.left.presheaf.stalk ((d.pointTranslationIso x y).hom z)) :=
  isReduced_stalk_iff_of_isOpenImmersion _ z

/-- Irreducibility of subsets of `d.J.left` — in particular of irreducible open
neighbourhoods — is translation-invariant (S1/S3 consumer). -/
theorem isIrreducible_pointTranslationIso_preimage_iff (d : JacobianData C)
    (x y : 𝟙_ (Over (Spec (.of k))) ⟶ d.J) (t : Set d.J.left) :
    IsIrreducible ((d.pointTranslationIso x y).hom ⁻¹' t) ↔ IsIrreducible t :=
  isIrreducible_preimage_iff_of_isIso _ t

end JacobianData

end AlgebraicGeometry
