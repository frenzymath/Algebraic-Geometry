/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.Grp.Adjunctions

/-!
# The units presheaf of a scheme

For a scheme `X`, this file defines the presheaf `𝒪_X^*` of unit groups of the structure
sheaf on the small Zariski site (the poset `X.Opens`), valued in `CommGrpCat`, together
with the element-level interface used by the Čech `H¹` layer of the Picard group:

* restriction of a unit section along `V ≤ U` is `Units.map` of the ring-level restriction;
* pullback of a unit section along a morphism of schemes, packaged as
  `Scheme.Hom.unitsAppLE` (the unit-group analogue of `Scheme.Hom.appLE`), with the same
  composition/restriction calculus as `appLE`.

## Main declarations

* `AlgebraicGeometry.Scheme.unitsPresheaf`: the units presheaf
  `X.presheaf ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units`, a functor
  `(X.Opens)ᵒᵖ ⥤ CommGrpCat.{u}`.
* `AlgebraicGeometry.Scheme.unitsPresheaf_map_apply`: restriction of unit sections,
  element form.
* `AlgebraicGeometry.Scheme.Hom.unitsAppLE`: for `f : X ⟶ Y`, `V : Y.Opens`,
  `U ≤ f ⁻¹ᵁ V`, the group homomorphism `Γ(Y, V)ˣ →* Γ(X, U)ˣ`.
* `AlgebraicGeometry.Scheme.Hom.unitsAppLE_map`, `Scheme.Hom.map_unitsAppLE`,
  `Scheme.Hom.unitsAppLE_unitsAppLE`, `Scheme.id_unitsAppLE`: the calculus mirroring
  `appLE_map`, `map_appLE`, `appLE_comp_appLE` and `id_app` at the unit level.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace Scheme

variable {X Y Z : Scheme.{u}}

/-- The units presheaf `𝒪_X^*` of a scheme `X`, on its small Zariski site: the composite
of the structure presheaf with the units functor, valued in commutative groups.

This is `abbrev` (reducible): the Čech layer constantly mixes sections typed through
`unitsPresheaf.obj` with sections typed `Γ(X, U)ˣ`, and rewriting across that boundary
requires the two to agree at instance transparency. -/
abbrev unitsPresheaf (X : Scheme.{u}) : (X.Opens)ᵒᵖ ⥤ CommGrpCat.{u} :=
  X.presheaf ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

lemma unitsPresheaf_obj (U : (X.Opens)ᵒᵖ) :
    X.unitsPresheaf.obj U = CommGrpCat.of Γ(X, unop U)ˣ :=
  rfl

lemma unitsPresheaf_map {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V) :
    X.unitsPresheaf.map i = CommGrpCat.ofHom (Units.map (X.presheaf.map i).hom) :=
  rfl

/-- Element form of the restriction maps of the units presheaf. This is the interface
through which cocycle computations reach the `Units` API. -/
@[simp]
lemma unitsPresheaf_map_apply {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V) (u : Γ(X, unop U)ˣ) :
    X.unitsPresheaf.map i u = Units.map (X.presheaf.map i).hom u :=
  rfl

/-- The composite with the forgetful functor to `GrpCat` (the shape consumed by
`CategoryTheory.PresheafOfGroups.OneCocycle`), element form. -/
@[simp]
lemma unitsPresheaf_forget₂_map_apply {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V) (u : Γ(X, unop U)ˣ) :
    (X.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat).map i u
      = Units.map (X.presheaf.map i).hom u :=
  rfl

/-- Split form of `unitsPresheaf_forget₂_map_apply`: after `Functor.comp_map` has fired,
the restriction maps appear as `(forget₂ _ _).map (X.unitsPresheaf.map i)`. -/
@[simp]
lemma forget₂_map_unitsPresheaf_map_apply {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V)
    (u : Γ(X, unop U)ˣ) :
    (forget₂ CommGrpCat GrpCat).map (X.unitsPresheaf.map i) u
      = Units.map (X.presheaf.map i).hom u :=
  rfl

namespace Hom

variable (f : X ⟶ Y) {V V' : Y.Opens} {U U' : X.Opens}

/-- The action of a morphism of schemes on unit sections: for `V : Y.Opens` and
`U ≤ f ⁻¹ᵁ V`, the induced group homomorphism `Γ(Y, V)ˣ →* Γ(X, U)ˣ`. This is the
unit-group analogue of `Scheme.Hom.appLE` and is treated as a suffix in lemma names. -/
def unitsAppLE (f : X.Hom Y) (V : Y.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    Γ(Y, V)ˣ →* Γ(X, U)ˣ :=
  Units.map (f.appLE V U e).hom

@[simp]
lemma coe_unitsAppLE (e : U ≤ f ⁻¹ᵁ V) (u : Γ(Y, V)ˣ) :
    (f.unitsAppLE V U e u : Γ(X, U)) = f.appLE V U e u :=
  rfl

/-- Restriction after pullback: the unit-level mirror of `Scheme.Hom.appLE_map`. -/
@[simp]
lemma unitsAppLE_map (e : U ≤ f ⁻¹ᵁ V) (i : op U ⟶ op U') (u : Γ(Y, V)ˣ) :
    Units.map (X.presheaf.map i).hom (f.unitsAppLE V U e u)
      = f.unitsAppLE V U' (i.unop.le.trans e) u := by
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, coe_unitsAppLE]
  rw [← CommRingCat.comp_apply, appLE_map]

/-- Pullback after restriction: the unit-level mirror of `Scheme.Hom.map_appLE`. -/
@[simp]
lemma map_unitsAppLE (e : U ≤ f ⁻¹ᵁ V) (i : op V' ⟶ op V) (u : Γ(Y, V')ˣ) :
    f.unitsAppLE V U e (Units.map (Y.presheaf.map i).hom u)
      = f.unitsAppLE V' U (e.trans ((TopologicalSpace.Opens.map f.base).map i.unop).le) u := by
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, coe_unitsAppLE]
  rw [← CommRingCat.comp_apply, map_appLE]

end Hom

/-- Pullback along a composite: the unit-level mirror of `Scheme.appLE_comp_appLE`. -/
@[simp]
lemma unitsAppLE_unitsAppLE (f : X ⟶ Y) (g : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    {U : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ W) (e₂ : U ≤ f ⁻¹ᵁ V) (u : Γ(Z, W)ˣ) :
    f.unitsAppLE V U e₂ (g.unitsAppLE W V e₁ u)
      = (f ≫ g).unitsAppLE W U
          (e₂.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE e₁)).le) u := by
  ext
  simp only [Hom.coe_unitsAppLE]
  rw [← CommRingCat.comp_apply, Hom.appLE_comp_appLE]

/-- Pullback along the identity is restriction: the unit-level mirror of `Scheme.id_app`. -/
lemma id_unitsAppLE {U V : X.Opens} (e : U ≤ V) (u : Γ(X, V)ˣ) :
    (𝟙 X : X ⟶ X).unitsAppLE V U e u
      = Units.map (X.presheaf.map (homOfLE e).op).hom u :=
  rfl

end Scheme

end AlgebraicGeometry
