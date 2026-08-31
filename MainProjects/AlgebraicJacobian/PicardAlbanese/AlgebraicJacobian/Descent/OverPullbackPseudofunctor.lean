/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The pullback pseudofunctor of over categories

This module equips `X \mapsto Over X` with its contravariant pullback pseudofunctor.
-/

universe v u

namespace CategoryTheory

open Limits Functor

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback functors along equal morphisms are canonically isomorphic. -/
noncomputable def Over.pullbackCongrIso {X Y : C} {f g : X ⟶ Y} (h : f = g) :
    Over.pullback f ≅ Over.pullback g :=
  NatIso.ofComponents (fun T =>
    Over.isoMk (pullback.congrHom rfl h) (by simp))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit comparison `pullbackCongrIso` is the equality transport of
pullback functors. -/
lemma Over.pullbackCongrIso_eq_eqToIso {X Y : C} {f g : X ⟶ Y} (h : f = g) :
    Over.pullbackCongrIso h =
      eqToIso (congrArg (fun q : X ⟶ Y => Over.pullback q) h) := by
  subst h
  ext T
  simp [Over.pullbackCongrIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison isomorphisms `Over.pullbackComp` satisfy associativity. -/
lemma Over.pullback_associativity
    {X₀ X₁ X₂ X₃ : C} (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂) :
    (Over.pullbackComp h (g ≫ f)).hom ≫
      whiskerRight (Over.pullbackComp g f).hom (Over.pullback h) ≫
        (associator _ _ _).hom ≫
          whiskerLeft (Over.pullback f) (Over.pullbackComp h g).inv ≫
            (Over.pullbackComp (h ≫ g) f).inv =
      eqToHom (congrArg
        (fun q : X₃ ⟶ X₀ => Over.pullback q)
        (Category.assoc h g f).symm) := by
  change _ = (eqToIso (congrArg
    (fun q : X₃ ⟶ X₀ => Over.pullback q)
    (Category.assoc h g f).symm)).hom
  rw [← congrArg Iso.hom
    (Over.pullbackCongrIso_eq_eqToIso (Category.assoc h g f).symm)]
  ext T
  apply pullback.hom_ext
  · simp [Over.pullbackComp, Over.pullbackCongrIso, conjugateEquiv, mateEquiv]
  · simp [Over.pullbackComp, Over.pullbackCongrIso, conjugateEquiv, mateEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback comparison is compatible with a right identity on the base map. -/
lemma Over.pullback_comp_id {X Y : C} (f : X ⟶ Y) :
    (Over.pullbackComp f (𝟙 Y)).hom ≫
      whiskerRight Over.pullbackId.hom (Over.pullback f) ≫
        (Over.pullback f).leftUnitor.hom =
      eqToHom (congrArg
        (fun q : X ⟶ Y => Over.pullback q)
        (Category.comp_id f)) := by
  change _ = (eqToIso (congrArg
    (fun q : X ⟶ Y => Over.pullback q)
    (Category.comp_id f))).hom
  rw [← congrArg Iso.hom
    (Over.pullbackCongrIso_eq_eqToIso (Category.comp_id f))]
  ext T
  apply pullback.hom_ext
  · simp [Over.pullbackComp, Over.pullbackId, Over.pullbackCongrIso,
      conjugateEquiv, mateEquiv]
  · simp [Over.pullbackComp, Over.pullbackId, Over.pullbackCongrIso,
      conjugateEquiv, mateEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback comparison is compatible with a left identity on the base map. -/
lemma Over.pullback_id_comp {X Y : C} (f : X ⟶ Y) :
    (Over.pullbackComp (𝟙 X) f).hom ≫
      whiskerLeft (Over.pullback f) Over.pullbackId.hom ≫
        (Over.pullback f).rightUnitor.hom =
      eqToHom (congrArg
        (fun q : X ⟶ Y => Over.pullback q)
        (Category.id_comp f)) := by
  change _ = (eqToIso (congrArg
    (fun q : X ⟶ Y => Over.pullback q)
    (Category.id_comp f))).hom
  rw [← congrArg Iso.hom
    (Over.pullbackCongrIso_eq_eqToIso (Category.id_comp f))]
  ext T
  apply pullback.hom_ext
  · simp [Over.pullbackComp, Over.pullbackId, Over.pullbackCongrIso,
      conjugateEquiv, mateEquiv]
  · simp [Over.pullbackComp, Over.pullbackId, Over.pullbackCongrIso,
      conjugateEquiv, mateEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open Opposite in
/-- The contravariant pseudofunctor sending `X` to the category `Over X` and a
morphism to its pullback functor. -/
noncomputable def Over.pullbackPseudofunctor :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (Over X.unop))
    (fun f => (Over.pullback f.unop).toCatHom)
    (fun _ => Cat.Hom.isoMk Over.pullbackId)
    (fun f g => Cat.Hom.isoMk (Over.pullbackComp g.unop f.unop))
    (fun f g h => by
      simp only [unop_comp]
      ext T
      simpa only [Cat.Hom.toNatTrans_comp, Cat.Hom.isoMk_hom,
        Cat.Hom.isoMk_inv, NatTrans.toCatHom₂_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.whiskerLeft_toNatTrans,
        Cat.associator_hom_toNatTrans, Cat.Hom₂.eqToHom_toNatTrans,
        NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app,
        Functor.toCatHom]
        using congrArg (fun η => η.app T)
          (Over.pullback_associativity f.unop g.unop h.unop))
    (fun f => by
      simp only [unop_comp, unop_id]
      ext T
      simpa only [Cat.Hom.toNatTrans_comp, Cat.Hom.isoMk_hom,
        Cat.Hom.isoMk_inv, NatTrans.toCatHom₂_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.leftUnitor_hom_toNatTrans,
        Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
        Functor.toCatHom]
        using congrArg (fun η => η.app T)
          (Over.pullback_comp_id f.unop))
    (fun f => by
      simp only [unop_comp, unop_id]
      ext T
      simpa only [Cat.Hom.toNatTrans_comp, Cat.Hom.isoMk_hom,
        Cat.Hom.isoMk_inv, NatTrans.toCatHom₂_toNatTrans,
        Cat.whiskerLeft_toNatTrans, Cat.rightUnitor_hom_toNatTrans,
        Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
        Functor.toCatHom]
        using congrArg (fun η => η.app T)
          (Over.pullback_id_comp f.unop))

/-- Regard an object over `X` as an object of the over-category appearing at
`X` in the pullback pseudofunctor. This bridge avoids repeatedly unfolding the
pseudofunctor's coherence data to reduce its object projection. -/
noncomputable def Over.pullbackPseudofunctorObj {X : C} (J : Over X) :
    (Over.pullbackPseudofunctor (C := C)).obj (.mk (Opposite.op X)) :=
  J

end CategoryTheory
