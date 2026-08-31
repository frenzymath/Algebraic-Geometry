/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Linear maps on module stalks

The stalk of a presheaf of modules carries the module structure induced by the
stalk of the coefficient-ring presheaf.  Mathlib provides this structure and
the compatibility of germs with scalar multiplication, but does not package
the stalk map of a module morphism as a linear map.  This file supplies that
small bridge for use by the residue-fibre Nakayama arguments.
-/

open CategoryTheory
open TopologicalSpace TopCat.Presheaf Opposite

universe u

namespace PresheafOfModules

/-- The linear map on stalks induced by a morphism of presheaves of modules. -/
noncomputable def stalkLinearMap
    {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N) (x : X) :
    (↑(TopCat.Presheaf.stalk M.presheaf x) : Type u) →ₗ[↑(R.stalk x)]
      (↑(TopCat.Presheaf.stalk N.presheaf x) : Type u) where
  toFun := (ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map g)))
  map_add' a b := map_add _ a b
  map_smul' r s := by
    dsimp only [RingHom.id_apply]
    obtain ⟨U, hxU, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
    obtain ⟨V, hxV, s₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf s
    set W : Opens X := U ⊓ V with hW
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    set iWU : W ⟶ U := homOfLE inf_le_left
    set iWV : W ⟶ V := homOfLE inf_le_right
    have hr : (ConcreteCategory.hom (R.germ U x hxU)) r₀
        = (ConcreteCategory.hom (R.germ W x hxW))
            ((ConcreteCategory.hom (R.map iWU.op)) r₀) :=
      (TopCat.Presheaf.germ_res_apply R iWU x hxW r₀).symm
    have hs : (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf V x hxV)) s₀
        = (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
            ((ConcreteCategory.hom (M.presheaf.map iWV.op)) s₀) :=
      (TopCat.Presheaf.germ_res_apply M.presheaf iWV x hxW s₀).symm
    have key : ∀ (z : (↑(M.obj (op W)) : Type u)),
        (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((toPresheaf _).map g)))
          ((ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW)) z)
        = (ConcreteCategory.hom (TopCat.Presheaf.germ N.presheaf W x hxW))
            ((ConcreteCategory.hom (g.app (op W))) z) := by
      intro z
      rw [show (ConcreteCategory.hom (g.app (op W))) z
            = (ConcreteCategory.hom (((toPresheaf _).map g).app (op W))) z from
            (toPresheaf_map_app_apply g (op W) z).symm]
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply (F := M.presheaf) (G := N.presheaf)
        W x hxW ((toPresheaf _).map g) z
    rw [hr, hs, ← PresheafOfModules.germ_smul M x W hxW, key, map_smul,
      PresheafOfModules.germ_smul N x W hxW, key]

@[simp]
theorem stalkLinearMap_germ
    {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N) (x : X)
    (U : Opens X) (hx : x ∈ U) (s : (↑(M.obj (op U)) : Type u)) :
    stalkLinearMap g x ((ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf U x hx)) s)
      = (ConcreteCategory.hom (TopCat.Presheaf.germ N.presheaf U x hx))
          ((ConcreteCategory.hom (g.app (op U))) s) := by
  change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((toPresheaf _).map g)))
      ((ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf U x hx)) s) = _
  rw [show (ConcreteCategory.hom (g.app (op U))) s
        = (ConcreteCategory.hom (((toPresheaf _).map g).app (op U))) s from
        (toPresheaf_map_app_apply g (op U) s).symm]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply (F := M.presheaf) (G := N.presheaf)
    U x hx ((toPresheaf _).map g) s

/-- A morphism that is an isomorphism on the underlying additive stalk gives
a bijective linear map on that stalk. -/
theorem stalkLinearMap_bijective_of_isIso
    {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N) (x : X)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map g))) :
    Function.Bijective (stalkLinearMap g x) := by
  change Function.Bijective ⇑(ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map g)))
  exact ConcreteCategory.bijective_of_isIso _

/-- The linear equivalence on stalks induced by an isomorphism of the
underlying additive stalks. -/
noncomputable def stalkLinearEquivOfIsIso
    {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N) (x : X)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map g))) :
    (↑(TopCat.Presheaf.stalk M.presheaf x) : Type u) ≃ₗ[↑(R.stalk x)]
      (↑(TopCat.Presheaf.stalk N.presheaf x) : Type u) :=
  LinearEquiv.ofBijective (stalkLinearMap g x)
    (stalkLinearMap_bijective_of_isIso g x h)

end PresheafOfModules
