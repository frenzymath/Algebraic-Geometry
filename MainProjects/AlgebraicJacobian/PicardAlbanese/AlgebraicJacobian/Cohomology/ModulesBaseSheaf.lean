/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.ModuleKSheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Restricting a scheme module to the base ring

For a scheme `X` over `Spec k`, this file views an `X.Modules` object as a sheaf of
`k`-modules.  The construction keeps the same section types and restriction maps; only the
scalar action is restricted along `k -> Gamma(X, U)`.  It is the dialect bridge needed to
compare a `Scheme.Modules` line bundle with the fixed-base module sheaves used by the Cech
cohomology engine.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [CommRing k]

/-- The base-ring module structure on sections of a scheme module. -/
@[reducible] noncomputable def moduleKSections
    (X : Over (Spec (CommRingCat.of k))) (M : X.left.Modules)
    (U : X.left.Opens) : Module k Γ(M, U) :=
  Module.compHom _ (X.left.overAlgebraMap k U)

attribute [local instance] moduleKSections

/-- The native structure-sheaf action, with section-notation binders kept explicit. -/
private noncomputable def smulSection
    (X : Over (Spec (CommRingCat.of k))) (M : X.left.Modules)
    (U : X.left.Opens) (r : Γ(X.left, U)) (x : Γ(M, U)) : Γ(M, U) :=
  r • x

/-- The presheaf underlying a scheme module after restriction of scalars to the base ring. -/
noncomputable def toModuleKPresheafOfModules
    (X : Over (Spec (CommRingCat.of k))) (M : X.left.Modules) :
    X.left.Opensᵒᵖ ⥤ ModuleCat.{u} k where
  obj U := ModuleCat.of k Γ(M, U.unop)
  map {U V} f := ModuleCat.ofHom
    { toFun := fun x => M.presheaf.map f x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x =>
        (Scheme.Modules.map_smul M f.unop (X.left.overAlgebraMap k U.unop r) x).trans
          (congrArg
            (fun (s : Γ(X.left, V.unop)) =>
              smulSection X M V.unop s (M.presheaf.map f x))
            (X.left.overAlgebraMap_apply_res k f r)) }
  map_id U := by
    ext x
    exact congrFun (congrArg (fun (f : M.presheaf.obj U ⟶ M.presheaf.obj U) =>
      (ConcreteCategory.hom f : _ → _)) (M.presheaf.map_id U)) x
  map_comp {U V W} f g := by
    ext x
    exact congrFun (congrArg (fun (h : M.presheaf.obj U ⟶ M.presheaf.obj W) =>
      (ConcreteCategory.hom h : _ → _)) (M.presheaf.map_comp f g)) x

/-- The restricted presheaf is a sheaf because its underlying additive presheaf is unchanged. -/
lemma toModuleKPresheafOfModules_isSheaf
    (X : Over (Spec (CommRingCat.of k))) (M : X.left.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X.left.toTopCat)
      (toModuleKPresheafOfModules X M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget (ModuleCat.{u} k))]
  convert (Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat.{u})).mp (Scheme.Modules.isSheaf M) using 1 <;> rfl

/-- A sheaf of `O_X`-modules, viewed as a sheaf of modules over the base ring. -/
noncomputable def toModuleKSheafOfModules
    (X : Over (Spec (CommRingCat.of k))) (M : X.left.Modules) :
    Sheaf (Opens.grothendieckTopology X.left.toTopCat) (ModuleCat.{u} k) :=
  ⟨toModuleKPresheafOfModules X M, toModuleKPresheafOfModules_isSheaf X M⟩

/-- Restriction maps of the base-ring sheaf are definitionally those of the scheme module. -/
lemma toModuleKSheafOfModules_obj_map_apply
    {X : Over (Spec (CommRingCat.of k))} (M : X.left.Modules)
    {V W : X.left.Opens} (h : W ≤ V)
    (x : (toModuleKSheafOfModules X M).obj.obj (op V)) :
    ((toModuleKSheafOfModules X M).obj.map (homOfLE h).op).hom x =
      M.presheaf.map (homOfLE h).op x :=
  rfl

namespace Modules

variable {X : Scheme.{u}}

/-- A scheme module which is locally isomorphic to the structure sheaf. -/
def IsLineBundle (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((restrictFunctor U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

end Modules

end AlgebraicGeometry.Scheme
