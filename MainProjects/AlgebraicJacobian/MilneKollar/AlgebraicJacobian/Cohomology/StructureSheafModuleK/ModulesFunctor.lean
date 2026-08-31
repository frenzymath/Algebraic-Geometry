/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.QuasicoherentDegreeOneVanishing
import AlgebraicJacobian.RiemannRoch.Ledger.Chi

/-!
# Restricting sheaves of modules to the ground ring, functorially

`Scheme.toModuleKSheafOfModules` views a sheaf of `O_C`-modules on a
`Spec k`-scheme as a sheaf of `k`-modules.  The existing construction is
object-level.  This file supplies its functorial form: an `O_C`-linear map is
`k`-linear after restricting scalars along the structure morphism.

The functor makes isomorphism transport available to cohomological invariants.
In particular, `chi_toModuleKSheafOfModules_congr` is the direct application of
the existing `CategoryTheory.Sheaf.chi_congr` to the image of a module
isomorphism.  No finiteness statement is added here; `Sheaf.chi` remains the
totalized degree-at-most-one index described in `RiemannRoch.Ledger.Chi`.

## Main declarations

* `Scheme.toModuleKSheafOfModulesFunctor`: functorial restriction of scalars
  from `O_C`-modules to sheaves of `k`-modules.
* `Scheme.chi_toModuleKSheafOfModules_congr`: invariance of the resulting
  truncated Euler index under an `O_C`-module isomorphism.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [CommRing k]

/-- Restriction of scalars from sheaves of `O_C`-modules to sheaves of
`k`-modules, for a scheme `C` over `Spec k`.

On objects this is `toModuleKSheafOfModules`.  On morphisms it uses the same
map on sections; `O_C`-linearity implies `k`-linearity through the structural
map `k -> Gamma(C, U)`. -/
noncomputable def toModuleKSheafOfModulesFunctor
    (C : Over (Spec (CommRingCat.of k))) :
    C.left.Modules ⥤
      Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k) where
  obj := toModuleKSheafOfModules C
  map {M N} f :=
    { hom :=
        { app := fun U =>
            letI := moduleKSections C M U.unop
            letI := moduleKSections C N U.unop
            ModuleCat.ofHom
              { toFun := (f.app U.unop).hom
                map_add' := (f.app U.unop).hom.map_add
                map_smul' := fun r x => by
                  change f.app U.unop ((algebraMap k Γ(C.left, U.unop)) r • x) =
                    (algebraMap k Γ(C.left, U.unop)) r • f.app U.unop x
                  exact f.app_smul _ _ }
          naturality := fun U V i => by
            ext x
            exact congrFun
              (congrArg (fun (g : Γ(M, U.unop) ⟶ Γ(N, V.unop)) =>
                (ConcreteCategory.hom g : _ → _)) (f.mapPresheaf.naturality i)) x } }
  map_id M := by ext U x; rfl
  map_comp f g := by ext U x; rfl

/-- The functorial restriction of scalars acts by the original module map on
sections. -/
@[simp]
lemma toModuleKSheafOfModulesFunctor_map_app_apply
    (C : Over (Spec (CommRingCat.of k))) {M N : C.left.Modules} (f : M ⟶ N)
    (U : C.left.Opens) (x : Γ(M, U)) :
    (((toModuleKSheafOfModulesFunctor C).map f).hom.app (Opposite.op U)).hom x =
      f.app U x :=
  rfl

/-- The totalized degree-at-most-one Euler index after restriction to `k` is
invariant under an isomorphism of sheaves of `O_C`-modules.  This is exactly
`Sheaf.chi_congr` applied through `toModuleKSheafOfModulesFunctor`. -/
theorem chi_toModuleKSheafOfModules_congr
    (C : Over (Spec (CommRingCat.of k))) {M N : C.left.Modules} (e : M ≅ N) :
    CategoryTheory.Sheaf.chi (toModuleKSheafOfModules C M) =
      CategoryTheory.Sheaf.chi (toModuleKSheafOfModules C N) :=
  CategoryTheory.Sheaf.chi_congr ((toModuleKSheafOfModulesFunctor C).mapIso e)

end AlgebraicGeometry.Scheme
