/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Std.Tactic.BVDecide.LRAT.Internal.Clause
import AlgebraicJacobian.Cohomology.StructureSheafAb

/-!
# Sheaves of `k`-modules: the structure presheaf

Sub-file (1/3) of the `StructureSheafModuleK` split (refactor iter-174). This file
ships the categorical gap-fills, the sheafification / `Ext` typeclass prerequisites,
and the per-open ring-map helpers (1)–(5) that culminate in the presheaf-of-
`k`-modules `toModuleKPresheaf` (helper 6). Its sibling `SheafProperty.lean`
discharges the sheaf condition and bundles `toModuleKSheaf` (helpers 7–8); the
sibling `Carriers.lean` carries the downstream finite-length carriers and producer
instances.

See `blueprint/src/chapters/Cohomology_StructureSheafModuleK.tex`.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace CategoryTheory

universe u₂ v₂

/-- Iter-046 (Mathlib gap-fill): `Functor.const C : D ⥤ C ⥤ D` is additive when `D`
is preadditive. The `map_add` field reduces to `f + g = f + g` componentwise after
`ext; rfl`. -/
instance Functor.const_additive {C : Type u} [Category.{v} C] {D : Type u₂}
    [Category.{v₂} D] [Preadditive D] : (Functor.const C : D ⥤ C ⥤ D).Additive where
  map_add := by intros; ext; rfl

/-- Iter-046 (Mathlib gap-fill): `Functor.const C : D ⥤ C ⥤ D` is `R`-linear when
`D` is `Linear R`-enriched. The `[CategoryTheory.Linear R D]` qualification is
load-bearing — bare `[Linear R D]` would be parsed as `Linear` of a functor. -/
instance Functor.const_linear {C : Type u} [Category.{v} C] {D : Type u₂}
    [Category.{v₂} D] [Preadditive D] (R : Type*) [Semiring R]
    [CategoryTheory.Linear R D] :
    (Functor.const C : D ⥤ C ⥤ D).Linear R where
  map_smul := by intros; ext; rfl

namespace Adjunction

variable {C₁ : Type u} {D₁ : Type u₂} [Category.{v} C₁] [Category.{v₂} D₁]
    [Preadditive C₁] [Preadditive D₁] {F : C₁ ⥤ D₁} {G : D₁ ⥤ C₁} (adj : F ⊣ G)
    (R : Type*) [Semiring R] [CategoryTheory.Linear R C₁] [CategoryTheory.Linear R D₁]

include adj

/-- Iter-046 (Mathlib gap-fill): if `G : D ⥤ C` is `R`-linear and `adj : F ⊣ G`,
then `F : C ⥤ D` is `R`-linear. Mirrors Mathlib's `left_adjoint_additive`; the
`simp` call closes via unit naturality + the `Linear.smul_comp` / `Linear.comp_smul`
default simp lemmas. -/
lemma left_adjoint_linear [G.Additive] [G.Linear R] : F.Linear R where
  map_smul {X Y} f r := (adj.homEquiv _ _).injective (by
    -- v4.31.0: the old `simp [adj.homEquiv_unit]` no longer closes; the categorical
    -- `Linear.comp_smul`/`smul_comp` only match via `erw` (the `≃ₗ` homModule smul is defeq but
    -- not syntactically the `Linear.smul` instance), with unit-naturality in between.
    simp only [adj.homEquiv_unit, Functor.map_smul, ← Functor.comp_map]
    erw [← adj.unit.naturality, Linear.comp_smul, ← adj.unit.naturality, Linear.smul_comp]
    rfl)

/-- Iter-046 (Mathlib gap-fill): if `F : C ⥤ D` is `R`-linear and `adj : F ⊣ G`,
then `G : D ⥤ C` is `R`-linear. The dual of `left_adjoint_linear`. -/
lemma right_adjoint_linear [F.Additive] [F.Linear R] : G.Linear R where
  map_smul {X Y} f r := (adj.homEquiv _ _).symm.injective (by
    simp [adj.homEquiv_counit])

/-- Iter-046 (Mathlib gap-fill): linear lifting of `Adjunction.homAddEquiv`. Under
`[F.Additive] [G.Additive] [G.Linear R]`, the additive equivalence
`(F.obj X ⟶ Y) ≃+ (X ⟶ G.obj Y)` upgrades to a `LinearEquiv` over `R`. The
`change` is load-bearing: it exposes the underlying `homEquiv` form, allowing
`simp [homEquiv_unit]` to close via the same naturality argument as in
`left_adjoint_linear`. -/
noncomputable def homLinearEquiv [F.Additive] [G.Additive] [G.Linear R]
    (X : C₁) (Y : D₁) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) :=
  haveI : F.Linear R := adj.left_adjoint_linear R
  { adj.homAddEquiv X Y with
    map_smul' := fun r f => by
      change adj.homEquiv _ _ (r • f) = r • adj.homEquiv _ _ f
      simp only [adj.homEquiv_unit, Functor.map_smul]
      erw [Linear.comp_smul] }

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.Cohomology

/-- Phase A step 5 prerequisite (a): sheafification on the topology of opens of
any topological space, valued in `ModuleCat k`. Inferable from Mathlib's
small-site / concrete-category sheafification API; the prover's task is the
universe pinning, mirroring the iter-004 `instHasSheafify_Opens_AddCommGrp`. -/
instance instHasSheafify_Opens_ModuleCatK
    (k : Type u) [CommRing k] (X : TopCat.{u}) :
    CategoryTheory.HasSheafify (Opens.grothendieckTopology X)
      (ModuleCat.{u} k) :=
  inferInstance

/-- Phase A step 5 prerequisite (b): `Ext` on the sheaf category. The universe
annotation `HasExt.{u+1}` is forced by the morphism universe of
`Sheaf (Opens.gT X) (ModuleCat.{u} k)`; mirrors the iter-004
`instHasExt_Sheaf_Opens_AddCommGrp`. -/
noncomputable instance instHasExt_Sheaf_Opens_ModuleCatK
    (k : Type u) [CommRing k] (X : TopCat.{u}) :
    CategoryTheory.HasExt.{u+1}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
        (ModuleCat.{u} k)) :=
  CategoryTheory.HasExt.standard _

end AlgebraicGeometry.Cohomology

namespace AlgebraicGeometry.Scheme.toModuleKSheaf

variable {k : Type u} [CommRing k]

/-- Phase A step 5 main, helper (1): the ring map `k → Γ(C, U)` induced by the
structure morphism `C.hom : C.left ⟶ Spec (CommRingCat.of k)` and the
restriction along `U ≤ ⊤`. -/
noncomputable def kToSection (C : Over (Spec (CommRingCat.of k)))
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    (CommRingCat.of k) ⟶ C.left.presheaf.obj U :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    C.hom.app ⊤ ≫ C.left.presheaf.map (homOfLE le_top).op

/-- Phase A step 5 main, helper (2): `Γ(C, U)` is a `k`-algebra via the ring
map of `kToSection`. -/
noncomputable instance algebraSection (C : Over (Spec (CommRingCat.of k)))
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    Algebra k (C.left.presheaf.obj U) :=
  RingHom.toAlgebra (kToSection C U).hom

/-- Phase A step 5 main, helper (3): unfolding lemma for the algebra map. -/
lemma algebraMap_eq_kToSection (C : Over (Spec (CommRingCat.of k)))
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    (algebraMap k (C.left.presheaf.obj U)) = (kToSection C U).hom :=
  rfl

/-- Phase A step 5 main, helper (4): the structure-morphism algebra map is
natural in `U`. -/
lemma kToSection_naturality (C : Over (Spec (CommRingCat.of k)))
    {U V : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ} (f : U ⟶ V) :
    kToSection C U ≫ C.left.presheaf.map f = kToSection C V := by
  simp only [kToSection, Category.assoc, ← C.left.presheaf.map_comp]
  rfl

/-- Phase A step 5 main, helper (5): corollary of (4) at the level of
`algebraMap`. -/
lemma algebraMap_naturality (C : Over (Spec (CommRingCat.of k)))
    {U V : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ} (f : U ⟶ V) (r : k) :
    (C.left.presheaf.map f).hom (algebraMap k (C.left.presheaf.obj U) r)
      = algebraMap k (C.left.presheaf.obj V) r := by
  rw [algebraMap_eq_kToSection, algebraMap_eq_kToSection]
  exact congrArg (fun (g : (CommRingCat.of k) ⟶ _) => g.hom r)
    (kToSection_naturality (C := C) f)

end AlgebraicGeometry.Scheme.toModuleKSheaf

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [CommRing k]

/-- Phase A step 5 main, helper (6): the presheaf of `k`-modules built from
`O_C` and the structure-morphism algebra structure. -/
noncomputable def toModuleKPresheaf (C : Over (Spec (CommRingCat.of k))) :
    (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj U := ModuleCat.of k (C.left.presheaf.obj U)
  map {U V} f := ModuleCat.ofHom
    { toFun := fun x => (C.left.presheaf.map f).hom x
      map_add' := fun x y => by
        simp [(C.left.presheaf.map f).hom.map_add]
      map_smul' := fun r x => by
        simp only [Algebra.smul_def, RingHom.map_mul, RingHom.id_apply]
        congr 1
        exact AlgebraicGeometry.Scheme.toModuleKSheaf.algebraMap_naturality
          (C := C) f r }
  map_id U := by
    ext x
    simp only [ConcreteCategory.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk,
      ModuleCat.hom_id, LinearMap.id_coe, id_eq]
    exact congrFun (congrArg (·.hom) (C.left.presheaf.map_id U)) x
  map_comp {U V W} f g := by
    ext x
    simp only [ConcreteCategory.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    exact congrFun (congrArg (·.hom) (C.left.presheaf.map_comp f g)) x

/-- Object-evaluation simp lemma for `toModuleKPresheaf`. Definitionally true
by construction; tagged `@[simp]` so consumers can rewrite without unfolding
the constructor. Phase A step 5 polish (iter-007). -/
@[simp] lemma toModuleKPresheaf_obj (C : Over (Spec (CommRingCat.of k)))
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    (toModuleKPresheaf C).obj U = ModuleCat.of k (C.left.presheaf.obj U) :=
  rfl

end AlgebraicGeometry.Scheme
