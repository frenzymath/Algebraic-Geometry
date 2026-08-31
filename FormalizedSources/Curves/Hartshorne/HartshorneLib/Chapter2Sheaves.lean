/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks

/-!
# Hartshorne II.1: Sheaves

This file gives the source-facing names used for the basic presheaf, stalk,
sheafification, and direct-image constructions.  The constructions themselves
are the corresponding mathlib ones; the wrappers keep the chapter API small
and avoid committing to a particular presentation of inverse image.
-/

namespace Hartshorne

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

abbrev Presheaf (C : Type u) [Category.{v} C] (X : TopCat.{w}) :=
  TopCat.Presheaf C X

abbrev Sheaf (C : Type u) [Category.{v} C] (X : TopCat.{w}) :=
  TopCat.Sheaf C X

abbrev IsSheaf {C : Type u} [Category.{v} C] {X : TopCat.{w}}
    (F : Presheaf C X) : Prop :=
  TopCat.Presheaf.IsSheaf F

abbrev Stalk {C : Type u} [Category.{v} C] {X : TopCat.{v}}
    (F : Presheaf C X) [HasColimits C] (x : X) : C :=
  TopCat.Presheaf.stalk F x

def stalkMap {C : Type u} [Category.{v} C] {X : TopCat.{v}}
    {F G : Presheaf C X} [HasColimits C] (φ : F ⟶ G) (x : X) :
    Stalk F x ⟶ Stalk G x :=
  (TopCat.Presheaf.stalkFunctor C x).map φ

@[simp] theorem stalkMap_id {C : Type u} [Category.{v} C] {X : TopCat.{v}}
    {F : Presheaf C X} [HasColimits C] (x : X) :
    stalkMap (𝟙 F) x = 𝟙 _ := by
  simp [stalkMap]

@[simp, reassoc] theorem stalkMap_comp {C : Type u} [Category.{v} C] {X : TopCat.{v}}
    {F G H : Presheaf C X} [HasColimits C] (f : F ⟶ G) (g : G ⟶ H) (x : X) :
    stalkMap (f ≫ g) x = stalkMap f x ≫ stalkMap g x := by
  simp [stalkMap]

def germ {C : Type u} [Category.{v} C] {X : TopCat.{v}} [HasColimits C]
    (F : Presheaf C X) (U : Opens X) (x : X) (hx : x ∈ U) :
    F.obj (op U) ⟶ Stalk F x :=
  TopCat.Presheaf.germ F U x hx

@[reassoc] theorem germ_restrict {C : Type u} [Category.{v} C] {X : TopCat.{v}}
    [HasColimits C]
    (F : Presheaf C X) {U V : Opens X} (i : U ⟶ V) (x : X) (hx : x ∈ U) :
    F.map i.op ≫ germ F U x hx = germ F V x (i.le hx) := by
  exact TopCat.Presheaf.germ_res F i x hx

/-- Taking germs commutes with a morphism of presheaves. -/
@[reassoc] theorem germ_stalkMap {C : Type u} [Category.{v} C] {X : TopCat.{v}}
    [HasColimits C] {F G : Presheaf C X} (φ : F ⟶ G)
    (U : Opens X) (x : X) (hx : x ∈ U) :
    germ F U x hx ≫ stalkMap φ x = φ.app (op U) ≫ germ G U x hx := by
  exact TopCat.Presheaf.stalkFunctor_map_germ U x hx φ

/-- An isomorphism of presheaves induces an isomorphism on every stalk. -/
instance stalkMap_isIso {C : Type u} [Category.{v} C] {X : TopCat.{v}}
    [HasColimits C] {F G : Presheaf C X} (φ : F ⟶ G) [IsIso φ] (x : X) :
    IsIso (stalkMap φ x) := by
  exact Functor.map_isIso (TopCat.Presheaf.stalkFunctor C x) φ

/-- The stalk map induced by an inverse is the inverse of the induced stalk map. -/
@[simp] theorem stalkMap_inv {C : Type u} [Category.{v} C] {X : TopCat.{v}}
    [HasColimits C] {F G : Presheaf C X} (φ : F ⟶ G) [IsIso φ] (x : X) :
    stalkMap (inv φ) x = inv (stalkMap φ x) := by
  simp [stalkMap]

abbrev TypePresheaf (X : TopCat.{u}) := TopCat.Presheaf (Type u) X

abbrev TypeSheaf (X : TopCat.{u}) := TopCat.Sheaf (Type u) X

noncomputable def sheafification {X : TopCat.{u}} (F : TypePresheaf X) :
    TypeSheaf X :=
  F.sheafify

theorem sheafification_condition {X : TopCat.{u}} (F : TypePresheaf X) :
    IsSheaf (sheafification F).presheaf := by
  exact (sheafification F).property

theorem sheafification_isSheaf {X : TopCat.{u}} (F : TypePresheaf X) :
    IsSheaf (sheafification F).presheaf := by
  exact sheafification_condition F

noncomputable def sheafification_stalkIso {X : TopCat.{u}}
    (F : TypePresheaf X) (x : X) :
    Stalk (sheafification F).presheaf x ≅ Stalk F x := by
  exact F.sheafifyStalkIso x

noncomputable def categoricalSheafification {X : TopCat.{u}} (F : TypePresheaf X) :
    TypeSheaf X :=
  (CategoryTheory.presheafToSheaf
    (Opens.grothendieckTopology X) (Type u)).obj F

noncomputable def categoricalSheafificationUnit {X : TopCat.{u}} (F : TypePresheaf X) :
    F ⟶ (categoricalSheafification F).presheaf :=
  (CategoryTheory.sheafificationAdjunction
    (Opens.grothendieckTopology X) (Type u)).unit.app F

noncomputable def categoricalSheafificationLift {X : TopCat.{u}} {G : TypeSheaf X}
    (F : TypePresheaf X) (η : F ⟶ G.presheaf) :
    (categoricalSheafification F).presheaf ⟶ G.presheaf :=
  CategoryTheory.sheafifyLift (Opens.grothendieckTopology X) η G.property

@[reassoc (attr := simp)]
theorem categoricalSheafificationUnit_lift {X : TopCat.{u}} {G : TypeSheaf X}
    (F : TypePresheaf X) (η : F ⟶ G.presheaf) :
    categoricalSheafificationUnit F ≫ categoricalSheafificationLift F η = η :=
  CategoryTheory.toSheafify_sheafifyLift
    (Opens.grothendieckTopology X) η G.property

theorem categoricalSheafificationLift_unique {X : TopCat.{u}} {G : TypeSheaf X}
    (F : TypePresheaf X) (η : F ⟶ G.presheaf)
    (γ : (categoricalSheafification F).presheaf ⟶ G.presheaf)
    (h : categoricalSheafificationUnit F ≫ γ = η) :
    γ = categoricalSheafificationLift F η := by
  apply CategoryTheory.sheafifyLift_unique
    (Opens.grothendieckTopology X) η G.property γ
  exact h

theorem categoricalSheafificationUnit_stalk_isIso {X : TopCat.{u}}
    (F : TypePresheaf X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map
      (categoricalSheafificationUnit F)) := by
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type u) F

def directImage {C : Type u} [Category.{v} C] {X Y : TopCat.{w}} (f : X ⟶ Y) :
    Sheaf C X ⥤ Sheaf C Y :=
  TopCat.Sheaf.pushforward C f

def presheafDirectImage {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Presheaf CommRingCat X ⥤ Presheaf CommRingCat Y :=
  TopCat.Presheaf.pushforward CommRingCat f

noncomputable def presheafInverseImage {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Presheaf CommRingCat Y ⥤ Presheaf CommRingCat X :=
  TopCat.Presheaf.pullback CommRingCat f

noncomputable def sheafInverseImage {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Sheaf CommRingCat Y ⥤ Sheaf CommRingCat X :=
  TopCat.Sheaf.pullback CommRingCat f

noncomputable def sheafInverseImageDirectImageAdjunction
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    sheafInverseImage f ⊣ directImage f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f

theorem directImage_presheaf_isSheaf {C : Type u} [Category.{v} C]
    {X Y : TopCat.{w}} (f : X ⟶ Y) {F : Presheaf C X} (hF : IsSheaf F) :
    IsSheaf ((TopCat.Presheaf.pushforward C f).obj F) :=
  TopCat.Sheaf.pushforward_sheaf_of_sheaf f hF

theorem sheaf_iso_iff_stalkMap_iso
    {C : Type u} [Category.{v} C] {X : TopCat.{v}}
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y : C, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [HasColimits C]
    [PreservesFilteredColimits (CategoryTheory.forget C)] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {F G : Sheaf C X} (f : F ⟶ G) :
    IsIso f ↔ ∀ x : X, IsIso (stalkMap f.hom x) := by
  exact TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso f

/-- Morphisms of sheaves are determined by their maps on all stalks. -/
theorem sheaf_hom_ext_of_stalkMap_eq
    {C : Type u} [Category.{v} C] {X : TopCat.{v}}
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y : C, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [HasColimits C]
    [PreservesFilteredColimits (CategoryTheory.forget C)] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {F G : Sheaf C X} (f g : F ⟶ G)
    (h : ∀ x : X, stalkMap f.hom x = stalkMap g.hom x) : f = g := by
  apply (TopCat.Sheaf.forget C X).map_injective
  change f.1 = g.1
  apply TopCat.Presheaf.ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.section_ext G U
  intro x hx
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact congrArg (fun k => (ConcreteCategory.hom k)
      ((ConcreteCategory.hom (TopCat.Presheaf.germ F.obj U x hx)) s)) (h x)

/-- A sheaf of objects in a concrete abelian category is zero exactly when all
of its stalks are zero. -/
theorem sheaf_isZero_iff_stalk_isZero
    {C : Type u} [Category.{v} C] [HasColimits C] [HasLimits C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y : C, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [PreservesLimits (CategoryTheory.forget C)] [Abelian C]
    {X : TopCat.{v}} (F : Sheaf C X) :
    IsZero F ↔ ∀ x : X, IsZero ((TopCat.Sheaf.forget C X ⋙
      TopCat.Presheaf.stalkFunctor C (X := X) x).obj F) := by
  exact TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero F

/-- Exactness of a short complex of sheaves can be checked on every stalk. -/
theorem sheaf_exact_iff_stalk_exact
    {C : Type u} [Category.{v} C] [HasColimits C] [HasLimits C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y : C, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [PreservesLimits (CategoryTheory.forget C)] [Abelian C]
    {X : TopCat.{v}} (S : ShortComplex (Sheaf C X)) :
    S.Exact ↔ ∀ x : X, (S.map (TopCat.Sheaf.forget C X ⋙
      TopCat.Presheaf.stalkFunctor C (X := X) x)).Exact := by
  exact TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S

/-- Exactness of a presheaf complex of abelian groups gives sectionwise
surjectivity at every open. -/
theorem presheaf_sections_exact_of_exact {X : TopCat.{u}} {U : Opens X}
    {S : ShortComplex (Presheaf AddCommGrpCat.{u} X)}
    (hS : S.Exact) {s : S.X₂.obj (op U)}
    (h : S.g.app (op U) s = 0) :
    ∃ t : S.X₁.obj (op U), S.f.app (op U) t = s := by
  exact TopCat.Presheaf.sections_exact_of_exact (X := X) (U := U) hS h

/-- For a short exact sheaf complex of abelian groups, a monomorphism on the
left gives surjectivity on sections over every open. -/
theorem sheaf_sections_exact_of_left_exact {X : TopCat.{u}} {U : Opens X}
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)}
    (hS : S.Exact) (hf : Mono S.f) (s : S.X₂.obj.obj (op U))
    (h : S.g.hom.app (op U) s = 0) :
    ∃ t : S.X₁.obj.obj (op U), S.f.hom.app (op U) t = s := by
  exact TopCat.Sheaf.sections_exact_of_left_exact hS hf s h

/-! ### Ringed and locally ringed spaces -/

/-- A ringed space is a topological space equipped with a sheaf of commutative rings. -/
abbrev RingedSpace := AlgebraicGeometry.RingedSpace

/-- A locally ringed space is a ringed space whose stalks are local rings. -/
abbrev LocallyRingedSpace := AlgebraicGeometry.LocallyRingedSpace

/-- The structure sheaf of a ringed space. -/
def ringedSpaceStructureSheaf (X : RingedSpace.{u}) :
    Sheaf CommRingCat (X : TopCat) :=
  X.sheaf

/-- The contravariant map of structure sheaves carried by a ringed-space morphism. -/
noncomputable def ringedSpaceSheafMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ringedSpaceStructureSheaf Y ⟶
      (directImage f.hom.base).obj (ringedSpaceStructureSheaf X) :=
  (TopCat.Sheaf.forget CommRingCat (Y : TopCat)).preimage f.hom.c

/-- Forgetting the sheaf condition recovers the defining presheaf morphism. -/
@[simp]
theorem ringedSpaceSheafMap_forget {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.forget CommRingCat (Y : TopCat)).map
      (ringedSpaceSheafMap f) = f.hom.c := by
  exact Functor.map_preimage _ _

/-- The underlying map of a ringed-space morphism is continuous. -/
theorem ringedSpaceHom_continuous {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Continuous f.hom.base :=
  f.hom.base.hom.continuous

/-- Every stalk of a locally ringed space is a local ring. -/
theorem locallyRingedSpace_stalk_isLocalRing
    (X : LocallyRingedSpace.{u}) (x : X) :
    IsLocalRing (X.presheaf.stalk x) := by
  infer_instance

/-- Stalk maps of locally ringed-space morphisms are local homomorphisms. -/
theorem locallyRingedSpace_stalkMap_isLocalHom
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.stalkMap x).hom := by
  infer_instance

/-- The identity morphism induces the identity map on every stalk. -/
@[simp]
theorem locallyRingedSpace_stalkMap_id (X : LocallyRingedSpace.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) := by
  exact AlgebraicGeometry.LocallyRingedSpace.stalkMap_id X x

/-- Stalk maps compose contravariantly under composition of morphisms. -/
theorem locallyRingedSpace_stalkMap_comp
    {X Y Z : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).stalkMap x = g.stalkMap (f.base x) ≫ f.stalkMap x := by
  exact AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp f g x

end

end Hartshorne
