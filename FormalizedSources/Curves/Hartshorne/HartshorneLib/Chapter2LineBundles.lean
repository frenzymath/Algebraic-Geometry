/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Line bundles

This file records the local-triviality definition of an invertible sheaf used in
Chapter II and its basic invariance under isomorphism.
-/

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace Hartshorne

universe u

open AlgebraicGeometry

/-- A scheme module is a line bundle if it is locally isomorphic to the structure sheaf. -/
def IsLineBundle {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- Being a line bundle is preserved by isomorphism of scheme modules. -/
theorem IsLineBundle.of_iso {X : Scheme.{u}} {M N : X.Modules}
    (hM : IsLineBundle M) (e : M ≅ N) : IsLineBundle N := by
  intro x
  obtain ⟨U, hx, ⟨i⟩⟩ := hM x
  exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ i⟩⟩

/-- Isomorphic scheme modules are line bundles simultaneously. -/
theorem isLineBundle_iff_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) : IsLineBundle M ↔ IsLineBundle N :=
  ⟨fun hM ↦ hM.of_iso e, fun hN ↦ hN.of_iso e.symm⟩

/-! ### Pullback of line bundles -/

/-- Pullback preserves the local triviality condition defining a line bundle.

The proof refines a trivialising neighbourhood to an affine open, factors the
restricted morphism through that chart, and transports the chart isomorphism
through the standard pullback/restriction comparison isomorphisms. -/
theorem IsLineBundle.pullback {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (hM : IsLineBundle M) :
    IsLineBundle ((Scheme.Modules.pullback f).obj M) := by
  intro y
  obtain ⟨U, hxU, eM⟩ := hM (f.base y)
  have hyU' : y ∈ f ⁻¹ᵁ U := hxU
  obtain ⟨V, hV_aff, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hyU'
  refine ⟨V, hyV, ?_⟩
  obtain ⟨eM⟩ := eM
  set g : (V : Scheme) ⟶ (U : Scheme) := f.resLE U V hVU with hg_def
  have hg_comp : g ≫ U.ι = V.ι ≫ f := Scheme.Hom.resLE_comp_ι f hVU
  haveI : (TopologicalSpace.Opens.map g.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  refine ⟨?_⟩
  let i1 :=
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app
      ((Scheme.Modules.pullback f).obj M)
  let i2 := (Scheme.Modules.pullbackComp V.ι f).app M
  let i3 := (Scheme.Modules.pullbackCongr hg_comp.symm).app M
  let i4 := ((Scheme.Modules.pullbackComp g U.ι).symm).app M
  let i5 := (Scheme.Modules.pullback g).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M)
  let i6 := (Scheme.Modules.pullback g).mapIso eM
  let i7 := asIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
  exact i1 ≪≫ i2 ≪≫ i3 ≪≫ i4 ≪≫ i5 ≪≫ i6 ≪≫ i7

/-! ### Pullback functoriality -/

/-- Pulling a line bundle back along a composite morphism preserves local
triviality, using the comparison isomorphism with successive pullbacks. -/
theorem IsLineBundle.pullback_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {M : X.Modules} (hM : IsLineBundle M) :
    IsLineBundle ((Scheme.Modules.pullback (g ≫ f)).obj M) := by
  have hgf : IsLineBundle
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M)) :=
    IsLineBundle.pullback g (IsLineBundle.pullback f hM)
  exact hgf.of_iso ((Scheme.Modules.pullbackComp g f).app M)

/-- Pulling a line bundle back along the identity morphism preserves the
line-bundle property. -/
theorem IsLineBundle.pullback_id {X : Scheme.{u}} {M : X.Modules}
    (hM : IsLineBundle M) :
    IsLineBundle ((Scheme.Modules.pullback (𝟙 X)).obj M) := by
  exact hM.of_iso ((Scheme.Modules.pullbackId X).app M).symm

/-! ### Restriction along open immersions -/

/-- Restricting a line bundle to an open subscheme preserves local triviality. -/
theorem IsLineBundle.restrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {M : X.Modules} (hM : IsLineBundle M) :
    IsLineBundle ((Scheme.Modules.restrictFunctor f).obj M) := by
  exact (hM.pullback f).of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm

/-- Restriction along a composite of open immersions preserves local triviality,
using the comparison isomorphism with successive restrictions. -/
theorem IsLineBundle.restrict_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] {M : X.Modules} (hM : IsLineBundle M) :
    IsLineBundle ((Scheme.Modules.restrictFunctor (g ≫ f)).obj M) := by
  have htwo : IsLineBundle
      ((Scheme.Modules.restrictFunctor g).obj
        ((Scheme.Modules.restrictFunctor f).obj M)) :=
    (hM.restrict f).restrict g
  exact htwo.of_iso ((Scheme.Modules.restrictFunctorComp g f).app M).symm

/-- Restriction along the identity immersion preserves the line-bundle property. -/
theorem IsLineBundle.restrict_id {X : Scheme.{u}} {M : X.Modules}
    (hM : IsLineBundle M) :
    IsLineBundle ((Scheme.Modules.restrictFunctor (𝟙 X)).obj M) := by
  exact hM.of_iso ((Scheme.Modules.restrictFunctorId).app M).symm

end Hartshorne
