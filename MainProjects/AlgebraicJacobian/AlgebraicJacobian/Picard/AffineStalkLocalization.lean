/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.TensorStalkLocalization
import AlgebraicJacobian.Cohomology.TildeExactness
import AlgebraicJacobian.Cohomology.FlatBaseChange

/-!
# Reconstructing affine sections from stalk localizations

Let `F` be an arbitrary sheaf of modules on `Spec R` and let
`f : N ⟶ Γ(Spec R, F)`.  If, at every prime, the composite of `f` with
the germ into `F`'s stalk exhibits that stalk as the corresponding localization
of `N`, then `f` is an isomorphism.

No quasi-coherence hypothesis on `F` is needed.  The adjoint morphism
`tilde N ⟶ F` is an isomorphism on stalks because both stalks are localizations
of `N`.  The fully faithful tilde functor then identifies `f` with a composite
of isomorphisms.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- A sheaf-module stalk on `Spec R`, regarded as an `R`-module through the
canonical map from `R` to the structure-sheaf stalk. -/
noncomputable abbrev moduleSpecStalkModule
    (F : (Spec R).Modules) (x : PrimeSpectrum.Top R) :
    Module R (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) := by
  letI : Module ((Spec R).presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    presheafStalkModule F.val x
  exact Module.compHom _
    (((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial).hom)

/-- The germ from global sections of a sheaf on `Spec R`, written as an
`R`-linear map using the scalar convention of `moduleSpecΓFunctor`. -/
noncomputable def moduleSpecGermLinearMap
    (F : (Spec R).Modules) (x : PrimeSpectrum.Top R) :
    letI : Module R (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      moduleSpecStalkModule F x
    moduleSpecΓFunctor.obj F →ₗ[R]
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) := by
  letI : Module ((Spec R).presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    presheafStalkModule F.val x
  letI : Module R (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    moduleSpecStalkModule F x
  letI : Module Γ(Spec R, ⊤) (moduleSpecΓFunctor.obj F : Type u) :=
    inferInstanceAs (Module Γ(Spec R, ⊤) Γ(F, ⊤))
  refine
    { toFun := ConcreteCategory.hom
        (TopCat.Presheaf.germ F.val.presheaf ⊤ x trivial)
      map_add' := map_add _
      map_smul' := fun r m => ?_ }
  change (ConcreteCategory.hom
      (TopCat.Presheaf.germ F.val.presheaf ⊤ x trivial))
        ((ConcreteCategory.hom (Scheme.ΓSpecIso R).inv) r • m) =
    (ConcreteCategory.hom ((Spec R).presheaf.germ ⊤ x trivial))
        ((ConcreteCategory.hom (Scheme.ΓSpecIso R).inv) r) •
      (ConcreteCategory.hom
        (TopCat.Presheaf.germ F.val.presheaf ⊤ x trivial)) m
  exact F.val.germ_smul x ⊤ trivial
    ((ConcreteCategory.hom (Scheme.ΓSpecIso R).inv) r) m

/-- The map on stalks induced by a morphism of modules on `Spec R`, with both
stalks regarded as `R`-modules. -/
noncomputable def moduleSpecStalkLinearMap
    {F G : (Spec R).Modules} (phi : F ⟶ G) (x : PrimeSpectrum.Top R) :
    letI : Module R (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      moduleSpecStalkModule F x
    letI : Module R (↑(TopCat.Presheaf.stalk G.val.presheaf x) : Type u) :=
      moduleSpecStalkModule G x
    (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) →ₗ[R]
      (↑(TopCat.Presheaf.stalk G.val.presheaf x) : Type u) := by
  letI : Module ((Spec R).presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    presheafStalkModule F.val x
  letI : Module ((Spec R).presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk G.val.presheaf x) : Type u) :=
    presheafStalkModule G.val x
  letI : Module R (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    moduleSpecStalkModule F x
  letI : Module R (↑(TopCat.Presheaf.stalk G.val.presheaf x) : Type u) :=
    moduleSpecStalkModule G x
  refine
    { toFun := PresheafOfModules.stalkLinearMap phi.val x
      map_add' := map_add _
      map_smul' := fun r m => ?_ }
  exact (PresheafOfModules.stalkLinearMap phi.val x).map_smul
    ((ConcreteCategory.hom
      ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial)) r) m

/-- The stalk map of the adjoint of `f : N ⟶ Γ(F)`, precomposed with
`tilde.toStalk`, is the germ of `f`. -/
theorem adjunctionTranspose_stalk_comp_toStalk
    (F : (Spec R).Modules) (N : ModuleCat.{u} R)
    (f : N ⟶ moduleSpecΓFunctor.obj F) (x : PrimeSpectrum.Top R) :
    let phi : tilde N ⟶ F := tilde.map f ≫ F.fromTildeΓ
    letI : Module R
        (↑(TopCat.Presheaf.stalk (tilde N).val.presheaf x) : Type u) :=
      moduleSpecStalkModule (tilde N) x
    letI : Module R
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      moduleSpecStalkModule F x
    (moduleSpecStalkLinearMap phi x).comp (tilde.toStalk N x).hom =
      (moduleSpecGermLinearMap F x).comp f.hom := by
  let phi : tilde N ⟶ F := tilde.map f ≫ F.fromTildeΓ
  letI : Module R
      (↑(TopCat.Presheaf.stalk (tilde N).val.presheaf x) : Type u) :=
    moduleSpecStalkModule (tilde N) x
  letI : Module R
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    moduleSpecStalkModule F x
  apply LinearMap.ext
  intro m
  change
    PresheafOfModules.stalkLinearMap phi.val x
      ((ConcreteCategory.hom
        (TopCat.Presheaf.germ (tilde N).val.presheaf ⊤ x trivial))
        ((tilde.toOpen N ⊤).hom m)) =
      (ConcreteCategory.hom
        (TopCat.Presheaf.germ F.val.presheaf ⊤ x trivial)) (f.hom m)
  have hgerm := PresheafOfModules.stalkLinearMap_germ phi.val x ⊤ trivial
    ((tilde.toOpen N ⊤).hom m)
  refine hgerm.trans ?_
  congr 1
  change (((modulesSpecToSheaf.map (tilde.map f ≫ F.fromTildeΓ)).hom.app
    (op ⊤)).hom ((tilde.toOpen N ⊤).hom m)) = f.hom m
  rw [Functor.map_comp]
  change ((modulesSpecToSheaf.map F.fromTildeΓ).hom.app (op ⊤)).hom
      (((modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤)).hom
        ((tilde.toOpen N ⊤).hom m)) = f.hom m
  have hmap := congrArg (fun q => q.hom m) (tilde.toOpen_map_app f ⊤)
  change
    ((modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤)).hom
        ((tilde.toOpen N ⊤).hom m) =
      (tilde.toOpen (moduleSpecΓFunctor.obj F) ⊤).hom (f.hom m) at hmap
  rw [hmap]
  have hfrom := congrArg (fun q => q.hom (f.hom m))
    (Scheme.Modules.toOpen_fromTildeΓ_app F ⊤)
  change
    ((modulesSpecToSheaf.map F.fromTildeΓ).hom.app (op ⊤)).hom
        ((tilde.toOpen (moduleSpecΓFunctor.obj F) ⊤).hom (f.hom m)) =
      ((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op).hom (f.hom m) at hfrom
  exact hfrom.trans (by simp)

/-- A map between two localizations of the same module is bijective if it
intertwines the two localization maps. -/
theorem linearMap_bijective_of_comp_localizations
    {R : Type u} [CommRing R] (S : Submonoid R)
    {M M' M'' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    {a : M →ₗ[R] M'} {b : M →ₗ[R] M''} {h : M' →ₗ[R] M''}
    (ha : IsLocalizedModule S a) (hb : IsLocalizedModule S b)
    (hh : h.comp a = b) : Function.Bijective h := by
  letI := ha
  letI := hb
  have heq : h = (IsLocalizedModule.linearEquiv S a b).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S a b
    apply LinearMap.ext
    intro m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply, hh,
      LinearEquiv.coe_toLinearMap, IsLocalizedModule.linearEquiv_apply]
  rw [heq]
  exact (IsLocalizedModule.linearEquiv S a b).bijective

/-- Affine stalk reconstruction.  A map into the global sections of an
arbitrary sheaf on `Spec R` is an isomorphism when its composite with every
germ map is localization at the corresponding prime. -/
theorem isIso_moduleSpec_hom_of_isLocalizedModule_stalk
    (F : (Spec R).Modules) (N : ModuleCat.{u} R)
    (f : N ⟶ moduleSpecΓFunctor.obj F)
    (H : ∀ x : PrimeSpectrum.Top R,
      letI : Module R (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
        moduleSpecStalkModule F x
      IsLocalizedModule x.asIdeal.primeCompl
        ((moduleSpecGermLinearMap F x).comp f.hom)) :
    IsIso f := by
  let phi : tilde N ⟶ F := tilde.map f ≫ F.fromTildeΓ
  have hphi : IsIso phi := by
    rw [AlgebraicGeometry.Modules.isIso_iff_isIso_stalkFunctor_map]
    intro x
    rw [ConcreteCategory.isIso_iff_bijective]
    letI : Module R
        (↑(TopCat.Presheaf.stalk (tilde N).val.presheaf x) : Type u) :=
      moduleSpecStalkModule (tilde N) x
    letI : Module R
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      moduleSpecStalkModule F x
    have ha : IsLocalizedModule x.asIdeal.primeCompl (tilde.toStalk N x).hom :=
      inferInstance
    have hb : IsLocalizedModule x.asIdeal.primeCompl
        ((moduleSpecGermLinearMap F x).comp f.hom) := H x
    have hh := adjunctionTranspose_stalk_comp_toStalk F N f x
    have hbij := linearMap_bijective_of_comp_localizations
      x.asIdeal.primeCompl ha hb hh
    change Function.Bijective (PresheafOfModules.stalkLinearMap phi.val x)
    exact hbij
  have hf := Equiv.apply_symm_apply (tilde.adjunction.homEquiv N F) f
  change (tilde.adjunction.homEquiv N F) phi = f at hf
  rw [Adjunction.homEquiv_unit] at hf
  let ephi : tilde N ≅ F := @asIso _ _ _ _ phi hphi
  let eunit := asIso (tilde.adjunction.unit.app N)
  let ef := eunit ≪≫ moduleSpecΓFunctor.mapIso ephi
  have hef : ef.hom = f := by
    change tilde.adjunction.unit.app N ≫ moduleSpecΓFunctor.map phi = f
    exact hf
  rw [← hef]
  exact ef.isIso_hom

/-- On an affine spectrum, the canonical map from the objectwise tensor of
global sections to the global sections of the sheaf tensor product is an
isomorphism.  The two module factors need only be quasi-coherent. -/
theorem tensorSectionHom_top_isIso
    (A B : (Spec R).Modules) [A.IsQuasicoherent] [B.IsQuasicoherent] :
    IsIso (tensorSectionHom A B (⊤ : (Spec R).Opens)) := by
  let e := Scheme.ΓSpecIso R
  let P := (tensorPresheaf A B).obj (op (⊤ : (Spec R).Opens))
  let N := (ModuleCat.restrictScalars e.inv.hom).obj P
  let fR : N ⟶ moduleSpecΓFunctor.obj (tensorObj A B) :=
    (ModuleCat.restrictScalars e.inv.hom).map (tensorSectionHom A B ⊤)
  suffices IsIso fR by
    rw [ConcreteCategory.isIso_iff_bijective] at this ⊢
    exact this
  apply isIso_moduleSpec_hom_of_isLocalizedModule_stalk (tensorObj A B) N fR
  intro x
  letI : Algebra R Γ(Spec R, ⊤) := e.inv.hom.toAlgebra
  let hU : IsAffineOpen (⊤ : (Spec R).Opens) := isAffineOpen_top (Spec R)
  let xU : (⊤ : (Spec R).Opens) := ⟨x, trivial⟩
  have hp : hU.primeIdealOf xU = Spec.map e.hom x := by
    haveI : IsIso hU.fromSpec := by
      rw [IsAffineOpen.fromSpec_top]
      infer_instance
    apply (ConcreteCategory.bijective_of_isIso hU.fromSpec.base).injective
    rw [hU.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_top,
      ← Scheme.isoSpec_Spec_hom]
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  have hS : Algebra.algebraMapSubmonoid Γ(Spec R, ⊤) x.asIdeal.primeCompl =
      (hU.primeIdealOf xU).asIdeal.primeCompl := by
    ext s
    change s ∈ Submonoid.map e.inv.hom x.asIdeal.primeCompl ↔
      s ∉ (hU.primeIdealOf xU).asIdeal
    rw [Submonoid.mem_map, hp]
    constructor
    · rintro ⟨r, hr, rfl⟩
      change e.hom (e.inv.hom r) ∉ x.asIdeal
      simpa using hr
    · intro hs
      refine ⟨e.hom s, hs, ?_⟩
      simp
  letI : Module ((Spec R).presheaf.stalk xU)
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf xU) : Type u) :=
    presheafStalkModule (tensorObj A B).val xU
  letI : Module Γ(Spec R, ⊤)
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf xU) : Type u) :=
    Module.compHom _ ((Spec R).presheaf.germ ⊤ xU trivial).hom
  let gΓ :=
    (presheafGermLinearMap (tensorObj A B).val xU).comp
      (tensorSectionHom A B ⊤).hom
  have hlocΓ : IsLocalizedModule (hU.primeIdealOf xU).asIdeal.primeCompl gΓ :=
    isLocalizedModule_tensorSectionHom_stalk A B hU xU
  rw [← hS] at hlocΓ
  letI modRP : Module R P := Module.compHom _ e.inv.hom
  letI modRT : Module R
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf xU) : Type u) :=
    moduleSpecStalkModule (tensorObj A B) xU.1
  let towerP : IsScalarTower R Γ(Spec R, ⊤) P :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let towerT : IsScalarTower R Γ(Spec R, ⊤)
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf xU) : Type u) :=
    IsScalarTower.of_algebraMap_smul (fun r m => by
      change e.inv.hom r • m =
        ((e.inv ≫ (Spec R).presheaf.germ ⊤ xU trivial).hom r) • m
      rfl)
  exact @IsLocalizedModule.restrictScalars
    R _ P _ Γ(Spec R, ⊤) _ (e.inv.hom.toAlgebra)
    modRP x.asIdeal.primeCompl
    (inferInstanceAs (Module Γ(Spec R, ⊤) P))
    (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf xU) : Type u) _
    modRT
    (Module.compHom _ ((Spec R).presheaf.germ ⊤ xU trivial).hom)
    towerP towerT gΓ hlocΓ

end AlgebraicGeometry.Scheme.Modules
