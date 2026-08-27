/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Topology.Sheaves.Over
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Restriction of an `𝒪_{Spec R}`-module to a basic open (Stacks 01I8) — Route-P step P1a

Project-local supplement for the affine quasi-coherence equivalence.
-/

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

/-! ## Project-local Mathlib supplement — continuity of `Opens.overEquivalence`

Mathlib provides `TopologicalSpace.Opens.overEquivalence U : Over U ≌ Opens ↥U` but, as recorded in
its source `## TODO`, does *not* yet prove that the two functors are continuous for the relevant
Grothendieck topologies.  These instances supply exactly that (the gateway brick for the Route B
restrict–over bridge B3): both functors are cover-preserving, and `CompatiblePreserving` is
automatic for the cover-dense functors of an equivalence, so `Functor.IsContinuous` follows. -/

open TopologicalSpace in
/-- The forward functor of `Opens.overEquivalence U` preserves covers. -/
theorem Opens.overEquivalence_functor_coverPreserving
    {X : Type u} [TopologicalSpace X] (U : Opens X) :
    CoverPreserving ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U)
      (Opens.overEquivalence U).functor where
  cover_preserve {Y S} hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS
    intro y hy
    obtain ⟨V, f, hVf, hyV⟩ := hS y.1 hy
    obtain ⟨W, h, h', hSh, hfeq⟩ := hVf
    refine ⟨(Opens.overEquivalence U).functor.obj W,
      (Opens.overEquivalence U).functor.map h, ⟨W, h, 𝟙 _, hSh, by simp⟩, ?_⟩
    change y.1 ∈ W.left
    exact leOfHom h' hyV

open TopologicalSpace in
/-- The inverse functor of `Opens.overEquivalence U` preserves covers. -/
theorem Opens.overEquivalence_inverse_coverPreserving
    {X : Type u} [TopologicalSpace X] (U : Opens X) :
    CoverPreserving (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U)
      (Opens.overEquivalence U).inverse where
  cover_preserve {Y S} hS := by
    rw [GrothendieckTopology.mem_over_iff]
    intro x hx
    obtain ⟨⟨x', hx'U⟩, hx'Y, rfl⟩ := hx
    obtain ⟨P, f, hSf, hxP⟩ := hS ⟨x', hx'U⟩ hx'Y
    exact ⟨((Opens.overEquivalence U).inverse.obj P).left,
      ((Opens.overEquivalence U).inverse.map f).left,
      ⟨(Opens.overEquivalence U).inverse.obj P, (Opens.overEquivalence U).inverse.map f, 𝟙 _,
        ⟨P, f, 𝟙 _, hSf, by simp⟩, by simp⟩,
      ⟨⟨x', hx'U⟩, hxP, rfl⟩⟩

open TopologicalSpace in
/-- The forward functor of `Opens.overEquivalence U` is continuous. -/
instance Opens.overEquivalence_functor_isContinuous
    {X : Type u} [TopologicalSpace X] (U : Opens X) :
    (Opens.overEquivalence U).functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) :=
  Functor.IsCoverDense.isContinuous _ _ _ (Opens.overEquivalence_functor_coverPreserving U)

open TopologicalSpace in
/-- The inverse functor of `Opens.overEquivalence U` is continuous. -/
instance Opens.overEquivalence_inverse_isContinuous
    {X : Type u} [TopologicalSpace X] (U : Opens X) :
    (Opens.overEquivalence U).inverse.IsContinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
  Functor.IsCoverDense.isContinuous _ _ _ (Opens.overEquivalence_inverse_coverPreserving U)

/-! ## Project-local Mathlib supplement — restriction of modules to a basic open -/

variable {R : CommRingCat.{u}} (f : R)

/-- The basic open `D(f) ⊆ Spec R`, as an open subscheme of `Spec R`. -/
abbrev specBasicOpen : (Spec R).Opens := PrimeSpectrum.basicOpen f

/-- The localisation morphism `Spec R_f ⟶ Spec R` factoring through `D(f)`: the inverse of the
affine identification `D(f) ≅ Spec R_f` followed by the open immersion of `D(f)`. -/
noncomputable abbrev specAwayToSpec :
    Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec R :=
  (basicOpenIsoSpecAway f).inv ≫ (specBasicOpen f).ι

/-- **Stacks 01I8, `lemma-widetilde-pullback`.** Restriction of an `𝒪_{Spec R}`-module to the basic
open `D(f)`, transported to a sheaf of `𝒪_{Spec R_f}`-modules along the affine identification
`D(f) ≅ Spec R_f`.  Built by restricting first along the open immersion `D(f) ↪ Spec R`, then along
the (iso, hence open) inverse of `basicOpenIsoSpecAway f`.  Project-local: assembles two Mathlib
restrictions into the single transport used by the affine quasi-coherence equivalence. -/
noncomputable def modulesRestrictBasicOpen (F : (Spec R).Modules) :
    (Spec (CommRingCat.of (Localization.Away f))).Modules :=
  (F.restrict (specBasicOpen f).ι).restrict (basicOpenIsoSpecAway f).inv

/-- **Stacks 01I8, `lemma-widetilde-pullback`.** The transported restriction
`modulesRestrictBasicOpen f F` is canonically isomorphic to the inverse image of `F` along the
localisation morphism `Spec R_f ⟶ Spec R`.  This identifies the double restriction with a single
pullback, and is the comparison isomorphism `F|_{D(f)} ≅ F_{(f)}` of the blueprint.  Project-local:
reconciles the (good-defeq) iterated `restrict` with the conceptual inverse-image description. -/
noncomputable def modulesRestrictBasicOpenIso (F : (Spec R).Modules) :
    modulesRestrictBasicOpen f F ≅
      (Scheme.Modules.pullback (specAwayToSpec f)).obj F :=
  ((Scheme.Modules.restrictFunctorComp (basicOpenIsoSpecAway f).inv (specBasicOpen f).ι).app F).symm
    ≪≫ (Scheme.Modules.restrictFunctorIsoPullback (specAwayToSpec f)).app F

/-- The localisation morphism `Spec R_f ⟶ Spec R` of `specAwayToSpec` is exactly the spectrum of the
away-localisation ring map `R → R_f`.  Project-local: identifies the geometric transport map with
the algebraic `Spec.map (algebraMap …)`, so that pullback along it computes base change. -/
theorem specAwayToSpec_eq :
    specAwayToSpec f = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
  rw [specAwayToSpec, Iso.inv_comp_eq]
  exact (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm

/-! ## Project-local Mathlib supplement — Route B presentation transport (B2–B4) -/

open SheafOfModules in
set_option backward.isDefEq.respectTransparency false in
/-- **Route B, step B2.** If `M.over U` carries a presentation and `D(g) ⊆ U`, then the further
over-restriction `M.over D(g)` admits a presentation. -/
noncomputable def presentationOverBasicOpen
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (P : (M.over U).Presentation) (g : R) (hg : specBasicOpen g ≤ U) :
    (M.over (specBasicOpen g)).Presentation :=
  letI W : Over U := Over.mk (homOfLE hg)
  letI e : SheafOfModules.{u} ((Spec R).ringCatSheaf.over W.left) ≌
      SheafOfModules.{u} (((Spec R).ringCatSheaf.over U).over W) :=
    pushforwardPushforwardEquivalence
    (Over.iteratedSliceEquiv W)
    (S := ((Spec R).ringCatSheaf.over U).over W)
    (R := (Spec R).ringCatSheaf.over W.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact (Spec R).ringCatSheaf.1.map_id _)
    (by ext : 2; exact (Spec R).ringCatSheaf.1.map_id _)
  letI P1 : ((M.over U).over W).Presentation :=
    P.map (pushforward (𝟙 (((Spec R).ringCatSheaf.over U).over W))) (by rfl)
  letI P2 : (e.inverse.obj ((M.over U).over W)).Presentation :=
    P1.map e.inverse (.refl _)
  letI iso : e.inverse.obj ((M.over U).over W) ≅ M.over W.left :=
    e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over U).over W))
  show (M.over W.left).Presentation from Presentation.ofIsIso.{u, u, u} iso.hom P2

section RestrictOverBridge

open SheafOfModules TopologicalSpace

private lemma specBasicOpen_ι_image_overEquivalence_functor (g : R) (V : Over (specBasicOpen g)) :
    (specBasicOpen g).ι ''ᵁ (Opens.overEquivalence (specBasicOpen g)).functor.obj V = V.left := by
  apply Opens.ext
  exact Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x, leOfHom V.hom hx⟩, rfl⟩)

/-- Continuity of `overEquivalence.functor` phrased for the open-subscheme carrier (defeq to the
plain subtype, but instance search needs the `toScheme` form to fire). -/
instance overEquivalence_functor_isContinuous_toScheme (g : R) :
    (Opens.overEquivalence (specBasicOpen g)).functor.IsContinuous
      ((Opens.grothendieckTopology ↥(Spec R)).over (specBasicOpen g))
      (Opens.grothendieckTopology ↥(specBasicOpen g).toScheme) :=
  Opens.overEquivalence_functor_isContinuous (specBasicOpen g)

/-- Continuity of `overEquivalence.inverse` phrased for the open-subscheme carrier. -/
instance overEquivalence_inverse_isContinuous_toScheme (g : R) :
    (Opens.overEquivalence (specBasicOpen g)).inverse.IsContinuous
      (Opens.grothendieckTopology ↥(specBasicOpen g).toScheme)
      ((Opens.grothendieckTopology ↥(Spec R)).over (specBasicOpen g)) :=
  Opens.overEquivalence_inverse_isContinuous (specBasicOpen g)

/-- The forgetful functor `Over D(g) ⥤ Opens (Spec R)` agrees (via the open-immersion image–preimage
identity `ι ''ᵁ (ι ⁻¹ᵁ V) = V` for `V ≤ D(g)`) with the over-site equivalence followed by the
open-immersion `opensFunctor`. In the thin `Opens` category naturality is automatic. Project-local:
the geometric datum underlying the Route B restrict–over bridge (B3a). -/
noncomputable def overForgetIso (g : R) :
    Over.forget (specBasicOpen g) ≅
      (Opens.overEquivalence (specBasicOpen g)).functor ⋙ (specBasicOpen g).ι.opensFunctor :=
  NatIso.ofComponents
    (fun V => eqToIso (specBasicOpen_ι_image_overEquivalence_functor g V).symm)
    (fun {_ _} _ => Subsingleton.elim _ _)

/-- The structure-sheaf comparison `φ` feeding `pushforwardPushforwardEquivalence`: the over-picture
ring sheaf `(Spec R).ringCatSheaf.over D(g)` maps to the `overEquivalence`-pushforward of the
subscheme ring sheaf. Built by whiskering `overForgetIso.inv` into `(Spec R).ringCatSheaf`. -/
noncomputable def overBasicOpenRingHom (g : R) :
    Sheaf.over (Spec R).ringCatSheaf (specBasicOpen g) ⟶
      ((Opens.overEquivalence (specBasicOpen g)).functor.sheafPushforwardContinuous RingCat
        ((Opens.grothendieckTopology ↥(Spec R)).over (specBasicOpen g))
        (Opens.grothendieckTopology ↥(specBasicOpen g).toScheme)).obj
      (specBasicOpen g).toScheme.ringCatSheaf :=
  ⟨Functor.whiskerRight (NatTrans.op (overForgetIso g).inv) (Spec R).ringCatSheaf.obj⟩

/-- The inverse over-site equivalence followed by `Over.forget` is *definitionally* the
open-immersion `opensFunctor` (`overEquivalence.inverse` sends `W` to `⟨Subtype.val '' W, _⟩`, whose
`.left` is `ι ''ᵁ W`). Project-local: the (trivial) reverse datum of the B3 bridge. -/
noncomputable def overForgetInvIso (g : R) :
    (Opens.overEquivalence (specBasicOpen g)).inverse ⋙ Over.forget (specBasicOpen g) ≅
      (specBasicOpen g).ι.opensFunctor :=
  Iso.refl _

/-- The reverse structure-sheaf comparison `ψ` feeding `pushforwardPushforwardEquivalence`
(whiskering of `overForgetInvIso.inv`, which is the identity). -/
noncomputable def overBasicOpenRingInvHom (g : R) :
    (specBasicOpen g).toScheme.ringCatSheaf ⟶
      ((Opens.overEquivalence (specBasicOpen g)).inverse.sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology ↥(specBasicOpen g).toScheme)
        ((Opens.grothendieckTopology ↥(Spec R)).over (specBasicOpen g))).obj
      (Sheaf.over (Spec R).ringCatSheaf (specBasicOpen g)) :=
  ⟨Functor.whiskerRight (NatTrans.op (overForgetInvIso g).inv) (Spec R).ringCatSheaf.obj⟩

/-- **Route B, step B3 (the load-bearing bridge — engine).** The equivalence of categories of
sheaves of modules between the open subscheme `D(g)` and the over-site
`(Spec R).ringCatSheaf.over D(g)`,
obtained from `pushforwardPushforwardEquivalence` along the (continuous) over-site equivalence
`Opens.overEquivalence (specBasicOpen g)` fed the structure-sheaf comparison data
`overBasicOpenRingHom`/`overBasicOpenRingInvHom`. Its functor sends a subscheme module
`F.restrict ι` to the over-picture restriction `F.over D(g)` (agreeing on sections by
`restrict_obj`);
this object correspondence is the bridge `overBasicOpenIsoRestrict` consumed by B4. -/
noncomputable def modulesOverBasicOpenEquivalence (g : R) :
    (specBasicOpen g).toScheme.Modules ≌
      SheafOfModules.{u} ((Spec R).ringCatSheaf.over (specBasicOpen g)) :=
  pushforwardPushforwardEquivalence (Opens.overEquivalence (specBasicOpen g))
    (overBasicOpenRingHom g) (overBasicOpenRingInvHom g)
    (by
      refine NatTrans.ext (funext fun (V : (Opens ↥(specBasicOpen g))ᵒᵖ) => ?_)
      simp only [overBasicOpenRingHom, overBasicOpenRingInvHom, NatTrans.comp_app,
        Functor.whiskerRight_app, NatTrans.op_app, Functor.whiskerLeft_app]
      erw [← Functor.map_comp]
      exact congrArg (Spec R).ringCatSheaf.obj.map (Subsingleton.elim _ _))
    (by
      refine NatTrans.ext (funext fun (V : (Over (specBasicOpen g))ᵒᵖ) => ?_)
      simp only [overBasicOpenRingHom, overBasicOpenRingInvHom, NatTrans.comp_app,
        Functor.whiskerRight_app, NatTrans.op_app, Functor.whiskerLeft_app,
        NatTrans.id_app, overForgetInvIso, Iso.refl_inv]
      erw [← Functor.map_comp]
      exact (congrArg (Spec R).ringCatSheaf.obj.map (Subsingleton.elim _ (𝟙 _))).trans
        ((Spec R).ringCatSheaf.obj.map_id _))

set_option backward.isDefEq.respectTransparency false in
/-- **Route B, step B3 object iso.** The bridge: the inverse engine applied to the over-picture
restriction `M.over D(g)` is the honest subscheme restriction `M.restrict ι`. -/
noncomputable def overBasicOpenIsoRestrict (g : R) (M : (Spec R).Modules) :
    (modulesOverBasicOpenEquivalence g).inverse.obj (M.over (specBasicOpen g)) ≅
      M.restrict (specBasicOpen g).ι := by
  haveI iinv := overEquivalence_inverse_isContinuous_toScheme g
  haveI icomp := CategoryTheory.Functor.isContinuous_comp
    (Opens.overEquivalence (specBasicOpen g)).inverse (Over.forget (specBasicOpen g))
    (Opens.grothendieckTopology ↥(specBasicOpen g).toScheme)
    ((Opens.grothendieckTopology ↥(Spec R)).over (specBasicOpen g))
    (Opens.grothendieckTopology ↥(Spec R))
  refine (SheafOfModules.pushforwardComp (G := Over.forget (specBasicOpen g))
    (R' := (Spec R).ringCatSheaf)
    (overBasicOpenRingInvHom g)
    (𝟙 ((Spec R).ringCatSheaf.over (specBasicOpen g)))).app M ≪≫ ?_
  refine (SheafOfModules.pushforwardCongr (F := (specBasicOpen g).ι.opensFunctor) ?heq).app M
  ext U : 3
  simp [overBasicOpenRingInvHom, overForgetInvIso, Scheme.Opens.ι_appIso]
  rfl

/-- `(basicOpenIsoSpecAway g).inv` is an isomorphism, so its `Opens.map` is final; hence the
unit-comparison `pullbackObjUnitToUnit` of the affine restriction is an isomorphism. -/
instance pullbackObjUnitToUnit_isIso_basicOpen (g : R) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit
      ((basicOpenIsoSpecAway g).inv).toRingCatSheafHom) := by
  haveI : IsIso (((basicOpenIsoSpecAway g).inv).base) := inferInstance
  haveI : (TopologicalSpace.Opens.map ((basicOpenIsoSpecAway g).inv).base).Final := by
    haveI : (TopologicalSpace.Opens.map ((basicOpenIsoSpecAway g).inv).base).IsEquivalence :=
      (TopologicalSpace.Opens.mapMapIso
        (asIso ((basicOpenIsoSpecAway g).inv).base)).isEquivalence_functor
    infer_instance
  infer_instance

/-- The restriction-along-the-affine-identification functor sends the structure-sheaf unit to the
structure-sheaf unit: `(restrict (basicOpenIsoSpecAway g).inv).obj 𝟙_{D(g)} ≅ 𝟙_{Spec R_g}`.
Built from `restrictFunctorIsoPullback` + `pullbackObjUnitToUnit` (an iso since
`(basicOpenIsoSpecAway g).inv`
is an isomorphism, hence its `Opens.map` is final). Extracted as its own declaration so the
instance search runs in a clean context. -/
noncomputable def restrictBasicOpenUnitIso (g : R) :
    (Scheme.Modules.restrictFunctor.{u} (basicOpenIsoSpecAway g).inv).obj
        (SheafOfModules.unit (specBasicOpen g).toScheme.ringCatSheaf) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away g))).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback (basicOpenIsoSpecAway g).inv).app _ ≪≫
    @asIso _ _ _ _ _ (pullbackObjUnitToUnit_isIso_basicOpen g)

set_option synthInstance.maxHeartbeats 400000 in
-- The transport crosses sheafification and colimit-preservation on the localized site; the default
-- synthesis budget is insufficient for this instance search.
open SheafOfModules in
/-- **Route B, step B4.** If `M.over U` carries a presentation and `D(g) ⊆ U`, then the affine
restriction `modulesRestrictBasicOpen g M`, as a `(Spec R_g).Modules`-object, admits a global
presentation. Assembled by transporting the B2 over-presentation across the B3 bridge isomorphism
`overBasicOpenIsoRestrict` and the restriction along the affine identification. -/
noncomputable def presentationModulesRestrictBasicOpen
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (P : (M.over U).Presentation) (g : R) (hg : specBasicOpen g ≤ U) :
    (modulesRestrictBasicOpen g M).Presentation := by
  letI P2 : (M.over (specBasicOpen g)).Presentation := presentationOverBasicOpen M U P g hg
  letI P3 : ((modulesOverBasicOpenEquivalence g).inverse.obj
      (M.over (specBasicOpen g))).Presentation :=
    P2.map (modulesOverBasicOpenEquivalence g).inverse (.refl _)
  letI P4 : (M.restrict (specBasicOpen g).ι).Presentation :=
    Presentation.ofIsIso.{u, u, u} (overBasicOpenIsoRestrict g M).hom P3
  -- The instance is supplied as `hpc` (and the functor universe pinned to `u`): inline instance
  -- search for `PreservesColimitsOfSize` of the affine restriction does not fire on its own here.
  haveI hpc : Limits.PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (Scheme.Modules.restrictFunctor.{u} (basicOpenIsoSpecAway g).inv) := inferInstance
  exact @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P4
    (Scheme.Modules.restrictFunctor.{u} (basicOpenIsoSpecAway g).inv) hpc
    (restrictBasicOpenUnitIso g).symm

end RestrictOverBridge

end AlgebraicGeometry
