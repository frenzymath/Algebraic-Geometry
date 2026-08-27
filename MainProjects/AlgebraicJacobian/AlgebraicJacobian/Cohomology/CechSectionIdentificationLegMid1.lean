/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLeg

/-!
# Sub-brick A — LegMid1: backbone projection and object-iso coordinate lemmas

`backboneIncl_proj` (the Stub-1 unwinding, 3.2M HB), `backboneIncl_nerveδ`, `GVΨ_map_eq`,
`piMapIso_hom_π` (private), `coreIso_objIso_π`, and `pushPullLegIso` (private def).

Split from `CechSectionIdentificationLeg` to keep per-file heartbeat budget under 10 min.
Depends on `CechSectionIdentificationLeg` (transitively Base).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}
/-- The cover-arrow inclusion of a member, as an over-`X` morphism. -/
private noncomputable def coverArrowIncl (𝒰 : X.OpenCover) (i : 𝒰.I₀) :
    Over.mk (𝒰.f i) ⟶ Over.mk (Sigma.desc 𝒰.f) :=
  Over.homMk (Sigma.ι 𝒰.X i) (Limits.Sigma.ι_desc 𝒰.f i)

/-- The universe-reduction reindexing of the cover arrow, as an over-`X` morphism. -/
private noncomputable def coverReindexHom (𝒰 : X.OpenCover) [Finite 𝒰.I₀] :
    Over.mk (Limits.Sigma.desc (fun j : Fin (Nat.card 𝒰.I₀) =>
      𝒰.f ((Finite.equivFin 𝒰.I₀).symm j))) ⟶ Over.mk (Sigma.desc 𝒰.f) :=
  Over.homMk (Sigma.whiskerEquiv (Finite.equivFin 𝒰.I₀).symm
    (fun j => Iso.refl (𝒰.X ((Finite.equivFin 𝒰.I₀).symm j)))).hom
    (by
      refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
      simp only [Sigma.whiskerEquiv, Iso.refl_inv, Limits.Sigma.ι_desc, Over.mk_hom]
      refine Eq.trans (Limits.Sigma.ι_comp_map'_assoc _ _ _ _) ?_
      exact Eq.trans (Category.id_comp _) (Limits.Sigma.ι_desc _ _))

/-- **Backbone inclusion/projection characterization** (the Stub-1 unwinding): the
`τ`-summand inclusion of the backbone followed by the `l`-th wide-pullback projection is
the canonical component map `interProj 𝒰 τ l`. -/
lemma backboneIncl_proj (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (p : ℕ)
    (τ : Fin (p + 1) → 𝒰.I₀) (l : Fin (p + 1)) :
    backboneIncl 𝒰 p τ ≫ backboneProj 𝒰 p l = interProj 𝒰 τ l := by
  -- absorption: any over-morphism into a member, followed by its cover-arrow inclusion,
  -- is the canonical `interProj` (mono-target rigidity of `𝒰.f _`)
  have habs : ∀ (j' : 𝒰.I₀) (hj : j' = τ l)
      (w : Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ)) ⟶ Over.mk (𝒰.f j')),
      w ≫ coverArrowIncl 𝒰 j' = interProj 𝒰 τ l := by
    rintro j' rfl w
    have hfact : interProj 𝒰 τ l =
        Over.homMk (coverInterToMember 𝒰 τ l) (coverInterToMember_fac 𝒰 τ l) ≫
          coverArrowIncl 𝒰 (τ l) := by
      apply Over.OverMorphism.ext
      rfl
    rw [hfact]
    exact congrArg (fun u => u ≫ coverArrowIncl 𝒰 (τ l))
      (over_hom_ext_mono w (Over.homMk (coverInterToMember 𝒰 τ l)
        (coverInterToMember_fac 𝒰 τ l)))
  -- the descent inclusion of the reindexed family lands on the cover-arrow inclusion
  have hred : ∀ j : Fin (Nat.card 𝒰.I₀),
      overDescIncl (fun j' : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j')) j ≫
        coverReindexHom 𝒰 =
      coverArrowIncl 𝒰 ((Finite.equivFin 𝒰.I₀).symm j) := by
    intro j
    apply Over.OverMorphism.ext
    exact Eq.trans (Limits.Sigma.ι_comp_map' _ _ _) (Category.id_comp _)
  -- the wide-pullback transport layer exchanges the projections
  have htail : ∀ (hw : _) , (widePullbackBaseCongr (Sigma.desc 𝒰.f)
        (Limits.Sigma.desc (fun j : Fin (Nat.card 𝒰.I₀) =>
          𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)))
        (Sigma.whiskerEquiv (Finite.equivFin 𝒰.I₀).symm
          (fun j => Iso.refl (𝒰.X ((Finite.equivFin 𝒰.I₀).symm j)))) hw (p + 1)).inv ≫
        backboneProj 𝒰 p l =
      overWPproj (fun j : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j))
          (p + 1) l ≫ coverReindexHom 𝒰 := by
    intro hw
    apply Over.OverMorphism.ext
    exact WidePullback.lift_π _ _ _ _ l
  -- collapse the descent-iso layer onto the plain coproduct inclusion
  have ha2 : coprodOverIncl (fun σ : Fin (p + 1) → 𝒰.I₀ =>
      Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) τ ≫
      (overSigmaDescIso (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).hom)).inv =
      Limits.Sigma.ι (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) τ := by
    rw [Iso.comp_inv_eq]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))
      (overSigmaDescIsColimit _) (Discrete.mk τ)).symm
  -- ASSEMBLY: the five backbone-iso layers are peeled in ONE generic reassociation pass
  -- (`glue_chain`, proved in a clean abstract context), fed by `ha2` (entry), `htail`
  -- (wide-pullback congruence layer), `ι_sigmaMapIso_inv` (coverInterProdIso layer), the
  -- combined reindex+distributivity characterization `ι_reindex_wpci_inv_overWPproj`, and
  -- `hred`; `habs` absorbs the residual prefix by mono-target rigidity.
  -- the wZ-triangle witness consumed by `htail`
  have hwZ : (Sigma.whiskerEquiv (Finite.equivFin 𝒰.I₀).symm
        (fun j => Iso.refl (𝒰.X ((Finite.equivFin 𝒰.I₀).symm j)))).hom ≫ Sigma.desc 𝒰.f =
      Limits.Sigma.desc (fun j : Fin (Nat.card 𝒰.I₀) =>
        𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)) := by
    refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
    simp only [Sigma.whiskerEquiv, Iso.refl_inv, Limits.Sigma.ι_comp_map'_assoc,
      Category.id_comp, Limits.Sigma.ι_desc]
  -- the five layers of the backbone identification, read backwards
  have hexp : (cechBackbone_left_sigma 𝒰 p).inv =
      ((((Limits.Sigma.mapIso (fun σ : Fin (p + 1) → 𝒰.I₀ => coverInterProdIso 𝒰 σ)).inv ≫
        (Sigma.whiskerEquiv (Equiv.arrowCongr (Equiv.refl (Fin (p + 1)))
            (Finite.equivFin 𝒰.I₀).symm)
          (fun σ : Fin (p + 1) → Fin (Nat.card 𝒰.I₀) =>
            Iso.refl (∏ᶜ fun k => Over.mk (𝒰.f ((Finite.equivFin 𝒰.I₀).symm (σ k)))))).inv) ≫
        (FinitaryPreExtensive.widePullback_coproduct_iso
          (fun j : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)) p).inv) ≫
        (widePullbackBaseCongr (Sigma.desc 𝒰.f)
          (Limits.Sigma.desc (fun j : Fin (Nat.card 𝒰.I₀) =>
            𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)))
          (Sigma.whiskerEquiv (Finite.equivFin 𝒰.I₀).symm
            (fun j => Iso.refl (𝒰.X ((Finite.equivFin 𝒰.I₀).symm j)))) hwZ (p + 1)).inv) ≫
        (cechBackbone_obj_widePullback 𝒰 p).inv := rfl
  refine Eq.trans (entry_chain _ _ _ (backboneProj 𝒰 p l) _ ha2) ?_
  rw [hexp]
  refine Eq.trans (glue_chain
    (Limits.Sigma.ι (fun σ : Fin (p + 1) → 𝒰.I₀ =>
      Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) τ)
    (Limits.Sigma.mapIso (fun σ : Fin (p + 1) → 𝒰.I₀ => coverInterProdIso 𝒰 σ)).inv
    (Sigma.whiskerEquiv (Equiv.arrowCongr (Equiv.refl (Fin (p + 1)))
        (Finite.equivFin 𝒰.I₀).symm)
      (fun σ : Fin (p + 1) → Fin (Nat.card 𝒰.I₀) =>
        Iso.refl (∏ᶜ fun k => Over.mk (𝒰.f ((Finite.equivFin 𝒰.I₀).symm (σ k)))))).inv
    (FinitaryPreExtensive.widePullback_coproduct_iso
      (fun j : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)) p).inv
    (widePullbackBaseCongr (Sigma.desc 𝒰.f)
      (Limits.Sigma.desc (fun j : Fin (Nat.card 𝒰.I₀) =>
        𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)))
      (Sigma.whiskerEquiv (Finite.equivFin 𝒰.I₀).symm
        (fun j => Iso.refl (𝒰.X ((Finite.equivFin 𝒰.I₀).symm j)))) hwZ (p + 1)).inv
    (cechBackbone_obj_widePullback 𝒰 p).inv
    (backboneProj 𝒰 p l) (backboneProj 𝒰 p l)
    (Category.id_comp (backboneProj 𝒰 p l))
    ((coverInterProdIso 𝒰 τ).inv)
    (Limits.Sigma.ι (fun σ : Fin (p + 1) → 𝒰.I₀ =>
      ∏ᶜ fun k => Over.mk (𝒰.f (σ k))) τ)
    (ι_sigmaMapIso_inv (fun σ : Fin (p + 1) → 𝒰.I₀ => coverInterProdIso 𝒰 σ) τ)
    (overWPproj (fun j : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j))
      (p + 1) l)
    (coverReindexHom 𝒰) (htail hwZ)
    (eqToHom (congrArg (fun fam : Fin (p + 1) → 𝒰.I₀ =>
        ∏ᶜ fun k => Over.mk (𝒰.f (fam k)))
      (funext (fun k => ((Finite.equivFin 𝒰.I₀).symm_apply_apply (τ k)).symm))) ≫
      Pi.π (fun k => Over.mk (𝒰.f ((Finite.equivFin 𝒰.I₀).symm
        ((Finite.equivFin 𝒰.I₀) (τ k))))) l)
    (overDescIncl (fun j : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j))
      ((Finite.equivFin 𝒰.I₀) (τ l)))
    ((ι_reindex_wpci_inv_overWPproj 𝒰.f (Finite.equivFin 𝒰.I₀) p τ l).trans
      ((Category.assoc _ _ _).symm))
    (coverArrowIncl 𝒰 ((Finite.equivFin 𝒰.I₀).symm ((Finite.equivFin 𝒰.I₀) (τ l))))
    (hred ((Finite.equivFin 𝒰.I₀) (τ l)))) ?_
  exact habs ((Finite.equivFin 𝒰.I₀).symm ((Finite.equivFin 𝒰.I₀) (τ l)))
    ((Finite.equivFin 𝒰.I₀).symm_apply_apply (τ l)) _

/-- **Per-leg coface factorization of the backbone inclusion** (★): the `σ'`-summand
inclusion of the degree-`(p+1)` backbone followed by the geometric nerve coface
factors as the open inclusion `U_{σ'} ⊆ U_{σ'∘δᵏ}` followed by the `σ'∘δᵏ`-summand
inclusion of the degree-`p` backbone.  Proved projection-by-projection
(`backbone_hom_ext`), where both sides become canonical component maps. -/
lemma backboneIncl_nerveδ (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (p : ℕ)
    (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀) :
    backboneIncl 𝒰 (p + 1) σ' ≫ (coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op) =
      interLegHom 𝒰 σ' k ≫ backboneIncl 𝒰 p (σ' ∘ (SimplexCategory.δ k).toOrderHom) := by
  apply backbone_hom_ext
  intro l
  rw [Category.assoc, nerveδ_backboneProj, backboneIncl_proj, Category.assoc,
    backboneIncl_proj, interLegHom_interProj]

/-! ### Section-level seam: projecting `coreIso_objIso` and the per-leg restriction. -/

/-- The section-at-`V` functor `Γ(V, ·) : X.Modules ⥤ Ab` (the `E` of
`pushPull_eval_prod_iso`). -/
noncomputable abbrev sectionFunctorV (V : TopologicalSpace.Opens ↥X) : X.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheaf X ⋙
    (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ Ab.{u}).obj (Opposite.op V)

/-- The statement-level evaluated adapter `G_V ∘ Ψ` agrees with `sectionFunctorV` on
morphisms of `X.Modules` (definitional: `restrictScalars (𝟙 _)` does not change the
underlying abelian presheaf map). -/
lemma GVΨ_map_eq (V : TopologicalSpace.Opens ↥X) {M N : X.Modules} (φ : M ⟶ N) :
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
        (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
      ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map φ) =
    (sectionFunctorV V).map φ :=
  rfl

/-- Projection of a `Pi.mapIso` onto a factor (the `limMap_π` instance for discrete
shapes, stated so it can be applied term-wise against the bundled section products). -/
@[reassoc]
private lemma piMapIso_hom_π {β : Type u} {f g : β → Ab.{u}}
    (w : ∀ b, f b ≅ g b) (b : β) :
    (Pi.mapIso w).hom ≫ Pi.π g b = Pi.π f b ≫ (w b).hom := by
  have h := limMap_π (F := Discrete.functor f) (G := Discrete.functor g)
    (Discrete.natIso (fun j => w j.as)).hom ⟨b⟩
  exact h

/-- **Coordinate formula for the degreewise object iso** (`coreIso_objIso`): its
`τ`-projection is the evaluated push–pull map of the backbone inclusion `backboneIncl`,
followed by the per-leg section identification `pushPull_leg_sections` and the open-meet
reindex of `coverInterOpen_inf_eq_iInf_inf`. -/
lemma coreIso_objIso_π (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (p : ℕ)
    (V : TopologicalSpace.Opens ↥X) (τ : Fin (p + 1) → 𝒰.I₀) :
    (coreIso_objIso 𝒰 F p V).hom ≫
        Pi.π (fun σ : Fin (p + 1) → 𝒰.I₀ =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
            (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) τ =
      (sectionFunctorV V).map (pushPullMap F (backboneIncl 𝒰 p τ)) ≫
        (pushPull_leg_sections 𝒰 F τ V).hom ≫
        eqToHom (congrArg (fun W =>
            ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
          (coverInterOpen_inf_eq_iInf_inf 𝒰 τ V)) := by
  simp only [coreIso_objIso, pushPull_eval_prod_iso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, PreservesProduct.iso_hom]
  -- project layer by layer (term-level, defeq-robust): the open-meet reindex …
  refine Eq.trans (congrArg (fun w => (sectionFunctorV V).map (pushPull_sigma_iso 𝒰 F p).hom ≫
      piComparison (sectionFunctorV V) (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≫
      (Pi.mapIso (fun σ : Fin (p + 1) → 𝒰.I₀ => pushPull_leg_sections 𝒰 F σ V)).hom ≫ w)
    (piMapIso_hom_π (fun σ : Fin (p + 1) → 𝒰.I₀ => eqToIso (congrArg (fun W =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
      (coverInterOpen_inf_eq_iInf_inf 𝒰 σ V))) τ)) ?_
  -- … the per-leg section identification …
  refine Eq.trans (congrArg (fun w => (sectionFunctorV V).map (pushPull_sigma_iso 𝒰 F p).hom ≫
      piComparison (sectionFunctorV V) (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≫ w)
    (piMapIso_hom_π_assoc (fun σ : Fin (p + 1) → 𝒰.I₀ => pushPull_leg_sections 𝒰 F σ V) τ
      (eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 τ V))))) ?_
  -- … the product comparison of the section functor …
  refine Eq.trans (congrArg (fun w => (sectionFunctorV V).map
      (pushPull_sigma_iso 𝒰 F p).hom ≫ w)
    (piComparison_comp_π_assoc (sectionFunctorV V) (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) τ
      ((pushPull_leg_sections 𝒰 F τ V).hom ≫ eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 τ V))))) ?_
  -- … and the σ-leg of the product decomposition (`pushPull_sigma_iso_π`).
  refine Eq.trans ((Functor.map_comp_assoc _ _ _ _).symm) ?_
  exact congrArg (fun w => (sectionFunctorV V).map w ≫
      (pushPull_leg_sections 𝒰 F τ V).hom ≫
      eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 τ V)))
    (pushPull_sigma_iso_π_incl 𝒰 F p τ)

/-- The canonical leg iso for the push–pull of an over-morphism with open-immersion
underlying map (replica of the Base `private pushPullCoprodLegIso`, whose proof never
uses the coproduct structure of its ambient scheme). -/
noncomputable def pushPullLegIso {A C' : Scheme.{u}} (q : A ⟶ X)
    (c : C' ⟶ A) [IsOpenImmersion c] (pC : C' ⟶ X) (wC : c ≫ q = pC) (F : X.Modules) :
    (pushforward q).obj ((pushforward c).obj
        (((Scheme.Modules.pullback q).obj F).restrict c)) ≅
      pushPullObj F (Over.mk pC) :=
  (pushforward q).mapIso ((pushforward c).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback c).app ((Scheme.Modules.pullback q).obj F) ≪≫
      (Scheme.Modules.pullbackComp c q).app F ≪≫
      (Scheme.Modules.pullbackCongr wC).app F)) ≪≫
  eqToIso (congrArg (fun p' => (pushforward p').obj ((Scheme.Modules.pullback pC).obj F)) wC)

-- The final `rfl` discharges the proof-irrelevant `eqToHom` over-triangle transports against
-- concrete pushforward/pullback objects, whose `whnf` exceeds the default heartbeat budget.
end AlgebraicGeometry
