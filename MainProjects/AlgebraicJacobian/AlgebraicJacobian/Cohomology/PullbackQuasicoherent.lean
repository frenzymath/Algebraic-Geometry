/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechTermAcyclic

/-!
# Pullback preserves quasi-coherence (Stacks 01BG, general morphism)

For an arbitrary morphism of schemes `g : Y ⟶ X` and a quasi-coherent
`F : X.Modules`, the module pullback `g^* F = (Scheme.Modules.pullback g).obj F`
is quasi-coherent (`pullback_isQuasicoherent_hom`).  This generalizes the
open-immersion case `isQuasicoherent_pullback_opens` (`CechTermAcyclic.lean`);
the previously-documented obstruction — `SheafOfModules.Presentation.map` only
transports a *global* presentation while quasi-coherence is *local* — is resolved
by localizing the pullback itself: over each member `U` of the quasi-coherence
cover of `X`, the restriction of `g^* F` to the preimage `W = g⁻¹(U)` is the
pullback of `F|_U` along the restricted morphism `g.resLE U W : W ⟶ U`
(the pullback pseudofunctor square `resLE_comp_ι`), and the *global* presentation
of `F|_U` transports along that restricted pullback.

Two supporting facts are proved on the way:

* `opensMap_final`: for any continuous map `φ`, the preimage functor
  `Opens.map φ` on opens is `Final` — the costructured comma poset
  `{U // d ≤ φ⁻¹(U)}` is nonempty (`⊤`) and `⊔`-directed, hence filtered.
* `pullbackObjUnitToUnit_isIso_hom`: consequently Mathlib's unit comparison
  `pullbackObjUnitToUnit` is an isomorphism for the module pullback along *any*
  scheme morphism, i.e. `g^* 𝒪_X ≅ 𝒪_Y` (`pullbackUnitIso`).

These feed the flat-base-change RHS tilde leaf
`pushPullObj_coverInter_baseChanged_pushforward_iso_tilde`
(`CechHigherDirectImageUnconditional.lean`), which needs quasi-coherence of the
base-changed module `g'^* F` to apply the altitude-2 bridge
`pushPullObj_pushforward_iso_tilde` on the base-changed side.
-/

universe u

set_option maxSynthPendingDepth 3

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

open Scheme.Modules

/-! ## Finality of the opens-preimage functor -/

/-- The costructured comma category `StructuredArrow d (Opens.map φ)` — the poset of opens
`U` of the target with `d ≤ φ⁻¹(U)` — is filtered: it is nonempty (`U = ⊤`) and closed
under binary joins (`φ⁻¹` is monotone and preserves `⊔`), and it is thin, so parallel
pairs are automatically equalized. -/
instance opensMapStructuredArrow_isFiltered {T T' : TopCat.{u}} (φ : T ⟶ T')
    (d : Opens T) : IsFiltered (StructuredArrow d (Opens.map φ)) := by
  haveI hne : Nonempty (StructuredArrow d (Opens.map φ)) :=
    ⟨StructuredArrow.mk (Y := ⊤) (homOfLE (fun x _ => trivial))⟩
  haveI hfe : IsFilteredOrEmpty (StructuredArrow d (Opens.map φ)) := by
    constructor
    · intro j₁ j₂
      refine ⟨StructuredArrow.mk (Y := j₁.right ⊔ j₂.right)
          (j₁.hom ≫ (Opens.map φ).map (homOfLE le_sup_left)),
        StructuredArrow.homMk (homOfLE le_sup_left) rfl,
        StructuredArrow.homMk (homOfLE le_sup_right) (Subsingleton.elim _ _), trivial⟩
    · intro j₁ j₂ f g
      exact ⟨j₂, 𝟙 j₂, by apply StructuredArrow.hom_ext; exact Subsingleton.elim _ _⟩
  constructor

/-- **The opens-preimage functor of any continuous map is final.**  Consequently global
sections of a pushforward along any scheme morphism compare correctly, and the module
pullback of the structure sheaf is the structure sheaf (`pullbackObjUnitToUnit` is an
isomorphism, Mathlib's `[F.Final]` instance in `PullbackFree.lean`). -/
instance opensMap_final {T T' : TopCat.{u}} (φ : T ⟶ T') : (Opens.map φ).Final :=
  Functor.final_of_isFiltered_structuredArrow _

/-- **`g^* 𝒪_X ≅ 𝒪_Y` for an arbitrary scheme morphism**: the unit comparison of the
module pullback along any scheme morphism is an isomorphism (the underlying site functor
`Opens.map g.base` is final by `opensMap_final`). -/
instance pullbackObjUnitToUnit_isIso_hom {Y X : Scheme.{u}} (g : Y ⟶ X) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) :=
  inferInstance

/-- The structure-sheaf unit iso `g^* 𝒪_X ≅ 𝒪_Y` for an arbitrary scheme morphism,
packaged for `Presentation.map`. -/
noncomputable def pullbackUnitIso {Y X : Scheme.{u}} (g : Y ⟶ X) :
    (Scheme.Modules.pullback g).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  @asIso _ _ _ _ _ (pullbackObjUnitToUnit_isIso_hom g)

/-! ## The per-slice presentation of a pullback -/

set_option backward.isDefEq.respectTransparency false in
/-- **The per-slice presentation of a pullback**: a presentation of `F.over A` induces a
presentation of the slice `(g^* F).over (g ⁻¹ᵁ A)`, for an arbitrary scheme morphism
`g : Y ⟶ X`.

Route: let `W := g ⁻¹ᵁ A` and `gA := g.resLE A W : W ⟶ A` the restricted morphism.  The
X-side bridge (`presentationRestrictOfOver` at `W := A`) presents the full restriction
`F.restrict A.ι`; the restricted pullback `(pullback gA)` transports it
(`Presentation.map`, unit iso by `pullbackUnitIso`); the pullback pseudofunctor square
`gA ≫ A.ι = W.ι ≫ g` (`resLE_comp_ι`) identifies `(pullback gA).obj (F.restrict A.ι)`
with `(g^* F).restrict W.ι`; the V-side bridge engine (`modulesOverOpensEquivalence`
over `Y`) carries the presentation back to the over-slice. -/
noncomputable def presentationPullbackSliceOfOver {Y X : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (A : X.Opens) (P : (F.over A).Presentation) :
    (((Scheme.Modules.pullback g).obj F).over (g ⁻¹ᵁ A)).Presentation := by
  set W : Y.Opens := g ⁻¹ᵁ A with hW
  set G : Y.Modules := (Scheme.Modules.pullback g).obj F with hG
  -- X-side: present the full restriction to `A`.
  letI P1 : (F.restrict A.ι).Presentation := presentationRestrictOfOver A F A P le_rfl
  -- The restricted morphism `W ⟶ A`.
  letI gA : W.toScheme ⟶ A.toScheme := g.resLE A W le_rfl
  -- Transport the presentation along the restricted pullback (colimit-preserving; unit ↦ unit).
  haveI hpc : Limits.PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (Scheme.Modules.pullback gA) := inferInstance
  letI P2 : ((Scheme.Modules.pullback gA).obj (F.restrict A.ι)).Presentation :=
    @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P1
      (Scheme.Modules.pullback gA) hpc (pullbackUnitIso gA).symm
  -- Identify with the restriction of the global pullback via the pseudofunctor square.
  have heq : gA ≫ A.ι = W.ι ≫ g := Scheme.Hom.resLE_comp_ι g le_rfl
  letI e : (Scheme.Modules.pullback gA).obj (F.restrict A.ι) ≅ G.restrict W.ι :=
    (Scheme.Modules.pullback gA).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback A.ι).app F) ≪≫
      (Scheme.Modules.pullbackComp gA A.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr heq).app F ≪≫
      ((Scheme.Modules.pullbackComp W.ι g).app F).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app G).symm
  letI P5 : (G.restrict W.ι).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u} e.hom P2
  -- V-side: carry the restriction presentation back to the over-slice through the engine.
  letI eV := modulesOverOpensEquivalence (X := Y) W
  letI P6 : (eV.inverse.obj (G.over W)).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u}
      (overOpensIsoRestrict W G).symm.hom P5
  letI ηV : eV.functor.obj (SheafOfModules.unit W.toScheme.ringCatSheaf) ≅
      SheafOfModules.unit (Sheaf.over Y.ringCatSheaf W) :=
    overOpensFunctorUnitIso (X := Y) W
  letI P7 : (eV.functor.obj (eV.inverse.obj (G.over W))).Presentation :=
    P6.map eV.functor ηV.symm
  exact SheafOfModules.Presentation.ofIsIso.{u, u, u}
    (eV.counitIso.app (G.over W)).hom P7

/-! ## Pullback preserves quasi-coherence -/

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
-- Cover-local quasi-coherence repeatedly synthesizes right adjoints through the
-- presentation transport; the default instance and elaboration budgets time out.
set_option maxHeartbeats 2000000 in
/-- **Pullback preserves quasi-coherence** (Stacks 01BG, general-morphism case).  For an
arbitrary morphism of schemes `g : Y ⟶ X` and a quasi-coherent `F : X.Modules`, the module
pullback `g^* F` is quasi-coherent.

Quasi-coherence is local (`SheafOfModules.IsQuasicoherent.of_coversTop`): the preimages
under `g` of the quasi-coherence cover of `X` cover `Y`, and over each preimage the
per-slice obligation is `presentationPullbackSliceOfOver`. -/
theorem pullback_isQuasicoherent_hom {Y X : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pullback g).obj F).IsQuasicoherent := by
  obtain ⟨⟨q⟩⟩ := hF
  -- The preimages of the quasi-coherence cover of `X` cover `Y`.
  have hcov : (Opens.grothendieckTopology Y).CoversTop
      (fun i => g ⁻¹ᵁ q.X i) := by
    intro W x hx
    obtain ⟨U', fU, hf, hU'⟩ := q.coversTop ⊤ (g.base x) (by trivial)
    obtain ⟨i, ⟨gi⟩⟩ := hf
    refine ⟨W ⊓ (g ⁻¹ᵁ q.X i), homOfLE inf_le_left, ⟨i, ⟨homOfLE inf_le_right⟩⟩,
      ⟨hx, ?_⟩⟩
    exact (leOfHom gi) hU'
  -- Per-slice presentations through the restricted-pullback bridge.
  haveI hslice : ∀ i,
      (((Scheme.Modules.pullback g).obj F).over (g ⁻¹ᵁ q.X i)).IsQuasicoherent := fun i =>
    (presentationPullbackSliceOfOver g F (q.X i) (q.presentation i)).isQuasicoherent
  exact SheafOfModules.IsQuasicoherent.of_coversTop
    ((Scheme.Modules.pullback g).obj F) (fun i => g ⁻¹ᵁ q.X i) hcov

end AlgebraicGeometry
