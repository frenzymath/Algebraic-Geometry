/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.PullbackQuasicoherent

/-!
# Pullback preserves finite presentation (Stacks 01BK-adjacent)

The finite-presentation refinement of the arbitrary-morphism pullback
quasi-coherence of `Cohomology/PullbackQuasicoherent.lean` (Stacks 01BG): the
pullback of a finitely presented sheaf of modules along an arbitrary scheme
morphism is finitely presented (`Scheme.Modules.pullback_isFinitePresentation`,
blueprint `lem:pullback_finite_presentation`).

## Finiteness bookkeeping

Every step of the per-slice presentation transports
(`presentationOverOpens`, `presentationRestrictOfOver` of
`Cohomology/CechTermAcyclic.lean`, and `Modules.pullbackSlicePresentation`
below) is a `SheafOfModules.Presentation.map` along a colimit-preserving
functor or a `SheafOfModules.Presentation.ofIsIso`, both of which keep the
generator and relation index types.  Mathlib supplies the `IsFinite` instance
for `Presentation.ofIsIso`; this file supplies the missing companion instance
for `Presentation.map` (the index types are preserved *definitionally*, by
iota-reduction through `presentationOfIsCokernelFree`), together with
`IsFinite` instances for the two project transports.  With one instance per
transport layer, instance search closes the finiteness of the eight-layer
chain by structural head-matching — no `whnf` through the heavy transport
terms is ever attempted (the earlier `inferInstanceAs`-on-the-unexpanded-`def`
approach exceeded 8M heartbeats and was abandoned; see the session notes on
`pullbackSlicePresentation_isFinite`).

## References

Blueprint: `lem:pullback_finite_presentation`, `def:quot_functor`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Nitsure] §1 (FGA Explained Ch. 5, arXiv:math/0504020); Stacks 01BK.
-/

set_option autoImplicit false

universe u u₁ u₂ v₁ v₂

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Mapping a presentation along a colimit-preserving functor preserves
finiteness: `Presentation.map` is `presentationOfIsCokernelFree` at the mapped
generator/relation data, which keeps the index types `generators.I` and
`relations.I` definitionally (Mathlib supplies the analogous instance for
`Presentation.ofIsIso`; this is the missing `map` companion). -/
instance Presentation.map_isFinite {M : SheafOfModules.{u} R} (P : Presentation M)
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] (η : unit S ≅ F.obj (unit R))
    [P.IsFinite] : (P.map F η).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite P.generators.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite P.relations.I)⟩

end SheafOfModules

namespace AlgebraicGeometry

/-- The over-restriction transport of presentations preserves finiteness:
`presentationOverOpens` is a chain of two `Presentation.map`s and one
`Presentation.ofIsIso`, each of which keeps the generator/relation index
types definitionally, so the finiteness of the indices transports by a
(cheap, projection-level) `inferInstanceAs`. -/
instance presentationOverOpens_isFinite {X : Scheme.{u}} (W : X.Opens)
    (M : X.Modules) (U : X.Opens) (P : (M.over U).Presentation) (hWU : W ≤ U)
    [P.IsFinite] : (presentationOverOpens W M U P hWU).IsFinite := by
  constructor
  case isFiniteType_generators =>
    constructor
    exact inferInstanceAs (Finite P.generators.I)
  case isFiniteType_relations =>
    constructor
    exact inferInstanceAs (Finite P.relations.I)

/-- The restriction-from-over transport of presentations preserves finiteness:
`presentationRestrictOfOver` is `presentationOverOpens` followed by a
`Presentation.map` and a `Presentation.ofIsIso` (same definitional
index-preservation as `presentationOverOpens_isFinite`). -/
instance presentationRestrictOfOver_isFinite {X : Scheme.{u}} (W : X.Opens)
    (M : X.Modules) (U : X.Opens) (P : (M.over U).Presentation) (hWU : W ≤ U)
    [P.IsFinite] : (presentationRestrictOfOver W M U P hWU).IsFinite := by
  constructor
  case isFiniteType_generators =>
    constructor
    exact inferInstanceAs (Finite P.generators.I)
  case isFiniteType_relations =>
    constructor
    exact inferInstanceAs (Finite P.relations.I)

namespace Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Term-mode variant of `presentationPullbackSliceOfOver`
(`Cohomology/PullbackQuasicoherent.lean`) — the same per-slice transport of a
presentation of `F.over A` to a presentation of `(g^* F).over (g ⁻¹ᵁ A)`,
restated without tactic-`set` wrappers so that the finiteness of the
presentation can be read off the transport chain by instance search
(every step is `Presentation.map` or `Presentation.ofIsIso`). -/
noncomputable def Modules.pullbackSlicePresentation {Y X : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (A : X.Opens) (P : (F.over A).Presentation) :
    (((Scheme.Modules.pullback g).obj F).over (g ⁻¹ᵁ A)).Presentation :=
  letI P1 : (F.restrict A.ι).Presentation := presentationRestrictOfOver A F A P le_rfl
  letI gA : (g ⁻¹ᵁ A).toScheme ⟶ A.toScheme := g.resLE A (g ⁻¹ᵁ A) le_rfl
  haveI hpc : Limits.PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (Scheme.Modules.pullback gA) := inferInstance
  letI P2 : ((Scheme.Modules.pullback gA).obj (F.restrict A.ι)).Presentation :=
    @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P1
      (Scheme.Modules.pullback gA) hpc (pullbackUnitIso gA).symm
  letI e : (Scheme.Modules.pullback gA).obj (F.restrict A.ι) ≅
      ((Scheme.Modules.pullback g).obj F).restrict (g ⁻¹ᵁ A).ι :=
    (Scheme.Modules.pullback gA).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback A.ι).app F) ≪≫
      (Scheme.Modules.pullbackComp gA A.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι g le_rfl)).app F ≪≫
      ((Scheme.Modules.pullbackComp (g ⁻¹ᵁ A).ι g).app F).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ A).ι).app
        ((Scheme.Modules.pullback g).obj F)).symm
  letI P5 : (((Scheme.Modules.pullback g).obj F).restrict (g ⁻¹ᵁ A).ι).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u} e.hom P2
  letI eV := modulesOverOpensEquivalence (X := Y) (g ⁻¹ᵁ A)
  letI P6 : (eV.inverse.obj (((Scheme.Modules.pullback g).obj F).over (g ⁻¹ᵁ A))).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u}
      (overOpensIsoRestrict (g ⁻¹ᵁ A) ((Scheme.Modules.pullback g).obj F)).symm.hom P5
  letI ηV : eV.functor.obj (SheafOfModules.unit (g ⁻¹ᵁ A).toScheme.ringCatSheaf) ≅
      SheafOfModules.unit (Sheaf.over Y.ringCatSheaf (g ⁻¹ᵁ A)) :=
    overOpensFunctorUnitIso (X := Y) (g ⁻¹ᵁ A)
  letI P7 : (eV.functor.obj (eV.inverse.obj
      (((Scheme.Modules.pullback g).obj F).over (g ⁻¹ᵁ A)))).Presentation :=
    P6.map eV.functor ηV.symm
  SheafOfModules.Presentation.ofIsIso.{u, u, u}
    (eV.counitIso.app (((Scheme.Modules.pullback g).obj F).over (g ⁻¹ᵁ A))).hom P7

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
-- Expanding the presentation transport makes instance search traverse every
-- `Presentation.map` and `Presentation.ofIsIso`; the default synthesis budget times out.
/-- The per-slice pullback presentation transport preserves finiteness: after
`delta`-exposing the transport chain, every layer is a `Presentation.map` or a
`Presentation.ofIsIso` applied to the opaque `presentationRestrictOfOver`
transport, so the per-layer `IsFinite` instances (Mathlib's `ofIsIso`
instance, `Presentation.map_isFinite`, `presentationRestrictOfOver_isFinite`)
close the goal by structural head-matching — no deep `whnf` through the
transport terms is attempted (`lem:pullback_finite_presentation`). -/
lemma Modules.pullbackSlicePresentation_isFinite {Y X : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (A : X.Opens) (P : (F.over A).Presentation) [P.IsFinite] :
    (Modules.pullbackSlicePresentation g F A P).IsFinite := by
  delta Modules.pullbackSlicePresentation
  infer_instance

/-- **Pullback preserves finite presentation** (Stacks 01BK-adjacent; the
finite-presentation refinement of `pullback_isQuasicoherent_hom`).  The
per-slice transport of `Cohomology/PullbackQuasicoherent.lean` preserves the
index types of the presentations, so the pullback of a finitely presented
sheaf of modules along an arbitrary scheme morphism is finitely presented. -/
theorem Modules.pullback_isFinitePresentation {Y X : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (hF : F.IsFinitePresentation) :
    ((Scheme.Modules.pullback g).obj F).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := hF.exists_quasicoherentData
  have hcov : (Opens.grothendieckTopology Y).CoversTop (fun i => g ⁻¹ᵁ q.X i) := by
    intro W x hx
    obtain ⟨U', fU, hf, hU'⟩ := q.coversTop ⊤ (g.base x) (by trivial)
    obtain ⟨i, ⟨gi⟩⟩ := hf
    exact ⟨W ⊓ (g ⁻¹ᵁ q.X i), homOfLE inf_le_left, ⟨i, ⟨homOfLE inf_le_right⟩⟩,
      ⟨hx, (leOfHom gi) hU'⟩⟩
  let q' : ((Scheme.Modules.pullback g).obj F).QuasicoherentData :=
    { I := q.I
      X := fun i => g ⁻¹ᵁ q.X i
      coversTop := hcov
      presentation := fun i => Modules.pullbackSlicePresentation g F (q.X i) (q.presentation i) }
  have hfin : q'.shrink.IsFinitePresentation := by
    apply SheafOfModules.QuasicoherentData.IsFinitePresentation.mk
    intro i
    exact Modules.pullbackSlicePresentation_isFinite g F _ _
  exact { exists_quasicoherentData := ⟨q'.shrink, hfin⟩ }

end Scheme

end AlgebraicGeometry
