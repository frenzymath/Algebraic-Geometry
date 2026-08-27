/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse.PresheafDualPullback

/-!
# Compatibility of dual units with open pullback

For an open immersion, the presheaf pushforward is strongly monoidal because its
sectionwise scalar maps are isomorphisms. This identifies the unit comparators for
pushforward and its adjoint pullback, and proves that the presheaf dual pullback
comparison carries the dual of the unit object to the canonical unit duality.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-- **Strong monoidality of the open-immersion presheaf pushforward `pushforward β`.**
For an open immersion `f`, the structure-ring comparison `β = whiskerRight α (forget₂ …)` (where
`α.app U = (f.appIso U.unop).inv`) is sectionwise an isomorphism, so the topological-pushforward /
restrict-scalars composite `pushforward β = pushforward₀OfCommRingCat ⋙ restrictScalars β` is a
*strong* monoidal functor (`pushforward₀OfCommRingCat` is Mathlib-strong; `restrictScalars β` is
strong by `restrictScalarsMonoidalOfBijective`).  This upgrades the ambient lax instance
`presheafPushforwardLaxMonoidal` to `Functor.Monoidal`, which makes the unit comparator `ε`
(and tensorator `μ`) sectionwise invertible. -/
@[implicit_reducible]
noncomputable def presheafPushforwardBetaMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] :
    letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    letI β : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        f.opensFunctor.op ⋙ (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    (PresheafOfModules.pushforward β).Monoidal := by
  letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv, naturality := fun _ _ i => f.appIso_inv_naturality i }
  letI β : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      f.opensFunctor.op ⋙ (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  have hβbij : ∀ U, Function.Bijective
      ((Functor.whiskerRight α (forget₂ CommRingCat RingCat)).app U).hom := by
    intro U
    haveI : IsIso (α.app U) := inferInstanceAs (IsIso (f.appIso U.unop).inv)
    have : IsIso ((Functor.whiskerRight α (forget₂ CommRingCat RingCat)).app U) := by
      rw [Functor.whiskerRight_app]
      exact Functor.map_isIso (forget₂ CommRingCat RingCat) (α.app U)
    exact ConcreteCategory.bijective_of_isIso _
  letI mβ : (PresheafOfModules.restrictScalars
      (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).Monoidal :=
    PresheafOfModules.restrictScalarsMonoidalOfBijective _ hβbij
  exact (inferInstance : (PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙
    PresheafOfModules.restrictScalars
      (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).Monoidal)

/-- **Pushforward-side unit comparator `q` (blueprint `def:presheaf_pushforward_unit_eps`).**
The inverse of the lax-monoidal unit map `ε (pushforward β)`, packaged as an isomorphism
`(pushforward β).obj 𝟙_X ≅ 𝟙_Y` using the strong monoidality
`presheafPushforwardBetaMonoidal`. -/
noncomputable def presheafPushforwardUnitIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    letI β : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        f.opensFunctor.op ⋙ (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    (PresheafOfModules.pushforward β).obj
        (𝟙_ (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)))
      ≅ 𝟙_ (_root_.PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) := by
  letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv, naturality := fun _ _ i => f.appIso_inv_naturality i }
  letI β : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      f.opensFunctor.op ⋙ (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  letI _hm : (PresheafOfModules.pushforward β).Monoidal := presheafPushforwardBetaMonoidal f
  exact (Functor.Monoidal.εIso (PresheafOfModules.pushforward β)).symm

/-- **Sectionwise carrier value of the lax-monoidal unit `ε (restrictScalars α)`.**
Abstract twin of `restrictScalars_oplaxMonoidal_η_app_one`, stated at the
`CommRingCat`-valued base functors `R, S`, so the unit-object `CommRing` instances
are native. The `ε` of `restrictScalars α` is sectionwise the `ModuleCat`-level
`ε`, whose carrier action is the ring map `α.app W`
(`ModuleCat.restrictScalars_η`). -/
lemma restrictScalars_laxMonoidal_ε_app {C : Type u} [Category.{u} C]
    {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : R ⋙ forget₂ CommRingCat RingCat ⟶ S ⋙ forget₂ CommRingCat RingCat) (W : Cᵒᵖ)
    (r : ((R ⋙ forget₂ CommRingCat RingCat).obj W : Type u)) :
    ((Functor.LaxMonoidal.ε (PresheafOfModules.restrictScalars α)).app W).hom r
      = (α.app W).hom r := by
  erw [ModuleCat.restrictScalars_η]

set_option backward.isDefEq.respectTransparency false in
/-- **Sectionwise carrier value of `q.inv = ε (pushforward β)`.**  The inverse comparator (lax unit
`ε` of the strong-monoidal `pushforward β`) acts on a section `V` as the structure-ring map
`(f.appIso V).inv.hom`.  Proved by the composite-`ε` split (`comp_ε`, with `ε pushforward₀ = 𝟙`),
reducing to the `ModuleCat` `ε`-value `restrictScalars_laxMonoidal_ε_app`. -/
lemma presheafPushforwardUnitIso_inv_app {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (V : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
    (w : ((𝟙_ (_root_.PresheafOfModules.{u}
        (Y.presheaf ⋙ forget₂ CommRingCat RingCat))).obj V : Type u)) :
    letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    letI _β : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        f.opensFunctor.op ⋙ (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    ((presheafPushforwardUnitIso f).inv.app V).hom w
      = (f.appIso V.unop).inv.hom w := by
  letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv, naturality := fun _ _ i => f.appIso_inv_naturality i }
  letI β : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      f.opensFunctor.op ⋙ (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  letI _hm : (PresheafOfModules.pushforward β).Monoidal := presheafPushforwardBetaMonoidal f
  have hq : (presheafPushforwardUnitIso f).inv
      = Functor.LaxMonoidal.ε (PresheafOfModules.pushforward β) := rfl
  rw [hq]
  change (ModuleCat.Hom.hom ((Functor.LaxMonoidal.ε
      (PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙
        PresheafOfModules.restrictScalars
          (Functor.whiskerRight α (forget₂ CommRingCat RingCat)))).app V)) w
    = (CommRingCat.Hom.hom (f.appIso V.unop).inv) w
  erw [Functor.LaxMonoidal.comp_ε]
  rw [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hmapid :
      (PresheafOfModules.restrictScalars (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).map
          (Functor.LaxMonoidal.ε
            (PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf))
        = 𝟙 _ := CategoryTheory.Functor.map_id _ _
  rw [hmapid]
  erw [restrictScalars_laxMonoidal_ε_app (Functor.whiskerRight α (forget₂ CommRingCat RingCat)) V w]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Unit-value of the pushforward comparator `q`
(blueprint `lem:pushforward_beta_unit_eps_app_one`).**
The sectionwise carrier action of `q.hom = (εIso (pushforward β)).inv = η (pushforward β)` at a
section `V` is the `f.appIso`-conjugation: it is the structure-ring isomorphism `(f.appIso V).hom`.
This is the unit-side analogue of the tensorator collapse `pushforward_mu_appIso_collapse`.  Proved
sectionwise: `q.hom = OplaxMonoidal.η (pushforward β)`; under the composite monoidal
instance (`pushforward β = pushforward₀ ⋙ restrictScalars β`, via
`presheafPushforwardBetaMonoidal`) the oplax
unit splits by `comp_η` with `η pushforward₀ = 𝟙`, leaving `η (restrictScalars β)`, whose section is
`inv (ε (restrictScalars (β.app V)))`; that is exactly `dualUnitRingSwap f V` whose carrier value is
`(f.appIso V).hom` (`dualUnitRingSwap_apply`).  Stated for an arbitrary carrier element `y` (the
blueprint's `1`-instance is the special case `y = 1`). -/
lemma pushforwardBetaUnitEpsAppOne {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (V : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
    (y : letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
           { app := fun U => (f.appIso U.unop).inv
             naturality := fun _ _ i => f.appIso_inv_naturality i }
         letI β : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
             f.opensFunctor.op ⋙ (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
           Functor.whiskerRight α (forget₂ CommRingCat RingCat)
         (((PresheafOfModules.pushforward β).obj
             (𝟙_ (_root_.PresheafOfModules.{u}
               (X.presheaf ⋙ forget₂ CommRingCat RingCat)))).obj V : Type u)) :
    ((presheafPushforwardUnitIso f).hom.app V).hom y
      = (f.appIso V.unop).hom.hom y := by
  letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv, naturality := fun _ _ i => f.appIso_inv_naturality i }
  letI β : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      f.opensFunctor.op ⋙ (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  letI _hm : (PresheafOfModules.pushforward β).Monoidal := presheafPushforwardBetaMonoidal f
  -- `q.inv = ε (pushforward β)`; the ε-value at a section `V` is the structure ring map
  -- `(β.app V).hom = (f.appIso V).inv.hom` (`restrictScalars_η`), via the composite-ε split
  -- (`comp_ε`, with `ε pushforward₀ = 𝟙`).
  have hεval := presheafPushforwardUnitIso_inv_app f V
  -- `q.inv.app V` (= ε.app V) is injective; both `q.hom.app V y` and `(f.appIso V).hom y` are sent
  -- to `y` by it (the round-trip `q.hom ≫ q.inv = 𝟙` and the `hεval` value `inv ∘ hom = 𝟙`).
  have hinj : Function.Injective ((presheafPushforwardUnitIso f).inv.app V).hom := by
    apply Function.LeftInverse.injective
      (g := ((presheafPushforwardUnitIso f).hom.app V).hom)
    intro x
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← PresheafOfModules.comp_app,
      (presheafPushforwardUnitIso f).inv_hom_id]
    rfl
  apply hinj
  rw [hεval ((f.appIso V.unop).hom.hom y)]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← PresheafOfModules.comp_app,
    (presheafPushforwardUnitIso f).hom_inv_id]
  rw [show ((f.appIso V.unop).inv.hom) ((f.appIso V.unop).hom.hom y) = y from
    ConcreteCategory.congr_hom (f.appIso V.unop).hom_inv_id y]
  rfl

/-- **Pullback-side unit comparator `p` (blueprint `def:presheaf_pullback_unit_eta`).**
The oplax-monoidal unit map `η (pullback φR) : (pullback φR).obj 𝟙_X ≅ 𝟙_Y`, realized here through
the **H1 reconciliation**: the pullback `(pullback φR).obj 𝟙_X` is identified with the pushforward
`(pushforward β).obj 𝟙_X` by the left-adjoint-uniqueness iso `H1` (both are left adjoints of
`pushforward φR`), and the latter is contracted to `𝟙_Y` by the pushforward unit comparator `q`
(`presheafPushforwardUnitIso`). This is exactly the H1 identification the blueprint
invokes to match the two flank comparators at the structure-sheaf unit. -/
noncomputable def presheafPullbackUnitIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    letI φR : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (Scheme.Hom.toRingCatSheafHom f).hom
    (PresheafOfModules.pullback φR).obj
        (𝟙_ (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)))
      ≅ 𝟙_ (_root_.PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) := by
  letI φR : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (Scheme.Hom.toRingCatSheafHom f).hom
  letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv, naturality := fun _ _ i => f.appIso_inv_naturality i }
  letI β : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      f.opensFunctor.op ⋙ (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  have hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φR :=
    PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φR
      (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
  letI H1 := hadj.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φR)
  exact (H1.app (𝟙_ (_root_.PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat RingCat)))).symm ≪≫ presheafPushforwardUnitIso f

/-- **L1′ (blueprint `lem:presheafdualunitiso_pullback_natural`): the θ-at-unit bridge.**
Evaluating the presheaf dual base-change comparison `θ` at the structure-sheaf unit
`M = 𝟙_X = SheafOfModules.unit X.ringCatSheaf`, the comparison `θ_𝟙` *is* the dual-of-unit
identification, with the two flank unit comparators on opposite sides: the pushforward-side
comparator `q = presheafPushforwardUnitIso` transported contravariantly through `dualIsoOfIso` on
the codomain, and the pullback-side comparator `p = presheafPullbackUnitIso` closing the domain.
This is the unit specialisation of `presheafDual_pullback_restrict_natural`, and the immersion
analogue of `presheafDualUnitIso_naturality`. -/
lemma presheafDualUnitIso_pullback_natural {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    letI φR : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (Scheme.Hom.toRingCatSheafHom f).hom
    presheafDualPullbackComparison f (SheafOfModules.unit X.ringCatSheaf)
        ≪≫ (PresheafOfModules.dualIsoOfIso (presheafPushforwardUnitIso f)).symm
        ≪≫ presheafDualUnitIso (Y := Y)
      = (PresheafOfModules.pullback φR).mapIso (presheafDualUnitIso (Y := X))
          ≪≫ presheafPullbackUnitIso f := by
  -- Rebuild the local context (`φR`, `α`, `β`, `hadj`, `H1`) exactly as
  -- `presheafDualPullbackComparison` / `presheafPullbackUnitIso` build it internally, so that the
  -- `H1` appearing after unfolding both definitions is syntactically this `H1`.
  letI φR : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    (Scheme.Hom.toRingCatSheafHom f).hom
  letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv, naturality := fun _ _ i => f.appIso_inv_naturality i }
  letI β : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      f.opensFunctor.op ⋙ (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  -- `letI` (NOT `have`) keeps `hadj`/`H1` *transparent*, so the `H1` produced by unfolding
  -- `presheafDualPullbackComparison` / `presheafPullbackUnitIso` is defeq to this `H1` and a `show`
  -- can fold the explicit unfolded term back to it.
  letI hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φR :=
    PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φR
      (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
  letI H1 := hadj.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φR)
  -- The pushforward-flank identity (★): the genuine eval-at-`1` content, after the two `H1` factors
  -- have been telescoped away by naturality.  `sDT = isoMk (sliceDualTransport f 𝟙_X)`.
  -- This is the immersion analogue of `presheafDualUnitIso_naturality`, proved sectionwise by
  -- `sliceDualTransport_app_apply` + eval-at-`1` (`internalHomEval`/`evalLin`) +
  -- `dualUnitRingSwap`.
  have FLANK :
      (PresheafOfModules.isoMk
            (fun V => sliceDualTransport f (SheafOfModules.unit X.ringCatSheaf) V)
            (by intro V W g; subsingleton)).hom ≫
          (PresheafOfModules.dualIsoOfIso (presheafPushforwardUnitIso f)).inv
            ≫ (presheafDualUnitIso (Y := Y)).hom
        = (PresheafOfModules.pushforward β).map (presheafDualUnitIso (Y := X)).hom
            ≫ (presheafPushforwardUnitIso f).hom := by
    -- Sectionwise (the immersion analogue of `presheafDualUnitIso_naturality`).  At a section `V`
    -- and dual section `φ`, the LHS is: transport `φ` by `sliceDualTransport` (reindexing across
    -- `f.opensFunctor`, conjugating by `f.appIso`), precompose by `q.hom` (`dualIsoOfIso` is
    -- precomposition, `dualPrecompEquiv`), then evaluate at `1`
    -- (`presheafDualUnitIso = dualUnitIsoGen`, `evalLin · 1`). The RHS pushes `φ`'s
    -- eval-at-`1` forward by `β`/`f.appIso` and then applies the unit comparator
    -- `q.hom`. Both reduce to
    -- `(f.appIso V).hom.hom (evalLin (𝟙_X) (op fV) φ 1)`; equality is
    -- `linearEndo_apply_comm`-style commutativity of `𝒪`-linear endomorphisms of the (commutative)
    -- structure ring, exactly as in `presheafDualUnitIso_naturality` (DualInverse.lean:317).
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    -- Reduce the LHS composite to function applications and fire the forward `sliceDualTransport`
    -- formula: at the terminal slice the transport is `dualUnitRingSwap ∘ φ.app(image slice) ∘
    -- (pushforward₀ q.inv eval-at-1)`.  This exposes `evalLin (𝟙_X) (op fV) φ 1` conjugated by
    -- `f.appIso`/`dualUnitRingSwap`.
    simp only [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
      PresheafOfModules.isoMk_hom_app]
    erw [sliceDualTransport_app_apply f (SheafOfModules.unit X.ringCatSheaf) V φ]
    -- LHS: `dualUnitRingSwap` carrier value is `(f.appIso V).hom`.  RHS: split the composite, fire
    -- the linchpin `pushforwardBetaUnitEpsAppOne` (the carrier value of `q.hom` is
    -- `(f.appIso V).hom`), then
    -- `pushforward_map_app_apply` reindexes `(pushforward β).map pdX.hom` to `pdX.hom.app (op fV)`.
    rw [dualUnitRingSwap_apply]
    erw [pushforwardBetaUnitEpsAppOne f V
      ((((PresheafOfModules.pushforward β).map (presheafDualUnitIso (Y := X)).hom).app V).hom φ)]
    congr 1
    erw [PresheafOfModules.pushforward_map_app_apply]
    -- `PUSH = (q.inv.app (op V)).hom 1 = (f.appIso V).inv.hom 1 = 1`; then the RHS
    -- `pdX.hom.app (op fV) φ = evalLin 𝟙_X (op fV) φ 1 = φ.app(termSlice).hom 1` (defeq).
    erw [presheafPushforwardUnitIso_inv_app f (Opposite.op (Opposite.unop V))]
    erw [map_one]
    rfl
  apply Iso.ext
  -- Fold the unfolded goal back to the transparent `H1` (`show` works up to defeq).  Both
  -- `θ_𝟙.hom = (H1.app (dual 𝟙_X)).inv ≫ sDT.hom` and `p.hom = (H1.app 𝟙_X).inv ≫ q.hom`.
  change ((H1.app ((𝟙_ (_root_.PresheafOfModules.{u}
              (X.presheaf ⋙ forget₂ CommRingCat RingCat))).dual)).inv ≫
        (PresheafOfModules.isoMk
          (fun V => sliceDualTransport f (SheafOfModules.unit X.ringCatSheaf) V)
          (by intro V W g; subsingleton)).hom) ≫
        (PresheafOfModules.dualIsoOfIso (presheafPushforwardUnitIso f)).inv
          ≫ (presheafDualUnitIso (Y := Y)).hom
      = (PresheafOfModules.pullback φR).map (presheafDualUnitIso (Y := X)).hom ≫
        (H1.app (𝟙_ (_root_.PresheafOfModules.{u}
            (X.presheaf ⋙ forget₂ CommRingCat RingCat)))).inv
          ≫ (presheafPushforwardUnitIso f).hom
  -- Naturality of the natural iso `H1 : pushforward β ≅ pullback φR` at `pdX.hom : dual 𝟙_X ⟶ 𝟙_X`.
  have hnat :
      (PresheafOfModules.pushforward β).map (presheafDualUnitIso (Y := X)).hom ≫
          (H1.app (𝟙_ (_root_.PresheafOfModules.{u}
            (X.presheaf ⋙ forget₂ CommRingCat RingCat)))).hom
        = (H1.app ((𝟙_ (_root_.PresheafOfModules.{u}
              (X.presheaf ⋙ forget₂ CommRingCat RingCat))).dual)).hom ≫
            (PresheafOfModules.pullback φR).map (presheafDualUnitIso (Y := X)).hom :=
    H1.hom.naturality (presheafDualUnitIso (Y := X)).hom
  -- LHS leading `H1d.inv` ↔ RHS: transpose, then cancel `H1d.hom ≫ pullback.map pdX` via `hnat`,
  -- then cancel `H1u.hom ≫ H1u.inv`, reducing to `FLANK`.
  rw [Category.assoc, Iso.inv_comp_eq,
    ← Category.assoc (H1.app ((𝟙_ (_root_.PresheafOfModules.{u}
        (X.presheaf ⋙ forget₂ CommRingCat RingCat))).dual)).hom
      ((PresheafOfModules.pullback φR).map (presheafDualUnitIso (Y := X)).hom),
    ← hnat, Category.assoc, Iso.hom_inv_id_assoc]
  exact FLANK

end Modules

end Scheme

end AlgebraicGeometry

end -- noncomputable section
