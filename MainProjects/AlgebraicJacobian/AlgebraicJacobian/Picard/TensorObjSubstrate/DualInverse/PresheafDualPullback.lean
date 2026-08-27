/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse

/-!
# Presheaf dual pullback comparison

This file contains the Cone B declarations for the presheaf-level dual base-change
comparison `θ_M` and its immersion naturality, as ordered by the blueprint
`Picard_TensorObjSubstrate.tex`.

## Declarations

**Under `namespace PresheafOfModules`** (siblings of `dualPrecompEquiv`/`dualIsoOfIso`):
- `dualPrecompHom`: the forward leg of `dualPrecompEquiv` for an arbitrary
  morphism `g : M ⟶ M'`; contravariant functoriality of the presheaf dual.
- `dualPrecompHom_restrict_apply`: sectionwise, `(dualPrecompHom g).app U φ` equals
  `(pushforward₀ (Over.forget U)).map g ≫ φ` — near-definitional.

**Under `namespace AlgebraicGeometry.Scheme.Modules`**:
- `presheafDualPullbackComparison` (θ_M, `def:presheafdual_pullback_comparison`): the presheaf
  iso `(pullback φ).obj (dual M.val) ≅ dual ((pullback φ).obj M.val)` (Step-4 residual of
  `dual_restrict_iso`, packaged as a named iso).
- `presheafDual_pullback_comparison_eval_apply` (L1): θ_M is sectionwise the internal-hom
  evaluation `internalHomEval` reindexed across `j.opensFunctor`.
- `presheafDual_eval_restrict_commute_apply` (L3a): the eval/restrict commutation
  `φ(s)|_V = (φ|_V)(s|_V)`; independent of θ/dualPrecompHom.
- `presheafDual_pullback_restrict_natural_apply` (L3b): pointwise naturality square,
  combining L1 + L2 + L3a.
- `presheafDual_pullback_restrict_natural`: Iso-level immersion-naturality of θ,
  mirroring `presheafDualUnitIso_naturality`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

-- ============================================================
-- §0. Generic mate calculus — the `leftAdjointUniq`/`leftAdjointCompIso` cocycle
-- ============================================================

namespace CategoryTheory.Adjunction

universe v₀ v₁ v₂ w₀ w₁ w₂

variable {C₀ : Type w₀} {C₁ : Type w₁} {C₂ : Type w₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]

/-- The mate (conjugate) of a `leftAdjointUniq` comparison of two left adjoints of the *same* right
adjoint `G` is the identity of `G`.  This is the abstract content behind every `leftAdjointUniq`
cocycle: the comparison transports the unit of one adjunction to the other and is therefore mate to
`𝟙 G`.  Used to collapse the `H1` factors in `leftAdjointUniq_leftAdjointCompIso_comm`. -/
lemma conjugateEquiv_leftAdjointUniq_hom {F F' : C₀ ⥤ C₁} {G : C₁ ⥤ C₀}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    conjugateEquiv adj2 adj1 (leftAdjointUniq adj1 adj2).hom = 𝟙 G := by
  rw [leftAdjointUniq, Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv,
    Equiv.apply_symm_apply]

variable {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}

/-- The mate (conjugate) of the *hom* of `leftAdjointCompIso` is `e.inv` (the companion of
`conjugateEquiv_leftAdjointCompIso_inv`, which computes the conjugate of the `inv`). -/
lemma conjugateEquiv_leftAdjointCompIso_hom
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)
        (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).hom = e.inv := by
  have hcomp : conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)
        (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).hom ≫ e.hom = 𝟙 _ := by
    conv_lhs => rw [show e.hom = conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂
      (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).inv from
        (conjugateEquiv_leftAdjointCompIso_inv adj₀₁ adj₁₂ adj₀₂ e).symm]
    rw [conjugateEquiv_comp, Iso.inv_hom_id, conjugateEquiv_id]
  rw [← cancel_mono e.hom, hcomp, e.inv_hom_id]

/-- **Abstract `H1` cocycle.**  Two families of left adjoints `F•` and `P•`, sharing the right
adjoints `G••` level-by-level, and a single right-adjoint composition iso `e : G₂₁ ⋙ G₁₀ ≅ G₂₀`.
The `leftAdjointUniq` comparisons `H1 = leftAdjointUniq adjF adjP : F ≅ P` intertwine the two
`leftAdjointCompIso`s built from the *same* `e`:
`FC.hom ≫ H1₀₂.hom = (H1₀₁ ▷ F₁₂) ≫ (P₀₁ ◁ H1₁₂) ≫ PC.hom`.
This is the dual-flank analogue of the project keystone `conjugateEquiv_restrictFunctorComp_inv`:
both reduce a composite-immersion comparison to a chain over `pullbackComp`/`pushforwardComp`. -/
lemma leftAdjointUniq_leftAdjointCompIso_comm
    {P₀₁ : C₀ ⥤ C₁} {P₁₂ : C₁ ⥤ C₂} {P₀₂ : C₀ ⥤ C₂}
    (adjF01 : F₀₁ ⊣ G₁₀) (adjF12 : F₁₂ ⊣ G₂₁) (adjF02 : F₀₂ ⊣ G₂₀)
    (adjP01 : P₀₁ ⊣ G₁₀) (adjP12 : P₁₂ ⊣ G₂₁) (adjP02 : P₀₂ ⊣ G₂₀)
    (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    (leftAdjointCompIso adjF01 adjF12 adjF02 e).hom ≫ (leftAdjointUniq adjF02 adjP02).hom =
      Functor.whiskerRight (leftAdjointUniq adjF01 adjP01).hom F₁₂ ≫
        Functor.whiskerLeft P₀₁ (leftAdjointUniq adjF12 adjP12).hom ≫
        (leftAdjointCompIso adjP01 adjP12 adjP02 e).hom := by
  apply (conjugateEquiv adjP02 (adjF01.comp adjF12)).injective
  -- LHS mate: `FC.hom ≫ H1₀₂.hom ↦ (𝟙) ≫ e.inv = e.inv`.
  rw [← conjugateEquiv_comp adjP02 adjF02 (adjF01.comp adjF12),
    conjugateEquiv_leftAdjointUniq_hom adjF02 adjP02,
    conjugateEquiv_leftAdjointCompIso_hom, Category.id_comp]
  -- RHS mate: split the 3-fold composite, collapse the two `H1` whiskers, then `PC.hom ↦ e.inv`.
  rw [← conjugateEquiv_comp adjP02 (adjP01.comp adjF12) (adjF01.comp adjF12)
        (Functor.whiskerLeft P₀₁ (leftAdjointUniq adjF12 adjP12).hom ≫
          (leftAdjointCompIso adjP01 adjP12 adjP02 e).hom)
        (Functor.whiskerRight (leftAdjointUniq adjF01 adjP01).hom F₁₂),
    ← conjugateEquiv_comp adjP02 (adjP01.comp adjP12) (adjP01.comp adjF12)
        (leftAdjointCompIso adjP01 adjP12 adjP02 e).hom
        (Functor.whiskerLeft P₀₁ (leftAdjointUniq adjF12 adjP12).hom),
    conjugateEquiv_whiskerRight adjP01 adjF01 adjF12,
    conjugateEquiv_whiskerLeft adjP12 adjF12 adjP01,
    conjugateEquiv_leftAdjointUniq_hom adjF01 adjP01,
    conjugateEquiv_leftAdjointUniq_hom adjF12 adjP12,
    conjugateEquiv_leftAdjointCompIso_hom]
  simp

end CategoryTheory.Adjunction

-- ============================================================
-- §1. `PresheafOfModules` — morphism-level dual precomposition
-- ============================================================

namespace PresheafOfModules

open InternalHom Opposite

variable {D : Type u} [Category.{u, u} D] {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}}

/-! ### Morphism-level dual transport (`dualPrecompHom`) -/

/-- Precomposition makes the presheaf dual contravariant in its module argument.
At a section `U`, `dualPrecompHom g` sends `φ` to
`(pushforward₀ (Over.forget U.unop) _).map g ≫ φ`. When `g` is the forward map
of an isomorphism, this is the forward map underlying `dualIsoOfIso`.

This is blueprint declaration `def:presheaf_dual_precomp_hom`. -/
noncomputable def dualPrecompHom
    {M M' : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)} (g : M ⟶ M') :
    dual M' ⟶ dual M where
  app U :=
    letI : Module (R₀.obj (op U.unop) : Type u) ((dual M').obj U : Type u) :=
      internalHomObjModule U.unop M'
        (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
    letI : Module (R₀.obj (op U.unop) : Type u)
        ((InternalHom.internalHomPresheaf M'
          (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))).obj U : Type u) :=
      internalHomObjModule U.unop M'
        (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
    letI : Module (R₀.obj (op U.unop) : Type u) ((dual M).obj U : Type u) :=
      internalHomObjModule U.unop M
        (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
    letI : Module (R₀.obj (op U.unop) : Type u)
        ((InternalHom.internalHomPresheaf M
          (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))).obj U : Type u) :=
      internalHomObjModule U.unop M
        (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
    ModuleCat.ofHom (R := (R₀.obj (op U.unop) : Type u))
      ({ toFun := fun φ =>
          (PresheafOfModules.pushforward₀ (Over.forget U.unop)
            (R₀ ⋙ forget₂ CommRingCat RingCat)).map g ≫ φ
         map_add' := fun φ ψ => Preadditive.comp_add _ _ _ _ φ ψ
         map_smul' := fun r φ => by
           simp only [RingHom.id_apply]
           exact (Category.assoc _ _ _).symm } :
        ((dual M').obj U : Type u) →ₗ[(R₀.obj (op U.unop) : Type u)] ((dual M).obj U : Type u))
  naturality {U U'} f := by
    -- Naturality of `dualPrecompHom`: precomposition by `g` commutes with the slice
    -- restriction maps of the dual (`restrictionMap`).  Same square that `isoMk` discharges
    -- by default for `dualIsoOfIso`, so `cat_disch` should close it.
    cat_disch

/-- Sectionwise, `dualPrecompHom g` is precomposition by the pushforward of `g` to
the slice over `U`. This is blueprint lemma `lem:dual_precomp_hom_restrict_apply`. -/
lemma dualPrecompHom_restrict_apply
    {M M' : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)} (g : M ⟶ M')
    (U : Dᵒᵖ) (φ : (dual M').obj U) :
    letI := internalHomObjModule U.unop M'
      (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
    letI := internalHomObjModule U.unop M
      (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
    (dualPrecompHom g).app U φ =
      (PresheafOfModules.pushforward₀ (Over.forget U.unop)
        (R₀ ⋙ forget₂ CommRingCat RingCat)).map g ≫ φ :=
  rfl

/-- Local re-statement of the (root-file `private`) sectionwise value of the
`pushforwardPushforwardAdj` unit; the body is `rfl`, so it re-derives here.  The unit, on a
section at `U`, is the presheaf restriction map of `M` along `adj.counit`. -/
lemma ppadj_unit_app_app_apply
    {A : Type u} [Category.{u} A] {B : Type u} [Category.{u} B]
    {F : A ⥤ B} {G : B ⥤ A} {S : Aᵒᵖ ⥤ RingCat.{u}} {Rr : Bᵒᵖ ⥤ RingCat.{u}}
    (adj : F ⊣ G) (φ : S ⟶ F.op ⋙ Rr) (ψ : Rr ⟶ G.op ⋙ S)
    (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) Rr = ψ ≫ G.op.whiskerLeft φ)
    (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)
    (M : _root_.PresheafOfModules Rr) (U : Bᵒᵖ) (x : M.obj U) :
    (((PresheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).app U).hom x
      = (M.map (adj.counit.app U.unop).op).hom x := rfl

/-- Local re-statement of the (root-file `private`) sectionwise value of the
`pushforwardPushforwardAdj` counit; the body is `rfl`.  The counit, on a section at `U`, is the
presheaf restriction map of `N` along `adj.unit`. -/
lemma ppadj_counit_app_app_apply
    {A : Type u} [Category.{u} A] {B : Type u} [Category.{u} B]
    {F : A ⥤ B} {G : B ⥤ A} {S : Aᵒᵖ ⥤ RingCat.{u}} {Rr : Bᵒᵖ ⥤ RingCat.{u}}
    (adj : F ⊣ G) (φ : S ⟶ F.op ⋙ Rr) (ψ : Rr ⟶ G.op ⋙ S)
    (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) Rr = ψ ≫ G.op.whiskerLeft φ)
    (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)
    (N : _root_.PresheafOfModules S) (U : Aᵒᵖ)
    (y : ((PresheafOfModules.pushforward ψ ⋙ PresheafOfModules.pushforward φ).obj N).obj U) :
    (((PresheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app N).app U).hom y
      = (N.map (adj.unit.app U.unop).op).hom y := rfl

/-- **Sectionwise value of the presheaf-dual restriction map.**  For `g : U ⟶ U'` in `Dᵒᵖ` and a
dual section `φ : (dual M).obj U`, evaluating the restricted section `(dual M).map g φ` at a slice
object `W₀` of `Over U'.unop` is `φ` evaluated at the `Over.map`-reindexed slice.  `rfl` via
`ofPresheaf_map` turns `internalHomPresheaf.map` into
`(pushforward₀ (Over.map g.unop)).map`, whose component is `φ.app (F.op.obj ·)`.
This reduces the dual-restriction composite in
`presheafDualPullbackComparison_restrict` to evaluation by `φ`. -/
lemma dual_map_app_apply {U U' : Dᵒᵖ} (g : U ⟶ U')
    (M : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))
    (φ : ((dual M).obj U : Type u))
    (W₀ : (Over (unop U'))ᵒᵖ) :
    (((dual M).map g).hom φ).app W₀ = φ.app ((Over.map g.unop).op.obj W₀) := rfl

end PresheafOfModules

-- ============================================================
-- §2. `AlgebraicGeometry.Scheme.Modules` — θ_M and naturality
-- ============================================================

namespace AlgebraicGeometry

open Opposite

namespace Scheme

namespace Modules

/-- The presheaf-level dual pullback comparison for an open immersion.
The adjunction-uniqueness isomorphism identifies pullback with the relevant
pushforward, after which `sliceDualTransport` compares the duals sectionwise.

This is blueprint declaration `def:presheafdual_pullback_comparison`. -/
noncomputable def presheafDualPullbackComparison {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules) :
    let φR := (Scheme.Hom.toRingCatSheafHom f).hom
    let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    (PresheafOfModules.pullback φR).obj (PresheafOfModules.dual (R₀ := X.presheaf) M.val) ≅
    PresheafOfModules.dual (R₀ := Y.presheaf)
      ((PresheafOfModules.pushforward β).obj M.val) := by
  -- Rebuild the local context from `dual_restrict_iso` Step 4.
  let φR := (Scheme.Hom.toRingCatSheafHom f).hom
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv
      naturality := fun _ _ i => f.appIso_inv_naturality i }
  let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  have hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φR :=
    PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φR
      (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
  let H1 := hadj.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φR)
  -- Verbatim Step-4 body (known to compile in the `dual_restrict_iso` context):
  exact (H1.app (PresheafOfModules.dual (R₀ := X.presheaf) M.val)).symm ≪≫
    PresheafOfModules.isoMk (fun V => sliceDualTransport f M V)
      (by intro V W g; subsingleton)

/-- The sectionwise evaluation formula for `sliceDualTransport`, the forward leg of
`presheafDualPullbackComparison`. Evaluation after transport is evaluation before
transport followed by the structure-ring isomorphism of the open immersion.

This is blueprint lemma `lem:presheafdual_pullback_comparison_eval_apply`. -/
lemma presheafDual_pullback_comparison_eval_apply {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules)
    (V : (TopologicalSpace.Opens Y)ᵒᵖ)
    (φ : letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
           { app := fun U => (f.appIso U.unop).inv
             naturality := fun _ _ i => f.appIso_inv_naturality i }
         letI β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
           Functor.whiskerRight α (forget₂ CommRingCat RingCat)
         (((PresheafOfModules.pushforward β).obj
            (PresheafOfModules.dual (R₀ := X.presheaf) M.val)).obj V))
    (s : letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
           { app := fun U => (f.appIso U.unop).inv
             naturality := fun _ _ i => f.appIso_inv_naturality i }
         letI β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
           Functor.whiskerRight α (forget₂ CommRingCat RingCat)
         (((PresheafOfModules.pushforward β).obj M.val).obj V)) :
    -- The load-bearing leg of `θ` (`sliceDualTransport`, which assembles the `isoMk` factor of
    -- `presheafDualPullbackComparison`) acts sectionwise as the internal-hom evaluation of `φ`
    -- reindexed across `f.opensFunctor`: on `(pushforward β _).obj V` (definitionally
    -- `(dual M.val).obj (op fV)` resp. `M.val.obj (op fV)`), evaluating the transported section at
    -- `s` recovers `evalLin M.val (op fV) φ s`. This is the pushforward-side core;
    -- `pullback φR` form rides on the H1 adjunction-uniqueness leg.
    letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    letI β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    PresheafOfModules.evalLin ((PresheafOfModules.pushforward β).obj M.val) V
        ((sliceDualTransport f M V).hom φ) s
      = (Scheme.Hom.appIso f V.unop).hom.hom
          (PresheafOfModules.evalLin M.val (op (f.opensFunctor.obj V.unop)) φ s) := by
  -- The forward `sliceDualTransport` app at the terminal slice is, by the def,
  -- `(restrictScalars β_V).map (φ.app (op (Over.mk 𝟙))) ≫ dualUnitRingSwap f V.unop`; evaluating at
  -- `s` and rewriting the swap via `dualUnitRingSwap_apply` (= `(appIso).hom.hom`) gives the RHS.
  -- The first rewrite exposes the codomain swap; the second identifies its carrier
  -- map with `(appIso f V.unop).hom.hom`.
  unfold PresheafOfModules.evalLin
  erw [sliceDualTransport_app_apply f M V φ (Opposite.op (Over.mk (𝟙 V.unop))) s,
    dualUnitRingSwap_apply]
  rfl

/-- **Generic eval/restrict commutation** (the abstract core of L3a, stated over a *variable*
presheaf of modules `N`).  It is the naturality of `internalHomEval N` at `j.op` read off the
simple tensor `s ⊗ₜ φ`. -/
private lemma evalLin_restrict_commute_aux {D : Type u} [Category.{u, u} D]
    {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}}
    (N : _root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) {U V : D} (j : V ⟶ U)
    (φ : (PresheafOfModules.dual N).obj (op U)) (s : (N.obj (op U) : Type u)) :
    ((R₀ ⋙ forget₂ CommRingCat RingCat).map j.op).hom
        (PresheafOfModules.evalLin N (op U) φ s)
      = PresheafOfModules.evalLin N (op V)
          ((PresheafOfModules.dual N).map j.op φ) (N.map j.op s) :=
  (PresheafOfModules.naturality_apply (PresheafOfModules.internalHomEval N) j.op
    (s ⊗ₜ[(R₀.obj (op U) : Type u)] φ)).symm

/-- Evaluation of a dual section commutes with restriction along an inclusion of
opens. This is the pullback specialization of `evalLin_restrict_commute_aux` and
blueprint lemma `lem:presheafdual_eval_restrict_commute_apply`. -/
lemma presheafDual_eval_restrict_commute_apply {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules)
    {U V : TopologicalSpace.Opens Y} (j : V ≤ U)
    (φ : (PresheafOfModules.dual (R₀ := Y.presheaf)
        ((PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom f).hom).obj M.val)).obj
        (Opposite.op U))
    (s : ((PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom f).hom).obj M.val).obj
        (Opposite.op U)) :
    letI N := (PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom f).hom).obj M.val
    -- Restricting the eval value `evalLin N (op U) φ s` along `j` (the ring/unit restriction map
    -- `Y.presheaf ⋙ forget₂`) equals evaluating the restricted dual section `(dual N).map j.op φ`
    -- at the restricted argument `N.map j.op s`.
    ((Y.presheaf ⋙ forget₂ CommRingCat RingCat).map (homOfLE j).op).hom
        (PresheafOfModules.evalLin N (Opposite.op U) φ s)
      = PresheafOfModules.evalLin N (Opposite.op V)
          ((PresheafOfModules.dual (R₀ := Y.presheaf) N).map (homOfLE j).op φ)
          (N.map (homOfLE j).op s) :=
  -- Instantiate the generic eval/restrict commutation at `N = (pullback φR).obj M.val`,
  -- `j = homOfLE j`.  The heavy `pullback`-object only appears as the *argument* (never whnf-ed),
  -- so this avoids the `isDefEq` heartbeat bomb of the inline form.
  evalLin_restrict_commute_aux
    ((PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom f).hom).obj M.val)
    (homOfLE j) φ s

/-- Pointwise naturality of `presheafDualPullbackComparison` under restriction from
`U` to `V`. Both sides evaluate the dual sections related by the naturality square
of its forward map. This is blueprint lemma
`lem:presheafdual_pullback_restrict_natural_apply`. -/
lemma presheafDual_pullback_restrict_natural_apply {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules)
    {U V : TopologicalSpace.Opens Y} (j : V ≤ U)
    (φ : ((PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom f).hom).obj
        (PresheafOfModules.dual (R₀ := X.presheaf) M.val)).obj (Opposite.op U))
    (s : (let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
            { app := fun U => (f.appIso U.unop).inv
              naturality := fun _ _ i => f.appIso_inv_naturality i }
          let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
            Functor.whiskerRight α (forget₂ CommRingCat RingCat)
          (PresheafOfModules.pushforward β).obj M.val).obj (Opposite.op V)) :
    PresheafOfModules.evalLin
        (let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
           { app := fun U => (f.appIso U.unop).inv
             naturality := fun _ _ i => f.appIso_inv_naturality i }
         let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
           Functor.whiskerRight α (forget₂ CommRingCat RingCat)
         (PresheafOfModules.pushforward β).obj M.val)
        (Opposite.op V)
        -- target side: θ applied then restricted
        ((presheafDualPullbackComparison f M).hom.app (Opposite.op V)
            ((PresheafOfModules.pullback
                (Scheme.Hom.toRingCatSheafHom f).hom).obj
              (PresheafOfModules.dual (R₀ := X.presheaf) M.val) |>.map (homOfLE j).op φ))
        s
      = PresheafOfModules.evalLin
          (let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
             { app := fun U => (f.appIso U.unop).inv
               naturality := fun _ _ i => f.appIso_inv_naturality i }
           let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
             Functor.whiskerRight α (forget₂ CommRingCat RingCat)
           (PresheafOfModules.pushforward β).obj M.val)
          (Opposite.op V)
          -- source side: θ applied at U, then the dual section restricted along `j`
          ((PresheafOfModules.dual (R₀ := Y.presheaf)
              ((let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
                  { app := fun U => (f.appIso U.unop).inv
                    naturality := fun _ _ i => f.appIso_inv_naturality i }
                let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
                  Functor.whiskerRight α (forget₂ CommRingCat RingCat)
                (PresheafOfModules.pushforward β).obj M.val))).map (homOfLE j).op
            ((presheafDualPullbackComparison f M).hom.app (Opposite.op U) φ))
          s :=
  -- Both sides evaluate, at `s`, the two dual sections related by the naturality square of `θ.hom`:
  -- `θ.app (op V) (source.map j.op φ) = (dual _).map j.op (θ.app (op U) φ)`.
  congrArg
    (fun ψ => PresheafOfModules.evalLin
      (let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
         { app := fun U => (f.appIso U.unop).inv
           naturality := fun _ _ i => f.appIso_inv_naturality i }
       let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
         Functor.whiskerRight α (forget₂ CommRingCat RingCat)
       (PresheafOfModules.pushforward β).obj M.val)
      (Opposite.op V) ψ s)
    (PresheafOfModules.naturality_apply (presheafDualPullbackComparison f M).hom
      (homOfLE j).op φ)

/-- Naturality of the forward map of `presheafDualPullbackComparison` under an
inclusion of opens. This exposes the ordinary presheaf naturality square in the
form used by the dual pullback construction. -/
lemma presheafDual_pullback_restrict_natural {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules)
    {U V : TopologicalSpace.Opens Y} (j : V ≤ U) :
    (presheafDualPullbackComparison f M).hom.app (Opposite.op V) ∘
      ((PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom f).hom).obj
        (PresheafOfModules.dual (R₀ := X.presheaf) M.val)).map (homOfLE j).op
    = (let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
         { app := fun U => (f.appIso U.unop).inv
           naturality := fun _ _ i => f.appIso_inv_naturality i }
       let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
         Functor.whiskerRight α (forget₂ CommRingCat RingCat)
       (PresheafOfModules.dual (R₀ := Y.presheaf) ((PresheafOfModules.pushforward β).obj M.val)).map
         (homOfLE j).op) ∘
      (presheafDualPullbackComparison f M).hom.app (Opposite.op U) := by
  -- This is the built-in naturality of
  -- `θ.hom = (presheafDualPullbackComparison f M).hom`,
  -- which is a genuine `PresheafOfModules.Hom`, hence natural by construction.  Pointwise this is
  -- `PresheafOfModules.naturality_apply θ.hom (homOfLE j).op`.
  funext φ
  exact PresheafOfModules.naturality_apply (presheafDualPullbackComparison f M).hom
    (homOfLE j).op φ

end Modules

end Scheme

end AlgebraicGeometry

end -- noncomputable section
