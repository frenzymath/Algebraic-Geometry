/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse.PresheafDualPullback

/-!
# Presheaf dual pullback comparison — module-naturality (Cone B, T1)

This file proves that the presheaf dual base-change comparison `θ_M`
(`presheafDualPullbackComparison f M`) is natural in the module argument `M`.
Blueprint: `lem:presheafdual_pullback_comparison_natural_module`.

## Declaration

**Under `namespace AlgebraicGeometry.Scheme.Modules`**:
- `presheafDual_pullback_comparison_natural` (T1): for an open immersion `f : Y ⟶ X` and
  a morphism `φ : M ⟶ M'` in `X.Modules`, the naturality square
  ```
  (pullback φR).map (dualPrecompHom φ.val) ≫ θ_M.hom
    = θ_{M'}.hom ≫ dualPrecompHom ((pushforward β).map φ.val)
  ```
  commutes (blueprint `lem:presheafdual_pullback_comparison_natural_module`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory Opposite

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-- Generic two-square paste used to assemble the module-naturality of `θ` across the
`SheafOfModules`/`Iso.hom` defeq seam: applied by `exact`, the morphism arguments are read off
the goal's giant `leftAdjointUniq` term first-order, so no giant-term defeq is required. -/
private lemma combine_naturality_squares {C : Type*} [Category C]
    {A B₁ B₂ E F G : C}
    (p : A ⟶ B₁) (i₁ : B₁ ⟶ E) (s₁ : E ⟶ F) (i₂ : A ⟶ B₂) (q : B₂ ⟶ E)
    (s₂ : B₂ ⟶ G) (d : G ⟶ F)
    (h1 : p ≫ i₁ = i₂ ≫ q) (h2 : q ≫ s₁ = s₂ ≫ d) :
    p ≫ i₁ ≫ s₁ = (i₂ ≫ s₂) ≫ d := by
  rw [← Category.assoc, h1, Category.assoc, h2, ← Category.assoc]

/-- Naturality of the inverse legs of a natural iso `e : F ≅ G`, in the `(e.app _).inv` spelling.
Stated generically over `e` so that, when applied with `e` a metavariable, the goal's giant
`leftAdjointUniq` term is captured first-order by `(?e.app _).inv` (no giant-term defeq). -/
private lemma natIso_inv_app_naturality {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (g : A ⟶ B) :
    G.map g ≫ (e.app B).inv = (e.app A).inv ≫ F.map g :=
  e.inv.naturality g

/-- The presheaf dual pullback comparison is natural in its module argument. The proof pastes
naturality of the adjoint-uniqueness isomorphism with the sectionwise `sliceDualTransport`
square. -/
lemma presheafDual_pullback_comparison_natural {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {M M' : X.Modules} (φ : M ⟶ M') :
    let φR := (Scheme.Hom.toRingCatSheafHom f).hom
    let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    (PresheafOfModules.pullback φR).map (PresheafOfModules.dualPrecompHom φ.val)
        ≫ (presheafDualPullbackComparison f M).hom
      = (presheafDualPullbackComparison f M').hom
        ≫ PresheafOfModules.dualPrecompHom ((PresheafOfModules.pushforward β).map φ.val) := by
  intro φR α β
  simp only [presheafDualPullbackComparison, Iso.trans_hom, Iso.symm_hom]
  -- Square 2: naturality of the `isoMk (sliceDualTransport)` factor.
  have sq2 : (PresheafOfModules.pushforward β).map (PresheafOfModules.dualPrecompHom φ.val)
        ≫ (PresheafOfModules.isoMk (fun V => sliceDualTransport f M V)
            (by intro V W g; subsingleton)).hom
      = (PresheafOfModules.isoMk (fun V => sliceDualTransport f M' V)
            (by intro V W g; subsingleton)).hom
        ≫ PresheafOfModules.dualPrecompHom ((PresheafOfModules.pushforward β).map φ.val) := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ψ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    -- At the deepest section level both composites bottom out at
    -- `dualUnitRingSwap f W.left (ψ.app (image slice) (φ.val reindexed across f.opensFunctor) z)`:
    -- the slice-transport reindexing and the `dualPrecompHom` precomposition reindex `φ` to the
    -- same image slice `(op (f.opensFunctor.obj W.left))`, so the equality is definitional (every
    -- intermediate `app`/`map` reduction — `sliceDualTransport_app_apply`,
    -- `dualPrecompHom_restrict_apply`, `pushforward_map_app`, `dual_map_app_apply` — is `rfl`).
    rfl
  -- Paste the two squares.  Square 1 is `natIso_inv_app_naturality` applied with its iso `e` left
  -- as a metavariable, so the goal's giant `leftAdjointUniq` term is captured first-order by
  -- `(?e.app _).inv` — no expensive giant-term defeq.
  exact combine_naturality_squares _ _ _ _ _ _ _
    (natIso_inv_app_naturality _ (PresheafOfModules.dualPrecompHom φ.val)) sq2

end Modules

end Scheme

end AlgebraicGeometry

end -- noncomputable section
