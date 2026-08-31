/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Over
import Std.Tactic.BVDecide.LRAT.Internal.Clause
import AlgebraicJacobian.Picard.TensorObjSubstrate.StalkTensor

/-!
# Vestigial / quarantine sub-module of `TensorObjSubstrate`

This file quarantines three sections of the substrate build that are NOT on the
primary `exists_tensorObj_inverse` closure path but may serve future prover work:

- `FlatWhisker` / `WhiskerOfW` (route-(e) flatness-free whiskering; the lemma
  `isLocallyInjective_whiskerLeft_of_W` is proved, axiom-clean)
- `StalkLinearMap` (route-(e) d.1 ingredient; axiom-clean)
- `OverSliceSheafEquiv` (the shared root for both ⊗-inverse bridges; axiom-clean)

Imported by `AlgebraicJacobian.Picard.TensorObjSubstrate` (the public API file).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace PresheafOfModules

universe v'

variable {C : Type u} [Category.{v'} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}}

/-! ## Project-local Mathlib supplement — flat left-whiskering preserves the
sheafification localizer

The single non-formal ingredient of the `⊗`-invertibility associator
(`AlgebraicGeometry.Scheme.Modules.tensorObj_assoc_iso`, blueprint
`lem:flat_whisker_localizer`): for a sectionwise-*flat* presheaf of modules `F`
and a morphism `g` that is locally injective / locally surjective for the
Grothendieck topology `J` (i.e. lies in the sheafification localizer `J.W`), the
left-whiskered morphism `F ◁ g` is again locally injective / surjective. Local
surjectivity is pure right-exactness of `⊗` (no flatness); local injectivity is
where sectionwise flatness enters, via `Module.Flat.lTensor_exact`. All
ingredients are present in Mathlib — the route uses **no** `MonoidalClosed`
structure. -/

section FlatWhisker

open MonoidalCategory CategoryTheory.Presheaf

variable {J : CategoryTheory.GrothendieckTopology C}

/-- Sectionwise computation: the underlying additive map of `(F ◁ g).app X` is
`LinearMap.lTensor (F.obj X) (g.app X).hom`, acting on a simple tensor by
`a ⊗ₜ b ↦ a ⊗ₜ g(b)`. -/
lemma toPresheaf_whiskerLeft_app_tmul
    (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N) (X : Cᵒᵖ)
    (a : F.obj X) (b : M.obj X) :
    (((toPresheaf _).map (F ◁ g)).app X).hom (a ⊗ₜ[(R.obj X)] b)
      = a ⊗ₜ[(R.obj X)] (g.app X).hom b := by
  erw [toPresheaf_map_app_apply]
  exact ModuleCat.MonoidalCategory.whiskerLeft_apply _ _ a b

/-- The underlying additive map of `(F ◁ g).app X` is `LinearMap.lTensor`. -/
lemma toPresheaf_whiskerLeft_app_apply
    (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N) (X : Cᵒᵖ)
    (z : (F ⊗ M).obj X) :
    (((toPresheaf _).map (F ◁ g)).app X).hom z
      = LinearMap.lTensor (R := (R.obj X : CommRingCat)) (F.obj X) (g.app X).hom z := by
  erw [toPresheaf_map_app_apply, PresheafOfModules.whiskerLeft_app]

/-- **Local surjectivity is preserved by left-whiskering.** Right-exactness of
`⊗`: no flatness needed. Blueprint `lem:flat_whisker_localizer`, surjectivity
half. -/
lemma isLocallySurjective_whiskerLeft
    (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N)
    (hg : IsLocallySurjective J g) :
    IsLocallySurjective J (F ◁ g) := by
  constructor
  intro U s
  induction s using TensorProduct.induction_on with
  | zero =>
      refine J.superset_covering ?_ (J.top_mem U)
      intro V i _
      exact ⟨0, by rw [map_zero]; exact (map_zero _).symm⟩
  | tmul a b =>
      refine J.superset_covering ?_ (hg.imageSieve_mem b)
      intro V i hi
      obtain ⟨c, hc⟩ := hi
      refine ⟨(F.map i.op).hom a ⊗ₜ[(R.obj (Opposite.op V))] c, ?_⟩
      rw [toPresheaf_whiskerLeft_app_tmul]
      erw [presheaf_map_apply_coe, PresheafOfModules.Monoidal.tensorObj_map_tmul]
      congr 1
  | add s t hs ht =>
      refine J.superset_covering ?_ (J.intersection_covering hs ht)
      intro V i hi
      obtain ⟨⟨ds, hds⟩, ⟨dt, hdt⟩⟩ := hi
      refine ⟨ds + dt, ?_⟩
      rw [map_add, hds, hdt]; exact (map_add _ s t).symm

/-- **Local injectivity is preserved by flat left-whiskering.** This is where
sectionwise flatness of `F` enters: via `Module.Flat.lTensor_exact` on the
kernel exact sequence `ker(gₓ) ↪ M(X) →gₓ N(X)`, an element of `ker(F ◁ g)` is
a sum of simple tensors with kernel entries, each of which restricts to `0` on a
covering sieve (local injectivity of `g`). Blueprint `lem:flat_whisker_localizer`,
injectivity half. -/
lemma isLocallyInjective_whiskerLeft_of_flat
    (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    [∀ X, Module.Flat (R.obj X) (F.obj X)]
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N)
    (hg : IsLocallyInjective J g) :
    IsLocallyInjective J (F ◁ g) := by
  constructor
  intro X ξ η h
  -- View the sectionwise map of `g` as `R.obj X`-linear (the ring is commutative).
  let gl : ((M.obj X : ModuleCat _) : Type _) →ₗ[(R.obj X : CommRingCat)]
      ((N.obj X : ModuleCat _) : Type _) := (g.app X).hom
  -- `h` says `F ◁ g` agrees on `ξ, η`, i.e. `lTensor` kills `ξ - η`.
  have hδ : LinearMap.lTensor (R := (R.obj X : CommRingCat)) (F.obj X) gl (ξ - η) = 0 := by
    have heq : LinearMap.lTensor (R := (R.obj X : CommRingCat)) (F.obj X) gl ξ
        = LinearMap.lTensor (R := (R.obj X : CommRingCat)) (F.obj X) gl η := by
      rw [← toPresheaf_whiskerLeft_app_apply, ← toPresheaf_whiskerLeft_app_apply]; exact h
    exact (map_sub (LinearMap.lTensor (R := (R.obj X : CommRingCat)) (F.obj X) gl) ξ η).trans
      (sub_eq_zero.mpr heq)
  -- Flatness: `ker(F ⊗ gl) = range(F ⊗ ker.subtype)`, so `ξ - η` is a sum of simple
  -- tensors with kernel entries.
  have hex : Function.Exact
      (LinearMap.lTensor (R := (R.obj X : CommRingCat)) (F.obj X) (LinearMap.ker gl).subtype)
      (LinearMap.lTensor (R := (R.obj X : CommRingCat)) (F.obj X) gl) :=
    Module.Flat.lTensor_exact (F.obj X) (LinearMap.exact_subtype_ker_map gl)
  obtain ⟨ζ, hζ⟩ := (hex (ξ - η)).mp hδ
  -- Each simple tensor `a ⊗ k` with `gl k = 0` restricts to `0` on a covering sieve
  -- (local injectivity of `g`); induct on the witness `ζ`.
  have key : ∀ ζ : TensorProduct (R.obj X) (F.obj X) (LinearMap.ker gl),
      Presheaf.equalizerSieve (F := (toPresheaf _).obj (F ⊗ M)) (X := X)
        (LinearMap.lTensor (R := (R.obj X : CommRingCat)) (F.obj X)
          (LinearMap.ker gl).subtype ζ) 0 ∈ J X.unop := by
    intro ζ
    induction ζ using TensorProduct.induction_on with
    | zero =>
        rw [map_zero]
        exact J.superset_covering (Presheaf.equalizerSieve_self_eq_top _).ge (J.top_mem _)
    | tmul a kk =>
        rw [LinearMap.lTensor_tmul]
        have hk : ((toPresheaf _).map g).app X kk.1
            = ((toPresheaf _).map g).app X (0 : ((toPresheaf _).obj M).obj X) := by
          rw [map_zero]
          erw [toPresheaf_map_app_apply]
          exact kk.2
        refine J.superset_covering ?_ (hg.equalizerSieve_mem kk.1 0 hk)
        intro V f hf
        rw [Presheaf.equalizerSieve_apply] at hf ⊢
        rw [map_zero] at hf ⊢
        erw [presheaf_map_apply_coe, PresheafOfModules.Monoidal.tensorObj_map_tmul]
        erw [presheaf_map_apply_coe] at hf
        rw [Submodule.subtype_apply, hf]
        erw [TensorProduct.tmul_zero]; rfl
    | add ζ₁ ζ₂ h₁ h₂ =>
        rw [map_add]
        refine J.superset_covering ?_ (J.intersection_covering h₁ h₂)
        intro V f hf
        obtain ⟨hf1, hf2⟩ := hf
        rw [Presheaf.equalizerSieve_apply] at hf1 hf2 ⊢
        rw [map_zero] at hf1 hf2 ⊢
        exact (map_add _ _ _).trans (by rw [hf1, hf2, add_zero])
  -- Transport `equalizerSieve (ξ - η) 0 ∈ J` to `equalizerSieve ξ η ∈ J`.
  have hmain : Presheaf.equalizerSieve (F := (toPresheaf _).obj (F ⊗ M)) (X := X)
      (ξ - η) 0 ∈ J X.unop := hζ ▸ key ζ
  refine J.superset_covering ?_ hmain
  intro V f hf
  rw [Presheaf.equalizerSieve_apply] at hf ⊢
  rw [map_zero, map_sub, sub_eq_zero] at hf
  exact hf

/-- **Flat left-whiskering preserves the sheafification localizer.**
(Blueprint `lem:flat_whisker_localizer`.) For a sectionwise-flat presheaf of
modules `F` and a morphism `g` lying in the sheafification localizer `J.W` (the
class of morphisms inverted by sheafification, equivalently the locally bijective
ones via `WEqualsLocallyBijective`), the left-whiskered morphism `F ◁ g` again
lies in `J.W`. The two halves are `isLocallyInjective_whiskerLeft_of_flat` (where
flatness enters) and `isLocallySurjective_whiskerLeft` (pure right-exactness).
This is the single non-formal ingredient of the `⊗`-invertibility associator
`tensorObj_assoc_iso`; the route uses no `MonoidalClosed` structure. -/
lemma W_whiskerLeft_of_flat [J.WEqualsLocallyBijective Ab.{u}]
    (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    [∀ X, Module.Flat (R.obj X) (F.obj X)]
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N)
    (hg : J.W ((toPresheaf _).map g)) :
    J.W ((toPresheaf _).map (F ◁ g)) := by
  rw [GrothendieckTopology.W_iff_isLocallyBijective] at hg ⊢
  exact ⟨isLocallyInjective_whiskerLeft_of_flat F g hg.1,
    isLocallySurjective_whiskerLeft F g hg.2⟩

/-- **Flat right-whiskering preserves the sheafification localizer.** The
braiding-conjugate of `W_whiskerLeft_of_flat`: for a sectionwise-flat presheaf of
modules `F` and a morphism `g` in the sheafification localizer `J.W`, the
right-whiskered morphism `g ▷ F` again lies in `J.W`. Obtained from the
left-whiskered statement by conjugating with the (iso) braiding of the symmetric
presheaf-of-modules monoidal structure, using that `J.W` respects isomorphisms. -/
lemma W_whiskerRight_of_flat [J.WEqualsLocallyBijective Ab.{u}]
    (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    [∀ X, Module.Flat (R.obj X) (F.obj X)]
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N)
    (hg : J.W ((toPresheaf _).map g)) :
    J.W ((toPresheaf _).map (g ▷ F)) := by
  have hwl := W_whiskerLeft_of_flat F g hg
  -- `g ▷ F = (β_ M F).hom ≫ (F ◁ g) ≫ (β_ N F).inv` by braiding naturality.
  have hconj : g ▷ F
      = (BraidedCategory.braiding M F).hom ≫ (F ◁ g) ≫ (BraidedCategory.braiding N F).inv := by
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left g F, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [hconj, Functor.map_comp, Functor.map_comp]
  -- `J.W` respects isos on both sides (it is the sheafification localizer).
  rw [(J.W).cancel_left_of_respectsIso, (J.W).cancel_right_of_respectsIso]
  exact hwl


/-- **The sheafification-localization bridge.** A morphism `f` of presheaves of
modules whose underlying additive-presheaf map lies in the sheafification localizer
`J.W` is sent by the associated-sheaf-of-modules functor to an isomorphism. This is
the single residual of the `⊗`-invertibility associator
`AlgebraicGeometry.Scheme.Modules.tensorObj_assoc_iso`. It is the morphism-property
identity `PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`
(the sheafification functor *is* the localization at `J.W.inverseImage (toPresheaf _)`)
read at a single morphism. -/
lemma isIso_sheafification_map_of_W
    {R₀ : Cᵒᵖ ⥤ RingCat} {Rsh : CategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ Rsh.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat] [CategoryTheory.HasWeakSheafify J AddCommGrpCat]
    {A B : PresheafOfModules.{u} R₀} (f : A ⟶ B)
    (hf : J.W ((PresheafOfModules.toPresheaf R₀).map f)) :
    IsIso ((PresheafOfModules.sheafification α).map f) := by
  have h := PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms (J := J) α
  have h2 : (CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules Rsh)).inverseImage
      (PresheafOfModules.sheafification α) f := by rw [← h]; exact hf
  exact h2

end FlatWhisker

/-! ## Project-local Mathlib supplement — the `R.stalk x`-linear stalk map
(ROUTE (e), ingredient d.1)

The route-(e) residual `isLocallyInjective_whiskerLeft_of_W` is a stalkwise
argument: a `J.W`-morphism `g` is a *stalkwise isomorphism*, so `(F ◁ g)_x =
id_{F_x} ⊗_{R_x} g_x` is again an isomorphism for arbitrary `F`. The stalkwise
characterisation it ultimately rests on (ingredient d.1) requires the induced
Ab-stalk map of a morphism `g : M ⟶ N` of presheaves of `R`-modules to be packaged
as an **`R.stalk x`-linear map** between the stalk modules.

Mathlib (`Mathlib.Algebra.Category.ModuleCat.Stalk`) already supplies, for `X : TopCat`
and `R : X.Presheaf CommRingCat`, the stalk module structure
`Module (R.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x)` together with the germ /
scalar compatibility `PresheafOfModules.germ_smul`; what it does **not** supply is the
linearity of the induced stalk map `(stalkFunctor Ab x).map ((toPresheaf _).map g)`.
This section provides that packaging (the first concrete ingredient of d.1 toward
`isLocallyInjective_whiskerLeft_of_W`). The base ring presheaf is necessarily
`CommRingCat`-valued, matching the project's `X.presheaf` carrier. -/

section StalkLinearMap

open TopologicalSpace TopCat.Presheaf Opposite

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}

/-- **The `R.stalk x`-linear stalk map of a morphism of presheaves of modules.**
For `g : M ⟶ N` in `PresheafOfModules (R ⋙ forget₂ _ _)` over a topological space
`X` and a point `x`, the induced Ab-stalk map `(stalkFunctor Ab x).map
((toPresheaf _).map g) : M.presheaf.stalk x ⟶ N.presheaf.stalk x` is `R.stalk x`-linear
for the stalk module structures of `Mathlib.Algebra.Category.ModuleCat.Stalk`.
Project-local: Mathlib packages the stalk module structure (`germ_smul`) but not the
linearity of the induced stalk map. This is ingredient (d.1) of the route-(e)
stalkwise argument for `isLocallyInjective_whiskerLeft_of_W`. -/
noncomputable def stalkLinearMap
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N) (x : X) :
    (↑(TopCat.Presheaf.stalk M.presheaf x) : Type u) →ₗ[↑(R.stalk x)]
      (↑(TopCat.Presheaf.stalk N.presheaf x) : Type u) where
  toFun := (ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map g)))
  map_add' a b := map_add _ a b
  map_smul' r s := by
    dsimp only [RingHom.id_apply]
    obtain ⟨U, hxU, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
    obtain ⟨V, hxV, s₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf s
    set W : Opens X := U ⊓ V with hW
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    set iWU : W ⟶ U := homOfLE inf_le_left
    set iWV : W ⟶ V := homOfLE inf_le_right
    have hr : (ConcreteCategory.hom (R.germ U x hxU)) r₀
        = (ConcreteCategory.hom (R.germ W x hxW)) ((ConcreteCategory.hom (R.map iWU.op)) r₀) :=
      (TopCat.Presheaf.germ_res_apply R iWU x hxW r₀).symm
    have hs : (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf V x hxV)) s₀
        = (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
            ((ConcreteCategory.hom (M.presheaf.map iWV.op)) s₀) :=
      (TopCat.Presheaf.germ_res_apply M.presheaf iWV x hxW s₀).symm
    have key : ∀ (z : (↑(M.obj (op W)) : Type u)),
        (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((toPresheaf _).map g)))
          ((ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW)) z)
        = (ConcreteCategory.hom (TopCat.Presheaf.germ N.presheaf W x hxW))
            ((ConcreteCategory.hom (g.app (op W))) z) := by
      intro z
      rw [show (ConcreteCategory.hom (g.app (op W))) z
            = (ConcreteCategory.hom (((toPresheaf _).map g).app (op W))) z from
            (toPresheaf_map_app_apply g (op W) z).symm]
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply (F := M.presheaf) (G := N.presheaf)
        W x hxW ((toPresheaf _).map g) z
    rw [hr, hs, ← PresheafOfModules.germ_smul M x W hxW, key, map_smul,
        PresheafOfModules.germ_smul N x W hxW, key]

/-- **Germ characterisation of `stalkLinearMap`.** On the germ of a section `s` over
an open `U ∋ x`, `stalkLinearMap g x` is the germ of `g.app (op U) s`. This is the
defining naturality of the stalk map, exposed for the downstream d.2 assembly
(identifying the stalk map of `F ◁ g` with `id_{F_x} ⊗ g_x`). -/
lemma stalkLinearMap_germ
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N) (x : X)
    (U : Opens X) (hx : x ∈ U) (s : (↑(M.obj (op U)) : Type u)) :
    stalkLinearMap g x ((ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf U x hx)) s)
      = (ConcreteCategory.hom (TopCat.Presheaf.germ N.presheaf U x hx))
          ((ConcreteCategory.hom (g.app (op U))) s) := by
  change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((toPresheaf _).map g)))
      ((ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf U x hx)) s) = _
  rw [show (ConcreteCategory.hom (g.app (op U))) s
        = (ConcreteCategory.hom (((toPresheaf _).map g).app (op U))) s from
        (toPresheaf_map_app_apply g (op U) s).symm]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply (F := M.presheaf) (G := N.presheaf)
    U x hx ((toPresheaf _).map g) s

/-- **A stalkwise-iso morphism induces a bijective `R.stalk x`-linear stalk map.**
If the underlying Ab-stalk map of `g` at `x` is an isomorphism, then `stalkLinearMap
g x` is bijective — hence (being `R.stalk x`-linear) an `R.stalk x`-linear
equivalence `M_x ≃ₗ N_x`. This is the form ingredient (d.1) feeds into the
`id_{F_x} ⊗ g_x` step (tensoring an `R.stalk x`-linear equivalence by `id` stays an
equivalence, flatness-free). -/
lemma stalkLinearMap_bijective_of_isIso
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N) (x : X)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map g))) :
    Function.Bijective (stalkLinearMap g x) := by
  change Function.Bijective ⇑(ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map g)))
  exact ConcreteCategory.bijective_of_isIso _

/-- **The `R.stalk x`-linear stalk equivalence of a stalkwise-iso morphism.** When the
underlying Ab-stalk map of `g` at `x` is an isomorphism, `stalkLinearMap g x` upgrades
to an `R.stalk x`-linear equivalence `M_x ≃ₗ N_x`. This is the exact object the route-(e)
`id_{F_x} ⊗ g_x` step consumes: tensoring it by `id_{F_x}` (`LinearEquiv.lTensor`) yields
an equivalence with no flatness hypothesis. -/
noncomputable def stalkLinearEquivOfIsIso
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N) (x : X)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map g))) :
    (↑(TopCat.Presheaf.stalk M.presheaf x) : Type u) ≃ₗ[↑(R.stalk x)]
      (↑(TopCat.Presheaf.stalk N.presheaf x) : Type u) :=
  LinearEquiv.ofBijective (stalkLinearMap g x) (stalkLinearMap_bijective_of_isIso g x h)

end StalkLinearMap

/-! ## Project-local Mathlib supplement — stalk bridges for the topological site

For the topological site `Opens X`, a morphism of presheaves valued in a concrete
category is locally injective iff it is injective on all stalks. Mathlib supplies the
*surjective* analogue for presheaves (`locally_surjective_iff_surjective_on_stalks`) and
the *injective* one only at the sheaf level (`app_injective_iff_stalkFunctor_map_injective`);
the presheaf-level local-injectivity bridge is project-local. Combined, they characterise
the sheafification localizer `J.W` stalkwise (`isIso_stalkFunctor_map_of_W`), the (d.1)
ingredient of the route-(d) whiskering closure. -/

section StalkBridge

open TopologicalSpace TopCat.Presheaf Opposite

universe w

variable {A : Type w} [Category.{u} A] [Limits.HasColimits A]
  {FA : A → A → Type*} {CA : A → Type u} [(P Q : A) → FunLike (FA P Q) (CA P) (CA Q)]
  [ConcreteCategory A FA] [Limits.PreservesFilteredColimits (forget A)]
  {Z : TopCat.{u}}

/-- **Injective on stalks ⇒ locally injective (topological site).** For a morphism `T` of
presheaves valued in a concrete category over a topological space `Z`, stalkwise injectivity
implies local injectivity for `Opens.grothendieckTopology Z`. Project-local: Mathlib provides
this only at the sheaf level (`app_injective_iff_stalkFunctor_map_injective`); here it is the
presheaf-level statement, proved directly through `germ_eq` (the equalizer sieve covers each
point because agreeing germs agree on a neighbourhood). -/
theorem isLocallyInjective_of_injective_stalk
    {F G : TopCat.Presheaf A Z} (T : F ⟶ G)
    (h : ∀ z : Z, Function.Injective ⇑(ConcreteCategory.hom ((stalkFunctor A z).map T))) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Z) T := by
  refine ⟨fun {U'} s t hst z hz => ?_⟩
  have hgerm : (ConcreteCategory.hom (F.germ (unop U') z hz)) s
      = (ConcreteCategory.hom (F.germ (unop U') z hz)) t := by
    apply h z
    rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply, hst]
  obtain ⟨W, hzW, iU, iV, heq⟩ := F.germ_eq z hz hz s t hgerm
  refine ⟨W, iU, ?_, hzW⟩
  rw [Subsingleton.elim iV iU] at heq
  rw [Presheaf.equalizerSieve_apply]
  exact heq

/-- **Locally injective ⇒ injective on stalks (topological site).** The converse of
`isLocallyInjective_of_injective_stalk`: a locally injective morphism of presheaves over a
topological space induces injective stalk maps. Proved via `germ_eq` and the covering of the
equalizer sieve. -/
theorem injective_stalk_of_isLocallyInjective
    {F G : TopCat.Presheaf A Z} (T : F ⟶ G)
    (hT : CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Z) T)
    (z : Z) :
    Function.Injective ⇑(ConcreteCategory.hom ((stalkFunctor A z).map T)) := by
  intro sₓ tₓ hxeq
  obtain ⟨U, hzU, s, rfl⟩ := F.exists_germ_eq sₓ
  obtain ⟨V, hzV, t, rfl⟩ := F.exists_germ_eq tₓ
  rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply] at hxeq
  obtain ⟨W, hzW, iU, iV, heqG⟩ := G.germ_eq z hzU hzV
    ((ConcreteCategory.hom (T.app (op U))) s) ((ConcreteCategory.hom (T.app (op V))) t) hxeq
  set a := (ConcreteCategory.hom (F.map iU.op)) s with ha
  set b := (ConcreteCategory.hom (F.map iV.op)) t with hb
  have hTab : (ConcreteCategory.hom (T.app (op W))) a
      = (ConcreteCategory.hom (T.app (op W))) b := by
    rw [ha, hb, NatTrans.naturality_apply T iU.op s, NatTrans.naturality_apply T iV.op t]
    exact heqG
  obtain ⟨W', f, hf, hzW'⟩ := hT.equalizerSieve_mem (X := op W) a b hTab z hzW
  rw [Presheaf.equalizerSieve_apply] at hf
  have e3 : (ConcreteCategory.hom (F.germ W z hzW)) a
      = (ConcreteCategory.hom (F.germ W z hzW)) b := by
    rw [← F.germ_res_apply f z hzW' a, ← F.germ_res_apply f z hzW' b, hf]
  rw [← F.germ_res_apply iU z hzW s, ← F.germ_res_apply iV z hzW t, ← ha, ← hb, e3]

/-- **The sheafification localizer is a stalkwise isomorphism (topological site).** For
presheaves of abelian groups on a topological space `Z` whose Grothendieck topology has
`WEqualsLocallyBijective`, a morphism in the sheafification localizer `J.W` induces an
isomorphism on every stalk. This is the (d.1) bridge: it combines the injective stalk bridge
`injective_stalk_of_isLocallyInjective` with Mathlib's surjective one
`locally_surjective_iff_surjective_on_stalks`, and `ConcreteCategory.isIso_iff_bijective`. -/
theorem isIso_stalkFunctor_map_of_W {Z : TopCat.{u}}
    [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : TopCat.Presheaf AddCommGrpCat.{u} Z} (T : F ⟶ G)
    (hT : (Opens.grothendieckTopology Z).W T) (z : Z) :
    IsIso ((stalkFunctor AddCommGrpCat.{u} z).map T) := by
  rw [GrothendieckTopology.W_iff_isLocallyBijective] at hT
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨injective_stalk_of_isLocallyInjective T hT.1 z,
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks T).mp hT.2 z⟩

end StalkBridge

/-! ## Project-local Mathlib supplement — flatness-FREE whiskering of a locally
bijective morphism (ROUTE (d), realized via the stalk–tensor commutation d.2)

The flat whiskering `W_whisker{Left,Right}_of_flat` needs the SECTIONWISE flatness instance
`∀ U, Module.Flat (R(U)) (F(U))`, which is FALSE for invertible sheaves over non-affine opens
and is therefore OFF the associator critical path. The associator only ever whiskers the
sheafification UNIT `η = toSheafify`, which is **locally bijective** (`∈ J.W`). Whiskering a
*locally bijective* `g` by an *arbitrary* `F` preserves local bijectivity with NO flatness
hypothesis: stalkwise `(F ◁ g)_x = id_{F_x} ⊗_{R_x} g_x`, and since `g_x` is an isomorphism
(d.1, `isIso_stalkFunctor_map_of_W`), the tensor `id ⊗ g_x` is again an isomorphism by the
stalk–tensor commutation (d.2, `stalkTensorIso`) — flatness-free, because *isomorphisms*
tensor to isomorphisms whereas mere *injections* need flatness. -/

section WhiskerOfW

open MonoidalCategory CategoryTheory.Presheaf TopologicalSpace TopCat.Presheaf Opposite
open PresheafOfModules.Monoidal

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}

/-- **Whiskering a locally bijective morphism preserves local injectivity (flatness-free).**
For an *arbitrary* presheaf of modules `F` and a morphism `g` whose underlying additive map is
locally bijective (`∈ J.W`), the left-whiskered morphism `F ◁ g` is locally injective. The
proof is the stalkwise computation `(F ◁ g)_x = id_{F_x} ⊗_{R_x} g_x`: by (d.1) `g_x` is an
isomorphism, and by the (d.2) stalk–tensor commutation `stalkTensorIso` the stalk of `F ◁ g`
is identified with `id_{F_x} ⊗ g_x`, hence an isomorphism — for *any* `F`, with neither
sectionwise flatness nor local triviality of `F`. This is the single residual ingredient of the
associator `tensorObj_assoc_iso` under ROUTE (d). -/
lemma isLocallyInjective_whiskerLeft_of_W
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N)
    (hg : (Opens.grothendieckTopology X).W ((toPresheaf _).map g)) :
    IsLocallyInjective (Opens.grothendieckTopology X) (F ◁ g) := by
  -- (d.1) `g` is a stalkwise isomorphism.
  have hgx : ∀ z : X, IsIso ((stalkFunctor AddCommGrpCat.{u} z).map ((toPresheaf _).map g)) :=
    fun z => isIso_stalkFunctor_map_of_W _ hg z
  -- Reduce to stalkwise injectivity of `F ◁ g`.
  apply isLocallyInjective_of_injective_stalk
  intro z
  -- The (d.2) stalk–tensor commutation isomorphisms and the stalkwise iso of `g`.
  set eM := stalkTensorIso F M z with heM
  set eN := stalkTensorIso F N z with heN
  set e := stalkLinearEquivOfIsIso g z (hgx z) with he
  set E := TensorProduct.congr
    (LinearEquiv.refl (↑(R.stalk z)) (↑(TopCat.Presheaf.stalk F.presheaf z))) e with hE
  set φ := (stalkFunctor AddCommGrpCat.{u} z).map ((toPresheaf _).map (F ◁ g)) with hφ
  -- B-naturality: under `eM`/`eN`, the stalk of `F ◁ g` is `id_{F_z} ⊗ g_z`.
  have key : ∀ w : ↑(TopCat.Presheaf.stalk (Monoidal.tensorObj F M).presheaf z),
      eN (ConcreteCategory.hom φ w) = E (eM w) := by
    intro w
    obtain ⟨W, hzW, p, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (Monoidal.tensorObj F M).presheaf w
    -- The germ map, `φ`, `eN`, `eM`, `E` are all additive; the `+`/`0` instances on the
    -- defeq carriers `(toPresheaf _).obj (F ⊗ M)` vs `(Monoidal.tensorObj F M).presheaf` differ
    -- syntactically, so we distribute `map_add`/`map_zero` via `have`-terms (defeq-coerced).
    induction p using TensorProduct.induction_on with
    | zero =>
        erw [map_zero (ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)),
          map_zero (ConcreteCategory.hom φ), map_zero eN, map_zero eM, map_zero E]
    | tmul a m =>
        -- RHS: `eM (germ (a ⊗ m)) = germ_F a ⊗ germ_M m`, then `E` sends it to
        -- `germ_F a ⊗ e (germ_M m) = germ_F a ⊗ germ_N (g_W m)`.
        have hRM : eM ((ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW))
              (a ⊗ₜ[↑((R ⋙ forget₂ CommRingCat RingCat).obj (op W))] m))
            = (ConcreteCategory.hom (TopCat.Presheaf.germ F.presheaf W z hzW)) a
              ⊗ₜ[↑(R.stalk z)]
                (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W z hzW)) m :=
          stalkTensorLinearMap_germ_tmul F M z W hzW a m
        have hLN : eN ((ConcreteCategory.hom (germ (Monoidal.tensorObj F N).presheaf W z hzW))
              (a ⊗ₜ[↑((R ⋙ forget₂ CommRingCat RingCat).obj (op W))]
                ((ConcreteCategory.hom (g.app (op W))) m)))
            = (ConcreteCategory.hom (TopCat.Presheaf.germ F.presheaf W z hzW)) a
              ⊗ₜ[↑(R.stalk z)]
                (ConcreteCategory.hom (TopCat.Presheaf.germ N.presheaf W z hzW))
                  ((ConcreteCategory.hom (g.app (op W))) m) :=
          stalkTensorLinearMap_germ_tmul F N z W hzW a ((ConcreteCategory.hom (g.app (op W))) m)
        have hL1 : (ConcreteCategory.hom φ)
              ((ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW))
                (a ⊗ₜ[↑((R ⋙ forget₂ CommRingCat RingCat).obj (op W))] m))
            = (ConcreteCategory.hom (germ (Monoidal.tensorObj F N).presheaf W z hzW))
                (a ⊗ₜ[↑((R ⋙ forget₂ CommRingCat RingCat).obj (op W))]
                  ((ConcreteCategory.hom (g.app (op W))) m)) := by
          erw [stalkFunctor_map_germ_apply]
          congr 1
        rw [hL1, hLN, hRM, hE, TensorProduct.congr_tmul, LinearEquiv.refl_apply, he]
        congr 1
        exact (stalkLinearMap_germ g z W hzW m).symm
    | add p q hp hq =>
        have hg2 : (ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) (p + q)
            = (ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) p
              + (ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) q :=
          map_add _ _ _
        rw [hg2]
        have hphi2 : (ConcreteCategory.hom φ)
              ((ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) p
                + (ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) q)
            = (ConcreteCategory.hom φ)
                ((ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) p)
              + (ConcreteCategory.hom φ)
                ((ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) q) :=
          map_add _ _ _
        rw [hphi2]
        have heN2 : eN ((ConcreteCategory.hom φ)
              ((ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) p)
            + (ConcreteCategory.hom φ)
              ((ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) q))
            = eN ((ConcreteCategory.hom φ)
                ((ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) p))
              + eN ((ConcreteCategory.hom φ)
                ((ConcreteCategory.hom (germ (Monoidal.tensorObj F M).presheaf W z hzW)) q)) :=
          map_add _ _ _
        rw [heN2]
        simp only [map_add]
        rw [hp, hq]
  -- Hence the stalk map of `F ◁ g` is a composite of bijections.
  have hbij : Function.Bijective ⇑(ConcreteCategory.hom φ) := by
    have hfun : ⇑(ConcreteCategory.hom φ) = ⇑eN.symm ∘ ⇑E ∘ ⇑eM := by
      funext w
      rw [Function.comp_apply, Function.comp_apply, ← key w, eN.symm_apply_apply]
    rw [hfun]
    exact eN.symm.bijective.comp (E.bijective.comp eM.bijective)
  exact hbij.1

/-- **Flatness-free left-whiskering preserves the sheafification localizer.** The ROUTE (d)
replacement for `W_whiskerLeft_of_flat`: for an *arbitrary* `F` and a locally bijective `g`
(`∈ J.W`), `F ◁ g` again lies in `J.W`. Local surjectivity is free
(`isLocallySurjective_whiskerLeft`, right-exactness); local injectivity is the flatness-free
stalkwise residual `isLocallyInjective_whiskerLeft_of_W`. -/
lemma W_whiskerLeft_of_W
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N)
    (hg : (Opens.grothendieckTopology X).W ((toPresheaf _).map g)) :
    (Opens.grothendieckTopology X).W ((toPresheaf _).map (F ◁ g)) := by
  have hbij := hg
  rw [GrothendieckTopology.W_iff_isLocallyBijective] at hbij
  rw [GrothendieckTopology.W_iff_isLocallyBijective]
  exact ⟨isLocallyInjective_whiskerLeft_of_W F g hg,
    isLocallySurjective_whiskerLeft F g hbij.2⟩

/-- **Flatness-free right-whiskering preserves the sheafification localizer.** The
braiding-conjugate of `W_whiskerLeft_of_W`, mirroring `W_whiskerRight_of_flat`. -/
lemma W_whiskerRight_of_W
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N)
    (hg : (Opens.grothendieckTopology X).W ((toPresheaf _).map g)) :
    (Opens.grothendieckTopology X).W ((toPresheaf _).map (g ▷ F)) := by
  have hwl := W_whiskerLeft_of_W F g hg
  have hconj : g ▷ F
      = (BraidedCategory.braiding M F).hom ≫ (F ◁ g) ≫ (BraidedCategory.braiding N F).inv := by
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left g F, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [hconj, Functor.map_comp, Functor.map_comp]
  rw [(Opens.grothendieckTopology X).W.cancel_left_of_respectsIso,
    (Opens.grothendieckTopology X).W.cancel_right_of_respectsIso]
  exact hwl

end WhiskerOfW

end PresheafOfModules

/-! ## Project-local Mathlib supplement — the open-immersion↔slice sheaf-site
equivalence (the SHARED root of both ⊗-inverse bridges)

For a topological space `X` and an open `U : Opens X`, Mathlib supplies the
1-categorical equivalence `TopologicalSpace.Opens.overEquivalence U : Over U ≌ Opens ↥U`
(`Mathlib/Topology/Sheaves/Over.lean`) but leaves, as a documented `## TODO`, the
upgrade of this to an *equivalence of sheaf categories*

  `Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A`.

This is the single Mathlib-absent root on which BOTH remaining ⊗-inverse bridges
(the A-engine `homOfLocalCompat` gluing and the C-bridge `dual_isLocallyTrivial`)
reduce: re-evaluating a slice-internal-hom along the open immersion `U ↪ X` is
exactly transport across this sheaf-site equivalence. It is value-category
parametric (`A` is arbitrary), so one build serves both lanes.

The proof routes through `CategoryTheory.Equivalence.sheafCongr`, which needs only
the dense-subsite instance `(overEquivalence U).inverse.IsDenseSubsite …`. The sole
non-formal content of that instance is the cover-correspondence
`functorPushforward_mem_iff`, which we discharge *pointwise*: on the thin poset
`Opens X` a covering sieve is a pointwise neighbourhood cover, and the open
embedding `↥U ↪ X` matches points and opens on both sides. No `Over.map`
pseudofunctor coherence appears — thinness trivialises it.

Per blueprint `lem:open_immersion_slice_sheaf_equiv`. -/

namespace AlgebraicGeometry.Scheme.Modules

section OverSliceSheafEquiv

open Topology CategoryTheory

universe v w

-- NOTE: within the `AlgebraicGeometry.Scheme.Modules` namespace the unqualified
-- identifier `Opens` resolves to the scheme-theoretic `Scheme.Opens` (expecting a
-- `Scheme`), shadowing the intended point-set `TopologicalSpace.Opens`. We therefore
-- fully qualify every `TopologicalSpace.Opens …` here; `Over`/`Sieve`/`GrothendieckTopology`
-- are `CategoryTheory` names with no scheme shadow and stay unqualified.

variable {X : Type u} [TopologicalSpace X] (U : TopologicalSpace.Opens X)

/-- Pointwise cover-correspondence underlying `overEquivInverseIsDenseSubsite`: a
sieve `S` on `W : Opens ↥U` is a covering sieve in the subspace topology iff its
pushforward along the open-embedding image functor `↥U ↪ X` is a covering sieve in
`X`. Both sides are the pointwise neighbourhood-cover condition of
`Opens.grothendieckTopology`, matched across the injection `Subtype.val`. -/
private lemma overEquiv_image_cover_iff (W : TopologicalSpace.Opens ↥U) (S : Sieve W) :
    (S.functorPushforward ((TopologicalSpace.Opens.overEquivalence U).inverse ⋙ Over.forget U))
        ∈ (Opens.grothendieckTopology X)
          (((TopologicalSpace.Opens.overEquivalence U).inverse ⋙ Over.forget U).obj W)
      ↔ S ∈ (Opens.grothendieckTopology ↥U) W := by
  constructor
  · intro h y hy
    have hx : (y : X) ∈
        (((TopologicalSpace.Opens.overEquivalence U).inverse ⋙ Over.forget U).obj W) :=
      ⟨y, hy, rfl⟩
    obtain ⟨V, f, hf, hxV⟩ := h y hx
    obtain ⟨W', a, b, hSa, _⟩ := hf
    refine ⟨W', a, hSa, ?_⟩
    have hyim : (y : X) ∈
        ((TopologicalSpace.Opens.overEquivalence U).inverse ⋙ Over.forget U).obj W' := b.le hxV
    obtain ⟨z, hz, hzeq⟩ := hyim
    rw [← (Subtype.ext hzeq : z = y)]; exact hz
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨W', a, hSa, hyW'⟩ := h y hy
    refine ⟨((TopologicalSpace.Opens.overEquivalence U).inverse ⋙ Over.forget U).obj W',
      ((TopologicalSpace.Opens.overEquivalence U).inverse ⋙ Over.forget U).map a, ?_,
      ⟨y, hyW', rfl⟩⟩
    exact ⟨W', a, 𝟙 _, hSa, by simp⟩

/-- The inverse of `overEquivalence U` exhibits `(Opens ↥U, subspace topology)` as a
dense subsite of `(Over U, slice topology)`. This is the dense-subsite datum
`Equivalence.sheafCongr` consumes; the only non-formal field is the pointwise
cover-correspondence `overEquiv_image_cover_iff`. -/
instance overEquivInverseIsDenseSubsite :
    (TopologicalSpace.Opens.overEquivalence U).inverse.IsDenseSubsite
      (Opens.grothendieckTopology ↥U)
      ((Opens.grothendieckTopology X).over U) where
  functorPushforward_mem_iff {W S} := by
    rw [GrothendieckTopology.mem_over_iff]
    rw [show Sieve.overEquiv ((TopologicalSpace.Opens.overEquivalence U).inverse.obj W)
          (S.functorPushforward (TopologicalSpace.Opens.overEquivalence U).inverse)
        = S.functorPushforward
            ((TopologicalSpace.Opens.overEquivalence U).inverse ⋙ Over.forget U) by
      rw [Sieve.functorPushforward_comp]; rfl]
    exact overEquiv_image_cover_iff U W S

/-- **The open-immersion↔slice sheaf-site equivalence.** For a topological space
`X`, an open `U : Opens X`, and any value category `A`, the slice sheaf category
over `U` is equivalent to the sheaf category on the open subspace `↥U`:

  `Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A`.

This completes the documented Mathlib `## TODO` at `Topology/Sheaves/Over.lean` and
is the SHARED root both ⊗-inverse bridges (`homOfLocalCompat`, `dual_isLocallyTrivial`)
reduce to. Built by transporting `TopologicalSpace.Opens.overEquivalence U` across
`CategoryTheory.Equivalence.sheafCongr`, using the project-local dense-subsite
instance `overEquivInverseIsDenseSubsite`.

Per blueprint `lem:open_immersion_slice_sheaf_equiv`. -/
noncomputable def overSliceSheafEquiv (A : Type w) [Category.{v} A] :
    Sheaf ((Opens.grothendieckTopology X).over U) A ≌
      Sheaf (Opens.grothendieckTopology ↥U) A :=
  (TopologicalSpace.Opens.overEquivalence U).sheafCongr
    ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology ↥U) A

end OverSliceSheafEquiv

end AlgebraicGeometry.Scheme.Modules
