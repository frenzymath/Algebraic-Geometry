/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.Carriers
import AlgebraicJacobian.Cohomology.MayerVietorisCore

/-!
# The H⁰-sections bridge: `HModule' k F 0 U ≃ₗ[k] Γ(U, F)`

For a sheaf `F` of `k`-modules on a site `(C, J)` and an object `U : C`, the
degree-zero open-evaluation cohomology `HModule' k F 0 U` (the `Ext⁰` from the
sheafified free `ModuleCat k`-presheaf on `yoneda.obj U` into `F`, see
`Carriers.lean`) is canonically the module of sections `Γ(U, F) = F.obj.obj (op U)`.
This file constructs that identification as a `k`-linear equivalence
(`HModule'_zero_sectionsLinearEquiv`) together with its two naturality
companions:

* naturality in the object `U` (restriction maps), stated against the
  contravariant functoriality `(HModule'_cohomologyPresheaf k F 0).map g.op`
  used by the in-tree Mayer-Vietoris LES (`MayerVietorisCore.lean`), and
* naturality in the sheaf `F` (postcomposition with `Abelian.Ext.mk₀ φ` for a
  sheaf morphism `φ : F ⟶ G`), the shape consumed by the second-variable
  (dimension-shift) `Ext` long exact sequence
  (`Abelian.Ext.covariant_sequence_exact₁/₂/₃`).

The equivalence is the composite of three identifications:

1. `HModule'_zero_linearEquiv` (`Carriers.lean`): `Ext⁰` is the Hom group
   `((presheafToSheaf J _).obj P_U ⟶ F)` where
   `P_U := (yoneda ⋙ (whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U`;
2. the `k`-linearised sheafification adjunction
   (`(sheafificationAdjunction J _).homLinearEquiv k`, gap-fill from
   `Presheaf.lean`): `((presheafToSheaf J _).obj P_U ⟶ F) ≃ₗ[k] (P_U ⟶ F.obj)`;
3. the **free-Yoneda sections equivalence** `freeYonedaSectionsLinearEquiv`
   (this file): for any presheaf of `k`-modules `M`,
   `(P_U ⟶ M) ≃ₗ[k] M.obj (op U)`, by evaluation of the `op U`-component at the
   generator `ModuleCat.freeMk (𝟙 U)`.  This is the `ModuleCat k`-linear
   incarnation of the enriched Yoneda lemma for the objectwise-free presheaf,
   and fills (in `ModuleCat k`-flavour) the TODO of
   `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean` asking for the
   identification of `(F.cohomologyPresheaf 0).obj (op U)` with sections at a
   general `U` (Mathlib's `Sheaf.H.equiv₀` only treats a terminal object).

The Mayer-Vietoris degree-0 corner consumption: the maps of the LES slice
`HModule'_toBiprod`/`HModule'_fromBiprod` at degree 0 are (elementwise, via
`HModule'_toBiprod_apply` and `HModule'_fromBiprod_biprodIsoProd_inv_apply`)
exactly `(HModule'_cohomologyPresheaf k F 0).map g.op` for the four arrows `g`
of the square; `HModule'_zero_sectionsLinearEquiv_naturality_map` identifies
those with the restriction maps `(F.obj.map g.op).hom`, i.e. with
`sectionRestrict`/`sectionDiff` of `RiemannRoch/Adelic/Cokernel.lean` after
specialising `C := Opens X` and `g := homOfLE h`.

Everything is stated over a field `k` to match the instance paths of the
`HModule'` lane (`Carriers.lean`); the presheaf-level statements hold verbatim
over any commutative ring.

The repeated `set_option backward.isDefEq.respectTransparency false in` is the
established project remedy (cf. `MayerVietorisCore.lean`) for unification past
structure-literal projections of `yoneda`/`whiskeringRight`/`Functor.flip`.

See `blueprint/src/chapters/Cohomology_StructureSheafModuleK.tex`.
-/

set_option autoImplicit false

universe u v w t u₂ v₂

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

/-! ## Degree-zero `Ext` composition compatibilities (Mathlib gap-fills)

Mathlib's `Abelian.Ext.linearEquiv₀ : Ext X Y 0 ≃ₗ[R] (X ⟶ Y)` is inverse to
`Abelian.Ext.mk₀` (`mk₀_linearEquiv₀_apply`), but the compatibility of the
*forward* direction with `Ext`-composition against `mk₀` on either side is not
stated in Mathlib.  Both follow from `mk₀_comp_mk₀` and the injectivity of
`mk₀` in degree 0. -/

namespace CategoryTheory.Abelian.Ext

variable {R : Type t} [Ring R] {C : Type u₂} [Category.{v₂} C] [Abelian C]
  [Linear R C] [HasExt.{w} C]

/-- Degree-zero compatibility of `Abelian.Ext.linearEquiv₀` with precomposition:
under the identification `Ext X Y 0 ≃ₗ[R] (X ⟶ Y)`, precomposition with
`mk₀ f` becomes precomposition with `f`.  Blueprint: for `f : X' ⟶ X` and
`x ∈ Ext⁰(X, Y)`, one has `linearEquiv₀(mk₀(f) ∘ x) = f ≫ linearEquiv₀(x)`.
Proof: apply the injective `mk₀` and use `mk₀_comp_mk₀`. -/
lemma linearEquiv₀_mk₀_comp {X' X Y : C} (f : X' ⟶ X) (x : Ext X Y 0) :
    linearEquiv₀ (R := R) ((mk₀ f).comp x (zero_add 0)) =
      f ≫ linearEquiv₀ (R := R) x := by
  apply (mk₀_bijective X' Y).injective
  rw [mk₀_linearEquiv₀_apply, ← mk₀_comp_mk₀, mk₀_linearEquiv₀_apply]

/-- Degree-zero compatibility of `Abelian.Ext.linearEquiv₀` with postcomposition:
under the identification `Ext X Y 0 ≃ₗ[R] (X ⟶ Y)`, postcomposition with
`mk₀ g` becomes postcomposition with `g`.  Blueprint: for `g : Y ⟶ Y'` and
`x ∈ Ext⁰(X, Y)`, one has `linearEquiv₀(x ∘ mk₀(g)) = linearEquiv₀(x) ≫ g`.
Proof: apply the injective `mk₀` and use `mk₀_comp_mk₀`. -/
lemma linearEquiv₀_comp_mk₀ {X Y Y' : C} (x : Ext X Y 0) (g : Y ⟶ Y') :
    linearEquiv₀ (R := R) (x.comp (mk₀ g) (add_zero 0)) =
      linearEquiv₀ (R := R) x ≫ g := by
  apply (mk₀_bijective X Y').injective
  rw [mk₀_linearEquiv₀_apply, ← mk₀_comp_mk₀, mk₀_linearEquiv₀_apply]

end CategoryTheory.Abelian.Ext

/-! ## The underlying function of the iter-046 `Adjunction.homLinearEquiv`

The project gap-fill `CategoryTheory.Adjunction.homLinearEquiv`
(`StructureSheafModuleK/Presheaf.lean`) is a structure-literal extension of
Mathlib's `Adjunction.homAddEquiv`, whose underlying function is
`Adjunction.homEquiv`.  We record the two unfolding lemmas so that the
naturality lemmas `Adjunction.homEquiv_naturality_left/right` apply to it. -/

namespace CategoryTheory.Adjunction

variable {C₁ : Type u₂} {D₁ : Type v₂} [Category.{u} C₁] [Category.{v} D₁]
  [Preadditive C₁] [Preadditive D₁] {F : C₁ ⥤ D₁} {G : D₁ ⥤ C₁} (adj : F ⊣ G)
  (R : Type t) [Semiring R] [CategoryTheory.Linear R C₁] [CategoryTheory.Linear R D₁]

/-- The underlying function of the iter-046 linearised adjunction equivalence
`Adjunction.homLinearEquiv` is `Adjunction.homEquiv`.  Definitional. -/
lemma homLinearEquiv_apply [F.Additive] [G.Additive] [G.Linear R]
    (X : C₁) (Y : D₁) (f : F.obj X ⟶ Y) :
    adj.homLinearEquiv R X Y f = adj.homEquiv X Y f :=
  rfl

/-- The underlying function of the inverse of the iter-046 linearised adjunction
equivalence `Adjunction.homLinearEquiv` is the inverse of
`Adjunction.homEquiv`.  Definitional. -/
lemma homLinearEquiv_symm_apply [F.Additive] [G.Additive] [G.Linear R]
    (X : C₁) (Y : D₁) (g : X ⟶ G.obj Y) :
    (adj.homLinearEquiv R X Y).symm g = (adj.homEquiv X Y).symm g :=
  rfl

end CategoryTheory.Adjunction

/-! ## The free-Yoneda sections equivalence

For a presheaf of `k`-modules `M : Cᵒᵖ ⥤ ModuleCat k` and an object `U : C`,
the module of natural transformations from the objectwise-free presheaf
`P_U := (yoneda ⋙ (whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U`
(that is, `V ↦ k[(V ⟶ U)]`, the free `k`-module on the hom-sets into `U`) to
`M` is `k`-linearly identified with the sections `M.obj (op U)`, by evaluating
the `op U`-component at the generator `freeMk (𝟙 U)`.  This is the
`ModuleCat k`-enriched Yoneda lemma for objectwise-free presheaves, obtained by
composing the objectwise free–forget adjunction with the ordinary Yoneda
lemma; we construct the equivalence directly (evaluation forward, `freeDesc`
of the orbit of a section backward), which makes the evaluation formula
definitional. -/

namespace CategoryTheory

variable (k : Type u) [Field k] {C : Type v} [Category.{u, v} C]

set_option backward.isDefEq.respectTransparency false in
/-- Generator-level naturality: a natural transformation `ψ : P_U ⟶ M` out of
the objectwise-free presheaf `P_U = (V ↦ k[(V ⟶ U)])` is determined on the
basis vector `freeMk f`, `f : V.unop ⟶ U`, by the restriction along `f` of its
value on the universal generator `freeMk (𝟙 U)`.  Blueprint: `ψ_V([f]) =
M(f)(ψ_U([𝟙_U]))` — the free-presheaf incarnation of the Yoneda-lemma
computation.  Proof: apply the naturality square of `ψ` at `f.op` to
`freeMk (𝟙 U)` and simplify `f ≫ 𝟙 U = f`. -/
lemma freeYonedaSections_app_freeMk {M : Cᵒᵖ ⥤ ModuleCat.{u} k} {U : C}
    (ψ : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U ⟶ M)
    {V : Cᵒᵖ} (f : V.unop ⟶ U) :
    (ψ.app V).hom (ModuleCat.freeMk f) =
      (M.map f.op).hom ((ψ.app (Opposite.op U)).hom (ModuleCat.freeMk (𝟙 U))) := by
  have h := ConcreteCategory.congr_hom (ψ.naturality f.op) (ModuleCat.freeMk (𝟙 U))
  simp only [CategoryTheory.comp_apply] at h
  have h2 : (((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj
        (ModuleCat.free k)).obj U).map f.op) (ModuleCat.freeMk (𝟙 U)) =
      ModuleCat.freeMk f := by
    change ((ModuleCat.free k).map ((yoneda.obj U).map f.op)) (ModuleCat.freeMk (𝟙 U)) =
      ModuleCat.freeMk f
    rw [ModuleCat.free_map_apply]
    simp
  rw [h2] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The underlying bijection of the free-Yoneda sections equivalence: the
composite of the objectwise free ⊣ forget adjunction (whiskered over `Cᵒᵖ`,
`Adjunction.whiskerRight`) with the set-valued Yoneda lemma (`yonedaEquiv`).
The `k`-linear upgrade is `freeYonedaSectionsLinearEquiv` below; the
evaluation formula is `freeYonedaSectionsEquiv_apply`. -/
noncomputable def freeYonedaSectionsEquiv (M : Cᵒᵖ ⥤ ModuleCat.{u} k) (U : C) :
    ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U ⟶ M) ≃
      M.obj (Opposite.op U) :=
  ((Adjunction.whiskerRight Cᵒᵖ (ModuleCat.adj k)).homEquiv (yoneda.obj U) M).trans
    yonedaEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation formula for `freeYonedaSectionsEquiv`: the composite of the
whiskered free ⊣ forget adjunction with the Yoneda lemma evaluates a natural
transformation `ψ : P_U ⟶ M` at the universal generator, `ψ ↦ ψ_U([𝟙_U])`. -/
lemma freeYonedaSectionsEquiv_apply (M : Cᵒᵖ ⥤ ModuleCat.{u} k) (U : C)
    (ψ : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U ⟶ M) :
    freeYonedaSectionsEquiv k M U ψ =
      (ψ.app (Opposite.op U)).hom (ModuleCat.freeMk (𝟙 U)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The free-Yoneda sections equivalence.**  For a presheaf of `k`-modules
`M : Cᵒᵖ ⥤ ModuleCat k` and `U : C`, the `k`-module of morphisms from the
objectwise-free presheaf `P_U = (yoneda ⋙ (whiskeringRight _ _ _).obj
(ModuleCat.free k)).obj U` (i.e. `V ↦ k[(V ⟶ U)]`) to `M` is `k`-linearly
equivalent to the sections `M.obj (op U)`, via `ψ ↦ ψ_U([𝟙_U])`.

Blueprint: this is the enriched Yoneda lemma
`Hom(k[Hom(-, U)], M) ≅ M(U)` for `ModuleCat k`-valued presheaves, the
composite of the objectwise free ⊣ forget adjunction with the set-valued
Yoneda lemma (`freeYonedaSectionsEquiv`).  Linearity of evaluation is direct:
natural-transformation addition and scalar action are componentwise, and
`ModuleCat` morphism evaluation is additive and `k`-linear in the morphism.

Fills, in `ModuleCat k`-flavour, the general-`U` H⁰-identification listed as a
TODO in `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`. -/
noncomputable def freeYonedaSectionsLinearEquiv (M : Cᵒᵖ ⥤ ModuleCat.{u} k) (U : C) :
    ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U ⟶ M) ≃ₗ[k]
      M.obj (Opposite.op U) where
  toFun ψ := (ψ.app (Opposite.op U)).hom (ModuleCat.freeMk (𝟙 U))
  map_add' ψ φ := by simp [NatTrans.app_add]
  map_smul' r ψ := by simp [NatTrans.app_smul]
  invFun := (freeYonedaSectionsEquiv k M U).symm
  left_inv ψ :=
    (freeYonedaSectionsEquiv k M U).symm_apply_eq.mpr
      (freeYonedaSectionsEquiv_apply k M U ψ).symm
  right_inv m :=
    (freeYonedaSectionsEquiv_apply k M U
      ((freeYonedaSectionsEquiv k M U).symm m)).symm.trans
      ((freeYonedaSectionsEquiv k M U).apply_symm_apply m)

/-- Evaluation formula for the free-Yoneda sections equivalence: definitional. -/
@[simp]
lemma freeYonedaSectionsLinearEquiv_apply (M : Cᵒᵖ ⥤ ModuleCat.{u} k) (U : C)
    (ψ : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U ⟶ M) :
    freeYonedaSectionsLinearEquiv k M U ψ =
      (ψ.app (Opposite.op U)).hom (ModuleCat.freeMk (𝟙 U)) :=
  rfl

/-- The underlying function of the free-Yoneda sections equivalence agrees with
the adjunction-chain bijection `freeYonedaSectionsEquiv`. -/
lemma freeYonedaSectionsLinearEquiv_coe (M : Cᵒᵖ ⥤ ModuleCat.{u} k) (U : C)
    (ψ : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U ⟶ M) :
    freeYonedaSectionsLinearEquiv k M U ψ = freeYonedaSectionsEquiv k M U ψ :=
  (freeYonedaSectionsEquiv_apply k M U ψ).symm

/-- Inverse formula for the free-Yoneda sections equivalence: definitional. -/
@[simp]
lemma freeYonedaSectionsLinearEquiv_symm_apply (M : Cᵒᵖ ⥤ ModuleCat.{u} k) (U : C)
    (m : M.obj (Opposite.op U)) :
    (freeYonedaSectionsLinearEquiv k M U).symm m =
      (freeYonedaSectionsEquiv k M U).symm m :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the free-Yoneda sections bijection in the object `U`:
precomposition with the free-Yoneda image of `g : V ⟶ U` corresponds to the
presheaf restriction `M.map g.op`.  Blueprint: the square
`Hom(k[Hom(-,U)], M) → Hom(k[Hom(-,V)], M)` versus `M(U) → M(V)` commutes.
Proof: left-naturality of the adjunction plus `yonedaEquiv_naturality`. -/
lemma freeYonedaSectionsEquiv_naturality (M : Cᵒᵖ ⥤ ModuleCat.{u} k)
    {U V : C} (g : V ⟶ U)
    (ψ : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U ⟶ M) :
    freeYonedaSectionsEquiv k M V
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).map g ≫ ψ) =
      (M.map g.op).hom (freeYonedaSectionsEquiv k M U ψ) := by
  have s : (Adjunction.whiskerRight Cᵒᵖ (ModuleCat.adj k)).homEquiv (yoneda.obj V) M
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).map g ≫ ψ) =
      yoneda.map g ≫
        (Adjunction.whiskerRight Cᵒᵖ (ModuleCat.adj k)).homEquiv (yoneda.obj U) M ψ :=
    (Adjunction.whiskerRight Cᵒᵖ (ModuleCat.adj k)).homEquiv_naturality_left
      (yoneda.map g) ψ
  exact (congrArg yonedaEquiv s).trans (yonedaEquiv_naturality _ g).symm

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the free-Yoneda sections equivalence in the object `U`
(`k`-linear form; the shape consumed by the H⁰-sections bridge). -/
lemma freeYonedaSectionsLinearEquiv_naturality (M : Cᵒᵖ ⥤ ModuleCat.{u} k)
    {U V : C} (g : V ⟶ U)
    (ψ : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U ⟶ M) :
    freeYonedaSectionsLinearEquiv k M V
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).map g ≫ ψ) =
      (M.map g.op).hom (freeYonedaSectionsLinearEquiv k M U ψ) := by
  rw [freeYonedaSectionsLinearEquiv_coe, freeYonedaSectionsLinearEquiv_coe]
  exact freeYonedaSectionsEquiv_naturality k M g ψ

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the free-Yoneda sections bijection in the presheaf `M`:
postcomposition with `α : M ⟶ N` corresponds to the component `α.app (op U)` on
sections.  Proof: right-naturality of the adjunction plus `yonedaEquiv_comp`. -/
lemma freeYonedaSectionsEquiv_postcomp {M N : Cᵒᵖ ⥤ ModuleCat.{u} k} (α : M ⟶ N)
    {U : C}
    (ψ : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U ⟶ M) :
    freeYonedaSectionsEquiv k N U (ψ ≫ α) =
      (α.app (Opposite.op U)).hom (freeYonedaSectionsEquiv k M U ψ) := by
  have s : (Adjunction.whiskerRight Cᵒᵖ (ModuleCat.adj k)).homEquiv (yoneda.obj U) N
        (ψ ≫ α) =
      (Adjunction.whiskerRight Cᵒᵖ (ModuleCat.adj k)).homEquiv (yoneda.obj U) M ψ ≫
        ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} k) (Type u)).obj
          (forget (ModuleCat.{u} k))).map α :=
    (Adjunction.whiskerRight Cᵒᵖ (ModuleCat.adj k)).homEquiv_naturality_right ψ α
  exact (congrArg yonedaEquiv s).trans (yonedaEquiv_comp _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the free-Yoneda sections equivalence in the presheaf `M`
(`k`-linear form; the shape consumed by the H⁰-sections bridge). -/
lemma freeYonedaSectionsLinearEquiv_postcomp {M N : Cᵒᵖ ⥤ ModuleCat.{u} k} (α : M ⟶ N)
    {U : C}
    (ψ : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U ⟶ M) :
    freeYonedaSectionsLinearEquiv k N U (ψ ≫ α) =
      (α.app (Opposite.op U)).hom (freeYonedaSectionsLinearEquiv k M U ψ) := by
  rw [freeYonedaSectionsLinearEquiv_coe, freeYonedaSectionsLinearEquiv_coe]
  exact freeYonedaSectionsEquiv_postcomp k α ψ

end CategoryTheory

/-! ## The H⁰-sections bridge for `HModule'` -/

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
  {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
  [HasExt (Sheaf J (ModuleCat.{u} k))]

set_option backward.isDefEq.respectTransparency false in
/-- **The H⁰-sections bridge.**  For a sheaf of `k`-modules `F` on a site
`(C, J)` and an object `U : C`, the degree-zero open-evaluation cohomology
`HModule' k F 0 U = Ext⁰((presheafToSheaf J _).obj P_U, F)` is `k`-linearly
equivalent to the module of sections `Γ(U, F) = F.obj.obj (op U)`.

Blueprint: `H⁰(U, F) ≅ Γ(U, F)`, the degree-zero part of the derived-functor
description of sheaf cohomology.  The composite chain is
`Ext⁰ ≃ Hom_{Sheaf}((P_U)^♯, F)` (`HModule'_zero_linearEquiv`,
`Abelian.Ext.linearEquiv₀`) `≃ Hom_{Presheaf}(P_U, F.obj)` (linearised
sheafification adjunction, `Adjunction.homLinearEquiv`)
`≃ F.obj.obj (op U)` (free-Yoneda sections equivalence,
`freeYonedaSectionsLinearEquiv`).

This is the degree-0 corner identification the Mayer-Vietoris LES slice
consumes (via the naturality companions below): it converts the H⁰ entries of
`HModule'_sequence` at `(n₀, n₁) = (0, 1)` into the concrete section modules
appearing in `AffineCoverMVSquare.sectionDiff`/`H1Cok`
(`RiemannRoch/Adelic/Cokernel.lean`).  Being `Module.finrank`-compatible
(a genuine `≃ₗ[k]`), it also transports `Module.Finite` statements.

**Statement audit (genus-lane wave 1', 2026-07-09): TRUE at stated
generality.**  Arbitrary site `(C, J)` at `Category.{u, v}`, arbitrary sheaf
of `k`-modules `F`, arbitrary `U : C`; no curve/scheme hypotheses.  The
sheaf-ness of `F` is exactly what the sheafification-adjunction hop uses; the
other two hops are unconditional.  The `[HasExt]` binder resolves at
`HasExt.{u}` through the `Type u` ascription of the `HModule'` abbrev
(supplied by `IsGrothendieckAbelian.hasExt` on the scheme site), matching
`Carriers.lean`; the whole chain lives at `Type u` with no `ULift`. -/
noncomputable def HModule'_zero_sectionsLinearEquiv
    (F : Sheaf J (ModuleCat.{u} k)) (U : C) :
    HModule' k F 0 U ≃ₗ[k] F.obj.obj (Opposite.op U) :=
  (HModule'_zero_linearEquiv k F U).trans
    (((sheafificationAdjunction J (ModuleCat.{u} k)).homLinearEquiv k
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U) F).trans
      (freeYonedaSectionsLinearEquiv k F.obj U))

set_option backward.isDefEq.respectTransparency false in
/-- Elementwise unfolding of the contravariant functoriality of the
`ModuleCat k`-flavoured cohomology presheaf: for `g : V ⟶ U` in `C` and
`x : HModule' k F n U`, the map `(HModule'_cohomologyPresheaf k F n).map g.op`
(the restriction map of the Mayer-Vietoris LES building blocks
`HModule'_toBiprod`/`HModule'_fromBiprod`) is `Ext`-precomposition with
`mk₀` of the sheafified free-Yoneda image of `g`.  Definitional, by
construction of `HModule'_cohomologyPresheafFunctor` from
`Abelian.extFunctor`. -/
lemma HModule'_cohomologyPresheaf_map_apply
    (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) {U V : C} (g : V ⟶ U)
    (x : HModule' k F n U) :
    (HModule'_cohomologyPresheaf k F n).map g.op x =
      (Abelian.Ext.mk₀ ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k) ⋙
        presheafToSheaf J (ModuleCat.{u} k)).map g)).comp x (zero_add n) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the H⁰-sections bridge in the object `U` (raw `Ext` form):
for `g : V ⟶ U`, precomposition with `mk₀` of the sheafified free-Yoneda image
of `g` corresponds, under `HModule'_zero_sectionsLinearEquiv`, to the presheaf
restriction `(F.obj.map g.op).hom`.

Blueprint: the square `H⁰(U, F) → H⁰(V, F)` versus `Γ(U, F) → Γ(V, F)`
commutes.  Proof: chain the degree-zero `Ext` compatibility
(`linearEquiv₀_mk₀_comp`), the left-naturality of the sheafification
adjunction (`homEquiv_naturality_left`), and the `U`-naturality of the
free-Yoneda sections equivalence.

Consumers should usually use the functorial form
`HModule'_zero_sectionsLinearEquiv_naturality_map`. -/
lemma HModule'_zero_sectionsLinearEquiv_naturality
    (F : Sheaf J (ModuleCat.{u} k)) {U V : C} (g : V ⟶ U) (x : HModule' k F 0 U) :
    HModule'_zero_sectionsLinearEquiv k F V
        ((Abelian.Ext.mk₀ ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k) ⋙
          presheafToSheaf J (ModuleCat.{u} k)).map g)).comp x (zero_add 0)) =
      (F.obj.map g.op).hom (HModule'_zero_sectionsLinearEquiv k F U x) := by
  simp only [HModule'_zero_sectionsLinearEquiv, LinearEquiv.trans_apply,
    HModule'_zero_linearEquiv]
  rw [Abelian.Ext.linearEquiv₀_mk₀_comp]
  simp only [Adjunction.homLinearEquiv_apply]
  have e : (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k) ⋙
      presheafToSheaf J (ModuleCat.{u} k)).map g =
      (presheafToSheaf J (ModuleCat.{u} k)).map
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).map g) :=
    rfl
  rw [e, Adjunction.homEquiv_naturality_left]
  exact freeYonedaSectionsLinearEquiv_naturality k F.obj g _

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the H⁰-sections bridge in the object `U` (consumable
form).**  For `g : V ⟶ U` in `C`, the restriction map
`(HModule'_cohomologyPresheaf k F 0).map g.op` — the exact shape of the four
structure maps of the degree-0 corner of the Mayer-Vietoris LES slice, via
`HModule'_toBiprod_apply` and `HModule'_fromBiprod_biprodIsoProd_inv_apply` —
corresponds, under `HModule'_zero_sectionsLinearEquiv`, to the presheaf
restriction `(F.obj.map g.op).hom`.

For `C := Opens X` and `g := homOfLE h`, the right-hand side is definitionally
`sectionRestrict F h` (`RiemannRoch/Adelic/Cokernel.lean`), so this lemma
identifies the degree-0 MV corner maps with `sectionDiff`'s constituents.

Blueprint: the diagram `H⁰(U, F) → H⁰(V, F)` versus restriction
`Γ(U, F) → Γ(V, F)` commutes.

**Statement audit: consumable shape CONFIRMED against the MV degree-0
corners.**  `HModule'_toBiprod`/`HModule'_fromBiprod`
(`MayerVietorisCore.lean`) are `biprod.lift`/`biprod.desc` of literally
`(HModule'_cohomologyPresheaf k F n).map S.f₂₄.op` (resp. `f₃₄`, `f₁₂`,
`−f₁₃`), and their elementwise formulas `HModule'_toBiprod_apply` /
`HModule'_fromBiprod_biprodIsoProd_inv_apply` expose exactly
`(….map g.op) x` terms — the LHS here.  The RHS is `sectionRestrict F h`
definitionally when `C := Opens X`, `g := homOfLE h`. -/
lemma HModule'_zero_sectionsLinearEquiv_naturality_map
    (F : Sheaf J (ModuleCat.{u} k)) {U V : C} (g : V ⟶ U) (x : HModule' k F 0 U) :
    HModule'_zero_sectionsLinearEquiv k F V
        ((HModule'_cohomologyPresheaf k F 0).map g.op x) =
      (F.obj.map g.op).hom (HModule'_zero_sectionsLinearEquiv k F U x) := by
  rw [HModule'_cohomologyPresheaf_map_apply]
  exact HModule'_zero_sectionsLinearEquiv_naturality k F g x

set_option backward.isDefEq.respectTransparency false in
/-- Inverse-direction naturality of the H⁰-sections bridge in the object `U`:
the inverse bridge intertwines the presheaf restriction with the
cohomology-presheaf restriction.  Formal consequence of
`HModule'_zero_sectionsLinearEquiv_naturality_map` by injectivity. -/
lemma HModule'_zero_sectionsLinearEquiv_symm_naturality_map
    (F : Sheaf J (ModuleCat.{u} k)) {U V : C} (g : V ⟶ U)
    (s : F.obj.obj (Opposite.op U)) :
    (HModule'_cohomologyPresheaf k F 0).map g.op
        ((HModule'_zero_sectionsLinearEquiv k F U).symm s) =
      (HModule'_zero_sectionsLinearEquiv k F V).symm ((F.obj.map g.op).hom s) := by
  apply (HModule'_zero_sectionsLinearEquiv k F V).injective
  rw [HModule'_zero_sectionsLinearEquiv_naturality_map, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the H⁰-sections bridge in the sheaf (consumable form for
the dimension-shift LES).**  For a morphism of sheaves of `k`-modules
`φ : F ⟶ G` and `U : C`, postcomposition `x ↦ x.comp (mk₀ φ)` — the exact
elementwise shape of the maps in the second-variable `Ext` long exact sequence
(`Abelian.Ext.covariant_sequence_exact₁/₂/₃`) — corresponds, under
`HModule'_zero_sectionsLinearEquiv`, to the component
`(φ.hom.app (op U)).hom : Γ(U, F) →ₗ Γ(U, G)`.

Blueprint: the square `H⁰(U, F) → H⁰(U, G)` versus `Γ(U, F) → Γ(U, G)`
commutes.  This identifies, e.g. for an injective resolution step
`0 → F → I → Q → 0`, the H⁰ part of the dimension-shift sequence with the
actual section-level maps `Γ(U, I) → Γ(U, Q)`.

Proof: chain the degree-zero `Ext` compatibility (`linearEquiv₀_comp_mk₀`),
the right-naturality of the sheafification adjunction
(`homEquiv_naturality_right`), and the `M`-naturality of the free-Yoneda
sections equivalence.

**Statement audit: consumable shape CONFIRMED against the second-variable
`Ext` LES.**  Mathlib's element-level forms
`Abelian.Ext.covariant_sequence_exact₁/₂/₃`
(`Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean`) are
phrased with literally `x.comp (mk₀ S.f) (add_zero n)` — the LHS here at
`n = 0` — so this lemma converts the H⁰ rungs of the dimension-shift LES
(e.g. `Hom(P_U, I) → Hom(P_U, Q)` for `0 → F → I → Q → 0`) into the honest
section maps `Γ(U, I) → Γ(U, Q)` with no reshaping. -/
lemma HModule'_zero_sectionsLinearEquiv_naturality_hom
    {F G : Sheaf J (ModuleCat.{u} k)} (φ : F ⟶ G) (U : C) (x : HModule' k F 0 U) :
    HModule'_zero_sectionsLinearEquiv k G U (x.comp (Abelian.Ext.mk₀ φ) (add_zero 0)) =
      (φ.hom.app (Opposite.op U)).hom (HModule'_zero_sectionsLinearEquiv k F U x) := by
  simp only [HModule'_zero_sectionsLinearEquiv, LinearEquiv.trans_apply,
    HModule'_zero_linearEquiv]
  rw [Abelian.Ext.linearEquiv₀_comp_mk₀]
  simp only [Adjunction.homLinearEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  exact freeYonedaSectionsLinearEquiv_postcomp k ((sheafToPresheaf J _).map φ) _

set_option backward.isDefEq.respectTransparency false in
/-- Inverse-direction naturality of the H⁰-sections bridge in the sheaf:
the inverse bridge intertwines the section-level component of `φ` with
`Ext`-postcomposition by `mk₀ φ`.  Formal consequence of
`HModule'_zero_sectionsLinearEquiv_naturality_hom` by injectivity. -/
lemma HModule'_zero_sectionsLinearEquiv_symm_naturality_hom
    {F G : Sheaf J (ModuleCat.{u} k)} (φ : F ⟶ G) (U : C)
    (s : F.obj.obj (Opposite.op U)) :
    ((HModule'_zero_sectionsLinearEquiv k F U).symm s).comp (Abelian.Ext.mk₀ φ)
        (add_zero 0) =
      (HModule'_zero_sectionsLinearEquiv k G U).symm
        ((φ.hom.app (Opposite.op U)).hom s) := by
  apply (HModule'_zero_sectionsLinearEquiv k G U).injective
  rw [HModule'_zero_sectionsLinearEquiv_naturality_hom, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme
