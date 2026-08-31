/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.ModuleKSheaf

/-!
# Cohomology of an object of the site with `ModuleCat k` coefficients

For a sheaf of `R`-modules `F` on a small site `(C, J)` and an object `U : C`, this file
defines the cohomology `Sheaf.HModule' F U n` of `U` with coefficients in `F`: the
`Ext`-group from the *free sheaf of `R`-modules on `U`* (the sheafification of the
composite `yoneda.obj U ⋙ ModuleCat.free R`) to `F`. This mirrors mathlib's
`CategoryTheory.Sheaf.H'` (which is `AddCommGrpCat`-valued) at `ModuleCat R`, so that the
Mayer–Vietoris (0,1)-slice can be run `R`-linearly
(`AlgebraicJacobian.Cohomology.MayerVietoris`).

## Main definitions

* `CategoryTheory.Sheaf.freeModuleSheaf J R U` — the free sheaf of `R`-modules on `U`.
* `CategoryTheory.Sheaf.freeModuleSheafMap J R i` — functoriality in `U`.
* `CategoryTheory.Sheaf.freeModuleSheafHomEquiv` — the `R`-linear "universal property of
  sections": `(freeModuleSheaf J R U ⟶ F) ≃ₗ[R] F(U)`, with naturality in `F`
  (`freeModuleSheafHomEquiv_comp`) and in `U` (`freeModuleSheafHomEquiv_map`).
* `CategoryTheory.Sheaf.HModule' F U n` — `Ext^n(R[U], F)`, a `Type u` with a `Module R`
  structure.
* `CategoryTheory.Sheaf.HModule'.linearEquiv₀` — `H'⁰(U, F) ≃ₗ[R] F(U)`.
* `CategoryTheory.Sheaf.freeModuleSheafIsoConstModuleSheaf` — for a terminal object `T`,
  the canonical isomorphism `R[T] ≅ R_X` with the constant sheaf, whence
  `Sheaf.HModule.linearEquivHModule' : HModule F n ≃ₗ[R] HModule' F T n`: cohomology of
  the site (`Sheaf.HModule`) is cohomology of a terminal object.

## Implementation notes

Morphisms out of `freeModuleSheaf J R U` are computed from the sheafification universal
property (`sheafifyLift`) against the explicit presheaf morphism `freeModuleSheafDesc`
determined by a section `s ∈ F(U)`; no adjunction unfolding is needed. All elementwise
computations are routed through `ModuleCat.free_hom_ext` after a `change` to the
`ModuleCat.Hom.hom` spelling (the concrete-category coercion produced by `free_hom_ext`
is only defeq to it, and `rw` chokes on the mismatch otherwise). The whole file is
single-universe (`Type u` site, `ModuleCat.{u} R` coefficients), matching
`AlgebraicJacobian.Cohomology.ModuleKSheaf`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace ModuleCat

/-- The free module functor preserves monomorphisms (mapping along an injection of index
types is injective on finitely supported functions). Mirrors the mathlib instance for
`AddCommGrpCat.free`. -/
instance free_preservesMonomorphisms (R : Type u) [Ring R] :
    (ModuleCat.free R).PreservesMonomorphisms where
  preserves {X Y} f hf := by
    rw [ModuleCat.mono_iff_injective]
    exact Finsupp.mapDomain_injective ((CategoryTheory.mono_iff_injective f).mp hf)

/-- The free module functor is a left adjoint (of the forgetful functor). Mirrors the
mathlib instance for `AddCommGrpCat.free`. -/
instance free_isLeftAdjoint (R : Type u) [Ring R] : (ModuleCat.free R).IsLeftAdjoint :=
  (ModuleCat.adj R).isLeftAdjoint

end ModuleCat

namespace CategoryTheory

namespace Abelian.Ext

variable {C : Type u} [Category.{u} C] [Abelian C] [HasExt.{u} C]
variable (R : Type u) [CommRing R] [Linear R C]

/-- Precomposition with `mk₀ f` corresponds to composition with `f` under the degree-zero
identification `Ext X Y 0 ≃ₗ[R] (X ⟶ Y)`. -/
lemma linearEquiv₀_mk₀_comp {X Y Z : C} (f : X ⟶ Y) (x : Ext Y Z 0) :
    linearEquiv₀ (R := R) ((mk₀ f).comp x (zero_add 0)) = f ≫ linearEquiv₀ (R := R) x := by
  apply (mk₀_bijective X Z).injective
  rw [mk₀_linearEquiv₀_apply, ← mk₀_comp_mk₀, mk₀_linearEquiv₀_apply]

end Abelian.Ext

namespace Sheaf

variable {C : Type u} [SmallCategory C]
variable (J : GrothendieckTopology C) (R : Type u) [CommRing R]
  [HasSheafify J (ModuleCat.{u} R)]

/-- The free sheaf of `R`-modules on an object `U` of the site: the sheafification of the
composite of the representable presheaf at `U` with the free module functor. Morphisms
out of it compute sections over `U` (`Sheaf.freeModuleSheafHomEquiv`); it is the
`ModuleCat R` analogue of the free abelian sheaves in mathlib's
`CategoryTheory.Sites.SheafCohomology.Basic`. -/
noncomputable def freeModuleSheaf (U : C) : Sheaf J (ModuleCat.{u} R) :=
  (presheafToSheaf J _).obj (yoneda.obj U ⋙ ModuleCat.free R)

/-- Functoriality of the free sheaf of modules in the object of the site. -/
noncomputable def freeModuleSheafMap {U V : C} (i : U ⟶ V) :
    freeModuleSheaf J R U ⟶ freeModuleSheaf J R V :=
  (presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map i) (ModuleCat.free R))

/-- The tautological generator of the free sheaf of modules on `U`: the image of the
basis vector at `𝟙 U` under sheafification. -/
noncomputable def freeModuleSheafGen (U : C) : (freeModuleSheaf J R U).obj.obj (op U) :=
  ((toSheafify J (yoneda.obj U ⋙ ModuleCat.free R)).app (op U)).hom
    (ModuleCat.freeMk (𝟙 U))

variable {J R}

section HomEquiv

variable {U V : C} {F G : Sheaf J (ModuleCat.{u} R)}

/-- Elementwise naturality for morphisms of `ModuleCat`-valued presheaves. -/
private lemma app_naturality {P Q : Cᵒᵖ ⥤ ModuleCat.{u} R} (η : P ⟶ Q) {W W' : Cᵒᵖ}
    (i : W ⟶ W') (x : P.obj W) :
    (η.app W').hom ((P.map i).hom x) = (Q.map i).hom ((η.app W).hom x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (η.naturality i)) x

variable (F) in
/-- The component at `V` of the presheaf morphism from the free presheaf of modules at
`U` classified by a section `s ∈ F(U)`: it sends the basis vector at `g : V.unop ⟶ U` to
the restriction of `s` along `g`. -/
noncomputable def freeModuleSheafDescApp (s : F.obj.obj (op U)) (V : Cᵒᵖ) :
    (ModuleCat.free R).obj ((yoneda.obj U).obj V) ⟶ F.obj.obj V :=
  ModuleCat.freeDesc (↾fun (g : V.unop ⟶ U) ↦ (F.obj.map g.op).hom s)

omit [HasSheafify J (ModuleCat.{u} R)] in
lemma freeModuleSheafDescApp_freeMk (s : F.obj.obj (op U)) {V : Cᵒᵖ} (g : V.unop ⟶ U) :
    (freeModuleSheafDescApp F s V).hom (ModuleCat.freeMk g) = (F.obj.map g.op).hom s := by
  simp [freeModuleSheafDescApp]

variable (F) in
/-- The presheaf morphism from the free presheaf of modules at `U` classified by a
section `s ∈ F(U)`: on `V`, it sends the basis vector at `g : V ⟶ U` to the restriction
of `s` along `g`. -/
noncomputable def freeModuleSheafDesc (s : F.obj.obj (op U)) :
    (yoneda.obj U ⋙ ModuleCat.free R) ⟶ F.obj where
  app V := freeModuleSheafDescApp F s V
  naturality {V W} h := ModuleCat.free_hom_ext fun (g : V.unop ⟶ U) ↦ by
    change ((yoneda.obj U ⋙ ModuleCat.free R).map h ≫ freeModuleSheafDescApp F s W).hom
        (ModuleCat.freeMk g) =
      (freeModuleSheafDescApp F s V ≫ F.obj.map h).hom (ModuleCat.freeMk g)
    have h1 : ((yoneda.obj U ⋙ ModuleCat.free R).map h ≫ freeModuleSheafDescApp F s W).hom
        (ModuleCat.freeMk g) =
        (freeModuleSheafDescApp F s W).hom (ModuleCat.freeMk (h.unop ≫ g)) := by
      rw [ModuleCat.hom_comp, LinearMap.comp_apply]
      congr 1
      exact ModuleCat.free_map_apply _ g
    have h2 : (freeModuleSheafDescApp F s V ≫ F.obj.map h).hom (ModuleCat.freeMk g) =
        (F.obj.map h).hom ((F.obj.map g.op).hom s) := by
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, freeModuleSheafDescApp_freeMk]
    rw [h1, h2, freeModuleSheafDescApp_freeMk]
    rw [show (h.unop ≫ g).op = g.op ≫ h from rfl, F.obj.map_comp]
    rfl

/-- Restriction of the tautological generator along `g : V ⟶ U` is the image of the
basis vector at `g` under sheafification. -/
lemma freeModuleSheaf_map_gen {V : C} (g : V ⟶ U) :
    ((freeModuleSheaf J R U).obj.map g.op).hom (freeModuleSheafGen J R U) =
      ((toSheafify J (yoneda.obj U ⋙ ModuleCat.free R)).app (op V)).hom
        (ModuleCat.freeMk g) := by
  have hmap : (((yoneda.obj U ⋙ ModuleCat.free R)).map g.op).hom
      (ModuleCat.freeMk (𝟙 U)) = ModuleCat.freeMk g := by
    change ((ModuleCat.free R).map ((yoneda.obj U).map g.op)).hom
      (ModuleCat.freeMk (𝟙 U)) = ModuleCat.freeMk g
    have h2 := ModuleCat.free_map_apply (R := R) ((yoneda.obj U).map g.op) (𝟙 U)
    rw [show (yoneda.obj U).map g.op (𝟙 U) = g by simp] at h2
    exact h2
  have hnat := app_naturality (toSheafify J (yoneda.obj U ⋙ ModuleCat.free R))
    (g.op : op U ⟶ op V) (ModuleCat.freeMk (𝟙 U))
  rw [hmap] at hnat
  exact hnat.symm

variable (F) in
/-- **Morphisms out of the free sheaf of modules compute sections**: the `R`-linear
equivalence `(R[U] ⟶ F) ≃ₗ[R] F(U)`, `φ ↦ φ(freeModuleSheafGen)`. -/
noncomputable def freeModuleSheafHomEquiv :
    (freeModuleSheaf J R U ⟶ F) ≃ₗ[R] F.obj.obj (op U) where
  toFun φ := (φ.hom.app (op U)).hom (freeModuleSheafGen J R U)
  map_add' φ ψ := rfl
  map_smul' r φ := rfl
  invFun s := ⟨sheafifyLift J (freeModuleSheafDesc F s) F.property⟩
  left_inv φ := by
    apply Sheaf.hom_ext
    refine (sheafifyLift_unique J _ F.property _ ?_).symm
    apply NatTrans.ext
    funext W
    obtain ⟨V⟩ := W
    refine ModuleCat.free_hom_ext fun (g : V ⟶ U) ↦ ?_
    change ((toSheafify J (yoneda.obj U ⋙ ModuleCat.free R)).app (op V) ≫
        φ.hom.app (op V)).hom (ModuleCat.freeMk g) =
      (freeModuleSheafDescApp F ((φ.hom.app (op U)).hom (freeModuleSheafGen J R U))
        (op V)).hom (ModuleCat.freeMk g)
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ← freeModuleSheaf_map_gen g,
      freeModuleSheafDescApp_freeMk]
    exact app_naturality φ.hom g.op (freeModuleSheafGen J R U)
  right_inv s := by
    have h := congrArg
      (fun (α : (yoneda.obj U ⋙ ModuleCat.free R) ⟶ F.obj) ↦
        (α.app (op U)).hom (ModuleCat.freeMk (𝟙 U)))
      (toSheafify_sheafifyLift J (freeModuleSheafDesc F s) F.property)
    dsimp at h
    have h3 := freeModuleSheafDescApp_freeMk (F := F) (V := op U) s (𝟙 U)
    have h2 : (F.obj.map ((𝟙 U).op : op U ⟶ op U)).hom s = s := by
      rw [show ((𝟙 U).op : op U ⟶ op U) = 𝟙 (op U) from rfl, F.obj.map_id]
      rfl
    exact (h.trans h3).trans h2

lemma freeModuleSheafHomEquiv_apply (φ : freeModuleSheaf J R U ⟶ F) :
    freeModuleSheafHomEquiv F φ = (φ.hom.app (op U)).hom (freeModuleSheafGen J R U) :=
  rfl

/-- Naturality of `Sheaf.freeModuleSheafHomEquiv` in the sheaf. -/
lemma freeModuleSheafHomEquiv_comp (φ : freeModuleSheaf J R U ⟶ F) (f : F ⟶ G) :
    freeModuleSheafHomEquiv G (φ ≫ f) =
      (f.hom.app (op U)).hom (freeModuleSheafHomEquiv F φ) :=
  rfl

/-- The generator of the free sheaf of modules maps to the basis vector at `i` under the
functoriality map `freeModuleSheafMap J R i`. -/
lemma freeModuleSheafMap_gen (i : U ⟶ V) :
    ((freeModuleSheafMap J R i).hom.app (op U)).hom (freeModuleSheafGen J R U) =
      ((toSheafify J (yoneda.obj V ⋙ ModuleCat.free R)).app (op U)).hom
        (ModuleCat.freeMk i) := by
  have hnat := congrArg
    (fun (α : (yoneda.obj U ⋙ ModuleCat.free R) ⟶
        sheafify J (yoneda.obj V ⋙ ModuleCat.free R)) ↦
      (α.app (op U)).hom (ModuleCat.freeMk (𝟙 U)))
    (toSheafify_naturality J (Functor.whiskerRight (yoneda.map i) (ModuleCat.free R)))
  dsimp at hnat
  have hFm : ((Functor.whiskerRight (yoneda.map i) (ModuleCat.free R)).app (op U)).hom
      (ModuleCat.freeMk (𝟙 U)) = ModuleCat.freeMk i := by
    change ((ModuleCat.free R).map ((yoneda.map i).app (op U))).hom
      (ModuleCat.freeMk (𝟙 U)) = ModuleCat.freeMk i
    have h2 := ModuleCat.free_map_apply (R := R) ((yoneda.map i).app (op U)) (𝟙 U)
    rw [show (yoneda.map i).app (op U) (𝟙 U) = i by simp] at h2
    exact h2
  rw [hFm] at hnat
  exact hnat.symm

/-- Naturality of `Sheaf.freeModuleSheafHomEquiv` in the object of the site:
precomposition with `freeModuleSheafMap J R i` corresponds to restriction of sections
along `i`. -/
lemma freeModuleSheafHomEquiv_map (i : U ⟶ V) (φ : freeModuleSheaf J R V ⟶ F) :
    freeModuleSheafHomEquiv F (freeModuleSheafMap J R i ≫ φ) =
      (F.obj.map i.op).hom (freeModuleSheafHomEquiv F φ) := by
  rw [freeModuleSheafHomEquiv_apply, freeModuleSheafHomEquiv_apply]
  have hcomp : ((freeModuleSheafMap J R i ≫ φ).hom.app (op U)).hom
      (freeModuleSheafGen J R U) =
      (φ.hom.app (op U)).hom (((freeModuleSheafMap J R i).hom.app (op U)).hom
        (freeModuleSheafGen J R U)) := rfl
  rw [hcomp, freeModuleSheafMap_gen, ← freeModuleSheaf_map_gen i]
  exact app_naturality φ.hom i.op (freeModuleSheafGen J R V)

end HomEquiv

section HModule'

variable {F G : Sheaf J (ModuleCat.{u} R)}

/-- The degree-`n` cohomology of an object `U` of the site with coefficients in a sheaf
of `R`-modules `F`: the `Ext`-group from the free sheaf of `R`-modules on `U` to `F`.
For `U` terminal this recovers `Sheaf.HModule F n` (see
`Sheaf.HModule.linearEquivHModule'`). -/
noncomputable abbrev HModule' (F : Sheaf J (ModuleCat.{u} R)) (U : C) (n : ℕ) : Type u :=
  Abelian.Ext (freeModuleSheaf J R U) F n

/-- Degree-zero cohomology of `U` is the module of sections over `U`, `R`-linearly. -/
noncomputable def HModule'.linearEquiv₀ (F : Sheaf J (ModuleCat.{u} R)) (U : C) :
    HModule' F U 0 ≃ₗ[R] F.obj.obj (op U) :=
  (Abelian.Ext.linearEquiv₀ (R := R)).trans (freeModuleSheafHomEquiv F)

lemma HModule'.linearEquiv₀_symm_apply (F : Sheaf J (ModuleCat.{u} R)) (U : C)
    (s : F.obj.obj (op U)) :
    (HModule'.linearEquiv₀ F U).symm s =
      Abelian.Ext.mk₀ ((freeModuleSheafHomEquiv F).symm s) := by
  rw [HModule'.linearEquiv₀, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Abelian.Ext.linearEquiv₀_symm_apply]

/-- Restriction in the site variable: `i : U ⟶ V` induces an `R`-linear map
`H'ⁿ(V, F) →ₗ[R] H'ⁿ(U, F)`, by precomposition with `freeModuleSheafMap J R i`. -/
noncomputable def HModule'.res {U V : C} (i : U ⟶ V) (F : Sheaf J (ModuleCat.{u} R))
    (n : ℕ) : HModule' F V n →ₗ[R] HModule' F U n :=
  (Abelian.Ext.mk₀ (freeModuleSheafMap J R i)).precompOfLinear R F (zero_add n)

lemma HModule'.res_apply {U V : C} (i : U ⟶ V) (F : Sheaf J (ModuleCat.{u} R)) {n : ℕ}
    (x : HModule' F V n) :
    HModule'.res i F n x =
      (Abelian.Ext.mk₀ (freeModuleSheafMap J R i)).comp x (zero_add n) :=
  rfl

end HModule'

section Terminal

/-! ### Comparison with the cohomology of the site at a terminal object

If `T` is terminal, the free sheaf of modules on `T` is the constant sheaf `R`, so
`Ext`-groups out of it (`Sheaf.HModule'`) agree with those out of the constant sheaf
(`Sheaf.HModule`), `R`-linearly. -/

variable {T : C} (hT : IsTerminal T)

variable (J R) in
/-- The distinguished global section of the constant sheaf of `R`-modules: the image of
`1 : R` (equivalently, the section classifying the identity). -/
noncomputable def constModuleSheafGen : (constModuleSheaf J R).obj.obj (op T) :=
  constModuleSheafHomEquiv J hT (constModuleSheaf J R) (𝟙 _)

/-- Morphisms out of the constant sheaf are computed by evaluation at the distinguished
generator. -/
lemma constModuleSheafHomEquiv_eq_app_gen {F : Sheaf J (ModuleCat.{u} R)}
    (φ : constModuleSheaf J R ⟶ F) :
    constModuleSheafHomEquiv J hT F φ =
      φ.hom.app (op T) (constModuleSheafGen J R hT) := by
  conv_lhs => rw [← Category.id_comp φ]
  exact constModuleSheafHomEquiv_naturality hT (𝟙 _) φ

variable (J R) in
/-- The free sheaf of modules on a terminal object is the constant sheaf `R`. -/
noncomputable def freeModuleSheafIsoConstModuleSheaf :
    freeModuleSheaf J R T ≅ constModuleSheaf J R where
  hom := (freeModuleSheafHomEquiv (constModuleSheaf J R)).symm (constModuleSheafGen J R hT)
  inv := (constModuleSheafHomEquiv J hT (freeModuleSheaf J R T)).symm
    (freeModuleSheafGen J R T)
  hom_inv_id := by
    apply (freeModuleSheafHomEquiv (freeModuleSheaf J R T)).injective
    rw [freeModuleSheafHomEquiv_comp, LinearEquiv.apply_symm_apply,
      ← constModuleSheafHomEquiv_eq_app_gen hT, LinearEquiv.apply_symm_apply]
    rfl
  inv_hom_id := by
    apply (constModuleSheafHomEquiv J hT (constModuleSheaf J R)).injective
    rw [constModuleSheafHomEquiv_naturality, LinearEquiv.apply_symm_apply]
    rw [← freeModuleSheafHomEquiv_apply, LinearEquiv.apply_symm_apply]
    rfl

variable (F : Sheaf J (ModuleCat.{u} R))

/-- Cohomology of the site (`Sheaf.HModule`, `Ext` out of the constant sheaf) is the
cohomology of a terminal object of the site (`Sheaf.HModule'`), `R`-linearly, in every
degree. -/
noncomputable def HModule.linearEquivHModule' (n : ℕ) :
    HModule F n ≃ₗ[R] HModule' F T n where
  __ := (Abelian.Ext.mk₀
      (freeModuleSheafIsoConstModuleSheaf J R hT).hom).precompOfLinear R F (zero_add n)
  invFun := (Abelian.Ext.mk₀
      (freeModuleSheafIsoConstModuleSheaf J R hT).inv).precompOfLinear R F (zero_add n)
  left_inv x := by
    change (Abelian.Ext.mk₀ _).comp ((Abelian.Ext.mk₀ _).comp x (zero_add n)) (zero_add n)
      = x
    rw [Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Abelian.Ext.mk₀_id_comp]
  right_inv x := by
    change (Abelian.Ext.mk₀ _).comp ((Abelian.Ext.mk₀ _).comp x (zero_add n)) (zero_add n)
      = x
    rw [Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Abelian.Ext.mk₀_id_comp]

lemma HModule.linearEquivHModule'_apply (n : ℕ) (x : HModule F n) :
    HModule.linearEquivHModule' hT F n x =
      (Abelian.Ext.mk₀ (freeModuleSheafIsoConstModuleSheaf J R hT).hom).comp x
        (zero_add n) :=
  rfl

end Terminal

end Sheaf

end CategoryTheory
