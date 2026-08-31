/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# `ModuleCat k`-valued sheaf cohomology and the structure sheaf as a sheaf of modules

This file provides the cohomology carrier for the genus lane of the Jacobian challenge:

1. For a small site `(C, J)` and a commutative ring `R`, the degree-`n` cohomology
   `Sheaf.HModule F n` of a sheaf `F` of `R`-modules, defined as the `Ext`-group from the
   constant sheaf with value `R` to `F` (mirroring `CategoryTheory.Sheaf.H`, which is
   `AddCommGrpCat`-valued; ours is `ModuleCat R`-valued so that `Module.finrank` applies).
   Each `Sheaf.HModule F n` is an `R`-module via the `R`-linear structure of the sheaf
   category, and `Sheaf.HModule.map` gives `R`-linear functoriality in `F`.
2. The degree-zero identification `Sheaf.HModule.linearEquiv₀ : HModule F 0 ≃ₗ[R] F(⊤)`
   via `Ext⁰ ≅ Hom` and the constant-sheaf adjunction, together with its naturality.
3. For a scheme `X` over `Spec k`, the structure sheaf of `X` as a sheaf of `k`-modules
   `Scheme.moduleKSheaf` on the small Zariski site `Opens.grothendieckTopology X`, by
   restriction of scalars along the structure morphism, with definitional (`rfl`) access
   to its sections and restriction maps.

## Universe discipline

Everything is single-universe: `k : Type u`, `X : Scheme.{u}`, the site `Opens X : Type u`
with hom-types in `Type u`, and coefficients `ModuleCat.{u} k`. Then
`Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)` is Grothendieck abelian relative
to `u` (`ModuleCat.{u} k` is, and the site is small), hence `HasExt.{u}` holds and
`Sheaf.HModule F n : Type u` with a `Module k` structure — no universe bump anywhere, so
`Module.finrank k` applies directly downstream.

## Design notes

* `Sheaf.HModule` is an `abbrev` for `Abelian.Ext`, so the entire mathlib `Ext` API
  (long exact sequences `Ext.covariant_sequence_exact₁/₂/₃`, `Ext.extClass`, the
  Mayer–Vietoris machinery of `CategoryTheory/Sites/SheafCohomology`) applies
  transparently; we do not rebuild any of it.
* No global `Algebra k Γ(X, U)` instance is introduced (it would overlap with mathlib's
  `Algebra R Γ(Spec R, U)` instance via the tautological `OverClass X X`); the module
  structure is carried by the explicit defs `Scheme.overAlgebraMap`/`Scheme.overModule`
  and, where needed, `attribute [local instance] Scheme.overModule`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [SmallCategory C]

section HModule

variable (J : GrothendieckTopology C) (R : Type u) [CommRing R]
  [HasSheafify J (ModuleCat.{u} R)]

/-- The constant sheaf of `R`-modules with value `R` on the site `(C, J)`; sheaf cohomology
of sheaves of `R`-modules is `Ext` out of this object. -/
noncomputable def constModuleSheaf : Sheaf J (ModuleCat.{u} R) :=
  (constantSheaf J (ModuleCat.{u} R)).obj (ModuleCat.of R R)

variable {J R}

/-- The degree-`n` cohomology of a sheaf of `R`-modules on a small site, as an `Ext`-group
in the Grothendieck abelian category `Sheaf J (ModuleCat R)`. It is a `Type u` carrying a
`Module R` instance (via the `R`-linear structure of the sheaf category). -/
noncomputable abbrev HModule (F : Sheaf J (ModuleCat.{u} R)) (n : ℕ) : Type u :=
  Abelian.Ext (constModuleSheaf J R) F n

namespace HModule

variable {F G G' : Sheaf J (ModuleCat.{u} R)}

/-- Functoriality of `Sheaf.HModule` in the sheaf, as an `R`-linear map. -/
noncomputable def map (f : F ⟶ G) (n : ℕ) : HModule F n →ₗ[R] HModule G n :=
  (Abelian.Ext.mk₀ f).postcompOfLinear R (constModuleSheaf J R) (add_zero n)

lemma map_apply (f : F ⟶ G) {n : ℕ} (x : HModule F n) :
    map f n x = x.comp (Abelian.Ext.mk₀ f) (add_zero n) := rfl

@[simp]
lemma map_id_apply {n : ℕ} (x : HModule F n) : map (𝟙 F) n x = x := by
  simp [map_apply]

lemma map_comp_apply (f : F ⟶ G) (g : G ⟶ G') {n : ℕ} (x : HModule F n) :
    map (f ≫ g) n x = map g n (map f n x) := by
  simp [map_apply]

instance [Injective F] (n : ℕ) : Subsingleton (HModule F (n + 1)) :=
  subsingleton_of_forall_eq 0 fun x ↦ x.eq_zero_of_injective

end HModule

section LinearEquivZero

variable {T : C} (hT : IsTerminal T)

/-- The hom-equivalence of the constant-sheaf ⊣ global-sections adjunction, upgraded to an
`R`-linear equivalence. -/
noncomputable def constantSheafAdjHomLinearEquiv (M : ModuleCat.{u} R)
    (F : Sheaf J (ModuleCat.{u} R)) :
    ((constantSheaf J (ModuleCat.{u} R)).obj M ⟶ F) ≃ₗ[R] (M ⟶ F.obj.obj (op T)) := by
  refine
    { toFun := (constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv M F
      invFun := ((constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv M F).symm
      left_inv := ((constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv M F).left_inv
      right_inv := ((constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv M F).right_inv
      map_add' := fun f g ↦ ?_
      map_smul' := fun r f ↦ ?_ } <;>
  · simp only [Adjunction.homEquiv_apply]
    ext v
    rfl

lemma constantSheafAdjHomLinearEquiv_apply (M : ModuleCat.{u} R)
    {F : Sheaf J (ModuleCat.{u} R)} (φ : (constantSheaf J (ModuleCat.{u} R)).obj M ⟶ F) :
    constantSheafAdjHomLinearEquiv hT M F φ =
      (constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv M F φ := rfl

lemma constantSheafAdjHomLinearEquiv_naturality (M : ModuleCat.{u} R)
    {F G : Sheaf J (ModuleCat.{u} R)}
    (φ : (constantSheaf J (ModuleCat.{u} R)).obj M ⟶ F) (f : F ⟶ G) :
    constantSheafAdjHomLinearEquiv hT M G (φ ≫ f) =
      constantSheafAdjHomLinearEquiv hT M F φ ≫ f.hom.app (op T) := by
  simp only [constantSheafAdjHomLinearEquiv_apply]
  exact (constantSheafAdj J (ModuleCat.{u} R) hT).homEquiv_naturality_right φ f

variable (J) in
/-- Morphisms out of the constant sheaf `R` compute global sections, `R`-linearly:
`Hom(R_X, F) ≃ₗ[R] F(⊤)`. -/
noncomputable def constModuleSheafHomEquiv (F : Sheaf J (ModuleCat.{u} R)) :
    (constModuleSheaf J R ⟶ F) ≃ₗ[R] F.obj.obj (op T) :=
  (constantSheafAdjHomLinearEquiv hT (ModuleCat.of R R) F).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R _))

lemma constModuleSheafHomEquiv_naturality {F G : Sheaf J (ModuleCat.{u} R)}
    (φ : constModuleSheaf J R ⟶ F) (f : F ⟶ G) :
    constModuleSheafHomEquiv J hT G (φ ≫ f) =
      f.hom.app (op T) (constModuleSheafHomEquiv J hT F φ) := by
  simp only [constModuleSheafHomEquiv]
  rfl

variable (J) in
/-- Degree-zero cohomology of a sheaf of `R`-modules is its module of global sections
(sections over a terminal object of the site), `R`-linearly. -/
noncomputable def HModule.linearEquiv₀ (F : Sheaf J (ModuleCat.{u} R)) :
    HModule F 0 ≃ₗ[R] F.obj.obj (op T) :=
  (Abelian.Ext.linearEquiv₀ (R := R)).trans (constModuleSheafHomEquiv J hT F)

variable {F G : Sheaf J (ModuleCat.{u} R)} (f : F ⟶ G)

lemma HModule.linearEquiv₀_map (x : HModule F 0) :
    Abelian.Ext.linearEquiv₀ (R := R) (HModule.map f 0 x) =
      Abelian.Ext.linearEquiv₀ (R := R) x ≫ f := by
  apply (Abelian.Ext.mk₀_bijective (constModuleSheaf J R) G).injective
  simp only [Abelian.Ext.mk₀_linearEquiv₀_apply, ← Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_linearEquiv₀_apply]
  exact HModule.map_apply f x

/-- Naturality of the degree-zero identification. -/
theorem HModule.linearEquiv₀_naturality (x : HModule F 0) :
    f.hom.app (op T) (HModule.linearEquiv₀ J hT F x) =
      HModule.linearEquiv₀ J hT G (HModule.map f 0 x) := by
  simp only [linearEquiv₀, LinearEquiv.trans_apply, HModule.linearEquiv₀_map f x]
  exact (constModuleSheafHomEquiv_naturality hT (Abelian.Ext.linearEquiv₀ x) f).symm

theorem HModule.linearEquiv₀_symm_naturality (s : F.obj.obj (op T)) :
    HModule.map f 0 ((HModule.linearEquiv₀ J hT F).symm s) =
      (HModule.linearEquiv₀ J hT G).symm (f.hom.app (op T) s) := by
  apply (HModule.linearEquiv₀ J hT G).injective
  simp [← HModule.linearEquiv₀_naturality]

end LinearEquivZero

end HModule

end Sheaf

end CategoryTheory

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The structure morphism of a scheme over `Spec k`, at the level of sections over an
open `U`: the canonical ring homomorphism `k →+* Γ(X, U)`. -/
noncomputable def Scheme.overAlgebraMap (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
    X.presheaf.map (homOfLE le_top).op).hom

lemma Scheme.overAlgebraMap_naturality {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    ((X.presheaf.map i).hom).comp (X.overAlgebraMap k U.unop) =
      X.overAlgebraMap k V.unop := by
  rw [Scheme.overAlgebraMap, Scheme.overAlgebraMap, ← CommRingCat.hom_comp]
  congr 1
  simp only [Category.assoc, ← X.presheaf.map_comp]
  congr 1

lemma Scheme.overAlgebraMap_apply_res {U V : X.Opensᵒᵖ} (i : U ⟶ V) (r : k) :
    (X.presheaf.map i).hom (X.overAlgebraMap k U.unop r) =
      X.overAlgebraMap k V.unop r :=
  DFunLike.congr_fun (X.overAlgebraMap_naturality k i) r

/-- The `k`-module structure on `Γ(X, U)` for a scheme over `Spec k`, by restriction of
scalars along `Scheme.overAlgebraMap`. Deliberately *not* a global instance: it would
overlap with mathlib's `Algebra R Γ(Spec R, U)` instance through the tautological
`OverClass X X`. Activate it with `attribute [local instance] Scheme.overModule` or `letI`
where needed. -/
@[reducible] noncomputable def Scheme.overModule (U : X.Opens) : Module k Γ(X, U) :=
  (X.overAlgebraMap k U).toModule

attribute [local instance] Scheme.overModule

lemma Scheme.overModule_smul_def {U : X.Opens} (r : k) (s : Γ(X, U)) :
    r • s = X.overAlgebraMap k U r * s := rfl

/-- The structure sheaf of a scheme `X` over `Spec k`, as a presheaf of `k`-modules on
`Opens X`: sections are `Γ(X, U)` with the `k`-action of `Scheme.overModule`, restriction
maps are those of the structure sheaf. -/
noncomputable def Scheme.moduleKPresheaf : X.Opensᵒᵖ ⥤ ModuleCat.{u} k where
  obj U := ModuleCat.of k Γ(X, U.unop)
  map {U V} i := ModuleCat.ofHom
    { toFun := (X.presheaf.map i).hom
      map_add' := map_add _
      map_smul' := fun r s ↦ by
        simp only [Scheme.overModule_smul_def, map_mul, RingHom.id_apply,
          X.overAlgebraMap_apply_res k i r] }
  map_id U := by
    ext s
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U)) s
  map_comp {U V W} i j := by
    ext s
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (X.presheaf.map_comp i j)) s

/-- The underlying types-valued presheaf of `Scheme.moduleKPresheaf` is that of the
structure sheaf. -/
noncomputable def Scheme.moduleKPresheafCompForgetIso :
    X.moduleKPresheaf k ⋙ CategoryTheory.forget (ModuleCat.{u} k) ≅
      X.presheaf ⋙ CategoryTheory.forget CommRingCat :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

lemma Scheme.isSheaf_moduleKPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (X : TopCat)) (X.moduleKPresheaf k) := by
  have h : TopCat.Presheaf.IsSheaf (C := ModuleCat.{u} k) (X := (X : TopCat))
      (X.moduleKPresheaf k) := by
    rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (CategoryTheory.forget (ModuleCat.{u} k))
      (X.moduleKPresheaf k)]
    change Presheaf.IsSheaf (Opens.grothendieckTopology (X : TopCat)) _
    rw [Presheaf.isSheaf_of_iso_iff (X.moduleKPresheafCompForgetIso k)]
    exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
      (CategoryTheory.forget CommRingCat) X.presheaf).mp X.toSheafedSpace.IsSheaf
  exact h

/-- The structure sheaf of a scheme `X` over `Spec k`, as a sheaf of `k`-modules on the
small Zariski site of `X`. Its sections over `U` are *definitionally*
`ModuleCat.of k Γ(X, U)` (with the `Scheme.overModule` action) and its restriction maps
are definitionally those of the structure sheaf; see `Scheme.moduleKSheaf_obj` and
`Scheme.moduleKSheaf_map_apply`. -/
noncomputable def Scheme.moduleKSheaf :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k) :=
  ⟨X.moduleKPresheaf k, X.isSheaf_moduleKPresheaf k⟩

@[simp]
lemma Scheme.moduleKSheaf_obj (U : X.Opens) :
    (X.moduleKSheaf k).obj.obj (op U) = ModuleCat.of k Γ(X, U) := rfl

lemma Scheme.moduleKSheaf_map_apply {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (s : Γ(X, U.unop)) :
    ((X.moduleKSheaf k).obj.map i).hom s = (X.presheaf.map i).hom s := rfl

/-- `H⁰` of the structure sheaf of `X` over `Spec k` is the module of global sections
`Γ(X, ⊤)`, `k`-linearly (with the `Scheme.overModule` structure on the right). -/
noncomputable def Scheme.moduleKSheafHZero :
    Sheaf.HModule (X.moduleKSheaf k) 0 ≃ₗ[k] Γ(X, ⊤) :=
  Sheaf.HModule.linearEquiv₀ (Opens.grothendieckTopology (X : TopCat))
    (isTerminalTop : IsTerminal (⊤ : X.Opens))
    (X.moduleKSheaf k)

end AlgebraicGeometry
