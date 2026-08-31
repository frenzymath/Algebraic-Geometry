/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.OverOpen

/-!
# The Mayer–Vietoris (0,1)-slice with `ModuleCat R` coefficients

For a Mayer–Vietoris square `S` (`GrothendieckTopology.MayerVietorisSquare`, typically:
opens `X₁ = U ⊓ V`, `X₂ = U`, `X₃ = V`, `X₄ = U ⊔ V` of a topological space) and a sheaf
of `R`-modules `F` on the site, this file produces the exactness of

`0 → F(X₄) → F(X₂) × F(X₃) → F(X₁) --δ--> H¹'(X₄, F) → H¹'(X₂, F) × H¹'(X₃, F)`

`R`-linearly, where `H¹' = Sheaf.HModule'` is the `Ext`-based cohomology of an object of
the site with `ModuleCat R` coefficients, and derives the **two-cover cokernel
computation**: if `H¹'(X₂, F)` and `H¹'(X₃, F)` vanish, then

`F(X₁) ⧸ range(F(X₂) × F(X₃) → F(X₁)) ≃ₗ[R] H¹'(X₄, F)`

(`GrothendieckTopology.MayerVietorisSquare.h1LinearEquiv`), the quotient map being the
connecting homomorphism `moduleDelta`.

## Design / plan (mathlib comparison)

Mathlib's `CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean` proves the long exact
Mayer–Vietoris sequence at `AddCommGrpCat` coefficients from the short exact sequence of
free abelian sheaves `0 → ℤ[X₁] → ℤ[X₂] ⊞ ℤ[X₃] → ℤ[X₄] → 0`
(`MayerVietorisSquare.shortComplex`), whose exactness comes from the defining pushout
property of the square in sheaves of types, transported along the left-adjoint
`Sheaf.composeAndSheafify J AddCommGrpCat.free`. We do **not** transport that LES to
`ModuleCat R` (which would require an `Ext`-comparison across a change of coefficient
category); instead we **re-derive** the short exact sequence at `ModuleCat R`
coefficients by literally mirroring the mathlib proof — every ingredient
(`Sheaf.composeAndSheafify`, `presheafToSheafCompComposeAndSheafifyIso`, the pushout
transport) is generic in the coefficient category, and only two `ModuleCat.free`-specific
instances are needed (`ModuleCat.free_preservesMonomorphisms`,
`ModuleCat.free_isLeftAdjoint`, both provided in
`AlgebraicJacobian.Cohomology.OverOpen`). The (0,1)-slice is then extracted elementwise
from `Abelian.Ext.contravariant_sequence_exact₁/₃` applied to
`moduleShortComplex_shortExact`; the degree-0 part is the sheaf condition
(`MayerVietorisSquare.SheafCondition`) of the square, which needs no `Ext` at all.
Working elementwise (rather than through a `ComposableArrows` incarnation of the LES)
keeps every map `R`-linear by construction — `Ext`-composition is `R`-bilinear via
`Abelian.Ext.bilinearCompOfLinear` — which is what the genus lane needs
(`Module.finrank k H¹`).

## Main declarations

* `MayerVietorisSquare.moduleShortComplex R S` — `0 → R[X₁] → R[X₂] ⊞ R[X₃] → R[X₄] → 0`,
  with `MayerVietorisSquare.moduleShortComplex_shortExact`.
* `MayerVietorisSquare.moduleDiff S F` — the restriction difference
  `F(X₂) × F(X₃) →ₗ[R] F(X₁)`, `(s₂, s₃) ↦ s₂|₁ - s₃|₁`.
* `MayerVietorisSquare.moduleDelta S F` — the connecting map
  `F(X₁) →ₗ[R] H¹'(X₄, F)`.
* degree-0 exactness: `sections_ext`, `moduleDiff_restriction`,
  `exists_glue_of_moduleDiff_eq_zero`.
* (0,1)-exactness: `moduleDelta_moduleDiff`, `exists_of_moduleDelta_eq_zero`,
  `res_moduleDelta₂/₃`, `exists_moduleDelta_eq`, `moduleDelta_surjective`.
* the cokernel computation: `MayerVietorisSquare.h1LinearEquiv`, with
  `h1LinearEquiv_mk` (compatibility with the connecting map).

The scheme-level two-affine-cover bridge (with `Sheaf.HModule` of the scheme's site on
the left) is in `AlgebraicJacobian.Cohomology.TwoCover`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace GrothendieckTopology

namespace MayerVietorisSquare

open Abelian

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Type u) [CommRing R]
variable [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} R)]
variable (S : J.MayerVietorisSquare)

/-- A Mayer–Vietoris square becomes a pushout square of sheaves of `R`-modules after
applying the free-module-sheaf functor. Mirrors
`MayerVietorisSquare.isPushoutAddCommGrpFreeSheaf`. -/
lemma isPushoutFreeModuleSheaf :
    (S.map (CategoryTheory.yoneda ⋙ (Functor.whiskeringRight _ _ _).obj
      (ModuleCat.free R) ⋙ presheafToSheaf J _)).IsPushout :=
  (S.isPushout.map (Sheaf.composeAndSheafify J (ModuleCat.free R))).of_iso
    ((Square.mapFunctor.mapIso
      (presheafToSheafCompComposeAndSheafifyIso J (ModuleCat.free R))).app
        (S.map CategoryTheory.yoneda))

/-- The short complex of sheaves of `R`-modules `R[X₁] ⟶ R[X₂] ⊞ R[X₃] ⟶ R[X₄]`
associated with a Mayer–Vietoris square, where the left map is a difference of
restrictions and the right map a sum. Mirrors `MayerVietorisSquare.shortComplex`.
(Reducible, so that its projections unify with their defining values during rewriting.)
-/
noncomputable abbrev moduleShortComplex : ShortComplex (Sheaf J (ModuleCat.{u} R)) where
  X₁ := Sheaf.freeModuleSheaf J R S.X₁
  X₂ := Sheaf.freeModuleSheaf J R S.X₂ ⊞ Sheaf.freeModuleSheaf J R S.X₃
  X₃ := Sheaf.freeModuleSheaf J R S.X₄
  f := biprod.lift (Sheaf.freeModuleSheafMap J R S.f₁₂)
    (-Sheaf.freeModuleSheafMap J R S.f₁₃)
  g := biprod.desc (Sheaf.freeModuleSheafMap J R S.f₂₄)
    (Sheaf.freeModuleSheafMap J R S.f₃₄)
  zero := (S.map (CategoryTheory.yoneda ⋙ (Functor.whiskeringRight _ _ _).obj
      (ModuleCat.free R) ⋙ presheafToSheaf J _)).cokernelCofork.condition

instance : Mono (S.moduleShortComplex R).f := by
  haveI hneg : Mono (-(presheafToSheaf J (ModuleCat.{u} R)).map
      (Functor.whiskerRight (CategoryTheory.yoneda.map S.f₁₃) (ModuleCat.free R))) :=
    inferInstance
  have : Mono ((S.moduleShortComplex R).f ≫ biprod.snd) := by
    have h : (S.moduleShortComplex R).f ≫ biprod.snd =
        -Sheaf.freeModuleSheafMap J R S.f₁₃ :=
      biprod.lift_snd _ _
    rw [h]
    exact hneg
  exact mono_of_mono _ biprod.snd

lemma moduleShortComplex_exact : (S.moduleShortComplex R).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (S.isPushoutFreeModuleSheaf R).isColimitCokernelCofork

instance : Epi (S.moduleShortComplex R).g :=
  ((S.moduleShortComplex R).exact_and_epi_g_iff_g_is_cokernel.2
    ⟨(S.isPushoutFreeModuleSheaf R).isColimitCokernelCofork⟩).2

/-- The short complex `0 → R[X₁] → R[X₂] ⊞ R[X₃] → R[X₄] → 0` of free sheaves of
`R`-modules on a Mayer–Vietoris square is short exact. -/
lemma moduleShortComplex_shortExact : (S.moduleShortComplex R).ShortExact where
  exact := S.moduleShortComplex_exact R

variable {R S}
variable (F : Sheaf J (ModuleCat.{u} R))

section DegreeZero

/-! ### Degree 0: the sheaf condition

Exactness of `0 → F(X₄) → F(X₂) × F(X₃) → F(X₁)` is the sheaf condition of the square
and needs no `Ext`. -/

omit [HasSheafify J (ModuleCat.{u} R)] in
/-- Two sections of a sheaf over `X₄` agreeing on `X₂` and on `X₃` agree. -/
theorem sections_ext (x y : F.obj.obj (op S.X₄))
    (h₂ : (F.obj.map S.f₂₄.op).hom x = (F.obj.map S.f₂₄.op).hom y)
    (h₃ : (F.obj.map S.f₃₄.op).hom x = (F.obj.map S.f₃₄.op).hom y) : x = y :=
  (S.sheafCondition_of_sheaf
    ((sheafCompose J (CategoryTheory.forget (ModuleCat.{u} R))).obj F)).ext h₂ h₃

variable (S) in
/-- The restriction-difference map `F(X₂) × F(X₃) →ₗ[R] F(X₁)`,
`(s₂, s₃) ↦ s₂|_{X₁} - s₃|_{X₁}`. -/
noncomputable def moduleDiff :
    (F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) →ₗ[R] F.obj.obj (op S.X₁) :=
  (F.obj.map S.f₁₂.op).hom.comp (LinearMap.fst R _ _) -
    (F.obj.map S.f₁₃.op).hom.comp (LinearMap.snd R _ _)

omit [HasSheafify J (ModuleCat.{u} R)] in
lemma moduleDiff_apply (t : F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) :
    S.moduleDiff F t = (F.obj.map S.f₁₂.op).hom t.1 - (F.obj.map S.f₁₃.op).hom t.2 :=
  rfl

omit [HasSheafify J (ModuleCat.{u} R)] in
/-- The restrictions of a section over `X₄` have vanishing difference on `X₁`. -/
theorem moduleDiff_restriction (x : F.obj.obj (op S.X₄)) :
    S.moduleDiff F ((F.obj.map S.f₂₄.op).hom x, (F.obj.map S.f₃₄.op).hom x) = 0 := by
  rw [moduleDiff_apply, sub_eq_zero]
  have h := congrArg (fun (φ : (op S.X₄) ⟶ (op S.X₁)) ↦ (F.obj.map φ).hom x)
    (congrArg Quiver.Hom.op S.fac)
  simpa only [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    using h

omit [HasSheafify J (ModuleCat.{u} R)] in
/-- Sections over `X₂` and `X₃` with vanishing difference on `X₁` glue to a section
over `X₄`. -/
theorem exists_glue_of_moduleDiff_eq_zero
    (t : F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) (ht : S.moduleDiff F t = 0) :
    ∃ x : F.obj.obj (op S.X₄),
      (F.obj.map S.f₂₄.op).hom x = t.1 ∧ (F.obj.map S.f₃₄.op).hom x = t.2 := by
  have hsc := S.sheafCondition_of_sheaf
    ((sheafCompose J (CategoryTheory.forget (ModuleCat.{u} R))).obj F)
  have huv : (F.obj.map S.f₁₂.op).hom t.1 = (F.obj.map S.f₁₃.op).hom t.2 := by
    rw [moduleDiff_apply, sub_eq_zero] at ht
    exact ht
  exact ⟨hsc.glue t.1 t.2 huv, hsc.map_f₂₄_op_glue t.1 t.2 huv,
    hsc.map_f₃₄_op_glue t.1 t.2 huv⟩

end DegreeZero

section Connecting

/-! ### The connecting map `δ : F(X₁) → H¹'(X₄, F)` and the (0,1)-slice exactness -/

variable (S) in
/-- The Mayer–Vietoris connecting homomorphism `F(X₁) →ₗ[R] H¹'(X₄, F)`: the class of a
section on the "overlap" `X₁` obstructing its decomposition as a difference of sections
on the two "pieces". Defined by pairing with the extension class of
`moduleShortComplex`. -/
noncomputable def moduleDelta :
    F.obj.obj (op S.X₁) →ₗ[R] Sheaf.HModule' F S.X₄ 1 :=
  ((S.moduleShortComplex_shortExact R).extClass.precompOfLinear R F rfl).comp
    (Sheaf.HModule'.linearEquiv₀ F S.X₁).symm.toLinearMap

lemma moduleDelta_apply (s : F.obj.obj (op S.X₁)) :
    S.moduleDelta F s = (S.moduleShortComplex_shortExact R).extClass.comp
      ((Sheaf.HModule'.linearEquiv₀ F S.X₁).symm s) rfl :=
  rfl

/-- `δ ∘ (difference of restrictions) = 0`: the classes of sections of the overlap
that extend to the pieces vanish. -/
theorem moduleDelta_moduleDiff (t : F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) :
    S.moduleDelta F (S.moduleDiff F t) = 0 := by
  set φ : Sheaf.freeModuleSheaf J R S.X₂ ⊞ Sheaf.freeModuleSheaf J R S.X₃ ⟶ F :=
    biprod.desc ((Sheaf.freeModuleSheafHomEquiv F).symm t.1)
      ((Sheaf.freeModuleSheafHomEquiv F).symm t.2) with hφ
  have hfφ : (Sheaf.freeModuleSheafHomEquiv F).symm (S.moduleDiff F t) =
      (S.moduleShortComplex R).f ≫ φ := by
    apply (Sheaf.freeModuleSheafHomEquiv F).injective
    rw [LinearEquiv.apply_symm_apply]
    have hcomp : (S.moduleShortComplex R).f ≫ φ =
        Sheaf.freeModuleSheafMap J R S.f₁₂ ≫ (Sheaf.freeModuleSheafHomEquiv F).symm t.1 -
          Sheaf.freeModuleSheafMap J R S.f₁₃ ≫
            (Sheaf.freeModuleSheafHomEquiv F).symm t.2 := by
      rw [hφ, biprod.lift_desc, Preadditive.neg_comp, ← sub_eq_add_neg]
    rw [hcomp, map_sub, Sheaf.freeModuleSheafHomEquiv_map,
      Sheaf.freeModuleSheafHomEquiv_map, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, moduleDiff_apply]
  rw [moduleDelta_apply, Sheaf.HModule'.linearEquiv₀_symm_apply, hfφ,
    ← Abelian.Ext.mk₀_comp_mk₀]
  exact (S.moduleShortComplex_shortExact R).extClass_comp_assoc _

/-- Exactness at `F(X₁)`: a section of the overlap whose connecting class vanishes is a
difference of restrictions from the pieces. -/
theorem exists_of_moduleDelta_eq_zero (s : F.obj.obj (op S.X₁))
    (hs : S.moduleDelta F s = 0) :
    ∃ t : F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃), S.moduleDiff F t = s := by
  rw [moduleDelta_apply] at hs
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁
    (S.moduleShortComplex_shortExact R) F ((Sheaf.HModule'.linearEquiv₀ F S.X₁).symm s)
    rfl hs
  set φ : Sheaf.freeModuleSheaf J R S.X₂ ⊞ Sheaf.freeModuleSheaf J R S.X₃ ⟶ F :=
    Abelian.Ext.linearEquiv₀ (R := R) x₂ with hφ
  refine ⟨(Sheaf.freeModuleSheafHomEquiv F (biprod.inl ≫ φ),
    Sheaf.freeModuleSheafHomEquiv F (biprod.inr ≫ φ)), ?_⟩
  have hmorph : (S.moduleShortComplex R).f ≫ φ =
      Abelian.Ext.linearEquiv₀ (R := R)
        ((Sheaf.HModule'.linearEquiv₀ F S.X₁).symm s) := by
    apply (Abelian.Ext.mk₀_bijective _ F).injective
    rw [Abelian.Ext.mk₀_linearEquiv₀_apply, ← Abelian.Ext.mk₀_comp_mk₀, hφ,
      Abelian.Ext.mk₀_linearEquiv₀_apply]
    exact hx₂
  have hf : (S.moduleShortComplex R).f ≫ φ =
      Sheaf.freeModuleSheafMap J R S.f₁₂ ≫ biprod.inl ≫ φ -
        Sheaf.freeModuleSheafMap J R S.f₁₃ ≫ biprod.inr ≫ φ := by
    rw [show (S.moduleShortComplex R).f =
        biprod.lift (Sheaf.freeModuleSheafMap J R S.f₁₂)
          (-Sheaf.freeModuleSheafMap J R S.f₁₃) from rfl, biprod.lift_eq]
    simp only [Preadditive.neg_comp, ← sub_eq_add_neg]
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc]
  rw [moduleDiff_apply, ← Sheaf.freeModuleSheafHomEquiv_map,
    ← Sheaf.freeModuleSheafHomEquiv_map, ← map_sub, ← hf, hmorph]
  exact LinearEquiv.apply_symm_apply (Sheaf.HModule'.linearEquiv₀ F S.X₁) s

/-- The connecting class dies on restriction to the first piece: exactness half of the
sequence at `H¹'(X₄)`. -/
theorem res_moduleDelta₂ (s : F.obj.obj (op S.X₁)) :
    Sheaf.HModule'.res S.f₂₄ F 1 (S.moduleDelta F s) = 0 := by
  rw [Sheaf.HModule'.res_apply, moduleDelta_apply,
    show Sheaf.freeModuleSheafMap J R S.f₂₄ = biprod.inl ≫ (S.moduleShortComplex R).g
      from (biprod.inl_desc _ _).symm,
    ← Abelian.Ext.mk₀_comp_mk₀_assoc,
    (S.moduleShortComplex_shortExact R).comp_extClass_assoc,
    Abelian.Ext.comp_zero]

/-- The connecting class dies on restriction to the second piece. -/
theorem res_moduleDelta₃ (s : F.obj.obj (op S.X₁)) :
    Sheaf.HModule'.res S.f₃₄ F 1 (S.moduleDelta F s) = 0 := by
  rw [Sheaf.HModule'.res_apply, moduleDelta_apply,
    show Sheaf.freeModuleSheafMap J R S.f₃₄ = biprod.inr ≫ (S.moduleShortComplex R).g
      from (biprod.inr_desc _ _).symm,
    ← Abelian.Ext.mk₀_comp_mk₀_assoc,
    (S.moduleShortComplex_shortExact R).comp_extClass_assoc,
    Abelian.Ext.comp_zero]

/-- Exactness at `H¹'(X₄)`: a degree-one class of `X₄` restricting to zero on both
pieces is a connecting class. -/
theorem exists_moduleDelta_eq (y : Sheaf.HModule' F S.X₄ 1)
    (h₂ : Sheaf.HModule'.res S.f₂₄ F 1 y = 0)
    (h₃ : Sheaf.HModule'.res S.f₃₄ F 1 y = 0) :
    ∃ s : F.obj.obj (op S.X₁), S.moduleDelta F s = y := by
  have hg : (Abelian.Ext.mk₀ (S.moduleShortComplex R).g).comp y (zero_add 1) = 0 := by
    apply Abelian.Ext.biprodAddEquiv.injective
    rw [map_zero]
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_zero, Prod.snd_zero]
    · rw [Abelian.Ext.biprodAddEquiv_apply_fst, Abelian.Ext.mk₀_comp_mk₀_assoc,
        show biprod.inl ≫ (S.moduleShortComplex R).g =
          Sheaf.freeModuleSheafMap J R S.f₂₄ from biprod.inl_desc _ _]
      exact h₂
    · rw [Abelian.Ext.biprodAddEquiv_apply_snd, Abelian.Ext.mk₀_comp_mk₀_assoc,
        show biprod.inr ≫ (S.moduleShortComplex R).g =
          Sheaf.freeModuleSheafMap J R S.f₃₄ from biprod.inr_desc _ _]
      exact h₃
  obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₃
    (S.moduleShortComplex_shortExact R) F y hg (n₀ := 0) rfl
  refine ⟨Sheaf.HModule'.linearEquiv₀ F S.X₁ x₁, ?_⟩
  rw [moduleDelta_apply, LinearEquiv.symm_apply_apply]
  exact hx₁

/-- If the degree-one cohomology of both pieces vanishes, the connecting map is
surjective. -/
theorem moduleDelta_surjective [Subsingleton (Sheaf.HModule' F S.X₂ 1)]
    [Subsingleton (Sheaf.HModule' F S.X₃ 1)] :
    Function.Surjective (S.moduleDelta F) := fun y ↦
  S.exists_moduleDelta_eq F y (Subsingleton.elim _ _) (Subsingleton.elim _ _)

end Connecting

section Cokernel

/-! ### The two-cover cokernel computation -/

theorem range_moduleDiff_le_ker_moduleDelta :
    LinearMap.range (S.moduleDiff F) ≤ LinearMap.ker (S.moduleDelta F) := by
  rintro - ⟨t, rfl⟩
  exact S.moduleDelta_moduleDiff F t

variable (S) in
/-- The connecting map descended to the cokernel of the restriction-difference map. -/
noncomputable def moduleDeltaQuotient :
    (F.obj.obj (op S.X₁) ⧸ LinearMap.range (S.moduleDiff F)) →ₗ[R]
      Sheaf.HModule' F S.X₄ 1 :=
  Submodule.liftQ _ (S.moduleDelta F) (S.range_moduleDiff_le_ker_moduleDelta F)

@[simp]
lemma moduleDeltaQuotient_mk (s : F.obj.obj (op S.X₁)) :
    S.moduleDeltaQuotient F (Submodule.Quotient.mk s) = S.moduleDelta F s :=
  rfl

/-- **The Mayer–Vietoris two-cover cokernel computation.** If the degree-one cohomology
of the two pieces of a Mayer–Vietoris square vanishes, the degree-one cohomology of
`X₄` is `R`-linearly the cokernel of the restriction-difference map
`F(X₂) × F(X₃) → F(X₁)`; the identification descends the connecting map
(`MayerVietorisSquare.h1LinearEquiv_mk`). -/
noncomputable def h1LinearEquiv [Subsingleton (Sheaf.HModule' F S.X₂ 1)]
    [Subsingleton (Sheaf.HModule' F S.X₃ 1)] :
    (F.obj.obj (op S.X₁) ⧸ LinearMap.range (S.moduleDiff F)) ≃ₗ[R]
      Sheaf.HModule' F S.X₄ 1 :=
  LinearEquiv.ofBijective (S.moduleDeltaQuotient F) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker, moduleDeltaQuotient_mk] at hx
      obtain ⟨t, ht⟩ := S.exists_of_moduleDelta_eq_zero F s hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨t, ht⟩
    · intro y
      obtain ⟨s, hs⟩ := S.moduleDelta_surjective F y
      exact ⟨Submodule.Quotient.mk s, hs⟩

@[simp]
lemma h1LinearEquiv_mk [Subsingleton (Sheaf.HModule' F S.X₂ 1)]
    [Subsingleton (Sheaf.HModule' F S.X₃ 1)] (s : F.obj.obj (op S.X₁)) :
    S.h1LinearEquiv F (Submodule.Quotient.mk s) = S.moduleDelta F s :=
  rfl

end Cokernel

end MayerVietorisSquare

end GrothendieckTopology

end CategoryTheory
