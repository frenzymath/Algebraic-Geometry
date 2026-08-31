/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.TwoCover
import AlgebraicJacobian.Cohomology.SectionsBaseChange
import AlgebraicJacobian.Picard.AffineTwoCover
import AlgebraicJacobian.Picard.UniversalSections

/-!
# Relative two-cover cohomology-and-base-change over an affine test ring

For the challenge curve `C` over a field `k`, a commutative `k`-algebra `R` (the **affine
test ring**), and an affine two-chart cover `D` of `C.left`, this file assembles the
curve-lite form of *cohomology-and-base-change* that Wave 4's representability route needs:
the relative curve `C_R := (C ⊗ Spec R).left` over `Spec R`, its base-changed affine
two-cover, and the degree-one cohomology of the structure sheaf as an explicit two-cover
cokernel over `R` — the general-coefficients carrier `Scheme.twoCoverH1LinearEquiv`
instantiated relatively at `k := R`.

## Main declarations

* `AlgebraicGeometry.relCurve C R` — the relative curve `(C ⊗ overSpec k R).left`, a scheme
  over `Spec R` via the second projection (`relCurve.instOver`).
* `AlgebraicGeometry.relCover C R D` — the base-changed affine two-cover
  (`Scheme.AffineTwoCover.pullbackProd`), with `relCover_isAffineOpen₀/₁`, `relCover_sup`,
  `relCover_inf` (**G-CBC-1**).
* `AlgebraicGeometry.relTwoCoverH1` — **CBC-0**: `H¹(C_R, 𝒪) ≃ₗ[R] Γ(C_R, V₀ᴿ ⊓ V₁ᴿ) ⧸
  range δ`, the two-cover cokernel over `R`, with the affine-vanishing instances discharged
  by the landed structure-sheaf vanishing.
* `AlgebraicGeometry.relStructureSectionsTop` — **H⁰ base change / CBC-3 anchor**:
  `Γ(C_R, ⊤) ≃+* R` (Kleiman's `𝒪_S ≅ f_* 𝒪_X`, read as base change of `H⁰`).

## The twisted-sheaf probe and the transport frontier

Alongside the structure sheaf, this brick probes the twisted line bundle `F_g` of design
§6.1 (`F_g(W) = {(s₀, s₁) | s₀ = g·s₁ on the overlap}` for a two-cover unit cocycle `g`),
whose intended vanishing route (G-CBC-3(i)) transports the affine `H¹'`-vanishing along a
trivialization `F_g|Vᵢ ≅ 𝒪|Vᵢ`. The **global** form of that transport is landed here as
`CategoryTheory.Sheaf.HModule'.congrCoeff` / `.subsingleton_of_congrCoeff` (a one-screen
consequence of `Ext`-bifunctoriality). The **local** form actually needed — transport along
`F|U ≅ G|U` rather than a global `F ≅ G` — is genuinely different: `HModule' F U n =
Ext(R[U], F)` is not computed from `F|U` by any in-tree lemma, and the landed affine-vanishing
engine (`IsAffineOpen.cokernel_app_surjective`, `IsAffineOpen.exists_cech_cobounding`) is
hard-wired to the *structure* sheaf. See the session report for the early-warning verdict.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open TensorProduct Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Type u} [CommRing R] [HasSheafify J (ModuleCat.{u} R)]
  {F G : Sheaf J (ModuleCat.{u} R)} {U : C}

/-- Functoriality of `HModule' _ U n` in the coefficient sheaf, as an `R`-linear map:
postcomposition with `f : F ⟶ G` (the coefficient-variable analogue of `HModule'.res`,
which is functoriality in the object of the site). -/
noncomputable def HModule'.mapCoeff (f : F ⟶ G) (n : ℕ) :
    HModule' F U n →ₗ[R] HModule' G U n :=
  (Abelian.Ext.mk₀ f).postcompOfLinear R (freeModuleSheaf J R U) (add_zero n)

lemma HModule'.mapCoeff_apply (f : F ⟶ G) {n : ℕ} (x : HModule' F U n) :
    HModule'.mapCoeff f n x = x.comp (Abelian.Ext.mk₀ f) (add_zero n) := rfl

@[simp] lemma HModule'.mapCoeff_id_apply {n : ℕ} (x : HModule' F U n) :
    HModule'.mapCoeff (𝟙 F) n x = x := by
  simp [mapCoeff_apply]

lemma HModule'.mapCoeff_comp_apply {G' : Sheaf J (ModuleCat.{u} R)} (f : F ⟶ G) (g : G ⟶ G')
    {n : ℕ} (x : HModule' F U n) :
    HModule'.mapCoeff (f ≫ g) n x = HModule'.mapCoeff g n (HModule'.mapCoeff f n x) := by
  simp [mapCoeff_apply]

/-- **Coefficient-iso transport for `HModule'`.** A global isomorphism `α : F ≅ G` of
coefficient sheaves induces an `R`-linear isomorphism `HModule' F U n ≃ₗ[R] HModule' G U n`.

Note (early-warning): this transports along a *global* iso. The twisted-sheaf probe needs
transport along a merely *local* trivialization `F|U ≅ G|U`; that is genuinely different
(see the module docstring) and is **not** an instance of this lemma. -/
noncomputable def HModule'.congrCoeff (α : F ≅ G) (n : ℕ) :
    HModule' F U n ≃ₗ[R] HModule' G U n where
  __ := HModule'.mapCoeff α.hom n
  invFun := HModule'.mapCoeff α.inv n
  left_inv x := by
    change HModule'.mapCoeff α.inv n (HModule'.mapCoeff α.hom n x) = x
    rw [← mapCoeff_comp_apply, α.hom_inv_id, mapCoeff_id_apply]
  right_inv x := by
    change HModule'.mapCoeff α.hom n (HModule'.mapCoeff α.inv n x) = x
    rw [← mapCoeff_comp_apply, α.inv_hom_id, mapCoeff_id_apply]

/-- Coefficient-iso transport of degree-one vanishing: if `H¹'(U, G)` vanishes and
`F ≅ G` globally, then `H¹'(U, F)` vanishes. -/
theorem HModule'.subsingleton_of_congrCoeff (α : F ≅ G) {n : ℕ}
    [Subsingleton (HModule' G U n)] : Subsingleton (HModule' F U n) :=
  (HModule'.congrCoeff α n).toEquiv.subsingleton

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]

/-- The **relative curve** `C ⊗ Spec R` over the affine test ring `R`: the underlying
scheme of the cartesian-monoidal product of `C` and `overSpec k R` in `Over (Spec k)`. -/
noncomputable def relCurve : Scheme.{u} := (C ⊗ overSpec k R).left

lemma relCurve_def : relCurve C R = (C ⊗ overSpec k R).left := rfl

/-- The relative curve is a scheme over `Spec R` via the second projection. -/
noncomputable instance relCurve.instOver : (relCurve C R).Over (Spec (.of R)) :=
  .ofHom (snd C (overSpec k R)).left

variable (D : C.left.AffineTwoCover)

/-- The **base-changed affine two-cover** of the relative curve: the preimages of the
charts of `D` under the first projection `relCurve C R ⟶ C.left`
(`Scheme.AffineTwoCover.pullbackProd`), an affine two-chart cover of `relCurve C R`. -/
noncomputable def relCover : (relCurve C R).AffineTwoCover := D.pullbackProd R

/-- The first base-changed chart is affine (`G-CBC-1`). -/
theorem relCover_isAffineOpen₀ : IsAffineOpen (relCover C R D).V₀ :=
  (relCover C R D).isAffineOpen₀

/-- The second base-changed chart is affine (`G-CBC-1`). -/
theorem relCover_isAffineOpen₁ : IsAffineOpen (relCover C R D).V₁ :=
  (relCover C R D).isAffineOpen₁

/-- The two base-changed charts cover the relative curve (`G-CBC-1`). -/
theorem relCover_sup : (relCover C R D).V₀ ⊔ (relCover C R D).V₁ = ⊤ :=
  (relCover C R D).sup_eq_top

/-- **CBC-0 (relative carrier).** For the structure sheaf of the relative curve as a sheaf
of `R`-modules, the degree-one cohomology over `Spec R` is the cokernel of the two-cover
restriction-difference map on `R`-module sections. This is
`Scheme.twoCoverH1LinearEquiv`/`TwoCover.h1CokEquiv` instantiated at `k := R`,
`X := relCurve C R`, `F := 𝒪`, with the two affine-vanishing instances discharged by the
landed structure-sheaf vanishing. -/
noncomputable def relTwoCoverH1 :
    Sheaf.HModule ((relCurve C R).moduleKSheaf R) 1 ≃ₗ[R]
      TwoCover.H1Cok R (relCurve C R) (relCover C R D).V₀ (relCover C R D).V₁ :=
  TwoCover.h1CokEquiv R (relCurve C R) (relCover C R D).V₀ (relCover C R D).V₁
    (relCover_sup C R D) (relCover_isAffineOpen₀ C R D) (relCover_isAffineOpen₁ C R D)

/-- The overlap of the two base-changed charts is the preimage of the overlap of `D`. -/
theorem relCover_inf :
    (relCover C R D).V₀ ⊓ (relCover C R D).V₁ =
      (fst C (overSpec k R)).left ⁻¹ᵁ (D.V₀ ⊓ D.V₁) :=
  (Scheme.Hom.preimage_inf (fst C (overSpec k R)).left).symm

section StandingBundle

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **H⁰ base change / CBC-3 anchor.** For the challenge curve `C`, the degree-zero
cohomology of the structure sheaf on the relative curve is the test ring itself:
`Γ(C_R, ⊤) ≃+* R`, universally in the commutative `k`-algebra `R`. This is Kleiman's
`𝒪_S ≅ f_* 𝒪_X` (`Over.universalSections`) read as an on-the-nose base-change statement:
`H⁰(C_R, 𝒪) = R = R ⊗_k k = H⁰(C, 𝒪) ⊗_k R`, the degree-zero case of "cohomology commutes
with base change". -/
noncomputable def relStructureSectionsTop : Γ(relCurve C R, ⊤) ≃+* R :=
  (Over.universalSectionsEquiv C R).symm

end StandingBundle

end AlgebraicGeometry
