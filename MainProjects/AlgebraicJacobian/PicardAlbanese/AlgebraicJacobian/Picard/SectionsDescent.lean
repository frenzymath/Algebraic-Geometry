/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.AmitsurEqualizer
import AlgebraicJacobian.Picard.WitnessAway
import AlgebraicJacobian.Picard.SpecDegeneracy

/-!
# Faithfully flat descent of sections along the curve-side base change (ζ3 brick D)

For a tower of `k`-algebras `k → A → B` with `A → B` faithfully flat and any `C` over
`Spec k`, the base-change morphism `cg : (C ⊗ Spec B).left ⟶ (C ⊗ Spec A).left`
(`C ◁ Spec (ofId A B)`) is a faithfully flat cover, and the structure sheaf satisfies
descent along it: a section of `C ⊗ Spec B` over the preimage of an **affine** open
`U ⊆ (C ⊗ Spec A).left` whose two pullbacks to `C ⊗ Spec (B ⊗[A] B)` agree descends
uniquely to a section over `U` (`AlgebraicGeometry.Over.existsUnique_appLE_eq`), and
likewise for unit sections (`Over.exists_unitsAppLE_eq`).  Pullback of sections along
`cg` is injective over **arbitrary** opens (`Over.appLE_whiskerLeft_injective`).

This is the "fppf sheaf property of `𝒪`/`𝒪ˣ` along `cg`" consumed by the final glue of
the (C1) étale-separatedness kernel lemma (`AlgebraicJacobian.Picard.CechKernelGlue`
and `AlgebraicJacobian.Picard.CechKernelLemma`): there, a trivializing unit for a Čech
class killed by `cg^*` is corrected until its two pullbacks agree and then descended
through this file.

## Route

* `AlgebraicGeometry.Over.isPullback_whiskerLeft_snd`: for any `g : T' ⟶ T` over
  `Spec k`, the square `(C ◁ g).left, (snd C T').left, (snd C T).left, g.left` is a
  pullback — pasting of the two product squares `Over.isPullback_left`.
* `Module.FaithfullyFlat.existsUnique_tmul_one_eq` (imported from
  `AlgebraicJacobian.Descent.AmitsurEqualizer`): the degree-`0` Amitsur equalizer for
  `S₀ ⊗[A] B ⇉ S₀ ⊗[A] (B ⊗[A] B)`.
* The two mathlib pushout-sections squares (`isIso_pushoutSection_of_isAffineOpen`) for
  the pullback squares at `B` and `B ⊗[A] B`, re-cornered from `Γ(Spec A, ⊤)`/`Γ(Spec
  B, ⊤)` to `A`/`B` along `ΓSpecIso` and compared with the tensor-product pushout
  (`CommRingCat.isPushout_tensorProduct`); the two coprojection triangles identify the
  scheme-side pullbacks `u₁^♯, u₂^♯` with `id ⊗ inl, id ⊗ inr` on tensors.

The `A`-algebra structure on `Γ((C ⊗ Spec A).left, U)` used throughout is the composite
of the projection pullback with `ΓSpecIso` (`Over.sectionsAlgebraA`); it is a scoped
instance of this file, reactivated by consumers.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-! ## The base-change pullback square on the curve product -/

namespace Over

/-- **The base-change square of the product is a pullback**: for `C, T, T'` over
`Spec k` and `g : T' ⟶ T`, the square

```
(C ⊗ T').left --(C ◁ g).left--> (C ⊗ T).left
     |  (snd C T').left               |  (snd C T).left
  T'.left --------g.left--------> T.left
```

is a pullback of schemes — pasting of the two product squares `Over.isPullback_left`
along the first-projection triangle `(C ◁ g).left ≫ (fst C T).left = (fst C T').left`. -/
theorem isPullback_whiskerLeft_snd (C : Over (Spec (.of k))) {T T' : Over (Spec (.of k))}
    (g : T' ⟶ T) :
    IsPullback (C ◁ g).left (snd C T').left (snd C T).left g.left := by
  refine IsPullback.of_right ?_ (snd_left_naturality C g) (Over.isPullback_left C T)
  have h₁ : (C ◁ g).left ≫ (fst C T).left = (fst C T').left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have h₂ : g.left ≫ T.hom = T'.hom := Over.w g
  rw [h₁, h₂]
  exact Over.isPullback_left C T'

end Over

/-! ## The concrete tower `k → A → B` -/

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k)))

set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "XBB" => (C ⊗ overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "gA" => Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)
set_option quotPrecheck false in
local notation "gA₂" => Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k)
set_option quotPrecheck false in
local notation "cg" => (C ◁ (gA)).left
set_option quotPrecheck false in
local notation "cg₂" => (C ◁ (gA₂)).left
set_option quotPrecheck false in
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "pA" => (snd C (overSpec k A)).left
set_option quotPrecheck false in
local notation "pB" => (snd C (overSpec k B)).left
set_option quotPrecheck false in
local notation "pBB" => (snd C (overSpec k (B ⊗[A] B))).left

namespace Over

/-! ### The coprojection composites -/

/-- Ring level: the first coprojection after the base inclusion is the base inclusion
of the tensor square. -/
lemma tensorInl_comp_ofId_eq_ofId :
    (tensorInl (A := A) (B := B)).comp ((Algebra.ofId A B).restrictScalars k)
      = (Algebra.ofId A (B ⊗[A] B)).restrictScalars k := by
  ext a
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.ofId_apply, tensorInl]
  exact (Algebra.TensorProduct.includeLeft (S := A)).commutes a

/-- Ring level: the second coprojection after the base inclusion is the base inclusion
of the tensor square. -/
lemma tensorInr_comp_ofId_eq_ofId :
    (tensorInr (A := A) (B := B)).comp ((Algebra.ofId A B).restrictScalars k)
      = (Algebra.ofId A (B ⊗[A] B)).restrictScalars k := by
  rw [← tensorInl_comp_ofId_eq_ofId, tensorInl_comp_ofId]

/-- `Spec` level, whiskered: `u₁ ≫ cg = cg₂`. -/
lemma whiskerLeft_inl_comp_ofId :
    (u₁) ≫ (cg) = (cg₂) := by
  rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp,
    tensorInl_comp_ofId_eq_ofId]

/-- `Spec` level, whiskered: `u₂ ≫ cg = cg₂`. -/
lemma whiskerLeft_inr_comp_ofId :
    (u₂) ≫ (cg) = (cg₂) := by
  rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← Over.overSpecMap_comp,
    tensorInr_comp_ofId_eq_ofId]

/-- The preimage of an open of `C ⊗ Spec A` under `cg₂` is the `u₁`-preimage of its
`cg`-preimage. -/
lemma cg₂_preimage_eq_inl (U : (XA).Opens) :
    (cg₂) ⁻¹ᵁ U = (u₁) ⁻¹ᵁ ((cg) ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, whiskerLeft_inl_comp_ofId]

/-- The preimage of an open of `C ⊗ Spec A` under `cg₂` is the `u₂`-preimage of its
`cg`-preimage. -/
lemma cg₂_preimage_eq_inr (U : (XA).Opens) :
    (cg₂) ⁻¹ᵁ U = (u₂) ⁻¹ᵁ ((cg) ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, whiskerLeft_inr_comp_ofId]

/-! ### The section-ring pushout squares, re-cornered to `A` and `B` -/

/-- The `A`-algebra structure on sections of `C ⊗ Spec A`: pull back along the second
projection through `ΓSpecIso`.  A scoped instance; consumers reactivate it with
`attribute [local instance] Over.sectionsAlgebraA`. -/
@[reducible] noncomputable def sectionsAlgebraA (U : (XA).Opens) : Algebra A Γ(XA, U) :=
  ((Scheme.ΓSpecIso (.of A)).inv
    ≫ (pA).appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top (pA)).ge)).hom.toAlgebra

attribute [local instance] sectionsAlgebraA

/-- Unfolding lemma for `Over.sectionsAlgebraA`. -/
lemma ofHom_algebraMap_sectionsA (U : (XA).Opens) :
    CommRingCat.ofHom (algebraMap A Γ(XA, U))
      = (Scheme.ΓSpecIso (.of A)).inv
          ≫ (pA).appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top (pA)).ge) :=
  rfl

section pushout

variable {C}
variable {R : Type u} [CommRing R] [Algebra k R] [Algebra A R] [IsScalarTower k A R]

/-- The mathlib pushout-sections square for the base-change square of the tower
`A → R`, with the `Spec R`-side at `⊤` and an affine open `U` on the product side. -/
private lemma isPushout_sections_gen {U : (XA).Opens} (hU : IsAffineOpen U) :
    IsPushout
      ((pA).appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top (pA)).ge))
      ((Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left.appLE ⊤ ⊤
        (Scheme.Hom.preimage_top (Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left).ge)
      ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left.appLE U
        ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U) le_rfl)
      ((snd C (overSpec k R)).left.appLE ⊤
        ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U)
        (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k R)).left).ge)) := by
  have H := Over.isPullback_whiskerLeft_snd C
    (Over.overSpecMap ((Algebra.ofId A R).restrictScalars k))
  have hUY : (C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U
      = (C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U
        ⊓ (snd C (overSpec k R)).left ⁻¹ᵁ (⊤ : ((overSpec k R).left).Opens) := by
    rw [Scheme.Hom.preimage_top, inf_top_eq]
  have h := isIso_pushoutSection_of_isAffineOpen H
    (le_top.trans
      (Scheme.Hom.preimage_top (Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left).ge)
    (le_top.trans (Scheme.Hom.preimage_top (pA)).ge) hUY
    (isAffineOpen_top_overSpec k A) (isAffineOpen_top_overSpec k R) hU
  exact (isIso_pushoutSection_iff _ _ _ _).mp h

/-- The pushout-sections square re-cornered to `A` and `R`: the `Γ(Spec A, ⊤)` and
`Γ(Spec R, ⊤)` corners are replaced by `A` and `R` along `ΓSpecIso`. -/
private lemma isPushout_algebraMap_gen {U : (XA).Opens} (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (algebraMap A Γ(XA, U)))
      (CommRingCat.ofHom (algebraMap A R))
      ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left.appLE U
        ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U) le_rfl)
      ((Scheme.ΓSpecIso (.of R)).inv
        ≫ (snd C (overSpec k R)).left.appLE ⊤
          ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U)
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k R)).left).ge)) := by
  refine (isPushout_sections_gen hU).of_iso
    (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Scheme.ΓSpecIso (.of R)) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [ofHom_algebraMap_sectionsA]
    exact (Iso.hom_inv_id_assoc _ _).symm
  · have h : (Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left.appLE ⊤ ⊤
        (Scheme.Hom.preimage_top (Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left).ge
        = (Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left.appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [h, Over.overSpecMap_left]
    have hφ : CommRingCat.ofHom ((Algebra.ofId A R).restrictScalars k).toRingHom
        = CommRingCat.ofHom (algebraMap A R) := rfl
    rw [hφ]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A R))
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id]
    exact (Iso.hom_inv_id_assoc _ _).symm

/-- The comparison isomorphism `Γ(XA, U) ⊗[A] R ≅ Γ((C ⊗ Spec R).left, preimage of U)`
for an affine open `U`, along the base-change square of the tower `A → R`. -/
private noncomputable def sectionsPushoutIso {U : (XA).Opens} (hU : IsAffineOpen U) :
    CommRingCat.of (Γ(XA, U) ⊗[A] R)
      ≅ Γ((C ⊗ overSpec k R).left,
          (C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U) :=
  (CommRingCat.isPushout_tensorProduct A Γ(XA, U) R).isoIsPushout _ _
    (isPushout_algebraMap_gen hU)

private lemma sectionsPushoutIso_tmul_one {U : (XA).Opens} (hU : IsAffineOpen U) (s : Γ(XA, U)) :
    (sectionsPushoutIso (R := R) hU).hom (s ⊗ₜ 1)
      = (C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left.appLE U
          ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U) le_rfl s :=
  congr($((CommRingCat.isPushout_tensorProduct A Γ(XA, U) R).inl_isoIsPushout_hom
    _ _ (isPushout_algebraMap_gen hU)).hom s)

private lemma sectionsPushoutIso_one_tmul {U : (XA).Opens} (hU : IsAffineOpen U) (r : R) :
    (sectionsPushoutIso (R := R) hU).hom (1 ⊗ₜ r)
      = ((Scheme.ΓSpecIso (.of R)).inv
          ≫ (snd C (overSpec k R)).left.appLE ⊤
            ((C ◁ Over.overSpecMap ((Algebra.ofId A R).restrictScalars k)).left ⁻¹ᵁ U)
            (le_top.trans
              (Scheme.Hom.preimage_top (snd C (overSpec k R)).left).ge)) r :=
  congr($((CommRingCat.isPushout_tensorProduct A Γ(XA, U) R).inr_isoIsPushout_hom
    _ _ (isPushout_algebraMap_gen hU)).hom r)

end pushout

/-! ### The coprojection face triangles -/

/-- Congruence in the morphism for `appLE`. -/
private lemma appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (V : Y.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    f.appLE V U e = g.appLE V U (h ▸ e) := by
  subst h; rfl

section faceTriangle

variable {C}

/-- **The coprojection face triangle**: under the pushout identifications, pullback of
sections along a whiskered coprojection `C ◁ Spec σ` (`σ` one of the two coprojections
`B → B ⊗[A] B`) is the algebra face `id ⊗ ρ` on tensors. -/
private lemma faceTriangle {U : (XA).Opens} (hU : IsAffineOpen U)
    (σ : B →ₐ[k] B ⊗[A] B) (ρ : B →ₐ[A] B ⊗[A] B) (hσρ : σ.toRingHom = ρ.toRingHom)
    (hcomp : (C ◁ Over.overSpecMap σ).left ≫ (cg) = (cg₂))
    (e : (cg₂) ⁻¹ᵁ U ≤ (C ◁ Over.overSpecMap σ).left ⁻¹ᵁ ((cg) ⁻¹ᵁ U)) :
    (sectionsPushoutIso (R := B) hU).hom
        ≫ (C ◁ Over.overSpecMap σ).left.appLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) e
      = CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A Γ(XA, U)) ρ).toRingHom
          ≫ (sectionsPushoutIso (R := B ⊗[A] B) hU).hom := by
  refine (CommRingCat.isPushout_tensorProduct A Γ(XA, U) B).hom_ext ?_ ?_
  · -- the `Γ(XA, U)`-leg: both composites are `cg₂^♯`
    ext s
    have hL : ((sectionsPushoutIso (C := C) (R := B) hU).hom.hom (s ⊗ₜ 1))
        = ((cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl).hom s :=
      sectionsPushoutIso_tmul_one (C := C) (R := B) hU s
    have hR : Algebra.TensorProduct.map (AlgHom.id A Γ(XA, U)) ρ (s ⊗ₜ 1)
        = s ⊗ₜ (1 : B ⊗[A] B) := by
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]
    change ((C ◁ Over.overSpecMap σ).left.appLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) e).hom
        ((sectionsPushoutIso (C := C) (R := B) hU).hom.hom (s ⊗ₜ 1))
      = (sectionsPushoutIso (C := C) (R := B ⊗[A] B) hU).hom.hom
          (Algebra.TensorProduct.map (AlgHom.id A Γ(XA, U)) ρ (s ⊗ₜ 1))
    rw [hL, hR, sectionsPushoutIso_tmul_one (C := C) (R := B ⊗[A] B) hU s,
      ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom hcomp U ((cg₂) ⁻¹ᵁ U) _]
  · -- the `B`-leg: both composites factor through `Spec` of the coprojection
    ext b
    have hR : Algebra.TensorProduct.map (AlgHom.id A Γ(XA, U)) ρ
        ((1 : Γ(XA, U)) ⊗ₜ b) = (1 : Γ(XA, U)) ⊗ₜ ρ b := by
      rw [Algebra.TensorProduct.map_tmul, map_one]
    change ((C ◁ Over.overSpecMap σ).left.appLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) e).hom
        ((sectionsPushoutIso (C := C) (R := B) hU).hom.hom (1 ⊗ₜ b))
      = (sectionsPushoutIso (C := C) (R := B ⊗[A] B) hU).hom.hom
          (Algebra.TensorProduct.map (AlgHom.id A Γ(XA, U)) ρ (1 ⊗ₜ b))
    have hψB := sectionsPushoutIso_one_tmul (C := C) (R := B) hU b
    rw [CommRingCat.comp_apply] at hψB
    have hψBB := sectionsPushoutIso_one_tmul (C := C) (R := B ⊗[A] B) hU (ρ b)
    rw [CommRingCat.comp_apply] at hψBB
    rw [hR, hψB, hψBB]
    -- both sides are now applications to `ΓSpecIso.inv`-values; chain the composites
    set z := (Scheme.ΓSpecIso (.of B)).inv.hom b with hz
    have l₀ : ((C ◁ Over.overSpecMap σ).left.appLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) e).hom
          (((pB).appLE ⊤ ((cg) ⁻¹ᵁ U)
            (le_top.trans (Scheme.Hom.preimage_top (pB)).ge)).hom z)
        = (((pB).appLE ⊤ ((cg) ⁻¹ᵁ U)
              (le_top.trans (Scheme.Hom.preimage_top (pB)).ge))
            ≫ (C ◁ Over.overSpecMap σ).left.appLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) e).hom z :=
      (CommRingCat.comp_apply _ _ _).symm
    have l₁ := congr($(Scheme.Hom.appLE_comp_appLE
      ((C ◁ Over.overSpecMap σ).left) (pB) ⊤ ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U)
      (le_top.trans (Scheme.Hom.preimage_top (pB)).ge) e).hom z)
    have l₂ := congr($(appLE_congr_hom
      (Over.snd_left_naturality C (Over.overSpecMap σ)) ⊤ ((cg₂) ⁻¹ᵁ U)
      (e.trans ((Opens.map _).map (homOfLE
        (le_top.trans (Scheme.Hom.preimage_top (pB)).ge))).le)).hom z)
    have l₃ := congr($(Scheme.Hom.appLE_comp_appLE
      (pBB) ((Over.overSpecMap σ).left) ⊤ ⊤ ((cg₂) ⁻¹ᵁ U)
      (Scheme.Hom.preimage_top (Over.overSpecMap σ).left).ge
      (le_top.trans (Scheme.Hom.preimage_top (pBB)).ge)).hom z)
    rw [CommRingCat.comp_apply] at l₃
    have l₄ : (((Over.overSpecMap σ).left).appLE ⊤ ⊤
          (Scheme.Hom.preimage_top (Over.overSpecMap σ).left).ge).hom z
        = (Scheme.ΓSpecIso (.of (B ⊗[A] B))).inv.hom (ρ b) := by
      rw [show ((Over.overSpecMap σ).left).appLE ⊤ ⊤
            (Scheme.Hom.preimage_top (Over.overSpecMap σ).left).ge
          = ((Over.overSpecMap σ).left).appTop from Scheme.Hom.appLE_eq_app _, hz]
      have hnat := ΓSpecIso_inv_appTop (CommRingCat.ofHom σ.toRingHom) b
      rw [show (CommRingCat.ofHom σ.toRingHom).hom b = ρ b from
        DFunLike.congr_fun hσρ b] at hnat
      exact hnat
    exact (l₀.trans l₁).trans (l₂.trans (l₃.symm.trans (congrArg _ l₄)))

end faceTriangle

/-! ### Descent of sections and of unit sections along `cg` -/

section descent

variable {C}
variable [Module.FaithfullyFlat A B]

attribute [local instance] Over.sectionsAlgebraA

/-- **Faithfully flat descent of sections along the base change of the curve product**
(brick D of the ζ3 close): a section of `C ⊗ Spec B` over the preimage of an affine open
`U` of `C ⊗ Spec A` whose two coprojection pullbacks to `C ⊗ Spec (B ⊗[A] B)` agree
descends uniquely through `cg = (C ◁ Spec (ofId A B)).left`. -/
theorem existsUnique_appLE_eq {U : (XA).Opens} (hU : IsAffineOpen U)
    (t : Γ(XB, (cg) ⁻¹ᵁ U))
    (ht : ((u₁).appLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) (cg₂_preimage_eq_inl C U).le).hom t
        = ((u₂).appLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) (cg₂_preimage_eq_inr C U).le).hom t) :
    ∃! s : Γ(XA, U), ((cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl).hom s = t := by
  classical
  set eB := (sectionsPushoutIso (C := C) (R := B) hU).commRingCatIsoToRingEquiv with heB
  set eBB := (sectionsPushoutIso (C := C) (R := B ⊗[A] B) hU).commRingCatIsoToRingEquiv
    with heBB
  set x : Γ(XA, U) ⊗[A] B := eB.symm t with hx
  -- transport the equalizer hypothesis through the face triangles
  have htriangle : ∀ (σ : B →ₐ[k] B ⊗[A] B) (ρ : B →ₐ[A] B ⊗[A] B)
      (hσρ : σ.toRingHom = ρ.toRingHom)
      (hcomp : (C ◁ Over.overSpecMap σ).left ≫ (cg) = (cg₂))
      (e : (cg₂) ⁻¹ᵁ U ≤ (C ◁ Over.overSpecMap σ).left ⁻¹ᵁ ((cg) ⁻¹ᵁ U)),
      ((C ◁ Over.overSpecMap σ).left.appLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) e).hom t
        = eBB (Algebra.TensorProduct.map (AlgHom.id A Γ(XA, U)) ρ x) := by
    intro σ ρ hσρ hcomp e
    have h := congr($(faceTriangle (C := C) hU σ ρ hσρ hcomp e).hom x)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
    have hex : (sectionsPushoutIso (C := C) (R := B) hU).hom.hom x = t := by
      rw [hx]
      exact eB.apply_symm_apply t
    rw [hex] at h
    exact h
  have hfaces : Algebra.TensorProduct.map (AlgHom.id A Γ(XA, U))
        (Module.descentIncl₁ A B) x
      = Algebra.TensorProduct.map (AlgHom.id A Γ(XA, U)) (Module.descentIncl₂ A B) x := by
    apply eBB.injective
    rw [← htriangle (tensorInl (A := A) (B := B)) (Module.descentIncl₁ A B) rfl
        (Over.whiskerLeft_inl_comp_ofId C) (cg₂_preimage_eq_inl C U).le,
      ← htriangle (tensorInr (A := A) (B := B)) (Module.descentIncl₂ A B) rfl
        (Over.whiskerLeft_inr_comp_ofId C) (cg₂_preimage_eq_inr C U).le]
    exact ht
  -- the Amitsur equalizer
  obtain ⟨s, hs, huniq⟩ :=
    Module.FaithfullyFlat.existsUnique_tmul_one_eq (A := A) (B := B) x hfaces
  have hval : ∀ s' : Γ(XA, U),
      ((cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl).hom s' = eB (s' ⊗ₜ 1) := by
    intro s'
    exact (sectionsPushoutIso_tmul_one (C := C) (R := B) hU s').symm
  refine ⟨s, ?_, ?_⟩
  · change ((cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl).hom s = t
    rw [hval s, hs, hx]
    exact eB.apply_symm_apply t
  · intro s' hs'
    replace hs' : ((cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl).hom s' = t := hs'
    refine huniq s' ?_
    change s' ⊗ₜ[A] (1 : B) = x
    apply eB.injective
    rw [← hval s', hs', hx]
    exact (eB.apply_symm_apply t).symm

/-- Pullback of sections along `cg` is injective over an affine open. -/
theorem appLE_whiskerLeft_injective_of_isAffineOpen {U : (XA).Opens}
    (hU : IsAffineOpen U) :
    Function.Injective ((cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl).hom := by
  intro s s' hss
  have hval : ∀ s'' : Γ(XA, U),
      ((cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl).hom s''
        = (sectionsPushoutIso (C := C) (R := B) hU).commRingCatIsoToRingEquiv
            (s'' ⊗ₜ 1) := fun s'' ↦
    (sectionsPushoutIso_tmul_one (C := C) (R := B) hU s'').symm
  have h1 : (s ⊗ₜ[A] (1 : B) : Γ(XA, U) ⊗[A] B) = s' ⊗ₜ[A] 1 := by
    apply (sectionsPushoutIso (C := C) (R := B) hU).commRingCatIsoToRingEquiv.injective
    rw [← hval s, ← hval s', hss]
  have h2 := congrArg (TensorProduct.comm A Γ(XA, U) B) h1
  rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul] at h2
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) Γ(XA, U) h2

/-- Pullback of sections along `cg` is injective over **arbitrary** opens, by sheaf
separation from the affine case. -/
theorem appLE_whiskerLeft_injective (W : (XA).Opens) :
    Function.Injective ((cg).appLE W ((cg) ⁻¹ᵁ W) le_rfl).hom := by
  intro s t hst
  refine (XA).sheaf.eq_of_locally_eq'
    (fun V : {V : (XA).Opens // IsAffineOpen V ∧ V ≤ W} ↦ V.1) W
    (fun V ↦ homOfLE V.2.2) (fun w hw ↦ ?_) s t (fun V ↦ ?_)
  · obtain ⟨V, hVaff, hwV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (XA).isBasis_affineOpens hw
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVaff, hVW⟩, hwV⟩
  · have hres := congrArg ((XB).presheaf.map (homOfLE
      (show (cg) ⁻¹ᵁ V.1 ≤ (cg) ⁻¹ᵁ W from fun x hx ↦ V.2.2 hx)).op).hom hst
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map] at hres
    have key : ((cg).appLE V.1 ((cg) ⁻¹ᵁ V.1) le_rfl).hom
          (((XA).presheaf.map (homOfLE V.2.2).op).hom s)
        = ((cg).appLE V.1 ((cg) ⁻¹ᵁ V.1) le_rfl).hom
          (((XA).presheaf.map (homOfLE V.2.2).op).hom t) := by
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      exact hres
    exact appLE_whiskerLeft_injective_of_isAffineOpen (C := C) V.2.1 key

/-- **Faithfully flat descent of unit sections along the base change of the curve
product**: the unit-group face of `existsUnique_appLE_eq`. -/
theorem exists_unitsAppLE_eq {U : (XA).Opens} (hU : IsAffineOpen U)
    (t : Γ(XB, (cg) ⁻¹ᵁ U)ˣ)
    (ht : (u₁).unitsAppLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) (cg₂_preimage_eq_inl C U).le t
        = (u₂).unitsAppLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U) (cg₂_preimage_eq_inr C U).le t) :
    ∃ s : Γ(XA, U)ˣ, (cg).unitsAppLE U ((cg) ⁻¹ᵁ U) le_rfl s = t := by
  have htval := congrArg Units.val ht
  rw [Scheme.Hom.coe_unitsAppLE, Scheme.Hom.coe_unitsAppLE] at htval
  have ht2 : (u₁).unitsAppLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U)
        (cg₂_preimage_eq_inl C U).le t⁻¹
      = (u₂).unitsAppLE ((cg) ⁻¹ᵁ U) ((cg₂) ⁻¹ᵁ U)
        (cg₂_preimage_eq_inr C U).le t⁻¹ := by
    rw [map_inv, map_inv, ht]
  have htval' := congrArg Units.val ht2
  rw [Scheme.Hom.coe_unitsAppLE, Scheme.Hom.coe_unitsAppLE] at htval'
  obtain ⟨a, ha, -⟩ := existsUnique_appLE_eq (C := C) hU t.val htval
  obtain ⟨b, hb, -⟩ := existsUnique_appLE_eq (C := C) hU (t⁻¹).val htval'
  have hab : a * b = 1 := by
    refine appLE_whiskerLeft_injective_of_isAffineOpen (C := C) (B := B) hU ?_
    rw [map_mul, map_one, ha, hb]
    exact t.mul_inv
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  exact ⟨⟨a, b, hab, hba⟩, Units.ext ha⟩

end descent

end Over

end AlgebraicGeometry
