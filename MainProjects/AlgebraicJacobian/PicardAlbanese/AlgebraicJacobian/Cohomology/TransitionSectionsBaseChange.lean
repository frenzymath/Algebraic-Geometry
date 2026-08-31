/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.BaseFieldTransition

/-!
# Base change of sections along the base-field transition (gap G-D5(b), SB-2)

For the challenge curve `C : Over (Spec k)` (`k` a field), field extensions `K₁ K₂` of `k`,
a `k`-algebra map `φ : K₁ →ₐ[k] K₂`, and the **base-field transition**

`π := (C ◁ Over.overSpecMap φ).left : (C ⊗ overSpec k K₂).left ⟶ (C ⊗ overSpec k K₁).left`,

this file identifies the sections of `C_{K₂} := (C ⊗ overSpec k K₂).left` over `π ⁻¹ᵁ V`
with the base change of the sections of `C_{K₁} := (C ⊗ overSpec k K₁).left` over `V`:

`Γ(C_{K₁}, V) ⊗[K₁] K₂ ≃+* Γ(C_{K₂}, π ⁻¹ᵁ V)`

(`AlgebraicGeometry.Over.transitionSectionsBaseChange`), for **affine** `V` — affine `V`
suffices for the whole E-iv-alg campaign (`informal/deg-d5b-worksheet.md` §2, §4 SB-2), so
this file descopes to the affine case throughout.

The `K₁`-algebra structure on `Γ(C_{K₁}, V)` is the one carried by the second-projection
`Over`-structure of `Curve.BaseChangeInstances` (`instOverBaseChange`, i.e.
`(C ⊗ overSpec k K₁).left ↘ Spec K₁ = (snd C (overSpec k K₁)).left`, worksheet risk 3(a)):
concretely `baseChangeSectionsAlgebra C K₁`, which is `Over.sectionsAlgebra` of the bundled
curve `Over.mk (snd C (overSpec k K₁)).left` but keyed on the `(C ⊗ overSpec k K₁).left`
spelling so typeclass resolution finds it.

## Template and engine

The template is the landed `Cohomology.SectionsBaseChange`; this file re-runs its (short)
proof pattern against the **pasted pullback square** `isPullback_baseFieldTransition` of
`Curve.BaseFieldTransition` (worksheet D3) in place of `Over.isPullback_left`. The engine is
mathlib's pushout-sections machinery on affine opens, `isIso_pushoutSection_of_isAffineOpen`.
As the worksheet warns, we do **not** instantiate the landed `Over.sectionsBaseChange` at base
`K₁` and transport along a scheme iso — that would manufacture the shuffle iso D1 avoids.

## Main declarations

* `AlgebraicGeometry.Over.isPushout_transitionSections_of_isAffineOpen` — the raw pushout
  square of section rings (no algebra structure; general `φ`), the direct analogue of
  `Over.isPushout_sections_of_isAffineOpen`.
* `AlgebraicGeometry.Over.isPushout_algebraMap_transitionSections` — the same square with the
  `Γ(Spec K₁, ⊤)`/`Γ(Spec K₂, ⊤)` corners replaced by `K₁`/`K₂`; the top edge is
  `algebraMap K₁ Γ(C_{K₁}, V)`, the left edge is `φ` (general `φ`, **no** `Algebra K₁ K₂`
  needed). This is the pushout-square form the downstream colength assembly consumes directly
  (worksheet SB-2 fallback), combining it with `CommRingCat.isPushout_tensorProduct`.
* `AlgebraicGeometry.Over.transitionSectionsBaseChangeIso`,
  `AlgebraicGeometry.Over.transitionSectionsBaseChange` — the comparison isomorphism (in
  `CommRingCat`, resp. as a ring equivalence) for a tower `[Algebra K₁ K₂] [IsScalarTower k
  K₁ K₂]` with `φ = IsScalarTower.toAlgHom k K₁ K₂`, with the computation rules
  `transitionSectionsBaseChange_tmul_one`, `_one_tmul`, `_tmul` and the restriction
  naturality `transitionSectionsBaseChange_naturality`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct

namespace AlgebraicGeometry

section Transition

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  {K₁ K₂ : Type u} [Field K₁] [Algebra k K₁] [Field K₂] [Algebra k K₂]

/-! ## The raw pushout square of section rings -/

/-- **Base change of sections along the transition, raw form.** For an affine open
`V ⊆ (C ⊗ overSpec k K₁).left`, the square of section rings

```
Γ(Spec K₁, ⊤) ⟶ Γ(C_{K₁}, V)
     |               |
     ↓               ↓
Γ(Spec K₂, ⊤) ⟶ Γ(C_{K₂}, π ⁻¹ᵁ V)
```

(top = second projection of `C_{K₁}`, left = `Spec.map φ`, bottom = the transition `π`,
right = second projection of `C_{K₂}`) is a pushout of commutative rings. No flatness is
needed in the affine case; the pasted square `isPullback_baseFieldTransition` feeds the
engine `isIso_pushoutSection_of_isAffineOpen`. -/
theorem Over.isPushout_transitionSections_of_isAffineOpen (φ : K₁ →ₐ[k] K₂)
    {V : (C ⊗ overSpec k K₁).left.Opens} (hV : IsAffineOpen V) :
    IsPushout
      ((snd C (overSpec k K₁)).left.appLE ⊤ V
        (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k K₁)).left).ge))
      ((Spec.map (CommRingCat.ofHom φ.toRingHom)).appLE ⊤ ⊤
        (Scheme.Hom.preimage_top (Spec.map (CommRingCat.ofHom φ.toRingHom))).ge)
      ((C ◁ Over.overSpecMap φ).left.appLE V ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl)
      ((snd C (overSpec k K₂)).left.appLE ⊤ ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V)
        (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k K₂)).left).ge)) := by
  have hUST : (⊤ : (overSpec k K₂).left.Opens) ≤
      Spec.map (CommRingCat.ofHom φ.toRingHom) ⁻¹ᵁ (⊤ : (overSpec k K₁).left.Opens) :=
    (Scheme.Hom.preimage_top _).ge
  have hUSX : V ≤ (snd C (overSpec k K₁)).left ⁻¹ᵁ (⊤ : (overSpec k K₁).left.Opens) :=
    le_top.trans (Scheme.Hom.preimage_top _).ge
  have hUY : (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V =
      (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V ⊓
        (snd C (overSpec k K₂)).left ⁻¹ᵁ (⊤ : (overSpec k K₂).left.Opens) := by
    rw [Scheme.Hom.preimage_top, inf_top_eq]
  have h := isIso_pushoutSection_of_isAffineOpen (isPullback_baseFieldTransition C φ)
    hUST hUSX hUY (isAffineOpen_top_overSpec k K₁) (isAffineOpen_top_overSpec k K₂) hV
  exact (isIso_pushoutSection_iff _ _ _ _).mp h

/-! ## The `K₁`-algebra structure on sections and the algebra corner -/

/-- `C_K := (C ⊗ overSpec k K).left` as a bundled object of `Over (Spec K)` via the
**second projection** (the `Curve.BaseChangeInstances` structure morphism); its `.left` is
`(C ⊗ overSpec k K).left` and its `.hom` is `(snd C (overSpec k K)).left`, both by `rfl`. -/
noncomputable abbrev baseChangeBundle (K : Type u) [Field K] [Algebra k K] :
    Over (Spec (.of K)) :=
  Over.mk (snd C (overSpec k K)).left

/-- **The `K`-algebra structure on sections of the base-changed curve** `C_K`, via the
second-projection `Over`-structure (worksheet risk 3(a)): `Over.sectionsAlgebra` of the
bundled curve `baseChangeBundle C K`, keyed on the `(C ⊗ overSpec k K).left` spelling so
typeclass resolution finds it. Activated as a local instance below. -/
@[reducible] noncomputable def baseChangeSectionsAlgebra (K : Type u) [Field K] [Algebra k K]
    (V : (C ⊗ overSpec k K).left.Opens) : Algebra K Γ((C ⊗ overSpec k K).left, V) :=
  Over.sectionsAlgebra (baseChangeBundle C K) V

attribute [local instance] baseChangeSectionsAlgebra Over.sectionsAlgebra

/-- The algebra structure map `K → Γ(C_K, V)` of `baseChangeSectionsAlgebra`, as a morphism of
`CommRingCat`, is the second projection on sections (preceded by `ΓSpecIso`). This is the
`rfl`-bridge `Over.ofHom_algebraMap_sections` for the bundled curve, keyed on the
`(C ⊗ overSpec k K).left` spelling. -/
lemma ofHom_algebraMap_baseChangeSections (K : Type u) [Field K] [Algebra k K]
    (V : (C ⊗ overSpec k K).left.Opens) :
    CommRingCat.ofHom (algebraMap K Γ((C ⊗ overSpec k K).left, V)) =
      (Scheme.ΓSpecIso (.of K)).inv ≫
        (snd C (overSpec k K)).left.appLE ⊤ V
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k K)).left).ge) :=
  Over.ofHom_algebraMap_sections (baseChangeBundle C K) V

set_option backward.isDefEq.respectTransparency false in
/-- The algebra structure maps of `baseChangeSectionsAlgebra` intertwine restriction. -/
lemma ofHom_algebraMap_baseChangeSections_comp_res (K : Type u) [Field K] [Algebra k K]
    {V W : (C ⊗ overSpec k K).left.Opens} (hWV : W ≤ V) :
    CommRingCat.ofHom (algebraMap K Γ((C ⊗ overSpec k K).left, V)) ≫
        (C ⊗ overSpec k K).left.presheaf.map (homOfLE hWV).op =
      CommRingCat.ofHom (algebraMap K Γ((C ⊗ overSpec k K).left, W)) := by
  rw [ofHom_algebraMap_baseChangeSections, ofHom_algebraMap_baseChangeSections, Category.assoc,
    Scheme.Hom.appLE_map]

/-- **Restriction of sections of `C_K` along `W ≤ V`, as a `K`-algebra homomorphism** for the
second-projection `baseChangeSectionsAlgebra`.  This is `Over.resAlgHom` of the bundled curve,
but keyed on the clean `(C ⊗ overSpec k K).left` spelling. -/
noncomputable def baseChangeResAlgHom (K : Type u) [Field K] [Algebra k K]
    {V W : (C ⊗ overSpec k K).left.Opens} (hWV : W ≤ V) :
    Γ((C ⊗ overSpec k K).left, V) →ₐ[K] Γ((C ⊗ overSpec k K).left, W) where
  __ := ((C ⊗ overSpec k K).left.presheaf.map (homOfLE hWV).op).hom
  commutes' r := congr($(ofHom_algebraMap_baseChangeSections_comp_res C K hWV).hom r)

@[simp] lemma baseChangeResAlgHom_apply (K : Type u) [Field K] [Algebra k K]
    {V W : (C ⊗ overSpec k K).left.Opens} (hWV : W ≤ V) (s : Γ((C ⊗ overSpec k K).left, V)) :
    baseChangeResAlgHom C K hWV s = (C ⊗ overSpec k K).left.presheaf.map (homOfLE hWV).op s :=
  rfl

/-- **Base change of sections with the `K₁`/`K₂` corners** (worksheet SB-2 fallback square):
for an affine open `V ⊆ (C ⊗ overSpec k K₁).left`, the square

```
   K₁    ⟶ Γ(C_{K₁}, V)
   |          |
   ↓ φ        ↓ π
   K₂    ⟶ Γ(C_{K₂}, π ⁻¹ᵁ V)
```

(top = `algebraMap K₁ Γ(C_{K₁}, V)` for the second-projection algebra structure; left = `φ`;
bottom = the transition `π`) is a pushout of commutative rings. Stated for a general
`φ : K₁ →ₐ[k] K₂` — the left edge is `CommRingCat.ofHom φ.toRingHom`, so **no** `Algebra K₁ K₂`
instance is needed here; the downstream colength assembly can consume this square directly
together with `CommRingCat.isPushout_tensorProduct`. -/
theorem Over.isPushout_algebraMap_transitionSections (φ : K₁ →ₐ[k] K₂)
    {V : (C ⊗ overSpec k K₁).left.Opens} (hV : IsAffineOpen V) :
    IsPushout
      (CommRingCat.ofHom (algebraMap K₁ Γ((C ⊗ overSpec k K₁).left, V)))
      (CommRingCat.ofHom φ.toRingHom)
      ((C ◁ Over.overSpecMap φ).left.appLE V ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl)
      ((Scheme.ΓSpecIso (.of K₂)).inv ≫
        (snd C (overSpec k K₂)).left.appLE ⊤ ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V)
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k K₂)).left).ge)) := by
  refine (Over.isPushout_transitionSections_of_isAffineOpen C φ hV).of_iso
    (Scheme.ΓSpecIso (.of K₁)) (Iso.refl _) (Scheme.ΓSpecIso (.of K₂)) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, ofHom_algebraMap_baseChangeSections]
    exact (Iso.hom_inv_id_assoc _ _).symm
  · have h : (Spec.map (CommRingCat.ofHom φ.toRingHom)).appLE ⊤ ⊤
        (Scheme.Hom.preimage_top (Spec.map (CommRingCat.ofHom φ.toRingHom))).ge =
        (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [h]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · rw [Iso.refl_hom, Category.comp_id]
    exact (Iso.hom_inv_id_assoc _ _).symm

/-! ## The comparison isomorphism (tensor-product form) -/

section TensorIso

variable [Algebra K₁ K₂] [IsScalarTower k K₁ K₂]

/-- **Base change of sections along the base-field transition** (SB-2), as an isomorphism of
`CommRingCat`: `Γ(C_{K₁}, V) ⊗[K₁] K₂ ≅ Γ(C_{K₂}, π ⁻¹ᵁ V)` for an affine open `V`, with
`φ = IsScalarTower.toAlgHom k K₁ K₂`. Built from the algebra-corner pushout square and
`CommRingCat.isPushout_tensorProduct`. -/
noncomputable def Over.transitionSectionsBaseChangeIso {V : (C ⊗ overSpec k K₁).left.Opens}
    (hV : IsAffineOpen V) :
    CommRingCat.of (Γ((C ⊗ overSpec k K₁).left, V) ⊗[K₁] K₂) ≅
      Γ((C ⊗ overSpec k K₂).left,
        (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V) :=
  (CommRingCat.isPushout_tensorProduct K₁ Γ((C ⊗ overSpec k K₁).left, V) K₂).isoIsPushout _ _
    (Over.isPushout_algebraMap_transitionSections C (IsScalarTower.toAlgHom k K₁ K₂) hV)

/-- **Base change of sections along the base-field transition** (SB-2, brick), as a ring
equivalence: `Γ(C_{K₁}, V) ⊗[K₁] K₂ ≃+* Γ(C_{K₂}, π ⁻¹ᵁ V)` for an affine open `V`. On a pure
tensor `s ⊗ a` it is the product of the pullback of `s` along `π` and the pullback of `a`
along the second projection (`transitionSectionsBaseChange_tmul`). The `K₁`-algebra structure
on `Γ(C_{K₁}, V)` is the second-projection `baseChangeSectionsAlgebra`. -/
noncomputable def Over.transitionSectionsBaseChange {V : (C ⊗ overSpec k K₁).left.Opens}
    (hV : IsAffineOpen V) :
    Γ((C ⊗ overSpec k K₁).left, V) ⊗[K₁] K₂ ≃+*
      Γ((C ⊗ overSpec k K₂).left,
        (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V) :=
  (Over.transitionSectionsBaseChangeIso C hV).commRingCatIsoToRingEquiv

theorem Over.transitionSectionsBaseChange_tmul_one {V : (C ⊗ overSpec k K₁).left.Opens}
    (hV : IsAffineOpen V) (s : Γ((C ⊗ overSpec k K₁).left, V)) :
    Over.transitionSectionsBaseChange C hV (s ⊗ₜ 1) =
      (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left.appLE V
        ((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V) le_rfl s :=
  congr($((CommRingCat.isPushout_tensorProduct K₁ Γ((C ⊗ overSpec k K₁).left, V)
    K₂).inl_isoIsPushout_hom _ _
    (Over.isPushout_algebraMap_transitionSections C (IsScalarTower.toAlgHom k K₁ K₂) hV)).hom s)

theorem Over.transitionSectionsBaseChange_one_tmul {V : (C ⊗ overSpec k K₁).left.Opens}
    (hV : IsAffineOpen V) (a : K₂) :
    Over.transitionSectionsBaseChange C hV (1 ⊗ₜ a) =
      ((Scheme.ΓSpecIso (.of K₂)).inv ≫
        (snd C (overSpec k K₂)).left.appLE ⊤
          ((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V)
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k K₂)).left).ge)) a :=
  congr($((CommRingCat.isPushout_tensorProduct K₁ Γ((C ⊗ overSpec k K₁).left, V)
    K₂).inr_isoIsPushout_hom _ _
    (Over.isPushout_algebraMap_transitionSections C (IsScalarTower.toAlgHom k K₁ K₂) hV)).hom a)

/-- The base-change equivalence on a pure tensor: `s ⊗ a` goes to the product of the pullback
of `s` along the transition `π` and the pullback of `a` along the second projection. -/
theorem Over.transitionSectionsBaseChange_tmul {V : (C ⊗ overSpec k K₁).left.Opens}
    (hV : IsAffineOpen V) (s : Γ((C ⊗ overSpec k K₁).left, V)) (a : K₂) :
    Over.transitionSectionsBaseChange C hV (s ⊗ₜ a) =
      (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left.appLE V
        ((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V) le_rfl s *
      ((Scheme.ΓSpecIso (.of K₂)).inv ≫
        (snd C (overSpec k K₂)).left.appLE ⊤
          ((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V)
          (le_top.trans (Scheme.Hom.preimage_top (snd C (overSpec k K₂)).left).ge)) a := by
  have h : (s ⊗ₜ[K₁] a : Γ((C ⊗ overSpec k K₁).left, V) ⊗[K₁] K₂) = (s ⊗ₜ 1) * (1 ⊗ₜ a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, Over.transitionSectionsBaseChange_tmul_one,
    Over.transitionSectionsBaseChange_one_tmul]

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the base-change equivalence in the open**: for `W ≤ V` (both affine),
restricting the base-changed section is base-changing the restriction. The map on tensor
products is `Algebra.TensorProduct.map` of the restriction `baseChangeResAlgHom` and the
identity of `K₂`. -/
theorem Over.transitionSectionsBaseChange_naturality {V W : (C ⊗ overSpec k K₁).left.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWV : W ≤ V)
    (x : Γ((C ⊗ overSpec k K₁).left, V) ⊗[K₁] K₂) :
    (C ⊗ overSpec k K₂).left.presheaf.map
        (homOfLE (show (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ W ≤
          (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V by gcongr)).op
      (Over.transitionSectionsBaseChange C hV x) =
      Over.transitionSectionsBaseChange C hW
        (Algebra.TensorProduct.map (baseChangeResAlgHom C K₁ hWV) (AlgHom.id K₁ K₂) x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, baseChangeResAlgHom_apply,
      Over.transitionSectionsBaseChange_tmul, Over.transitionSectionsBaseChange_tmul, map_mul]
    congr 1
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
        Scheme.Hom.map_appLE]
    · rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]

end TensorIso

end Transition

end AlgebraicGeometry
