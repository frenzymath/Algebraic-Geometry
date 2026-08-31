/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Base change of sections along the projection `C ⊗ Spec A ⟶ C`

For an object `C` of `Over (Spec k)` (`k` a field), a commutative `k`-algebra `A`, and a
quasi-compact quasi-separated open `V ⊆ C.left`, this file identifies the sections of the
base change `(C ⊗ Spec A).left` over the preimage `V_A := (fst C (Spec A)).left ⁻¹ᵁ V` of
`V` under the first projection with the tensor product of the sections over `V`:

`Γ(C.left, V) ⊗[k] A ≃+* Γ((C ⊗ overSpec k A).left, V_A)`

(`AlgebraicGeometry.Over.sectionsBaseChange`), sending `s ⊗ a` to the product of the two
pullbacks (`sectionsBaseChange_tmul`), compatibly with restriction along `W ≤ V`
(`sectionsBaseChange_naturality`). Here `C ⊗ T` is the cartesian-monoidal product of
`Over (Spec k)`, realized by `Limits.pullback`; the single bridge lemma between the two
languages is `AlgebraicGeometry.Over.isPullback_left`.

This is brick 1 of the separatedness ledger (design §4.4): one brick, three consumers —
étale separatedness (arbitrary `A`), the dual-numbers tangent engine (`A = k[ε]`), and the
χ-ledger under field extension (`A = K`). Hence the statements are for an arbitrary
commutative `k`-algebra `A`, and `V` is allowed to be any quasi-compact quasi-separated
open (e.g. the intersection of two affines of the curve), not just an affine one.

## Main declarations

* `AlgebraicGeometry.Over.isPullback_left` — the bridge: for `X T : Over S`, the scheme-level
  square `(fst X T).left, (snd X T).left, X.hom, T.hom` is a pullback.
* `AlgebraicGeometry.overSpec k A` — `Spec A` as an object of `Over (Spec k)`, together with
  the instance `Flat (overSpec k A).hom` (automatic over a field).
* `AlgebraicGeometry.Over.sectionsAlgebra` — the `k`-algebra structure on `Γ(X.left, V)` by
  restriction of scalars along the structure morphism. Deliberately **not** a global instance
  (house rule, cf. `Scheme.overModule`); consumers activate it with
  `attribute [local instance] Over.sectionsAlgebra`.
* `AlgebraicGeometry.Over.resAlgHom` — restriction of sections as a `k`-algebra homomorphism.
* `AlgebraicGeometry.Over.isPushout_sections_of_isAffineOpen`,
  `AlgebraicGeometry.Over.isPushout_sections` — the master pushout squares on sections, for
  an arbitrary test object `T` with `T.left` affine (affine `V` needs no flatness; qcqs `V`
  needs `[Flat T.hom]`).
* `AlgebraicGeometry.Over.isPushout_algebraMap_sections` — the same square with the
  `Γ(Spec k, ⊤)`/`Γ(Spec A, ⊤)` corners replaced by `k` and `A`.
* `AlgebraicGeometry.Over.sectionsBaseChangeIso`, `AlgebraicGeometry.Over.sectionsBaseChange`
  — the comparison isomorphism (in `CommRingCat`, resp. as a ring equivalence), with the
  computation rules `sectionsBaseChange_tmul_one`, `sectionsBaseChange_one_tmul`,
  `sectionsBaseChange_tmul` and the restriction-naturality
  `sectionsBaseChange_naturality`.

## Implementation notes

The heavy lifting is mathlib's `pushoutSection` API
(`Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`): for a pullback square of schemes the
canonical map `Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, ...)` is an isomorphism for
affine `Uₛ, Uₜ` and qcqs `Uₓ` when `T ⟶ S` is flat — which over a field is automatic.
This file only supplies the Over-category bridge, the corner bookkeeping (`ΓSpecIso`), and
the tensor-product face.

The `k`-linear faces consumers may need are one line away from `sectionsBaseChange`:
it is `k`-algebra-compatible by `sectionsBaseChange_tmul_one` applied to
`algebraMap k Γ(X.left, V) r` (both sides land in the structure-map image), and
`A`-algebra-compatible by `sectionsBaseChange_one_tmul`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct

namespace AlgebraicGeometry

section Bridge

variable {S : Scheme.{u}}

/-- **The bridge between the Over-category product and Scheme-level pullbacks.** For two
objects `X, T` of `Over S`, the underlying scheme of the cartesian-monoidal product
`(X ⊗ T).left` together with the two projections is the fibre product of `X.hom` and
`T.hom`. This is the single point where `C ⊗ Spec A` is unfolded to `Limits.pullback`;
everything downstream consumes this `IsPullback` datum. -/
theorem Over.isPullback_left (X T : Over S) :
    IsPullback (fst X T).left (snd X T).left X.hom T.hom := by
  simp only [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback X.hom T.hom

end Bridge

section OverSpec

variable (k : Type u) [CommRing k] (A : Type u) [CommRing A] [Algebra k A]

/-- `Spec A` as an object of `Over (Spec k)`, for a commutative `k`-algebra `A`. -/
noncomputable abbrev overSpec : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

@[simp]
lemma overSpec_left : (overSpec k A).left = Spec (.of A) := rfl

@[simp]
lemma overSpec_hom :
    (overSpec k A).hom = Spec.map (CommRingCat.ofHom (algebraMap k A)) := rfl

/-- The underlying scheme of `overSpec k A` is affine (it is `Spec A`); form usable where
`IsAffineOpen (⊤ : (overSpec k A).left.Opens)` is expected. -/
lemma isAffineOpen_top_overSpec : IsAffineOpen (⊤ : (overSpec k A).left.Opens) :=
  isAffineOpen_top (Spec (.of A))

/-- Over a field, `Spec A ⟶ Spec k` is flat, for every commutative `k`-algebra `A`. -/
instance flat_overSpec_hom {k : Type u} [Field k] (A : Type u) [CommRing A] [Algebra k A] :
    Flat (overSpec k A).hom :=
  Flat.SpecMap_iff.mpr (by
    rw [CommRingCat.hom_ofHom]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance)

end OverSpec

section Pushout

variable {k : Type u} [Field k] (X T : Over (Spec (.of k)))

/-- **Base change of sections, affine opens.** For `X, T` over `Spec k` with `T.left`
affine and an affine open `V ⊆ X.left`, the square of section rings

```
Γ(Spec k, ⊤) ⟶ Γ(X.left, V)
     |               |
     ↓               ↓
Γ(T.left, ⊤) ⟶ Γ((X ⊗ T).left, fst⁻¹ V)
```

is a pushout of commutative rings. No flatness is needed in the affine case. -/
theorem Over.isPushout_sections_of_isAffineOpen
    (hT : IsAffineOpen (⊤ : T.left.Opens)) {V : X.left.Opens} (hV : IsAffineOpen V) :
    IsPushout (X.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top X.hom).ge))
      (T.hom.appLE ⊤ ⊤ (Scheme.Hom.preimage_top T.hom).ge)
      ((fst X T).left.appLE V ((fst X T).left ⁻¹ᵁ V) le_rfl)
      ((snd X T).left.appLE ⊤ ((fst X T).left ⁻¹ᵁ V)
        (le_top.trans (Scheme.Hom.preimage_top (snd X T).left).ge)) := by
  have hUST : (⊤ : T.left.Opens) ≤ T.hom ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) :=
    (Scheme.Hom.preimage_top T.hom).ge
  have hUSX : V ≤ X.hom ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) :=
    le_top.trans (Scheme.Hom.preimage_top X.hom).ge
  have hUY : (fst X T).left ⁻¹ᵁ V =
      (fst X T).left ⁻¹ᵁ V ⊓ (snd X T).left ⁻¹ᵁ (⊤ : T.left.Opens) := by
    rw [Scheme.Hom.preimage_top, inf_top_eq]
  have h := isIso_pushoutSection_of_isAffineOpen (Over.isPullback_left X T) hUST hUSX hUY
    (isAffineOpen_top _) hT hV
  exact (isIso_pushoutSection_iff _ _ _ _).mp h

/-- **Base change of sections, qcqs opens.** For `X, T` over `Spec k` with `T.hom` flat,
`T.left` affine, and a quasi-compact quasi-separated open `V ⊆ X.left` (e.g. an
intersection of two affine opens of a separated scheme, or all of a proper curve), the
square of section rings

```
Γ(Spec k, ⊤) ⟶ Γ(X.left, V)
     |               |
     ↓               ↓
Γ(T.left, ⊤) ⟶ Γ((X ⊗ T).left, fst⁻¹ V)
```

is a pushout of commutative rings. Flatness of `T.hom` holds automatically for
`T = overSpec k A` (`AlgebraicGeometry.flat_overSpec_hom`). -/
theorem Over.isPushout_sections [Flat T.hom] (hT : IsAffineOpen (⊤ : T.left.Opens))
    {V : X.left.Opens} (hV : IsCompact (V : Set X.left))
    (hV' : IsQuasiSeparated (V : Set X.left)) :
    IsPushout (X.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top X.hom).ge))
      (T.hom.appLE ⊤ ⊤ (Scheme.Hom.preimage_top T.hom).ge)
      ((fst X T).left.appLE V ((fst X T).left ⁻¹ᵁ V) le_rfl)
      ((snd X T).left.appLE ⊤ ((fst X T).left ⁻¹ᵁ V)
        (le_top.trans (Scheme.Hom.preimage_top (snd X T).left).ge)) := by
  have hUST : (⊤ : T.left.Opens) ≤ T.hom ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) :=
    (Scheme.Hom.preimage_top T.hom).ge
  have hUSX : V ≤ X.hom ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) :=
    le_top.trans (Scheme.Hom.preimage_top X.hom).ge
  have hUY : (fst X T).left ⁻¹ᵁ V =
      (fst X T).left ⁻¹ᵁ V ⊓ (snd X T).left ⁻¹ᵁ (⊤ : T.left.Opens) := by
    rw [Scheme.Hom.preimage_top, inf_top_eq]
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (Over.isPullback_left X T) hUST hUSX hUY (isAffineOpen_top _) hT hV hV'
  exact (isIso_pushoutSection_iff _ _ _ _).mp h

end Pushout

section TensorFace

variable {k : Type u} [Field k] (X : Over (Spec (.of k)))

/-- The `k`-algebra structure on `Γ(X.left, V)` for `X` an object of `Over (Spec k)`:
restriction of scalars along the structure morphism `X.hom`. Deliberately **not** a global
instance (it would overlap with mathlib's `Algebra R Γ(Spec R, U)` instances; cf. the house
rule for `Scheme.overModule`). Activate it locally with
`attribute [local instance] Over.sectionsAlgebra` — the statements of this file mention it
explicitly, so consumers must activate the same instance for the statements to elaborate
identically. -/
@[reducible] noncomputable def Over.sectionsAlgebra (V : X.left.Opens) :
    Algebra k Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫
    X.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top X.hom).ge)).hom.toAlgebra

attribute [local instance] Over.sectionsAlgebra

/-- Unfolding lemma for `Over.sectionsAlgebra`: the algebra structure map, as a morphism of
`CommRingCat`, is the structure morphism of `X` on sections. -/
lemma Over.ofHom_algebraMap_sections (V : X.left.Opens) :
    CommRingCat.ofHom (algebraMap k Γ(X.left, V)) =
      (Scheme.ΓSpecIso (.of k)).inv ≫
        X.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top X.hom).ge) :=
  rfl

/-- The algebra structure maps of `Over.sectionsAlgebra` intertwine restriction. -/
lemma Over.algebraMap_sections_comp_res {V W : X.left.Opens} (h : W ≤ V) :
    CommRingCat.ofHom (algebraMap k Γ(X.left, V)) ≫ X.left.presheaf.map (homOfLE h).op =
      CommRingCat.ofHom (algebraMap k Γ(X.left, W)) := by
  rw [Over.ofHom_algebraMap_sections, Over.ofHom_algebraMap_sections, Category.assoc,
    Scheme.Hom.appLE_map]

/-- Restriction of sections along `W ≤ V` as a `k`-algebra homomorphism (with the
`Over.sectionsAlgebra` structures). -/
noncomputable def Over.resAlgHom {V W : X.left.Opens} (h : W ≤ V) :
    Γ(X.left, V) →ₐ[k] Γ(X.left, W) where
  __ := (X.left.presheaf.map (homOfLE h).op).hom
  commutes' r := congr($(Over.algebraMap_sections_comp_res X h).hom r)

@[simp]
lemma Over.resAlgHom_apply {V W : X.left.Opens} (h : W ≤ V) (s : Γ(X.left, V)) :
    Over.resAlgHom X h s = X.left.presheaf.map (homOfLE h).op s :=
  rfl

variable (A : Type u) [CommRing A] [Algebra k A]

/-- **Base change of sections with the `k`/`A` corners.** For a qcqs open `V ⊆ X.left`, the
square

```
   k    ⟶ Γ(X.left, V)
   |         |
   ↓         ↓
   A    ⟶ Γ((X ⊗ Spec A).left, fst⁻¹ V)
```

(with the `Over.sectionsAlgebra` structure map on top and the second-projection pullback
`A ≅ Γ(Spec A, ⊤) ⟶ Γ(..)` at the bottom) is a pushout of commutative rings. -/
theorem Over.isPushout_algebraMap_sections {V : X.left.Opens}
    (hV : IsCompact (V : Set X.left)) (hV' : IsQuasiSeparated (V : Set X.left)) :
    IsPushout (CommRingCat.ofHom (algebraMap k Γ(X.left, V)))
      (CommRingCat.ofHom (algebraMap k A))
      ((fst X (overSpec k A)).left.appLE V ((fst X (overSpec k A)).left ⁻¹ᵁ V) le_rfl)
      ((Scheme.ΓSpecIso (.of A)).inv ≫
        (snd X (overSpec k A)).left.appLE ⊤ ((fst X (overSpec k A)).left ⁻¹ᵁ V)
          (le_top.trans (Scheme.Hom.preimage_top (snd X (overSpec k A)).left).ge)) := by
  refine (Over.isPushout_sections X (overSpec k A)
    (isAffineOpen_top_overSpec k A) hV hV').of_iso
    (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Scheme.ΓSpecIso (.of A)) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [Over.ofHom_algebraMap_sections, Iso.hom_inv_id_assoc]
  · have h : (overSpec k A).hom.appLE ⊤ ⊤ (Scheme.Hom.preimage_top (overSpec k A).hom).ge =
        (overSpec k A).hom.appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [h, overSpec_hom]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k A))
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id]
    exact (Iso.hom_inv_id_assoc _ _).symm

/-- **Base change of sections, comparison isomorphism** (in `CommRingCat`):
`Γ(X.left, V) ⊗[k] A ≅ Γ((X ⊗ Spec A).left, fst⁻¹ V)` for a qcqs open `V ⊆ X.left`.
On pure tensors this is the product of the two pullbacks; see
`Over.sectionsBaseChange_tmul`. -/
noncomputable def Over.sectionsBaseChangeIso {V : X.left.Opens}
    (hV : IsCompact (V : Set X.left)) (hV' : IsQuasiSeparated (V : Set X.left)) :
    CommRingCat.of (Γ(X.left, V) ⊗[k] A) ≅
      Γ((X ⊗ overSpec k A).left, (fst X (overSpec k A)).left ⁻¹ᵁ V) :=
  (CommRingCat.isPushout_tensorProduct k Γ(X.left, V) A).isoIsPushout _ _
    (Over.isPushout_algebraMap_sections X A hV hV')

/-- **Base change of sections** (brick 1 of the separatedness ledger, design §4.4): for `X`
over the field `k`, a commutative `k`-algebra `A` and a qcqs open `V ⊆ X.left`, the ring
equivalence `Γ(X.left, V) ⊗[k] A ≃+* Γ((X ⊗ Spec A).left, fst⁻¹ V)`, sending `s ⊗ a` to
the product of the pullbacks of `s` (along the first projection) and of `a` (along the
second). The `k`-algebra structure on `Γ(X.left, V)` is `Over.sectionsAlgebra`. -/
noncomputable def Over.sectionsBaseChange {V : X.left.Opens}
    (hV : IsCompact (V : Set X.left)) (hV' : IsQuasiSeparated (V : Set X.left)) :
    Γ(X.left, V) ⊗[k] A ≃+*
      Γ((X ⊗ overSpec k A).left, (fst X (overSpec k A)).left ⁻¹ᵁ V) :=
  (Over.sectionsBaseChangeIso X A hV hV').commRingCatIsoToRingEquiv

/-- `Over.sectionsBaseChange` for an affine open `V` (affine opens are qcqs) — the form
pinned by design §4.4 brick 1. -/
noncomputable def Over.sectionsBaseChangeOfIsAffineOpen {V : X.left.Opens}
    (hV : IsAffineOpen V) :
    Γ(X.left, V) ⊗[k] A ≃+*
      Γ((X ⊗ overSpec k A).left, (fst X (overSpec k A)).left ⁻¹ᵁ V) :=
  Over.sectionsBaseChange X A hV.isCompact hV.isQuasiSeparated

theorem Over.sectionsBaseChange_tmul_one {V : X.left.Opens}
    (hV : IsCompact (V : Set X.left)) (hV' : IsQuasiSeparated (V : Set X.left))
    (s : Γ(X.left, V)) :
    Over.sectionsBaseChange X A hV hV' (s ⊗ₜ 1) =
      (fst X (overSpec k A)).left.appLE V ((fst X (overSpec k A)).left ⁻¹ᵁ V) le_rfl s :=
  congr($((CommRingCat.isPushout_tensorProduct k Γ(X.left, V) A).inl_isoIsPushout_hom _ _
    (Over.isPushout_algebraMap_sections X A hV hV')).hom s)

theorem Over.sectionsBaseChange_one_tmul {V : X.left.Opens}
    (hV : IsCompact (V : Set X.left)) (hV' : IsQuasiSeparated (V : Set X.left)) (a : A) :
    Over.sectionsBaseChange X A hV hV' (1 ⊗ₜ a) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫
        (snd X (overSpec k A)).left.appLE ⊤ ((fst X (overSpec k A)).left ⁻¹ᵁ V)
          (le_top.trans (Scheme.Hom.preimage_top (snd X (overSpec k A)).left).ge)) a :=
  congr($((CommRingCat.isPushout_tensorProduct k Γ(X.left, V) A).inr_isoIsPushout_hom _ _
    (Over.isPushout_algebraMap_sections X A hV hV')).hom a)

/-- The base-change equivalence on a pure tensor: `s ⊗ a` goes to the product of the
pullback of `s` along the first projection and the pullback of `a` along the second. -/
theorem Over.sectionsBaseChange_tmul {V : X.left.Opens}
    (hV : IsCompact (V : Set X.left)) (hV' : IsQuasiSeparated (V : Set X.left))
    (s : Γ(X.left, V)) (a : A) :
    Over.sectionsBaseChange X A hV hV' (s ⊗ₜ a) =
      (fst X (overSpec k A)).left.appLE V ((fst X (overSpec k A)).left ⁻¹ᵁ V) le_rfl s *
      ((Scheme.ΓSpecIso (.of A)).inv ≫
        (snd X (overSpec k A)).left.appLE ⊤ ((fst X (overSpec k A)).left ⁻¹ᵁ V)
          (le_top.trans (Scheme.Hom.preimage_top (snd X (overSpec k A)).left).ge)) a := by
  have h : (s ⊗ₜ[k] a : Γ(X.left, V) ⊗[k] A) = (s ⊗ₜ 1) * (1 ⊗ₜ a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, Over.sectionsBaseChange_tmul_one, Over.sectionsBaseChange_one_tmul]

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the base-change equivalence in the open**: for `W ≤ V` (both qcqs),
restricting the base-changed section is base-changing the restriction. The map on tensor
products is `Algebra.TensorProduct.map` of the restriction `Over.resAlgHom` and the
identity of `A`. -/
theorem Over.sectionsBaseChange_naturality {V W : X.left.Opens}
    (hV : IsCompact (V : Set X.left)) (hV' : IsQuasiSeparated (V : Set X.left))
    (hW : IsCompact (W : Set X.left)) (hW' : IsQuasiSeparated (W : Set X.left))
    (hWV : W ≤ V) (x : Γ(X.left, V) ⊗[k] A) :
    (X ⊗ overSpec k A).left.presheaf.map
        (homOfLE (show (fst X (overSpec k A)).left ⁻¹ᵁ W ≤
          (fst X (overSpec k A)).left ⁻¹ᵁ V by gcongr)).op
      (Over.sectionsBaseChange X A hV hV' x) =
      Over.sectionsBaseChange X A hW hW'
        (Algebra.TensorProduct.map (Over.resAlgHom X hWV) (AlgHom.id k A) x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Over.resAlgHom_apply,
      Over.sectionsBaseChange_tmul, Over.sectionsBaseChange_tmul, map_mul]
    congr 1
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
        Scheme.Hom.map_appLE]
    · rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]

end TensorFace

end AlgebraicGeometry
