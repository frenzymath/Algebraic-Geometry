/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAffBaseFieldShuffle

/-!
# The base-field comparison of the étale Picard functor on all tests (Wave 7, B-4b lift)

For a field embedding `k → L`, a curve bundle `C` over `k` with base change
`C_L = (baseChange k L).obj C`, and an `L`-test object `T`, the B-2 base-field shuffle
`PicEtAff.baseFieldShuffle` lifts componentwise through the affine-opens limit: étale
Picard classes of `C` on the pushed-forward test `(Over.map σ).obj T`
(`σ = Spec.map (algebraMap k L)`) correspond to étale Picard classes of `C_L` on `T`
itself.  The carriers of `T` and `(Over.map σ).obj T` agree definitionally, so the affine
opens are literally shared; the only genuine seam is the section-ring scalar tower.

* `AlgebraicGeometry.Over.isScalarTower_sections_map`: **the section-ring tower seam** —
  the `k`-algebra structure `Over.sectionsAlgebra ((Over.map σ).obj T) U` and the
  `L`-algebra structure `Over.sectionsAlgebra T U` on `Γ(T.left, U)` form a scalar tower
  (`CommRingCat`-level form: `Over.ofHom_algebraMap_sections_map`).
* `AlgebraicGeometry.sectionShuffle`: the B-2 shuffle at the section ring of an open of
  an `L`-test object, with the `k`-structure through the pushforward; the componentwise
  ingredient of θ, with the restriction squares `mapAlg_sectionShuffle`/`_symm` and the
  pullback square `appLE_sectionShuffle` (the `restrictScalars` reconciliations
  `Over.resAlgHom_map_restrictScalars`/`Over.appLEAlgHom_map_restrictScalars` are
  `rfl`-grade).
* `AlgebraicGeometry.picEtCrossBase`/`picEtCrossBaseInv`/`picEtCrossBaseEquiv`: **the
  componentwise lift** `picEt C ((Over.map σ).obj T) ≃* picEt C_L T`, transporting a
  compatible family of plus classes affine open by affine open along the shuffle.
* `AlgebraicGeometry.picEtMap_picEtCrossBase` (and `_inv`): **naturality in the test
  object** — the lift commutes with restriction along an arbitrary morphism of `L`-tests
  against its pushforward.  The glued value of `picEtMap` is pinned by the
  `IsPullbackValue` characterization, which the transported family satisfies through the
  `mapAlg`/`appLE` squares of the section-ring shuffle.
* `AlgebraicGeometry.picEtAffineEquiv_picEtCrossBase`: **the affine face** — at an affine
  test `overSpec L A` the lift collapses under the two affine comparisons to the B-2
  shuffle itself, the pushed side being read through the affine matching
  `mapOverSpecIso`.  This is the reduction through which the θ assembly
  (`Picard/Pic0ThetaAssembly.lean`) discharges the `degAt` matching at field points.

Nothing here unfolds the limit carrier beyond the componentwise interface of
`AlgebraicJacobian.Picard.PicEt`, and `picEtMap` is consumed only through its
`IsPullbackValue` characterization (the w4/F-3 discipline).  Per the I-0206 elaboration
lesson, every seam-crossing step (the `Γ(T.left, U)` vs
`Γ(((Over.map σ).obj T).left, U)` spellings) is done in term mode with type-ascribed
local instances, never by rewriting.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-! ## The section-ring tower seam -/

section Seam

variable (T : Over (Spec (.of L)))

/-- The `k`-algebra structure map of a section ring of the pushed-forward `L`-test
`(Over.map σ).obj T` factors through the base extension `k → L`: the `CommRingCat`-level
form of the section-ring tower seam. -/
lemma Over.ofHom_algebraMap_sections_map (U : T.left.Opens) :
    CommRingCat.ofHom (algebraMap k
        Γ(((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T).left, U))
      = CommRingCat.ofHom (algebraMap k L)
          ≫ CommRingCat.ofHom (algebraMap L Γ(T.left, U)) := by
  have happ : (Spec.map (CommRingCat.ofHom (algebraMap k L))).appLE ⊤ ⊤
        (le_top.trans
          (Scheme.Hom.preimage_top (Spec.map (CommRingCat.ofHom (algebraMap k L)))).ge)
      = (Spec.map (CommRingCat.ofHom (algebraMap k L))).appTop :=
    Scheme.Hom.appLE_eq_app _
  have hnat : (Spec.map (CommRingCat.ofHom (algebraMap k L))).appTop
        ≫ (Scheme.ΓSpecIso (.of L)).hom
      = (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k L) :=
    Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k L))
  have h1 : (Scheme.ΓSpecIso (.of k)).inv
        ≫ (Spec.map (CommRingCat.ofHom (algebraMap k L))).appTop
      = CommRingCat.ofHom (algebraMap k L) ≫ (Scheme.ΓSpecIso (.of L)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hpush : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T).hom.appLE
        ⊤ U (le_top.trans (Scheme.Hom.preimage_top
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T).hom).ge)
      = (Spec.map (CommRingCat.ofHom (algebraMap k L))).appLE ⊤ ⊤
          (le_top.trans (Scheme.Hom.preimage_top
            (Spec.map (CommRingCat.ofHom (algebraMap k L)))).ge)
        ≫ T.hom.appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top T.hom).ge) := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_congr_hom rfl ⊤ U _ _
  have hmain : (Scheme.ΓSpecIso (.of k)).inv
        ≫ ((Spec.map (CommRingCat.ofHom (algebraMap k L))).appLE ⊤ ⊤
            (le_top.trans (Scheme.Hom.preimage_top
              (Spec.map (CommRingCat.ofHom (algebraMap k L)))).ge)
          ≫ T.hom.appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top T.hom).ge))
      = CommRingCat.ofHom (algebraMap k L)
          ≫ ((Scheme.ΓSpecIso (.of L)).inv
            ≫ T.hom.appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top T.hom).ge)) := by
    rw [happ, ← Category.assoc, ← Category.assoc, h1]
  exact (Over.ofHom_algebraMap_sections
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) U).trans
    ((congrArg (fun ψ => (Scheme.ΓSpecIso (.of k)).inv ≫ ψ) hpush).trans
      (hmain.trans
        (congrArg (fun ψ => CommRingCat.ofHom (algebraMap k L) ≫ ψ)
          (Over.ofHom_algebraMap_sections T U).symm)))

/-- **The section-ring tower seam**: on `Γ(T.left, U)` for an `L`-test object `T`, the
`k`-algebra structure through the pushforward `(Over.map σ).obj T` and the `L`-algebra
structure of `T` itself form a scalar tower. -/
theorem Over.isScalarTower_sections_map (U : T.left.Opens) :
    letI : Algebra k Γ(T.left, U) := Over.sectionsAlgebra
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) U
    IsScalarTower k L Γ(T.left, U) := by
  letI : Algebra k Γ(T.left, U) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) U
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  exact congr($(Over.ofHom_algebraMap_sections_map k L T U).hom r)

end Seam

/-! ## The shuffle at section rings and its restriction squares -/

variable (C : Over (Spec (.of k)))

section SectionShuffle

variable (T : Over (Spec (.of L)))

/-- **The base-field shuffle at a section ring**: for an open `U` of an `L`-test object
`T`, the B-2 shuffle at the test algebra `Γ(T.left, U)`, whose `k`-structure is the
`Over.sectionsAlgebra` of the pushforward `(Over.map σ).obj T` — the componentwise
ingredient of the θ lift. -/
noncomputable def sectionShuffle (U : T.left.Opens) :
    PicEtAff C
        Γ(((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T).left, U)
      ≃* PicEtAff ((baseChange k L).obj C) Γ(T.left, U) :=
  letI : Algebra k Γ(T.left, U) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) U
  haveI : IsScalarTower k L Γ(T.left, U) := Over.isScalarTower_sections_map k L T U
  PicEtAff.baseFieldShuffle k L C Γ(T.left, U)

/-- The `restrictScalars` reconciliation of the two restriction algebra maps: restriction
of sections of the pushforward is the scalar restriction of restriction of sections. -/
lemma Over.resAlgHom_map_restrictScalars {V W : T.left.Opens} (h : W ≤ V) :
    letI : Algebra k Γ(T.left, V) := Over.sectionsAlgebra
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) V
    letI : Algebra k Γ(T.left, W) := Over.sectionsAlgebra
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) W
    haveI : IsScalarTower k L Γ(T.left, V) := Over.isScalarTower_sections_map k L T V
    haveI : IsScalarTower k L Γ(T.left, W) := Over.isScalarTower_sections_map k L T W
    (Over.resAlgHom T h).restrictScalars k
      = Over.resAlgHom
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) h := by
  letI : Algebra k Γ(T.left, V) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) V
  letI : Algebra k Γ(T.left, W) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) W
  haveI : IsScalarTower k L Γ(T.left, V) := Over.isScalarTower_sections_map k L T V
  haveI : IsScalarTower k L Γ(T.left, W) := Over.isScalarTower_sections_map k L T W
  exact AlgHom.ext fun _ => rfl

/-- **The restriction square of the section-ring shuffle**: shuffling commutes with
restriction of sections along an inclusion of opens (the `mapAlg` bilateral square of
B-2, read at the section rings). -/
theorem mapAlg_sectionShuffle {V W : T.left.Opens} (h : W ≤ V)
    (x : PicEtAff C
      Γ(((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T).left, V)) :
    sectionShuffle k L C T W
        (PicEtAff.mapAlg C
          (Over.resAlgHom
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) h) x)
      = PicEtAff.mapAlg ((baseChange k L).obj C) (Over.resAlgHom T h)
          (sectionShuffle k L C T V x) := by
  letI : Algebra k Γ(T.left, V) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) V
  letI : Algebra k Γ(T.left, W) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) W
  haveI : IsScalarTower k L Γ(T.left, V) := Over.isScalarTower_sections_map k L T V
  haveI : IsScalarTower k L Γ(T.left, W) := Over.isScalarTower_sections_map k L T W
  exact Over.resAlgHom_map_restrictScalars k L T h
    ▸ PicEtAff.mapAlg_baseFieldShuffle k L C (Over.resAlgHom T h) x

/-- The restriction square of the inverse section-ring shuffle. -/
theorem mapAlg_sectionShuffle_symm {V W : T.left.Opens} (h : W ≤ V)
    (y : PicEtAff ((baseChange k L).obj C) Γ(T.left, V)) :
    (sectionShuffle k L C T W).symm
        (PicEtAff.mapAlg ((baseChange k L).obj C) (Over.resAlgHom T h) y)
      = PicEtAff.mapAlg C
          (Over.resAlgHom
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) h)
          ((sectionShuffle k L C T V).symm y) := by
  letI : Algebra k Γ(T.left, V) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) V
  letI : Algebra k Γ(T.left, W) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) W
  haveI : IsScalarTower k L Γ(T.left, V) := Over.isScalarTower_sections_map k L T V
  haveI : IsScalarTower k L Γ(T.left, W) := Over.isScalarTower_sections_map k L T W
  exact Over.resAlgHom_map_restrictScalars k L T h
    ▸ PicEtAff.mapAlg_baseFieldShuffle_symm k L C (Over.resAlgHom T h) y

end SectionShuffle

section AppLE

variable (T T' : Over (Spec (.of L))) (f : T' ⟶ T)

/-- The `restrictScalars` reconciliation of the two pullback algebra maps: pullback of
sections along the pushforward of a test morphism is the scalar restriction of pullback
of sections along the morphism itself. -/
lemma Over.appLEAlgHom_map_restrictScalars (V : T.left.Opens) (U : T'.left.Opens)
    (e : U ≤ f.left ⁻¹ᵁ V)
    (e' : U ≤ ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map f).left
      ⁻¹ᵁ V) :
    letI : Algebra k Γ(T.left, V) := Over.sectionsAlgebra
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) V
    letI : Algebra k Γ(T'.left, U) := Over.sectionsAlgebra
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T') U
    haveI : IsScalarTower k L Γ(T.left, V) := Over.isScalarTower_sections_map k L T V
    haveI : IsScalarTower k L Γ(T'.left, U) := Over.isScalarTower_sections_map k L T' U
    (Over.appLEAlgHom f V U e).restrictScalars k
      = Over.appLEAlgHom
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map f) V U e' := by
  letI : Algebra k Γ(T.left, V) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) V
  letI : Algebra k Γ(T'.left, U) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T') U
  haveI : IsScalarTower k L Γ(T.left, V) := Over.isScalarTower_sections_map k L T V
  haveI : IsScalarTower k L Γ(T'.left, U) := Over.isScalarTower_sections_map k L T' U
  exact AlgHom.ext fun _ => rfl

/-- **The pullback square of the section-ring shuffle**: shuffling commutes with pullback
of sections along a morphism of `L`-test objects against its pushforward. -/
theorem appLE_sectionShuffle (V : T.left.Opens) (U : T'.left.Opens)
    (e : U ≤ f.left ⁻¹ᵁ V)
    (e' : U ≤ ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map f).left
      ⁻¹ᵁ V)
    (x : PicEtAff C
      Γ(((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T).left, V)) :
    sectionShuffle k L C T' U
        (PicEtAff.mapAlg C
          (Over.appLEAlgHom
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map f) V U e')
          x)
      = PicEtAff.mapAlg ((baseChange k L).obj C) (Over.appLEAlgHom f V U e)
          (sectionShuffle k L C T V x) := by
  letI : Algebra k Γ(T.left, V) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) V
  letI : Algebra k Γ(T'.left, U) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T') U
  haveI : IsScalarTower k L Γ(T.left, V) := Over.isScalarTower_sections_map k L T V
  haveI : IsScalarTower k L Γ(T'.left, U) := Over.isScalarTower_sections_map k L T' U
  exact Over.appLEAlgHom_map_restrictScalars k L T T' f V U e e'
    ▸ PicEtAff.mapAlg_baseFieldShuffle k L C (Over.appLEAlgHom f V U e) x

end AppLE

/-! ## The componentwise lift through the affine-opens limit -/

section CrossBase

variable (T : Over (Spec (.of L)))

/-- **The componentwise lift of the base-field shuffle** (forward direction): étale
Picard classes of the `k`-curve `C` on the pushed-forward test `(Over.map σ).obj T`
transport to étale Picard classes of the base-changed curve `C_L` on `T` itself,
affine open by affine open along the section-ring shuffle; the `mapAlg` restriction
square keeps the family compatible. -/
noncomputable def picEtCrossBase :
    picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)
      →* picEt ((baseChange k L).obj C) T where
  toFun s := ⟨fun U => sectionShuffle k L C T U.1 (s.1 ⟨U.1, U.2⟩), fun U V h => by
    rw [← mapAlg_sectionShuffle k L C T h, s.compat ⟨U.1, U.2⟩ ⟨V.1, V.2⟩ h]⟩
  map_one' := picEt.ext fun U => map_one (sectionShuffle k L C T U.1)
  map_mul' s t := picEt.ext fun U =>
    map_mul (sectionShuffle k L C T U.1) (s.1 ⟨U.1, U.2⟩) (t.1 ⟨U.1, U.2⟩)

/-- The componentwise computation rule of `picEtCrossBase`. -/
@[simp]
lemma picEtCrossBase_val
    (s : picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T))
    (U : T.left.affineOpens) :
    (picEtCrossBase k L C T s).1 U = sectionShuffle k L C T U.1 (s.1 ⟨U.1, U.2⟩) :=
  rfl

/-- **The componentwise lift of the base-field shuffle** (backward direction). -/
noncomputable def picEtCrossBaseInv :
    picEt ((baseChange k L).obj C) T
      →* picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) where
  toFun t := ⟨fun W => (sectionShuffle k L C T W.1).symm (t.1 ⟨W.1, W.2⟩),
    fun U V h => by
      rw [← mapAlg_sectionShuffle_symm k L C T h, t.compat ⟨U.1, U.2⟩ ⟨V.1, V.2⟩ h]⟩
  map_one' := picEt.ext fun W => map_one (sectionShuffle k L C T W.1).symm
  map_mul' s t := picEt.ext fun W =>
    map_mul (sectionShuffle k L C T W.1).symm (s.1 ⟨W.1, W.2⟩) (t.1 ⟨W.1, W.2⟩)

/-- The componentwise computation rule of `picEtCrossBaseInv`. -/
@[simp]
lemma picEtCrossBaseInv_val (t : picEt ((baseChange k L).obj C) T)
    (W : ((Over.map (Spec.map (CommRingCat.ofHom
      (algebraMap k L)))).obj T).left.affineOpens) :
    (picEtCrossBaseInv k L C T t).1 W
      = (sectionShuffle k L C T W.1).symm (t.1 ⟨W.1, W.2⟩) :=
  rfl

/-- **The componentwise lift of the base-field shuffle is an isomorphism**: the two
directions collapse componentwise by the two-sidedness of the B-2 shuffle. -/
noncomputable def picEtCrossBaseEquiv :
    picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)
      ≃* picEt ((baseChange k L).obj C) T where
  toFun := picEtCrossBase k L C T
  invFun := picEtCrossBaseInv k L C T
  left_inv s := picEt.ext fun W =>
    (sectionShuffle k L C T W.1).symm_apply_apply (s.1 ⟨W.1, W.2⟩)
  right_inv t := picEt.ext fun U =>
    (sectionShuffle k L C T U.1).apply_symm_apply (t.1 ⟨U.1, U.2⟩)
  map_mul' := map_mul (picEtCrossBase k L C T)

@[simp]
lemma picEtCrossBaseEquiv_apply
    (s : picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) :
    picEtCrossBaseEquiv k L C T s = picEtCrossBase k L C T s :=
  rfl

@[simp]
lemma picEtCrossBaseEquiv_symm_apply (t : picEt ((baseChange k L).obj C) T) :
    (picEtCrossBaseEquiv k L C T).symm t = picEtCrossBaseInv k L C T t :=
  rfl

end CrossBase

/-! ## Naturality in the test object -/

section Naturality

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- **Naturality of the componentwise lift in the test object**: the lift commutes with
restriction along an arbitrary morphism `f` of `L`-test objects against its pushforward
`(Over.map σ).map f`.  The glued value of `picEtMap` is pinned by its `IsPullbackValue`
characterization, which the transported family satisfies through the `mapAlg`/`appLE`
squares of the section-ring shuffle. -/
theorem picEtMap_picEtCrossBase {T T' : Over (Spec (.of L))} (f : T' ⟶ T)
    (s : picEt C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) :
    picEtMap ((baseChange k L).obj C) f (picEtCrossBase k L C T s)
      = picEtCrossBase k L C T'
          (picEtMap C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map f)
            s) := by
  refine picEt.ext fun W => ?_
  rw [picEtMap_val]
  refine picEtMapVal_eq_of ((baseChange k L).obj C) f (picEtCrossBase k L C T s) ?_
  intro W₀ hW₀ V hV
  rw [picEtCrossBase_val, picEtCrossBase_val, picEtMap_val,
    ← mapAlg_sectionShuffle k L C T' hW₀,
    ← appLE_sectionShuffle k L C T T' f V.1 W₀.1 hV hV]
  exact congrArg (sectionShuffle k L C T' W₀.1)
    (picEtMapVal_spec C
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map f) s
      ⟨W.1, W.2⟩ ⟨W₀.1, W₀.2⟩ hW₀ ⟨V.1, V.2⟩ hV)

/-- Naturality of the backward lift in the test object. -/
theorem picEtMap_picEtCrossBaseInv {T T' : Over (Spec (.of L))} (f : T' ⟶ T)
    (t : picEt ((baseChange k L).obj C) T) :
    picEtMap C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map f)
        (picEtCrossBaseInv k L C T t)
      = picEtCrossBaseInv k L C T' (picEtMap ((baseChange k L).obj C) f t) := by
  refine (picEtCrossBaseEquiv k L C T').injective ?_
  rw [picEtCrossBaseEquiv_apply, picEtCrossBaseEquiv_apply,
    show picEtCrossBase k L C T'
        (picEtCrossBaseInv k L C T' (picEtMap ((baseChange k L).obj C) f t))
      = picEtMap ((baseChange k L).obj C) f t from
      (picEtCrossBaseEquiv k L C T').apply_symm_apply _,
    ← picEtMap_picEtCrossBase k L C f,
    show picEtCrossBase k L C T (picEtCrossBaseInv k L C T t) = t from
      (picEtCrossBaseEquiv k L C T).apply_symm_apply _]

end Naturality

/-! ## The affine face -/

section Affine

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (A : Type u) [CommRing A] [Algebra k A] [Algebra L A] [IsScalarTower k L A]

/-- The `restrictScalars` reconciliation of the affine face: reading the top sections of
`overSpec L A` in the test algebra `A` over `k` is reading them through the affine
matching `mapOverSpecIso` into `overSpec k A` and then over `k`. -/
lemma overSpecΓTop_map_restrictScalars :
    letI : Algebra k Γ((overSpec L A).left, ⊤) := Over.sectionsAlgebra
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj (overSpec L A)) ⊤
    haveI : IsScalarTower k L Γ((overSpec L A).left, ⊤) :=
      Over.isScalarTower_sections_map k L (overSpec L A) ⊤
    (Over.overSpecΓTopAlgEquiv L A).toAlgHom.restrictScalars k
      = (Over.overSpecΓTopAlgEquiv k A).toAlgHom.comp
          (Over.appLEAlgHom (mapOverSpecIso k L A).inv ⊤ ⊤
            (le_top.trans
              (Scheme.Hom.preimage_top (mapOverSpecIso k L A).inv.left).ge)) := by
  letI : Algebra k Γ((overSpec L A).left, ⊤) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj (overSpec L A)) ⊤
  haveI : IsScalarTower k L Γ((overSpec L A).left, ⊤) :=
    Over.isScalarTower_sections_map k L (overSpec L A) ⊤
  have key : (mapOverSpecIso k L A).inv.left.appLE ⊤ ⊤
        (le_top.trans (Scheme.Hom.preimage_top (mapOverSpecIso k L A).inv.left).ge)
      = 𝟙 Γ((overSpec L A).left, ⊤) :=
    (Scheme.Hom.appLE_congr_hom (mapOverSpecIso_inv_left k L A) ⊤ ⊤ _
        (le_top.trans (Scheme.Hom.preimage_top (𝟙 (Spec (.of A)))).ge)).trans
      ((Scheme.Hom.appLE_eq_app (𝟙 (Spec (.of A)))).trans
        (Scheme.Hom.id_app (X := Spec (.of A)) ⊤))
  ext s
  exact (congrArg (Scheme.ΓSpecIso (.of A)).hom congr($(key).hom s)).symm

/-- **The affine face of the componentwise lift**: at an affine test `overSpec L A` the
lift collapses under the two affine comparisons to the B-2 shuffle itself, the pushed
side being read through the affine matching `mapOverSpecIso`.  This is the reduction
through which the θ assembly discharges the `degAt` matching at field points. -/
theorem picEtAffineEquiv_picEtCrossBase
    (w : picEt C
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj (overSpec L A))) :
    picEtAffineEquiv ((baseChange k L).obj C) A (picEtCrossBase k L C (overSpec L A) w)
      = PicEtAff.baseFieldShuffle k L C A
          (picEtAffineEquiv C A (picEtMap C (mapOverSpecIso k L A).inv w)) := by
  letI : Algebra k Γ((overSpec L A).left, ⊤) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj (overSpec L A)) ⊤
  haveI : IsScalarTower k L Γ((overSpec L A).left, ⊤) :=
    Over.isScalarTower_sections_map k L (overSpec L A) ⊤
  have hval : (picEtMap C (mapOverSpecIso k L A).inv w).1 (overSpecTopAffine (k := k) A)
      = PicEtAff.mapAlg C
          (Over.appLEAlgHom (mapOverSpecIso k L A).inv ⊤ ⊤
            (le_top.trans
              (Scheme.Hom.preimage_top (mapOverSpecIso k L A).inv.left).ge))
          (w.1 ⟨(overSpecTopAffine (k := L) A).1, (overSpecTopAffine (k := L) A).2⟩) := by
    rw [picEtMap_val]
    exact picEtMapVal_eq_mapAlg C (mapOverSpecIso k L A).inv w
      (W := overSpecTopAffine (k := k) A)
      (V := ⟨(overSpecTopAffine (k := L) A).1, (overSpecTopAffine (k := L) A).2⟩)
      (le_top.trans (Scheme.Hom.preimage_top (mapOverSpecIso k L A).inv.left).ge)
  have hsh := @PicEtAff.mapAlg_baseFieldShuffle k L _ _ _ C _ _ _ _ this A _ _ _ _
    (Over.overSpecΓTopAlgEquiv L A).toAlgHom
    (w.1 ⟨(overSpecTopAffine (k := L) A).1, (overSpecTopAffine (k := L) A).2⟩)
  rw [picEtAffineEquiv_apply, picEtCrossBase_val]
  refine Eq.trans hsh.symm ?_
  refine congrArg (PicEtAff.baseFieldShuffle k L C A) ?_
  exact (congrArg (fun φ => PicEtAff.mapAlg C φ
      (w.1 ⟨(overSpecTopAffine (k := L) A).1, (overSpecTopAffine (k := L) A).2⟩))
      (overSpecΓTop_map_restrictScalars k L A)).trans
    ((PicEtAff.mapAlg_comp C
        (Over.appLEAlgHom (mapOverSpecIso k L A).inv ⊤ ⊤
          (le_top.trans (Scheme.Hom.preimage_top (mapOverSpecIso k L A).inv.left).ge))
        (Over.overSpecΓTopAlgEquiv k A).toAlgHom
        (w.1 ⟨(overSpecTopAffine (k := L) A).1, (overSpecTopAffine (k := L) A).2⟩)).trans
      ((congrArg (fun z => PicEtAff.mapAlg C (Over.overSpecΓTopAlgEquiv k A).toAlgHom z)
        hval.symm).trans
        (picEtAffineEquiv_apply C A (picEtMap C (mapOverSpecIso k L A).inv w)).symm))

end Affine

end AlgebraicGeometry
