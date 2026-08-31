/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Challenge
import AlgebraicJacobian.Cohomology.SectionsBaseChange

/-!
# The cross-base pasted pullback square (Wave 7, W7-B1)

For a morphism of base schemes `f : S' ⟶ S`, an object `X : Over S`, and a test object
`T : Over S'`, the tensor product `((Over.pullback f).obj X ⊗ T).left` — formed in the slice
over `S'` — is canonically a pullback of the *cross-base* cospan
`X.left ⟶ S ⟵ T.left` (the test leg being `T.hom ≫ f = ((Over.map f).obj T).hom`).  Pasting
this square against the same-slice square `Over.isPullback_left X ((Over.map f).obj T)` and
taking `IsPullback.isoIsPullback` yields the **cross-base comparison isomorphism**

`(((Over.pullback f).obj X) ⊗ T).left ≅ (X ⊗ (Over.map f).obj T).left`,

natural in `T`.  Instantiated at `f = Spec.map (algebraMap k L)` this is the Wave-7 seam
between the base-changed curve `C_L = (baseChange k L).obj C` tensored with an `L`-test and
the original curve `C` tensored with the pushed-forward test — the iso family through which
`PicEtAff`/`picEt` transport crosses the base field (`informal/w7-worksheet.md` §D2 B-1;
designed for inheritance by `informal/deg-d5b-worksheet.md` §3).  The same-base sibling is
`Over.isPullback_whiskerLeft_left` (`Curve/BaseFieldTransition.lean`).

## Main declarations

* `AlgebraicGeometry.Over.isPullback_crossBase` — the pasted square, general form: for
  `f : S' ⟶ S`, `((Over.pullback f).obj X ⊗ T).left` is a pullback of `X.hom` against
  `((Over.map f).obj T).hom`.
* `AlgebraicGeometry.Over.crossBaseIso` — the comparison iso, with projection lemmas
  (`crossBaseIso_hom_fst/snd`, `crossBaseIso_inv_fst/snd`) and naturality in the test
  (`crossBaseIso_naturality`).
* `AlgebraicGeometry.isPullback_crossBase`, `AlgebraicGeometry.crossBaseIso`,
  `AlgebraicGeometry.crossBaseIso_naturality` — the instantiations at the frozen Challenge
  spelling `(baseChange k L).obj C` (definitionally `Over.pullback σ` for
  `σ = Spec.map (CommRingCat.ofHom (algebraMap k L))`).
* `AlgebraicGeometry.mapOverSpecIso` — the affine matching: for an `L`-algebra `A` in a
  scalar tower `k → L → A`, pushing the affine test `overSpec L A` forward along `σ` gives
  `overSpec k A` (the restrictScalars seam of the shared étale-cover index).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-! ## The general cross-base square -/

section General

variable {S' S : Scheme.{u}} (f : S' ⟶ S)

/-- **The cross-base pasted square** (general form): for `X : Over S` and `T : Over S'`, the
square

```
((pullback f).obj X ⊗ T).left --(fst).left ≫ pullback.fst--> X.left
        |                                                      |
    (snd).left                                               X.hom
        ↓                                                      ↓
      T.left -----------------T.hom ≫ f----------------------> S
```

is a pullback: the horizontal paste of the slice square
`Over.isPullback_left ((Over.pullback f).obj X) T` (over `S'`) with the defining base-change
square of `(Over.pullback f).obj X` (whose second projection *is* the structure morphism of
the pulled-back object). -/
theorem Over.isPullback_crossBase (X : Over S) (T : Over S') :
    IsPullback ((fst ((Over.pullback f).obj X) T).left ≫ pullback.fst X.hom f)
      ((snd ((Over.pullback f).obj X) T).left) X.hom ((Over.map f).obj T).hom :=
  (Over.isPullback_left ((Over.pullback f).obj X) T).paste_horiz
    (IsPullback.of_hasPullback X.hom f)

/-- **The cross-base comparison isomorphism**: the slice tensor of the pulled-back object
with an `S'`-test agrees with the slice tensor of the original object with the
pushed-forward test, as schemes.  Both are pullbacks of the cospan
`X.left ⟶ S ⟵ T.left`. -/
noncomputable def Over.crossBaseIso (X : Over S) (T : Over S') :
    (((Over.pullback f).obj X) ⊗ T).left ≅ (X ⊗ (Over.map f).obj T).left :=
  IsPullback.isoIsPullback _ _ (Over.isPullback_crossBase f X T)
    (Over.isPullback_left X ((Over.map f).obj T))

@[reassoc (attr := simp)]
lemma Over.crossBaseIso_hom_fst (X : Over S) (T : Over S') :
    (Over.crossBaseIso f X T).hom ≫ (fst X ((Over.map f).obj T)).left
      = (fst ((Over.pullback f).obj X) T).left ≫ pullback.fst X.hom f :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc (attr := simp)]
lemma Over.crossBaseIso_hom_snd (X : Over S) (T : Over S') :
    (Over.crossBaseIso f X T).hom ≫ (snd X ((Over.map f).obj T)).left
      = (snd ((Over.pullback f).obj X) T).left :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

@[reassoc (attr := simp)]
lemma Over.crossBaseIso_inv_fst (X : Over S) (T : Over S') :
    (Over.crossBaseIso f X T).inv
        ≫ ((fst ((Over.pullback f).obj X) T).left ≫ pullback.fst X.hom f)
      = (fst X ((Over.map f).obj T)).left :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

@[reassoc (attr := simp)]
lemma Over.crossBaseIso_inv_snd (X : Over S) (T : Over S') :
    (Over.crossBaseIso f X T).inv ≫ (snd ((Over.pullback f).obj X) T).left
      = (snd X ((Over.map f).obj T)).left :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

/-- **Naturality of the cross-base iso in the test object**: for `t : T' ⟶ T` in `Over S'`,
the comparison isos intertwine the two whiskered restrictions `(pullback f).obj X ◁ t` and
`X ◁ (Over.map f).map t`. -/
theorem Over.crossBaseIso_naturality (X : Over S) {T T' : Over S'} (t : T' ⟶ T) :
    (((Over.pullback f).obj X) ◁ t).left ≫ (Over.crossBaseIso f X T).hom
      = (Over.crossBaseIso f X T').hom ≫ (X ◁ (Over.map f).map t).left := by
  refine (Over.isPullback_left X ((Over.map f).obj T)).hom_ext ?_ ?_
  · have h1 : (((Over.pullback f).obj X) ◁ t).left ≫ (fst ((Over.pullback f).obj X) T).left
        = (fst ((Over.pullback f).obj X) T').left := by
      rw [← Over.comp_left, whiskerLeft_fst]
    have h2 : (X ◁ (Over.map f).map t).left ≫ (fst X ((Over.map f).obj T)).left
        = (fst X ((Over.map f).obj T')).left := by
      rw [← Over.comp_left, whiskerLeft_fst]
    calc (((Over.pullback f).obj X) ◁ t).left ≫ (Over.crossBaseIso f X T).hom
          ≫ (fst X ((Over.map f).obj T)).left
        = ((((Over.pullback f).obj X) ◁ t).left
            ≫ (fst ((Over.pullback f).obj X) T).left) ≫ pullback.fst X.hom f := by
          rw [Over.crossBaseIso_hom_fst, Category.assoc]
      _ = (fst ((Over.pullback f).obj X) T').left ≫ pullback.fst X.hom f := by rw [h1]
      _ = (Over.crossBaseIso f X T').hom ≫ (fst X ((Over.map f).obj T')).left := by
          rw [Over.crossBaseIso_hom_fst]
      _ = (Over.crossBaseIso f X T').hom
            ≫ (X ◁ (Over.map f).map t).left ≫ (fst X ((Over.map f).obj T)).left := by
          rw [h2]
  · have h1 : (((Over.pullback f).obj X) ◁ t).left ≫ (snd ((Over.pullback f).obj X) T).left
        = (snd ((Over.pullback f).obj X) T').left ≫ t.left := by
      rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
    have h2 : (X ◁ (Over.map f).map t).left ≫ (snd X ((Over.map f).obj T)).left
        = (snd X ((Over.map f).obj T')).left ≫ ((Over.map f).map t).left := by
      rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
    have e1 : (((Over.pullback f).obj X) ◁ t).left ≫ (Over.crossBaseIso f X T).hom
          ≫ (snd X ((Over.map f).obj T)).left
        = (snd ((Over.pullback f).obj X) T').left ≫ t.left := by
      rw [Over.crossBaseIso_hom_snd]
      exact h1
    have e2 : ((Over.crossBaseIso f X T').hom ≫ (X ◁ (Over.map f).map t).left)
          ≫ (snd X ((Over.map f).obj T)).left
        = (snd ((Over.pullback f).obj X) T').left ≫ t.left := by
      rw [Category.assoc, h2, ← Category.assoc, Over.crossBaseIso_hom_snd]
      rfl
    rw [Category.assoc]
    exact e1.trans e2.symm

end General

/-! ## Instantiation at the frozen base-change spelling -/

section BaseChange

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- **The Wave-7 cross-base square at the frozen spelling**: for the base-changed curve
`C_L = (baseChange k L).obj C` and an `L`-test `T`, the slice tensor `(C_L ⊗ T).left` is a
pullback of `C.hom` against the pushed-forward test `(Over.map σ).obj T`, where
`σ = Spec.map (CommRingCat.ofHom (algebraMap k L))`. -/
theorem isPullback_crossBase (C : Over (Spec (.of k))) (T : Over (Spec (.of L))) :
    IsPullback
      ((fst ((baseChange k L).obj C) T).left
          ≫ pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      ((snd ((baseChange k L).obj C) T).left) C.hom
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T).hom :=
  Over.isPullback_crossBase (Spec.map (CommRingCat.ofHom (algebraMap k L))) C T

/-- **The Wave-7 cross-base comparison iso at the frozen spelling**:
`(C_L ⊗_L T).left ≅ (C ⊗_k (Over.map σ).obj T).left` (worksheet §D2 B-1 (ii)).  An abbrev
of the general `Over.crossBaseIso`, so its projection lemmas
(`Over.crossBaseIso_hom_fst/snd`, `_inv_fst/snd`) apply directly. -/
noncomputable abbrev crossBaseIso (C : Over (Spec (.of k))) (T : Over (Spec (.of L))) :
    (((baseChange k L).obj C) ⊗ T).left
      ≅ (C ⊗ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T).left :=
  Over.crossBaseIso (Spec.map (CommRingCat.ofHom (algebraMap k L))) C T

/-- Naturality of the frozen-spelling cross-base iso in the test object. -/
theorem crossBaseIso_naturality (C : Over (Spec (.of k))) {T T' : Over (Spec (.of L))}
    (t : T' ⟶ T) :
    (((baseChange k L).obj C) ◁ t).left ≫ (crossBaseIso k L C T).hom
      = (crossBaseIso k L C T').hom
          ≫ (C ◁ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map t).left :=
  Over.crossBaseIso_naturality (Spec.map (CommRingCat.ofHom (algebraMap k L))) C t

/-! ### The affine test matching -/

/-- **The affine matching (worksheet §D2 B-1 (iv))**: for an `L`-algebra `A` in a scalar
tower `k → L → A` (e.g. the restriction of scalars of an `L`-algebra), pushing the affine
test `overSpec L A` forward along `σ` is the affine test `overSpec k A`.  The underlying
scheme is `Spec A` on both sides; the triangle is the tower identity
`algebraMap k A = algebraMap L A ∘ algebraMap k L`. -/
noncomputable def mapOverSpecIso (A : Type u) [CommRing A] [Algebra k A] [Algebra L A]
    [IsScalarTower k L A] :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj (overSpec L A)
      ≅ overSpec k A :=
  Over.isoMk (Iso.refl (Spec (.of A))) (by
    have key : Spec.map (CommRingCat.ofHom (algebraMap L A))
          ≫ Spec.map (CommRingCat.ofHom (algebraMap k L))
        = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq k L A]
    exact (Category.id_comp _).trans key.symm)

@[simp]
lemma mapOverSpecIso_hom_left (A : Type u) [CommRing A] [Algebra k A] [Algebra L A]
    [IsScalarTower k L A] :
    (mapOverSpecIso k L A).hom.left = 𝟙 (Spec (.of A)) :=
  rfl

@[simp]
lemma mapOverSpecIso_inv_left (A : Type u) [CommRing A] [Algebra k A] [Algebra L A]
    [IsScalarTower k L A] :
    (mapOverSpecIso k L A).inv.left = 𝟙 (Spec (.of A)) :=
  rfl

end BaseChange

end AlgebraicGeometry
