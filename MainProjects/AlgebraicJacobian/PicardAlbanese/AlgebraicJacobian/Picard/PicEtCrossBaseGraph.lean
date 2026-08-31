/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtCrossBase
import AlgebraicJacobian.Picard.PicEtUnit

/-!
# The base-field shuffle commutes with the étale unit at a general test (Wave 7, W7-A1)

For a field embedding `k → L`, a curve bundle `C` over `k` with base change
`C_L = (baseChange k L).obj C`, and an `L`-test object `T`, this file proves that the
componentwise base-field shuffle `picEtCrossBase` (landed `Picard/PicEtCrossBase.lean`)
commutes with the unit of the étale sheafification `relPicToPicEt`
(`Picard/PicEtUnit.lean`) at a *general* test object — the general-test lift of the
affine `PicEtAff.baseFieldShuffle_unit`, which the affine-only `relPicCrossBase`
(`Picard/Pic0Theta.lean`) cannot supply.

Concretely: shuffling the unit image of a relative Picard class on the pushed-forward
test `(Over.map σ).obj T` (`σ = Spec.map (algebraMap k L)`) equals the unit image on `T`
of the same Čech class transported along the cross-base comparison iso
`crossBaseIso` (`Curve/CrossBaseSquare.lean`).

* `AlgebraicGeometry.Over.mapOverSpecIso_hom_fromSpecAffine` — the affine-open bridge:
  the affine-open test object of an open `U` of `T`, pushed forward, matches (through the
  affine matching `mapOverSpecIso`) the pushed-forward affine-open test object of `U`.
* `AlgebraicGeometry.picEtCrossBase_relPicToPicEt` — **the general-test naturality**: the
  base-field shuffle intertwines the étale units, via `crossBaseIso`.  Proved affine open
  by affine open through `PicEtAff.baseFieldShuffle_unit` and the affine/general
  cross-base reconciliation `crossBaseIso_naturality`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.Scheme (CechPic)

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable (C : Over (Spec (.of k)))

/-- The affine-open bridge between the affine same-carrier comparison `crossBaseAffineIso`
and the general-test cross-base comparison `crossBaseIso`, mediated by the affine-open test
objects `fromSpecAffine`: on the section ring of an affine open `U` of an `L`-test `T`, the
`hom`-composite `crossBaseAffineIso ≫ (C ◁ fromSpecAffine (pushed))` equals
`(C_L ◁ fromSpecAffine) ≫ crossBaseIso`.  Proved by `crossBaseIso_naturality` at the
affine-open test map, reconciled with `crossBaseAffineIso_hom` through
`mapOverSpecIso ≫ fromSpecAffine (pushed) = (Over.map σ).map fromSpecAffine`
(`Over.OverMorphism.ext`). -/
private theorem crossBaseAffineIso_hom_whiskerLeft_fromSpecAffine (T : Over (Spec (.of L)))
    (U : T.left.affineOpens) :
    letI : Algebra k Γ(T.left, U.1) := Over.sectionsAlgebra
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) U.1
    haveI : IsScalarTower k L Γ(T.left, U.1) := Over.isScalarTower_sections_map k L T U.1
    (crossBaseAffineIso k L C Γ(T.left, U.1)).hom
        ≫ (C ◁ Over.fromSpecAffine
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) ⟨U.1, U.2⟩).left
      = (((baseChange k L).obj C) ◁ Over.fromSpecAffine T U).left
          ≫ (crossBaseIso k L C T).hom := by
  letI : Algebra k Γ(T.left, U.1) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) U.1
  haveI : IsScalarTower k L Γ(T.left, U.1) := Over.isScalarTower_sections_map k L T U.1
  have hbridge : (mapOverSpecIso k L Γ(T.left, U.1)).hom
        ≫ Over.fromSpecAffine
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) ⟨U.1, U.2⟩
      = (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map
          (Over.fromSpecAffine T U) := Over.OverMorphism.ext (Category.id_comp _)
  have hover : (C ◁ (mapOverSpecIso k L Γ(T.left, U.1)).hom)
        ≫ (C ◁ Over.fromSpecAffine
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) ⟨U.1, U.2⟩)
      = C ◁ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map
          (Over.fromSpecAffine T U) := by
    rw [← MonoidalCategory.whiskerLeft_comp, hbridge]
  have key := congrArg Over.Hom.left hover
  rw [Over.comp_left] at key
  calc (crossBaseAffineIso k L C Γ(T.left, U.1)).hom
          ≫ (C ◁ Over.fromSpecAffine
              ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) ⟨U.1, U.2⟩).left
      = (crossBaseIso k L C (overSpec L Γ(T.left, U.1))).hom
          ≫ ((C ◁ (mapOverSpecIso k L Γ(T.left, U.1)).hom).left
            ≫ (C ◁ Over.fromSpecAffine
                ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)
                  ⟨U.1, U.2⟩).left) := by
        rw [crossBaseAffineIso_hom, Category.assoc]
    _ = (crossBaseIso k L C (overSpec L Γ(T.left, U.1))).hom
          ≫ (C ◁ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map
              (Over.fromSpecAffine T U)).left :=
        congrArg (fun m => (crossBaseIso k L C (overSpec L Γ(T.left, U.1))).hom ≫ m) key
    _ = (((baseChange k L).obj C) ◁ Over.fromSpecAffine T U).left
          ≫ (crossBaseIso k L C T).hom :=
        (crossBaseIso_naturality k L C (Over.fromSpecAffine T U)).symm

/-- **The general-test naturality of the base-field shuffle vs the étale unit**: for an
`L`-test `T`, shuffling the unit image of a relative Picard class on the pushed-forward
test `(Over.map σ).obj T` equals the unit image on `T` of the class transported along the
cross-base comparison iso `crossBaseIso`.  The general-test lift of the affine
`PicEtAff.baseFieldShuffle_unit`, proved affine open by affine open through the
affine/general reconciliation `crossBaseAffineIso_hom_whiskerLeft_fromSpecAffine`. -/
theorem picEtCrossBase_relPicToPicEt (T : Over (Spec (.of L)))
    (Λ : (C ⊗ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T).left.CechPic) :
    picEtCrossBase k L C T (relPicToPicEt C
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)
        (relPicMk C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) Λ))
      = relPicToPicEt ((baseChange k L).obj C) T
          (relPicMk ((baseChange k L).obj C) T (CechPic.map (crossBaseIso k L C T).hom Λ)) := by
  refine picEt.ext fun U => ?_
  letI iA : Algebra k Γ(T.left, U.1) := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) U.1
  haveI itA : IsScalarTower k L Γ(T.left, U.1) := Over.isScalarTower_sections_map k L T U.1
  have hcech : CechPic.map (crossBaseAffineIso k L C Γ(T.left, U.1)).hom
        (CechPic.map (C ◁ Over.fromSpecAffine
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) ⟨U.1, U.2⟩).left Λ)
      = CechPic.map (((baseChange k L).obj C) ◁ Over.fromSpecAffine T U).left
          (CechPic.map (crossBaseIso k L C T).hom Λ) := by
    have hsq := crossBaseAffineIso_hom_whiskerLeft_fromSpecAffine C T U
    calc CechPic.map (crossBaseAffineIso k L C Γ(T.left, U.1)).hom
            (CechPic.map (C ◁ Over.fromSpecAffine
              ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) ⟨U.1, U.2⟩).left Λ)
        = CechPic.map ((crossBaseAffineIso k L C Γ(T.left, U.1)).hom
            ≫ (C ◁ Over.fromSpecAffine
              ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) ⟨U.1, U.2⟩).left)
            Λ := by rw [Scheme.CechPic.map_comp]; rfl
      _ = CechPic.map ((((baseChange k L).obj C) ◁ Over.fromSpecAffine T U).left
            ≫ (crossBaseIso k L C T).hom) Λ := congrArg (fun φ => CechPic.map φ Λ) hsq
      _ = CechPic.map (((baseChange k L).obj C) ◁ Over.fromSpecAffine T U).left
            (CechPic.map (crossBaseIso k L C T).hom Λ) := by rw [Scheme.CechPic.map_comp]; rfl
  change PicEtAff.baseFieldShuffle k L C Γ(T.left, U.1)
      (PicEtAff.unit C Γ(T.left, U.1) (relPicMk C (overSpec k Γ(T.left, U.1))
        (CechPic.map (C ◁ Over.fromSpecAffine
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) ⟨U.1, U.2⟩).left Λ)))
    = PicEtAff.unit ((baseChange k L).obj C) Γ(T.left, U.1)
        (relPicMk ((baseChange k L).obj C) (overSpec L Γ(T.left, U.1))
          (CechPic.map (((baseChange k L).obj C) ◁ Over.fromSpecAffine T U).left
            (CechPic.map (crossBaseIso k L C T).hom Λ)))
  rw [PicEtAff.baseFieldShuffle_unit, relPicCrossBase_mk]
  exact congrArg (fun z => PicEtAff.unit ((baseChange k L).obj C) Γ(T.left, U.1)
    (relPicMk ((baseChange k L).obj C) (overSpec L Γ(T.left, U.1)) z)) hcech

end AlgebraicGeometry
