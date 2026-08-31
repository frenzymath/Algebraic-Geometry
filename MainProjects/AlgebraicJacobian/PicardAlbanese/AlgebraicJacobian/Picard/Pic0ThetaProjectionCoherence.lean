/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ThetaAssembly
import AlgebraicJacobian.Picard.Pic0Pullback

/-!
# Projection coherence for the degree-zero Picard base-change comparison

This file supplies the scheme-level equalities used to compare the affine transport
families underlying `pic0Theta`. It proves that the inverse same-carrier comparison has
the expected first projection over any field extension, and identifies the whole
comparison at the identity extension with whiskering by `baseChange.idIso`.

The proof keeps the proof-bearing `eqToIso` in `baseChange.idIso` opaque. Its component
projection is obtained from adjunction conjugation and proof irrelevance, avoiding a
large simplifier expansion of `Over.pullbackId`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-! ## Congruence of étale-plus transports (the reduction key)

Both the base-field shuffle (`PicEtAff.baseFieldShuffle`, via `crossBaseTransportFamily`) and
the curve transport (`PicEtAff.curveMap`, via `curveTransportFamily`) are
`RelPicTransportFamily.picEtAffHom`s, and `picEtAffHom_mk`/`descentHom_coe`/`relPicHom_mk`
express the transport as `CechPic.map` of the family's `hom` scheme morphism. Hence two
families with pointwise-equal `hom` fields induce equal transports — the lemma through which
the two θ-cocycle atoms reduce to a scheme-morphism identity on the product carriers. -/
theorem RelPicTransportFamily.picEtAffHom_congr {kD kE kT : Type u}
    [Field kD] [Field kE] [Field kT] [Algebra kD kT] [Algebra kE kT]
    {D : Over (Spec (.of kD))} {E : Over (Spec (.of kE))}
    (S T : RelPicTransportFamily kT D E)
    (h : ∀ (B : Type u) [CommRing B] [Algebra kD B] [Algebra kE B] [Algebra kT B]
      [IsScalarTower kD kT B] [IsScalarTower kE kT B], S.hom B = T.hom B)
    (A : Type u) [CommRing A] [Algebra kD A] [Algebra kE A] [Algebra kT A]
    [IsScalarTower kD kT A] [IsScalarTower kE kT A] (a : PicEtAff E A) :
    S.picEtAffHom A a = T.picEtAffHom A a := by
  induction a using PicEtAff.ind with
  | _ U x =>
    rw [RelPicTransportFamily.picEtAffHom_mk, RelPicTransportFamily.picEtAffHom_mk]
    refine congrArg (PicEtAff.mk D U) (Subtype.ext ?_)
    rw [RelPicTransportFamily.descentHom_coe, RelPicTransportFamily.descentHom_coe]
    generalize (x : relPic E (overSpec kE U.Carrier)) = y
    induction y using relPic.ind with
    | mk L =>
      rw [RelPicTransportFamily.relPicHom_mk, RelPicTransportFamily.relPicHom_mk, h]

/-! ## Base-change-identity/composite pullback helpers -/

open Limits in
/-- `Over.pullbackId`'s forward comparison has first projection the identity: the
base-change-along-`𝟙` section reads off the original object on the first factor. -/
theorem pullbackId_hom_app_left.{w} {D : Type w} [Category.{u} D] [HasPullbacks D]
    {S : D} (X : Over S) :
    (Over.pullbackId.hom.app X).left = pullback.fst X.hom (𝟙 S) := by
  change ((conjugateEquiv (Over.mapPullbackAdj (𝟙 S))
    (Adjunction.id (C := Over S)) (Over.mapId S).inv).app X).left = _
  rw [conjugateEquiv_adjunction_id]
  simp only [Over.comp_left, Over.mapId_inv_app_left,
    Over.mapPullbackAdj_counit_app, Over.homMk_left]
  simp

open Limits in
private theorem pullbackId_transport_hom_app_left.{w}
    {D : Type w} [Category.{u} D] [HasPullbacks D] {S : D}
    (f : S ⟶ S) (hf : f = 𝟙 S)
    (h : Over.pullback f = Over.pullback (𝟙 S)) (X : Over S) :
    ((eqToIso h ≪≫ Over.pullbackId).hom.app X).left = pullback.fst X.hom f := by
  subst f
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_refl,
    Over.comp_left, Category.id_comp] using pullbackId_hom_app_left X

open Limits in
/-- The forward identity base-change iso on the frozen `Challenge` spelling has first
projection `pullback.fst` along the trivial base map. -/
theorem baseChange_idIso_hom_app_left (k : Type u) [Field k] (C : Over (Spec (.of k))) :
    ((baseChange.idIso k).app C).hom.left
      = pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
  unfold baseChange.idIso
  exact pullbackId_transport_hom_app_left _ (by simp) _ C

open MonoidalCategory CartesianMonoidalCategory in
/-- The inverse same-carrier comparison followed by the first projection is the first
projection of the original curve, after composing with the base-change pullback map. -/
theorem crossBaseAffineIso_inv_fst (k L : Type u) [Field k] [Field L]
    [Algebra k L] (C : Over (Spec (.of k))) (A : Type u) [CommRing A]
    [Algebra k A] [Algebra L A] [IsScalarTower k L A] :
    (crossBaseAffineIso k L C A).inv ≫
        ((fst ((baseChange k L).obj C) (overSpec L A)).left ≫
          Limits.pullback.fst C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k L)))) =
      (fst C (overSpec k A)).left := by
  rw [crossBaseAffineIso, Iso.trans_inv, Functor.mapIso_inv, Category.assoc,
    Over.crossBaseIso_inv_fst]
  change (C ◁ (mapOverSpecIso k L A).inv).left ≫
    (fst C ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj
      (overSpec L A))).left = (fst C (overSpec k A)).left
  exact Over.whiskerLeft_left_fst (mapOverSpecIso k L A).inv

/-! ## The identity-extension comparison

The K-1a Leg-4 atom is the scheme identity
`((baseChange.idIso k).app C).inv ▷ overSpec k B).left = (crossBaseAffineIso k k C B).inv`,
is proved by `(Over.isPullback_left _ _).hom_ext` on the two projections. -/

open MonoidalCategory CartesianMonoidalCategory in
/-- **The `snd` leg of the K-1a Leg-4 atom**: the whiskered identity base-change comparison
and the affine same-carrier comparison agree on the second projection — both are
`(snd C (overSpec k B)).left`.

Term-mode by necessity: the identity base change spells its codomain `(𝟭 _).obj C`, so `rw`
reports "did not find an occurrence" on a goal that visibly contains the pattern (the R4/R5
spelling friction of I-0216, measured here). -/
theorem crossBaseAffineIso_inv_whiskerRight_snd (k : Type u) [Field k]
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (B : Type u) [CommRing B] [Algebra k B] :
    (((baseChange.idIso k).app C).inv ▷ overSpec k B).left
        ≫ (snd ((baseChange k k).obj C) (overSpec k B)).left
      = (crossBaseAffineIso k k C B).inv
          ≫ (snd ((baseChange k k).obj C) (overSpec k B)).left := by
  calc
    (((baseChange.idIso k).app C).inv ▷ overSpec k B).left ≫
        (snd ((baseChange k k).obj C) (overSpec k B)).left =
      (snd ((𝟭 (Over (Spec (.of k)))).obj C) (overSpec k B)).left :=
      Over.whiskerRight_left_snd ((baseChange.idIso k).app C).inv
    _ = (snd C (overSpec k B)).left := rfl
    _ = (crossBaseAffineIso k k C B).inv ≫
        (snd ((baseChange k k).obj C) (overSpec k B)).left :=
      (crossBaseAffineIso_inv_snd k k C B).symm

open MonoidalCategory CartesianMonoidalCategory in
/-- The inverse cross-base comparison and the whiskered identity base-change comparison
agree on the first projection. -/
theorem crossBaseAffineIso_inv_whiskerRight_fst (k : Type u) [Field k]
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (B : Type u) [CommRing B] [Algebra k B] :
    (((baseChange.idIso k).app C).inv ▷ overSpec k B).left
        ≫ (fst ((baseChange k k).obj C) (overSpec k B)).left =
      (crossBaseAffineIso k k C B).inv
        ≫ (fst ((baseChange k k).obj C) (overSpec k B)).left := by
  haveI : IsIso
      (Limits.pullback.fst C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k k)))) := by
    rw [← baseChange_idIso_hom_app_left k C]
    exact ((Over.forget _).mapIso ((baseChange.idIso k).app C)).isIso_hom
  apply (cancel_mono
    (Limits.pullback.fst C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k k))))).1
  have hunit :
      (((fst ((𝟭 (Over (Spec (.of k)))).obj C) (overSpec k B)).left ≫
          ((baseChange.idIso k).app C).inv.left) ≫
        Limits.pullback.fst C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k k)))) =
        (fst ((𝟭 (Over (Spec (.of k)))).obj C) (overSpec k B)).left := by
    have hcancel : ((baseChange.idIso k).app C).inv.left ≫
        ((baseChange.idIso k).app C).hom.left = 𝟙 _ :=
      Over.inv_left_hom_left ((baseChange.idIso k).app C)
    calc
      (((fst ((𝟭 (Over (Spec (.of k)))).obj C) (overSpec k B)).left ≫
            ((baseChange.idIso k).app C).inv.left) ≫
          Limits.pullback.fst C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k k)))) =
        (fst ((𝟭 (Over (Spec (.of k)))).obj C) (overSpec k B)).left ≫
          (((baseChange.idIso k).app C).inv.left ≫
            ((baseChange.idIso k).app C).hom.left) := by
        rw [← baseChange_idIso_hom_app_left, Category.assoc]
        rfl
      _ = (fst ((𝟭 (Over (Spec (.of k)))).obj C) (overSpec k B)).left ≫ 𝟙 _ :=
        congrArg (fun q =>
          (fst ((𝟭 (Over (Spec (.of k)))).obj C) (overSpec k B)).left ≫ q) hcancel
      _ = (fst ((𝟭 (Over (Spec (.of k)))).obj C) (overSpec k B)).left :=
        Category.comp_id _
  have hunit' :
      (((fst ((𝟭 (Over (Spec (.of k)))).obj C) (overSpec k B)).left ≫
          ((baseChange.idIso k).app C).inv.left) ≫
        Limits.pullback.fst C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k k)))) =
        (fst C (overSpec k B)).left := by
    simpa only [Functor.id_obj] using hunit
  calc
    ((((baseChange.idIso k).app C).inv ▷ overSpec k B).left
          ≫ (fst ((baseChange k k).obj C) (overSpec k B)).left) ≫
        Limits.pullback.fst C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k k))) =
      (((fst ((𝟭 (Over (Spec (.of k)))).obj C) (overSpec k B)).left ≫
          ((baseChange.idIso k).app C).inv.left) ≫
        Limits.pullback.fst C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k k)))) :=
      congrArg (fun q => q ≫ Limits.pullback.fst C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k k))))
        (Over.whiskerRight_left_fst ((baseChange.idIso k).app C).inv)
    _ = (fst C (overSpec k B)).left := hunit'
    _ = ((crossBaseAffineIso k k C B).inv ≫
          (fst ((baseChange k k).obj C) (overSpec k B)).left) ≫
        Limits.pullback.fst C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
      rw [Category.assoc, crossBaseAffineIso_inv_fst]

open MonoidalCategory CartesianMonoidalCategory in
/-- The inverse same-carrier comparison at the identity field extension is exactly
whiskering by the inverse identity base-change comparison. -/
theorem crossBaseAffineIso_inv_eq_whiskerRight (k : Type u) [Field k]
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (B : Type u) [CommRing B] [Algebra k B] :
    (crossBaseAffineIso k k C B).inv =
      (((baseChange.idIso k).app C).inv ▷ overSpec k B).left := by
  apply (Over.isPullback_left ((baseChange k k).obj C) (overSpec k B)).hom_ext
  · exact (crossBaseAffineIso_inv_whiskerRight_fst k C B).symm
  · exact (crossBaseAffineIso_inv_whiskerRight_snd k C B).symm

/-! ## Composite base change

The tower cocycle needs the projection formula for mathlib's adjunction-defined
`Over.pullbackComp`.  We derive it from the counit characterization of conjugate
natural transformations, then transport it across the proof-bearing equality used by
the frozen `baseChange.compIso` spelling. -/

open Limits in
private theorem pullbackComp_hom_app_left_fst_fst.{w} {D : Type w}
    [Category.{u} D] [HasPullbacks D] {X Y Z : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Over Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫
        pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g =
      pullback.fst A.hom (f ≫ g) := by
  have h := conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)) (Over.mapComp f g).inv A
  have hl := congrArg Over.Hom.left h
  simp only [Functor.comp_map, Over.map_map_left, Adjunction.comp_counit_app,
    Over.comp_left, Over.mapPullbackAdj_counit_app, Over.homMk_left,
    Over.mapComp_inv_app_left] at hl
  change (((conjugateEquiv (Over.mapPullbackAdj (f ≫ g))
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)))
      (Over.mapComp f g).inv).app A).left ≫
      pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g = _
  exact hl.trans (Category.id_comp _)

open Limits in
private theorem pullbackComp_transport_hom_app_left_fst_fst.{w} {D : Type w}
    [Category.{u} D] [HasPullbacks D] {X Y Z : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (h : Over.pullback fg = Over.pullback (f ≫ g)) (A : Over Z) :
    ((eqToIso h ≪≫ Over.pullbackComp f g).hom.app A).left ≫
        pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g =
      pullback.fst A.hom fg := by
  subst fg
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_refl,
    Over.comp_left, Category.id_comp] using pullbackComp_hom_app_left_fst_fst f g A

open Limits in
/-- The forward frozen tower comparison preserves the composite first projection. -/
theorem baseChange_compIso_hom_app_left_fst_fst (k L M : Type u)
    [Field k] [Field L] [Field M] [Algebra k L] [Algebra L M] [Algebra k M]
    [IsScalarTower k L M] (C : Over (Spec (.of k))) :
    ((baseChange.compIso k L M).app C).hom.left ≫
        pullback.fst ((baseChange k L).obj C).hom
          (Spec.map (CommRingCat.ofHom (algebraMap L M))) ≫
        pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k M))) := by
  unfold baseChange.compIso
  exact pullbackComp_transport_hom_app_left_fst_fst
    (Spec.map (CommRingCat.ofHom (algebraMap L M)))
    (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (Spec.map (CommRingCat.ofHom (algebraMap k M)))
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]) _ C

open Limits in
/-- The inverse frozen tower comparison reads the iterated first projection. -/
theorem baseChange_compIso_inv_app_left_fst_fst (k L M : Type u)
    [Field k] [Field L] [Field M] [Algebra k L] [Algebra L M] [Algebra k M]
    [IsScalarTower k L M] (C : Over (Spec (.of k))) :
    ((baseChange.compIso k L M).app C).inv.left ≫
        pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k M))) =
      pullback.fst ((baseChange k L).obj C).hom
          (Spec.map (CommRingCat.ofHom (algebraMap L M))) ≫
        pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  calc
    ((baseChange.compIso k L M).app C).inv.left ≫
        pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k M))) =
      ((baseChange.compIso k L M).app C).inv.left ≫
        (((baseChange.compIso k L M).app C).hom.left ≫
          pullback.fst ((baseChange k L).obj C).hom
            (Spec.map (CommRingCat.ofHom (algebraMap L M))) ≫
          pullback.fst C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
      congrArg (fun q => ((baseChange.compIso k L M).app C).inv.left ≫ q)
        (baseChange_compIso_hom_app_left_fst_fst k L M C).symm
    _ = pullback.fst ((baseChange k L).obj C).hom
          (Spec.map (CommRingCat.ofHom (algebraMap L M))) ≫
        pullback.fst C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
      rw [← Category.assoc, Over.inv_left_hom_left, Category.id_comp]
      rfl

open MonoidalCategory CartesianMonoidalCategory in
/-- The inverse affine same-carrier comparison over `k → M` is the composite of the
comparisons over `k → L` and `L → M`, followed by transport along the inverse
`baseChange.compIso`. -/
theorem crossBaseAffineIso_inv_tower
    (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M]
    (C : Over (Spec (.of k))) (B : Type u) [CommRing B]
    [Algebra k B] [Algebra L B] [Algebra M B]
    [IsScalarTower k L B] [IsScalarTower L M B] [IsScalarTower k M B] :
    (crossBaseAffineIso k M C B).inv =
      (crossBaseAffineIso k L C B).inv ≫
        (crossBaseAffineIso L M ((baseChange k L).obj C) B).inv ≫
          (((baseChange.compIso k L M).app C).inv ▷ overSpec M B).left := by
  let CL := (baseChange k L).obj C
  let CLM := (baseChange k L ⋙ baseChange L M).obj C
  let CM := (baseChange k M).obj C
  let eKM : (C ⊗ overSpec k B).left ⟶ (CM ⊗ overSpec M B).left :=
    (crossBaseAffineIso k M C B).inv
  let eKL : (C ⊗ overSpec k B).left ⟶ (CL ⊗ overSpec L B).left :=
    (crossBaseAffineIso k L C B).inv
  let eLM : (CL ⊗ overSpec L B).left ⟶ (CLM ⊗ overSpec M B).left :=
    (crossBaseAffineIso L M CL B).inv
  let g : (CLM ⊗ overSpec M B).left ⟶ (CM ⊗ overSpec M B).left :=
    (((baseChange.compIso k L M).app C).inv ▷ overSpec M B).left
  let fM : (CM ⊗ overSpec M B).left ⟶ CM.left :=
    (fst CM (overSpec M B)).left
  let fLM : (CLM ⊗ overSpec M B).left ⟶ CLM.left :=
    (fst CLM (overSpec M B)).left
  let fL : (CL ⊗ overSpec L B).left ⟶ CL.left :=
    (fst CL (overSpec L B)).left
  let fk : (C ⊗ overSpec k B).left ⟶ C.left :=
    (fst C (overSpec k B)).left
  let sM : (CM ⊗ overSpec M B).left ⟶ Spec (.of B) :=
    (snd CM (overSpec M B)).left
  let sLM : (CLM ⊗ overSpec M B).left ⟶ Spec (.of B) :=
    (snd CLM (overSpec M B)).left
  let sL : (CL ⊗ overSpec L B).left ⟶ Spec (.of B) :=
    (snd CL (overSpec L B)).left
  let sk : (C ⊗ overSpec k B).left ⟶ Spec (.of B) :=
    (snd C (overSpec k B)).left
  let pKM : CM.left ⟶ C.left :=
    Limits.pullback.fst C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k M)))
  let pLM : CLM.left ⟶ CL.left :=
    Limits.pullback.fst CL.hom
      (Spec.map (CommRingCat.ofHom (algebraMap L M)))
  let pKL : CL.left ⟶ C.left :=
    Limits.pullback.fst C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  let qKM : CM.left ⟶ Spec (.of M) :=
    Limits.pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k M)))
  let bM : Spec (.of B) ⟶ Spec (.of M) := (overSpec M B).hom
  let c : CLM.left ⟶ CM.left :=
    ((baseChange.compIso k L M).app C).inv.left
  change eKM = eKL ≫ eLM ≫ g
  have hsKM : eKM ≫ sM = sk :=
    crossBaseAffineIso_inv_snd k M C B
  have hsKL : eKL ≫ sL = sk :=
    crossBaseAffineIso_inv_snd k L C B
  have hsLM : eLM ≫ sLM = sL :=
    crossBaseAffineIso_inv_snd L M CL B
  have hgs : g ≫ sM = sLM :=
    Over.whiskerRight_left_snd ((baseChange.compIso k L M).app C).inv
  have hsnd : eKM ≫ sM = (eKL ≫ eLM ≫ g) ≫ sM := by
    apply hsKM.trans
    symm
    calc
      (eKL ≫ eLM ≫ g) ≫ sM = eKL ≫ (eLM ≫ (g ≫ sM)) := by
        simp only [Category.assoc]
      _ = eKL ≫ (eLM ≫ sLM) :=
        congrArg (fun q => eKL ≫ (eLM ≫ q)) hgs
      _ = eKL ≫ sL := congrArg (fun q => eKL ≫ q) hsLM
      _ = sk := hsKL
  have hKM : eKM ≫ fM ≫ pKM = fk :=
    crossBaseAffineIso_inv_fst k M C B
  have hKL : eKL ≫ fL ≫ pKL = fk :=
    crossBaseAffineIso_inv_fst k L C B
  have hLM : eLM ≫ fLM ≫ pLM = fL :=
    crossBaseAffineIso_inv_fst L M CL B
  have hgf : g ≫ fM = fLM ≫ c :=
    Over.whiskerRight_left_fst ((baseChange.compIso k L M).app C).inv
  have hc : c ≫ pKM = pLM ≫ pKL :=
    baseChange_compIso_inv_app_left_fst_fst k L M C
  have hprojC :
      (eKM ≫ fM) ≫ pKM = ((eKL ≫ eLM ≫ g) ≫ fM) ≫ pKM := by
    apply hKM.trans
    calc
      fk = eKL ≫ fL ≫ pKL := hKL.symm
      _ = eKL ≫ (eLM ≫ fLM ≫ pLM) ≫ pKL :=
        congrArg (fun q => eKL ≫ q ≫ pKL) hLM.symm
      _ = eKL ≫ eLM ≫ fLM ≫ (pLM ≫ pKL) := by
        simp only [Category.assoc]
      _ = eKL ≫ eLM ≫ fLM ≫ (c ≫ pKM) :=
        congrArg (fun q => eKL ≫ eLM ≫ fLM ≫ q) hc.symm
      _ = eKL ≫ eLM ≫ (fLM ≫ c) ≫ pKM := by
        simp only [Category.assoc]
      _ = eKL ≫ eLM ≫ (g ≫ fM) ≫ pKM :=
        congrArg (fun q => eKL ≫ eLM ≫ q ≫ pKM) hgf.symm
      _ = ((eKL ≫ eLM ≫ g) ≫ fM) ≫ pKM := by
        simp only [Category.assoc]
  have hprod : fM ≫ qKM = sM ≫ bM :=
    (Over.isPullback_left CM (overSpec M B)).w
  have hprojM :
      (eKM ≫ fM) ≫ qKM = ((eKL ≫ eLM ≫ g) ≫ fM) ≫ qKM := by
    calc
      (eKM ≫ fM) ≫ qKM = eKM ≫ (sM ≫ bM) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun q => eKM ≫ q) hprod)
      _ = (eKM ≫ sM) ≫ bM := (Category.assoc _ _ _).symm
      _ = ((eKL ≫ eLM ≫ g) ≫ sM) ≫ bM :=
        congrArg (fun q => q ≫ bM) hsnd
      _ = (eKL ≫ eLM ≫ g) ≫ (sM ≫ bM) :=
        Category.assoc _ _ _
      _ = ((eKL ≫ eLM ≫ g) ≫ fM) ≫ qKM :=
        ((Category.assoc _ _ _).trans
          (congrArg (fun q => (eKL ≫ eLM ≫ g) ≫ q) hprod)).symm
  have hfst : eKM ≫ fM = (eKL ≫ eLM ≫ g) ≫ fM := by
    apply Limits.pullback.hom_ext
    · exact hprojC
    · exact hprojM
  apply (Over.isPullback_left CM (overSpec M B)).hom_ext
  · exact hfst
  · exact hsnd

private theorem crossBase_relPicHom_tower
    (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M]
    (C : Over (Spec (.of k))) (B : Type u) [CommRing B]
    [Algebra k B] [Algebra L B] [Algebra M B]
    [IsScalarTower k L B] [IsScalarTower L M B] [IsScalarTower k M B]
    (g : (baseChange L M).obj ((baseChange k L).obj C) ⟶ (baseChange k M).obj C)
    (hg : g = ((baseChange.compIso k L M).app C).inv)
    (x : relPic ((baseChange k M).obj C) (overSpec M B)) :
    (crossBaseTransportFamilyInv k M C).relPicHom B x =
      (crossBaseTransportFamilyInv k L C).relPicHom B
        ((crossBaseTransportFamilyInv L M ((baseChange k L).obj C)).relPicHom B
          ((curveTransportFamily g).relPicHom B x)) := by
  induction x using relPic.ind with
  | mk Λ =>
      rw [RelPicTransportFamily.relPicHom_mk, RelPicTransportFamily.relPicHom_mk,
        RelPicTransportFamily.relPicHom_mk, RelPicTransportFamily.relPicHom_mk]
      refine congrArg (relPicMk C (overSpec k B)) ?_
      rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply,
        ← Scheme.CechPic.map_comp, ← Scheme.CechPic.map_comp,
        crossBaseTransportFamilyInv_hom, crossBaseTransportFamilyInv_hom,
        crossBaseTransportFamilyInv_hom, curveTransportFamily_hom,
        hg,
        crossBaseAffineIso_inv_tower k L M C B]
      rw [Category.assoc]
      rfl

private theorem crossBase_picEtAffHom_tower_mk
    (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M]
    (C : Over (Spec (.of k))) (B : Type u) [CommRing B]
    [Algebra k B] [Algebra L B] [Algebra M B]
    [IsScalarTower k L B] [IsScalarTower L M B] [IsScalarTower k M B]
    (g : (baseChange L M).obj ((baseChange k L).obj C) ⟶ (baseChange k M).obj C)
    (hg : g = ((baseChange.compIso k L M).app C).inv)
    (U : Algebra.EtaleCover B)
    (x : descentClasses ((baseChange k M).obj C) U) :
    (crossBaseTransportFamilyInv k M C).picEtAffHom B (PicEtAff.mk _ U x) =
      (crossBaseTransportFamilyInv k L C).picEtAffHom B
        ((crossBaseTransportFamilyInv L M ((baseChange k L).obj C)).picEtAffHom B
          ((curveTransportFamily g).picEtAffHom B (PicEtAff.mk _ U x))) := by
  rw [RelPicTransportFamily.picEtAffHom_mk, RelPicTransportFamily.picEtAffHom_mk,
    RelPicTransportFamily.picEtAffHom_mk, RelPicTransportFamily.picEtAffHom_mk]
  refine congrArg (PicEtAff.mk C U) (Subtype.ext ?_)
  rw [RelPicTransportFamily.descentHom_coe, RelPicTransportFamily.descentHom_coe,
    RelPicTransportFamily.descentHom_coe, RelPicTransportFamily.descentHom_coe]
  exact crossBase_relPicHom_tower k L M C U.Carrier g hg
    (x : relPic ((baseChange k M).obj C) (overSpec M U.Carrier))

/-- The inverse affine base-field shuffle over a scalar tower is the composite of the two
successive inverse shuffles and transport along the frozen curve comparison. -/
theorem PicEtAff.baseFieldShuffle_symm_tower
    (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M]
    (C : Over (Spec (.of k))) (B : Type u) [CommRing B]
    [Algebra k B] [Algebra L B] [Algebra M B]
    [IsScalarTower k L B] [IsScalarTower L M B] [IsScalarTower k M B]
    (a : PicEtAff ((baseChange k M).obj C) B) :
    (PicEtAff.baseFieldShuffle k M C B).symm a =
      (PicEtAff.baseFieldShuffle k L C B).symm
        ((PicEtAff.baseFieldShuffle L M ((baseChange k L).obj C) B).symm
          (PicEtAff.curveMap B ((baseChange.compIso k L M).app C).inv a)) := by
  let g : (baseChange L M).obj ((baseChange k L).obj C) ⟶ (baseChange k M).obj C :=
    ((baseChange.compIso k L M).app C).inv
  change (crossBaseTransportFamilyInv k M C).picEtAffHom B a =
    (crossBaseTransportFamilyInv k L C).picEtAffHom B
      ((crossBaseTransportFamilyInv L M ((baseChange k L).obj C)).picEtAffHom B
        ((curveTransportFamily g).picEtAffHom B a))
  induction a using PicEtAff.ind with
  | mk U x =>
    exact crossBase_picEtAffHom_tower_mk k L M C B g (by rfl) U x

end AlgebraicGeometry
