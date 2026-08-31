/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ThetaProjectionCoherence

/-!
# Identity coherence for the degree-zero Picard base-change comparison

This file proves that `pic0Theta` over the identity field extension agrees with the
canonical collapse of the base-changed curve and pushed test object.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

section Identity

variable (k : Type u) [Field k]
variable (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- The iso-grade curve transport at the identity base change. -/
noncomputable def eCurveId : pic0Functor ((baseChange k k).obj C) ≅ pic0Functor C where
  hom := pic0PullbackNat ((baseChange.idIso k).app C).inv
  inv := pic0PullbackNat ((baseChange.idIso k).app C).hom
  hom_inv_id := by rw [← pic0PullbackNat_comp, Iso.hom_inv_id, pic0PullbackNat_id]
  inv_hom_id := by rw [← pic0PullbackNat_comp, Iso.inv_hom_id, pic0PullbackNat_id]

/-- Pushing a test object along the identity field map leaves its carrier unchanged. -/
noncomputable def mIdσ :
    Over.map (Spec.map (CommRingCat.ofHom (algebraMap k k))) ≅ 𝟭 (Over (Spec (.of k))) :=
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k k))
  have hσ : σ = 𝟙 (Spec (.of k)) := by
    dsimp [σ]
    simp
  NatIso.ofComponents (fun T => Over.isoMk (Iso.refl T.left) (by
    exact (Category.id_comp T.hom).trans
      ((congrArg (fun q => T.hom ≫ q) hσ).trans (Category.comp_id T.hom)).symm)) (fun f => by
      apply Over.OverMorphism.ext
      simp)

@[simp]
theorem mIdσ_hom_app_left (T : Over (Spec (.of k))) :
    ((mIdσ k).hom.app T).left = 𝟙 T.left := by
  simp [mIdσ]

private theorem algebra_eq_of_self_tower {B : Type u} [CommRing B]
    (iT iD : Algebra k B)
    (tw : @IsScalarTower k k B (Algebra.id k).toSMul iT.toSMul iD.toSMul) :
    iD = iT := by
  refine Algebra.algebra_ext _ _ fun r => ?_
  rw [@IsScalarTower.algebraMap_eq k k B _ _ _ (Algebra.id k) iT iD tw]
  rfl

/-- At the identity extension, the section algebra of a pushed test is the original
section algebra. -/
theorem sectionsAlgebra_mapSelf_eq (T : Over (Spec (.of k))) (U : T.left.Opens) :
    Over.sectionsAlgebra
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k k)))).obj T) U =
      Over.sectionsAlgebra T U := by
  exact algebra_eq_of_self_tower k
    (Over.sectionsAlgebra T U)
    (Over.sectionsAlgebra
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k k)))).obj T) U)
    (Over.isScalarTower_sections_map k k T U)

set_option linter.overlappingInstances false in
-- The transport core intentionally records the domain, codomain, and tower algebra slots.
private theorem identity_transport_hom_eq :
    ∀ (B : Type u) [CommRing B]
      [iD : Algebra k B] [iE : Algebra k B] [iT : Algebra k B]
      [twD : @IsScalarTower k k B (Algebra.id k).toSMul iT.toSMul iD.toSMul]
      [twE : @IsScalarTower k k B (Algebra.id k).toSMul iT.toSMul iE.toSMul],
      @RelPicTransportFamily.hom k k _ _ k _ (Algebra.id k) (Algebra.id k)
          C ((baseChange k k).obj C) (crossBaseTransportFamilyInv k k C)
          B _ iD iE iT twD twE =
        @RelPicTransportFamily.hom k k _ _ k _ (Algebra.id k) (Algebra.id k)
          C ((baseChange k k).obj C)
          (curveTransportFamily ((baseChange.idIso k).app C).inv)
          B _ iD iE iT twD twE := by
  intro B _ iD iE iT twD twE
  obtain rfl : iE = iD :=
    (algebra_eq_of_self_tower k iT iE twE).trans
      (algebra_eq_of_self_tower k iT iD twD).symm
  obtain rfl : iE = iT := algebra_eq_of_self_tower k iT iE twE
  rw [crossBaseTransportFamilyInv_hom, curveTransportFamily_hom,
    crossBaseAffineIso_inv_eq_whiskerRight]
  rfl

private theorem curve_transport_eq_mapAlg {D E : Over (Spec (.of k))} (g : D ⟶ E)
    {A : Type u} [CommRing A] (iD iE : Algebra k A) (hDE : iD = iE)
    (twD : @IsScalarTower k k A (Algebra.id k).toSMul iE.toSMul iD.toSMul)
    (twE : @IsScalarTower k k A (Algebra.id k).toSMul iE.toSMul iE.toSMul)
    (φ : @AlgHom k A A _ _ _ iE iD) (hφ : ∀ a, φ a = a)
    (a : @PicEtAff k _ E A _ iE) :
    @RelPicTransportFamily.picEtAffHom k k _ _ k _
        (Algebra.id k) (Algebra.id k) D E (curveTransportFamily g)
        A _ iD iE iE twD twE a =
      @PicEtAff.mapAlg k _ D A _ iE A _ iD φ
        (@PicEtAff.curveMap k _ D E A _ iE g a) := by
  cases hDE
  have hφ' : φ = AlgHom.id k A := AlgHom.ext fun x => hφ x
  subst φ
  rw [PicEtAff.mapAlg_id]
  rfl

set_option maxHeartbeats 1000000 in
-- The explicit equality of section-algebra instances requires a wider local budget.
private theorem sectionShuffle_symm_identity (T : Over (Spec (.of k)))
    (W : T.left.affineOpens)
    (hW : W.1 ≤ ((mIdσ k).hom.app T).left ⁻¹ᵁ W.1)
    (a : PicEtAff ((baseChange k k).obj C) Γ(T.left, W.1)) :
    (sectionShuffle k k C T W.1).symm a =
      PicEtAff.mapAlg C
        (Over.appLEAlgHom ((mIdσ k).hom.app T) W.1 W.1 hW)
        (PicEtAff.curveMap Γ(T.left, W.1) ((baseChange.idIso k).app C).inv a) := by
  let iD := Over.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k k)))).obj T) W.1
  let iE := Over.sectionsAlgebra T W.1
  let twD : @IsScalarTower k k Γ(T.left, W.1) (Algebra.id k).toSMul
      iE.toSMul iD.toSMul := Over.isScalarTower_sections_map k k T W.1
  let twE : @IsScalarTower k k Γ(T.left, W.1) (Algebra.id k).toSMul
      iE.toSMul iE.toSMul := .of_algebraMap_eq fun _ => rfl
  change @RelPicTransportFamily.picEtAffHom k k _ _ k _
      (Algebra.id k) (Algebra.id k) C ((baseChange k k).obj C)
      (crossBaseTransportFamilyInv k k C) Γ(T.left, W.1) _ iD iE iE twD twE a =
    @PicEtAff.mapAlg k _ C Γ(T.left, W.1) _ iE Γ(T.left, W.1) _ iD
      (Over.appLEAlgHom ((mIdσ k).hom.app T) W.1 W.1 hW)
      (@PicEtAff.curveMap k _ C ((baseChange k k).obj C) Γ(T.left, W.1) _ iE
        ((baseChange.idIso k).app C).inv a)
  calc
    _ = @RelPicTransportFamily.picEtAffHom k k _ _ k _
        (Algebra.id k) (Algebra.id k) C ((baseChange k k).obj C)
        (curveTransportFamily ((baseChange.idIso k).app C).inv)
        Γ(T.left, W.1) _ iD iE iE twD twE a := by
      exact @RelPicTransportFamily.picEtAffHom_congr k k k _ _ _
        (Algebra.id k) (Algebra.id k) C ((baseChange k k).obj C)
        (crossBaseTransportFamilyInv k k C)
        (curveTransportFamily ((baseChange.idIso k).app C).inv)
        (identity_transport_hom_eq k C) Γ(T.left, W.1) _ iD iE iE twD twE a
    _ = _ := by
      refine curve_transport_eq_mapAlg k ((baseChange.idIso k).app C).inv iD iE
        (sectionsAlgebra_mapSelf_eq k T W.1) twD twE _ ?_ a
      intro s
      change ((mIdσ k).hom.app T).left.appLE W.1 W.1 hW s = s
      rw [Scheme.Hom.appLE_congr_hom (mIdσ_hom_app_left k T) W.1 W.1 hW le_rfl]
      change Over.resAlgHom
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k k)))).obj T)
          (show W.1 ≤ W.1 from le_rfl) s = s
      rw [Over.resAlgHom_rfl]
      rfl

/-- The collapse of the pushed-test functor at the identity field extension. -/
noncomputable def σkkCollapse :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k k)))).op ⋙ pic0Functor C
      ≅ pic0Functor C :=
  Functor.isoWhiskerRight (NatIso.op (mIdσ k)).symm (pic0Functor C)
    ≪≫ Functor.leftUnitor (pic0Functor C)

/-- The canonical right-hand side of the theta identity coherence. -/
noncomputable def cocycleIdRHS :
    pic0Functor ((baseChange k k).obj C)
      ≅ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k k)))).op ⋙ pic0Functor C :=
  eCurveId k C ≪≫ (σkkCollapse k C).symm

set_option maxHeartbeats 1000000 in
-- Each affine value is compared before extensionality assembles the compatible family.
private theorem picEtCrossBaseInv_identity (T : (Over (Spec (.of k)))ᵒᵖ)
    (lam : (pic0Functor ((baseChange k k).obj C)).obj T) :
    picEtCrossBaseInv k k C (Opposite.unop T) lam.1 =
      picEtMap C ((mIdσ k).hom.app (Opposite.unop T))
        (picEtPullback ((baseChange.idIso k).app C).inv (Opposite.unop T) lam.1) := by
  apply Subtype.ext
  funext W
  have hW : W.1 ≤ ((mIdσ k).hom.app (Opposite.unop T)).left ⁻¹ᵁ W.1 := by
    rw [mIdσ_hom_app_left]
    exact le_rfl
  calc
    (picEtCrossBaseInv k k C (Opposite.unop T) lam.1).1 W =
        (sectionShuffle k k C (Opposite.unop T) W.1).symm
          (lam.1.1 ⟨W.1, W.2⟩) :=
      picEtCrossBaseInv_val k k C (Opposite.unop T) lam.1 W
    _ = PicEtAff.mapAlg C
        (Over.appLEAlgHom ((mIdσ k).hom.app (Opposite.unop T)) W.1 W.1 hW)
        (PicEtAff.curveMap Γ((Opposite.unop T).left, W.1)
          ((baseChange.idIso k).app C).inv (lam.1.1 ⟨W.1, W.2⟩)) :=
      sectionShuffle_symm_identity k C (Opposite.unop T) W hW _
    _ = PicEtAff.mapAlg C
        (Over.appLEAlgHom ((mIdσ k).hom.app (Opposite.unop T)) W.1 W.1 hW)
        ((picEtPullback ((baseChange.idIso k).app C).inv
          (Opposite.unop T) lam.1).1 W) :=
      congrArg (PicEtAff.mapAlg C
        (Over.appLEAlgHom ((mIdσ k).hom.app (Opposite.unop T)) W.1 W.1 hW))
        (picEtPullback_val ((baseChange.idIso k).app C).inv
          (Opposite.unop T) lam.1 W).symm
    _ = picEtMapVal C ((mIdσ k).hom.app (Opposite.unop T))
        (picEtPullback ((baseChange.idIso k).app C).inv
          (Opposite.unop T) lam.1) W :=
      (picEtMapVal_eq_mapAlg C ((mIdσ k).hom.app (Opposite.unop T))
        (picEtPullback ((baseChange.idIso k).app C).inv (Opposite.unop T) lam.1)
        (W := W) (V := W) hW).symm
    _ = (picEtMap C ((mIdσ k).hom.app (Opposite.unop T))
        (picEtPullback ((baseChange.idIso k).app C).inv
          (Opposite.unop T) lam.1)).1 W :=
      (picEtMap_val C ((mIdσ k).hom.app (Opposite.unop T))
        (picEtPullback ((baseChange.idIso k).app C).inv
          (Opposite.unop T) lam.1) W).symm

set_option maxHeartbeats 1000000 in
-- Unfolding both natural isomorphisms at one test object requires a wider local budget.
private theorem pic0Theta_id_app (T : (Over (Spec (.of k)))ᵒᵖ)
    (lam : (pic0Functor ((baseChange k k).obj C)).obj T) :
    (pic0Theta k k C).hom.app T lam = (cocycleIdRHS k C).hom.app T lam := by
  refine Subtype.ext ?_
  change picEtCrossBaseInv k k C (Opposite.unop T) lam.1 =
    picEtMap C ((mIdσ k).hom.app (Opposite.unop T))
      (picEtPullback ((baseChange.idIso k).app C).inv (Opposite.unop T) lam.1)
  exact picEtCrossBaseInv_identity k C T lam

/-- The theta comparison over `k -> k` is the canonical identity comparison. -/
theorem pic0Theta_id : pic0Theta k k C = cocycleIdRHS k C := by
  apply Iso.ext
  ext T lam
  exact pic0Theta_id_app k C T lam

end Identity

end AlgebraicGeometry
