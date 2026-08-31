/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ThetaCocycleIdentity

/-!
# The tower cocycle for the degree-zero Picard base-change comparison

This file contains the composition coherence for `pic0Theta` over a tower of field
extensions.  The identity coherence is proved in `Pic0ThetaCocycleIdentity`; separating the
two units keeps each large natural-isomorphism calculation independently kernel-checkable.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

section Cocycle

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M]
variable (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- The iso-grade curve transport at the tower composite: `pic0PullbackNat` of the frozen
`baseChange.compIso`. -/
noncomputable def eCurve :
    pic0Functor ((baseChange k M).obj C)
      ≅ pic0Functor ((baseChange k L ⋙ baseChange L M).obj C) where
  hom := pic0PullbackNat ((baseChange.compIso k L M).app C).inv
  inv := pic0PullbackNat ((baseChange.compIso k L M).app C).hom
  hom_inv_id := by rw [← pic0PullbackNat_comp, Iso.hom_inv_id, pic0PullbackNat_id]
  inv_hom_id := by rw [← pic0PullbackNat_comp, Iso.inv_hom_id, pic0PullbackNat_id]

/-- The `Over.mapComp` reassociation of the covariant base-change maps. -/
noncomputable def σMapCompIso :
    Over.map (Spec.map (CommRingCat.ofHom (algebraMap k M)))
      ≅ Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))
          ⋙ Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
  Over.mapCongr _ _ (by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap k M)) =
      Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k L)) by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]]) ≪≫
    Over.mapComp _ _

/-- The opposite-side bridge from the iterated pushforward to the composite pushforward. -/
noncomputable def αOp :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).op
        ⋙ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).op
      ≅ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k M)))).op :=
  eqToIso rfl ≪≫ NatIso.op (σMapCompIso k L M)

/-- The iterated right-hand side of the theta tower coherence. -/
noncomputable def cocycleRHS :
    pic0Functor ((baseChange k M).obj C)
      ≅ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k M)))).op ⋙
          pic0Functor C :=
  eCurve k L M C
    ≪≫ pic0Theta L M ((baseChange k L).obj C)
    ≪≫ Functor.isoWhiskerLeft
        (Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).op (pic0Theta k L C)
    ≪≫ (Functor.associator _ _ _).symm
    ≪≫ Functor.isoWhiskerRight (αOp k L M) (pic0Functor C)

/-- The theta comparison for `k → M` is the composite of the comparisons for
`k → L` and `L → M`, transported across the canonical pullback reassociation. -/
private theorem baseFieldShuffle_symm_tower_mapAlg
    (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M]
    (C : Over (Spec (.of k))) (B : Type u) [CommRing B]
    (iKD iKI : Algebra k B) (iL : Algebra L B) (iM : Algebra M B)
    (tKL : @IsScalarTower k L B (inferInstance : SMul k L)
      iL.toSMul iKI.toSMul)
    (tLM : @IsScalarTower L M B (inferInstance : SMul L M)
      iM.toSMul iL.toSMul)
    (tKM : @IsScalarTower k M B (inferInstance : SMul k M)
      iM.toSMul iKD.toSMul)
    (phi : @AlgHom k B B _ _ _ iKI iKD) (hphi : ∀ b, phi b = b)
    (a : @PicEtAff M _ ((baseChange k M).obj C) B _ iM) :
    (@PicEtAff.baseFieldShuffle k M _ _ _ C B _ iKD iM tKM).symm a =
      @PicEtAff.mapAlg k _ C B _ iKI B _ iKD phi
        ((@PicEtAff.baseFieldShuffle k L _ _ _ C B _ iKI iL tKL).symm
          ((@PicEtAff.baseFieldShuffle L M _ _ _ ((baseChange k L).obj C)
              B _ iL iM tLM).symm
            (@PicEtAff.curveMap M _ _ _ B _ iM
              ((baseChange.compIso k L M).app C).inv a))) := by
  have hK : iKI = iKD := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    exact (hphi (@algebraMap k B _ _ iKI r)).symm.trans
      (@AlgHom.commutes k B B _ _ _ iKI iKD phi r)
  cases hK
  have hphi' : phi = AlgHom.id k B := AlgHom.ext hphi
  subst phi
  rw [PicEtAff.mapAlg_id]
  exact @PicEtAff.baseFieldShuffle_symm_tower k L M _ _ _ _ _ _ _ C B _
    iKD iL iM tKL tLM tKM a

private theorem sectionShuffle_symm_tower_mapAlg
    (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M]
    (C : Over (Spec (.of k))) (T : Over (Spec (.of M)))
    (f : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k M)))).obj T ⟶
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).obj T))
    (hf : f.left = 𝟙 T.left) (W : T.left.affineOpens)
    (hW : W.1 ≤ f.left ⁻¹ᵁ W.1)
    (a : @PicEtAff M _ ((baseChange k M).obj C) Γ(T.left, W.1) _
      (Over.sectionsAlgebra T W.1)) :
    (sectionShuffle k M C T W.1).symm a =
      @PicEtAff.mapAlg k _ C Γ(T.left, W.1) _
        (Over.sectionsAlgebra
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).obj T)) W.1)
        Γ(T.left, W.1) _
          (Over.sectionsAlgebra
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k M)))).obj T) W.1)
        (Over.appLEAlgHom f W.1 W.1 hW)
        ((sectionShuffle k L C
            ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).obj T)
            W.1).symm
          ((sectionShuffle L M ((baseChange k L).obj C) T W.1).symm
            (@PicEtAff.curveMap M _ _ _ Γ(T.left, W.1) _
              (Over.sectionsAlgebra T W.1)
              ((baseChange.compIso k L M).app C).inv a))) := by
  let TI := (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).obj T)
  let TD := (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k M)))).obj T
  let TL := (Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).obj T
  let iKD := Over.sectionsAlgebra TD W.1
  let iKI := Over.sectionsAlgebra TI W.1
  let iL := Over.sectionsAlgebra TL W.1
  let iM := Over.sectionsAlgebra T W.1
  let tKL : @IsScalarTower k L Γ(T.left, W.1) (inferInstance : SMul k L)
      iL.toSMul iKI.toSMul := Over.isScalarTower_sections_map k L TL W.1
  let tLM : @IsScalarTower L M Γ(T.left, W.1) (inferInstance : SMul L M)
      iM.toSMul iL.toSMul := Over.isScalarTower_sections_map L M T W.1
  let tKM : @IsScalarTower k M Γ(T.left, W.1) (inferInstance : SMul k M)
      iM.toSMul iKD.toSMul := Over.isScalarTower_sections_map k M T W.1
  let phi : @AlgHom k Γ(T.left, W.1) Γ(T.left, W.1) _ _ _ iKI iKD :=
    Over.appLEAlgHom f W.1 W.1 hW
  have hphi : ∀ b, phi b = b := by
    intro b
    change f.left.appLE W.1 W.1 hW b = b
    rw [Scheme.Hom.appLE_congr_hom hf W.1 W.1 hW le_rfl]
    change Over.resAlgHom TI (show W.1 ≤ W.1 from le_rfl) b = b
    rw [Over.resAlgHom_rfl]
    rfl
  change (@PicEtAff.baseFieldShuffle k M _ _ _ C Γ(T.left, W.1) _
      iKD iM tKM).symm a =
    @PicEtAff.mapAlg k _ C Γ(T.left, W.1) _ iKI Γ(T.left, W.1) _ iKD phi
      ((@PicEtAff.baseFieldShuffle k L _ _ _ C Γ(T.left, W.1) _
          iKI iL tKL).symm
        ((@PicEtAff.baseFieldShuffle L M _ _ _ ((baseChange k L).obj C)
            Γ(T.left, W.1) _ iL iM tLM).symm
          (@PicEtAff.curveMap M _ _ _ Γ(T.left, W.1) _ iM
            ((baseChange.compIso k L M).app C).inv a)))
  exact baseFieldShuffle_symm_tower_mapAlg k L M C Γ(T.left, W.1)
    iKD iKI iL iM tKL tLM tKM phi hphi a

private theorem picEtCrossBaseInv_tower
    (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M]
    (C : Over (Spec (.of k))) (T : Over (Spec (.of M)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    (lam : picEt ((baseChange k M).obj C) T) :
    picEtCrossBaseInv k M C T lam =
      picEtMap C (((αOp k L M).hom.app (Opposite.op T)).unop)
        (picEtCrossBaseInv k L C
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).obj T)
          (picEtCrossBaseInv L M ((baseChange k L).obj C) T
            (picEtPullback ((baseChange.compIso k L M).app C).inv T lam))) := by
  let TD := (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k M)))).obj T
  let TL := (Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).obj T
  let TI := (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj TL
  apply Subtype.ext
  funext W
  let f : TD ⟶ TI := ((αOp k L M).hom.app (Opposite.op T)).unop
  have hf : f.left = 𝟙 T.left := rfl
  have hW : W.1 ≤ f.left ⁻¹ᵁ W.1 := by
    rw [hf]
    exact le_rfl
  let iM : Algebra M Γ(T.left, W.1) := Over.sectionsAlgebra T W.1
  let iL : Algebra L Γ(T.left, W.1) :=
    Over.sectionsAlgebra
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).obj T) W.1
  let iKD : Algebra k Γ(T.left, W.1) := Over.sectionsAlgebra TD W.1
  let iKI : Algebra k Γ(T.left, W.1) := Over.sectionsAlgebra TI W.1
  let iKD' : Algebra k Γ(TD.left, W.1) := Over.sectionsAlgebra TD W.1
  let iKI' : Algebra k Γ(TI.left, W.1) := Over.sectionsAlgebra TI W.1
  let iL' : Algebra L Γ(TL.left, W.1) := Over.sectionsAlgebra TL W.1
  let iM' : Algebra M Γ(T.left, W.1) := Over.sectionsAlgebra T W.1
  letI : Algebra M Γ(T.left, W.1) := iM
  letI : Algebra L Γ(T.left, W.1) := iL
  letI : Algebra k Γ(T.left, W.1) := iKD
  letI : Algebra k Γ(TD.left, W.1) := iKD'
  letI : Algebra k Γ(TI.left, W.1) := iKI'
  letI : Algebra L Γ(TL.left, W.1) := iL'
  letI : Algebra M Γ(T.left, W.1) := iM'
  let pulled := picEtPullback ((baseChange.compIso k L M).app C).inv T lam
  let liftedM := picEtCrossBaseInv L M ((baseChange k L).obj C) T pulled
  let liftedL := picEtCrossBaseInv k L C TL liftedM
  calc
    (picEtCrossBaseInv k M C T lam).1 W =
        (sectionShuffle k M C T W.1).symm (lam.1 ⟨W.1, W.2⟩) :=
      picEtCrossBaseInv_val k M C T lam W
    _ = PicEtAff.mapAlg C (Over.appLEAlgHom f W.1 W.1 hW)
        ((sectionShuffle k L C TL W.1).symm
          ((sectionShuffle L M ((baseChange k L).obj C) T W.1).symm
            (@PicEtAff.curveMap M _ _ _ Γ(T.left, W.1) _ iM
              ((baseChange.compIso k L M).app C).inv (lam.1 ⟨W.1, W.2⟩)))) :=
      sectionShuffle_symm_tower_mapAlg k L M C T f hf W hW (lam.1 ⟨W.1, W.2⟩)
    _ = PicEtAff.mapAlg C (Over.appLEAlgHom f W.1 W.1 hW)
        ((sectionShuffle k L C TL W.1).symm
          ((sectionShuffle L M ((baseChange k L).obj C) T W.1).symm
            (pulled.1 W))) := by
      refine congrArg (fun q => PicEtAff.mapAlg C (Over.appLEAlgHom f W.1 W.1 hW)
        ((sectionShuffle k L C TL W.1).symm
          ((sectionShuffle L M ((baseChange k L).obj C) T W.1).symm q))) ?_
      exact (picEtPullback_val ((baseChange.compIso k L M).app C).inv T lam W).symm
    _ = PicEtAff.mapAlg C (Over.appLEAlgHom f W.1 W.1 hW)
        ((sectionShuffle k L C TL W.1).symm (liftedM.1 W)) := by
      refine congrArg (fun q => PicEtAff.mapAlg C (Over.appLEAlgHom f W.1 W.1 hW)
        ((sectionShuffle k L C TL W.1).symm q)) ?_
      exact (picEtCrossBaseInv_val L M ((baseChange k L).obj C) T pulled W).symm
    _ = PicEtAff.mapAlg C (Over.appLEAlgHom f W.1 W.1 hW) (liftedL.1 W) := by
      exact congrArg (PicEtAff.mapAlg C (Over.appLEAlgHom f W.1 W.1 hW))
        (picEtCrossBaseInv_val k L C TL liftedM W).symm
    _ = picEtMapVal C f liftedL W :=
      (picEtMapVal_eq_mapAlg C f liftedL (W := W) (V := W) hW).symm
    _ = (picEtMap C f liftedL).1 W :=
      (picEtMap_val C f liftedL W).symm

theorem pic0Theta_comp : pic0Theta k M C = cocycleRHS k L M C := by
  apply Iso.ext
  ext T lam
  refine Subtype.ext ?_
  change picEtCrossBaseInv k M C (Opposite.unop T) lam.1 =
    picEtMap C (((αOp k L M).hom.app T).unop)
      (picEtCrossBaseInv k L C
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap L M)))).obj
          (Opposite.unop T))
        (picEtCrossBaseInv L M ((baseChange k L).obj C) (Opposite.unop T)
          (picEtPullback ((baseChange.compIso k L M).app C).inv
            (Opposite.unop T) lam.1)))
  exact picEtCrossBaseInv_tower k L M C (Opposite.unop T) lam.1

end Cocycle

end AlgebraicGeometry
