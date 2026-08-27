/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechAcyclic
import AlgebraicJacobian.Cohomology.FreePresheafComplex

/-!
# The augmented section Cech complex

This file defines the concrete section Cech augmentation directly as a product of
presheaf restriction maps. It is independent of the comparison with the evaluated
scheme-level Cech complex.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Applying two presheaf restrictions is the same as applying their composite. -/
lemma presheaf_restriction_comp_apply
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab.{u})
    {A B C : TopologicalSpace.Opens X} (hAB : A ≤ B) (hBC : B ≤ C)
    (x : ToType (P.obj (Opposite.op C))) :
    ConcreteCategory.hom (P.map (homOfLE hAB).op)
        (ConcreteCategory.hom (P.map (homOfLE hBC).op) x) =
      ConcreteCategory.hom (P.map (homOfLE (hAB.trans hBC)).op) x := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp]
  rfl

/-- Presheaf restrictions along two parallel inclusions of opens agree. -/
lemma presheaf_restriction_eq_of_parallel
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab.{u})
    {A C : TopologicalSpace.Opens X} (f g : Opposite.op C ⟶ Opposite.op A)
    (x : ToType (P.obj (Opposite.op C))) :
    ConcreteCategory.hom (P.map f) x = ConcreteCategory.hom (P.map g) x := by
  rw [show f = g from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

/-- A nonempty intersection of opens contained in `V` is contained in `V`. -/
lemma sectionCech_intersection_le {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) (V : TopologicalSpace.Opens X)
    (hU : ∀ i, U i ≤ V) {m : ℕ} (σ : Fin (m + 1) → ι) :
    (⨅ k, U (σ k)) ≤ V :=
  le_trans (iInf_le _ 0) (hU (σ 0))

/-- The direct augmentation from sections on `V` to the degree-zero section Cech term. -/
noncomputable def sectionCechAugmentation {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) (F : X.PresheafOfModules)
    (V : TopologicalSpace.Opens X) (hU : ∀ i, U i ≤ V) :
    F.presheaf.obj (Opposite.op V) ⟶ (sectionCechComplex U F).X 0 :=
  Pi.lift fun σ : Fin 1 → ι =>
    F.presheaf.map (homOfLE (sectionCech_intersection_le U V hU σ)).op

/-- A coordinate of the direct section Cech augmentation is the corresponding restriction. -/
lemma sectionCechAugmentation_π {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) (F : X.PresheafOfModules)
    (V : TopologicalSpace.Opens X) (hU : ∀ i, U i ≤ V)
    (σ : Fin 1 → ι) :
    sectionCechAugmentation U F V hU ≫
        Pi.π (fun τ : Fin 1 → ι => F.presheaf.obj (Opposite.op (⨅ k, U (τ k)))) σ =
      F.presheaf.map (homOfLE (sectionCech_intersection_le U V hU σ)).op := by
  exact Pi.lift_π _ σ

private lemma sectionCechAugmentation_coord {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) (F : X.PresheafOfModules)
    (V : TopologicalSpace.Opens X) (hU : ∀ i, U i ≤ V)
    (x : ToType (F.presheaf.obj (Opposite.op V))) (σ : Fin 1 → ι) :
    sectionCechProductEquiv U F 0
        (ConcreteCategory.hom (sectionCechAugmentation U F V hU) x) σ =
      ConcreteCategory.hom
        (F.presheaf.map (homOfLE (sectionCech_intersection_le U V hU σ)).op) x := by
  refine Eq.trans (sectionCechProductEquiv_apply U F 0 _ σ) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ x).symm ?_
  exact ConcreteCategory.congr_hom (sectionCechAugmentation_π U F V hU σ) x

private lemma sectionCechFaceRestr_augmentation {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) (F : X.PresheafOfModules)
    (V : TopologicalSpace.Opens X) (hU : ∀ i, U i ≤ V)
    (x : ToType (F.presheaf.obj (Opposite.op V))) (σ : Fin 2 → ι) (i : Fin 2) :
    ConcreteCategory.hom (sectionCechFaceRestr U F σ i)
        (sectionCechProductEquiv U F 0
          (ConcreteCategory.hom (sectionCechAugmentation U F V hU) x)
          (σ ∘ (SimplexCategory.δ i).toOrderHom)) =
      ConcreteCategory.hom
        (F.presheaf.map (homOfLE (sectionCech_intersection_le U V hU σ)).op) x := by
  refine Eq.trans (congrArg (ConcreteCategory.hom (sectionCechFaceRestr U F σ i))
    (sectionCechAugmentation_coord U F V hU x
      (σ ∘ (SimplexCategory.δ i).toOrderHom))) ?_
  refine Eq.trans (presheaf_restriction_comp_apply F.presheaf
    (A := ⨅ k, U (σ k))
    (B := ⨅ l, U ((σ ∘ (SimplexCategory.δ i).toOrderHom) l))
    (C := V)
    (le_iInf (fun l => iInf_le _ ((SimplexCategory.δ i).toOrderHom l)))
    (sectionCech_intersection_le U V hU
      (σ ∘ (SimplexCategory.δ i).toOrderHom)) x) ?_
  exact presheaf_restriction_eq_of_parallel F.presheaf _ _ x

/-- The direct section Cech augmentation composes to zero with the first differential. -/
lemma sectionCechAugmentation_comp_d {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) (F : X.PresheafOfModules)
    (V : TopologicalSpace.Opens X) (hU : ∀ i, U i ≤ V) :
    sectionCechAugmentation U F V hU ≫ (sectionCechComplex U F).d 0 1 = 0 := by
  apply ConcreteCategory.hom_ext
  intro x
  apply (sectionCechProductEquiv U F 1).injective
  funext σ
  rw [ConcreteCategory.comp_apply]
  change sectionCechProductEquiv U F 1
    (ConcreteCategory.hom
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (sectionCechCosimplicial U F) 0)
      (ConcreteCategory.hom (sectionCechAugmentation U F V hU) x)) σ = _
  rw [sectionCech_objD_apply, Fin.sum_univ_two]
  simp only [sectionCechFaceRestr_augmentation U F V hU x σ 0,
    sectionCechFaceRestr_augmentation U F V hU x σ 1, Fin.val_zero, pow_zero,
    one_smul, Fin.val_one, pow_one, neg_one_zsmul, add_neg_cancel]
  rw [sectionCechProductEquiv_apply]
  have hx : ConcreteCategory.hom
      (0 : F.presheaf.obj (Opposite.op V) ⟶ (sectionCechComplex U F).X 1) x = 0 := rfl
  rw [hx]
  exact (ConcreteCategory.hom (Pi.π
    (fun τ : Fin 2 → ι => F.presheaf.obj (Opposite.op (⨅ k, U (τ k)))) σ)).map_zero.symm

open Scheme.Modules

/-- The concrete section Cech complex over `V` for the restricted cover. -/
noncomputable abbrev sectionCechComplexV (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (V : TopologicalSpace.Opens X) : CochainComplex Ab.{u} ℕ :=
  sectionCechComplex (fun i : 𝒰.I₀ => coverOpen 𝒰 i ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F)

/-- A restricted cover intersection is contained in the ambient open `V`. -/
lemma sectionCechV_intersection_le (𝒰 : X.OpenCover)
    (V : TopologicalSpace.Opens X) {m : ℕ} (σ : Fin (m + 1) → 𝒰.I₀) :
    (⨅ k, (coverOpen 𝒰 (σ k) ⊓ V)) ≤ V :=
  le_trans (iInf_le _ (0 : Fin (m + 1))) inf_le_right

/-- The direct augmentation of the concrete section Cech complex over `V`. -/
noncomputable def sectionCechAugV (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (V : TopologicalSpace.Opens X) :
    ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op V) ⟶
      (sectionCechComplexV 𝒰 F V).X 0 :=
  sectionCechAugmentation (fun i : 𝒰.I₀ => coverOpen 𝒰 i ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) V (fun _ => inf_le_right)

/-- A coordinate of the concrete section Cech augmentation is the corresponding restriction. -/
lemma sectionCechAugV_π (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (V : TopologicalSpace.Opens X) (σ : Fin 1 → 𝒰.I₀) :
    sectionCechAugV 𝒰 F V ≫ Pi.π (fun τ : Fin 1 → 𝒰.I₀ =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op (⨅ k, (coverOpen 𝒰 (τ k) ⊓ V)))) σ =
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
        (homOfLE (sectionCechV_intersection_le 𝒰 V σ)).op := by
  exact sectionCechAugmentation_π _ _ V (fun _ => inf_le_right) σ

/-- The concrete section Cech augmentation composes to zero with the first differential. -/
lemma sectionCechAugV_comp_d (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (V : TopologicalSpace.Opens X) :
    sectionCechAugV 𝒰 F V ≫ (sectionCechComplexV 𝒰 F V).d 0 1 = 0 := by
  exact sectionCechAugmentation_comp_d _ _ V (fun _ => inf_le_right)

end AlgebraicGeometry
