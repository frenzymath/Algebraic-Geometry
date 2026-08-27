/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegTop

/-!
# Naturality of the Čech complex comparison

This file assembles the coordinatewise naturality theorem `coreIso_comm_leg` into
per-coface, alternating-sum, and cochain-complex comparison squares.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

private lemma comp_univ_sum {C : Type*} [Category C] [Preadditive C]
    {P Q R : C} {J : Type*} [Fintype J] (f : P ⟶ Q) (g : J → (Q ⟶ R)) :
    f ≫ (∑ j, g j) = ∑ j, f ≫ g j := by
  simpa using Preadditive.comp_sum Finset.univ f g

private lemma sum_univ_comp {C : Type*} [Category C] [Preadditive C]
    {P Q R : C} {J : Type*} [Fintype J] (f : J → (P ⟶ Q)) (g : Q ⟶ R) :
    (∑ j, f j) ≫ g = ∑ j, f j ≫ g := by
  simpa using Preadditive.sum_comp Finset.univ f g

private lemma map_univ_sum {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive]
    {P Q : C} {J : Type*} [Fintype J] (f : J → (P ⟶ Q)) :
    G.map (∑ j, f j) = ∑ j, G.map (f j) := by
  simp

private lemma comp_sum_zsmul_eq_sum_zsmul_comp
    {C : Type*} [Category C] [Preadditive C] {P Q R S : C}
    {J : Type*} [Fintype J] (a : P ⟶ Q) (b : S ⟶ R) (n : J → ℤ)
    (f : J → (Q ⟶ R)) (g : J → (P ⟶ S))
    (h : ∀ j, a ≫ f j = g j ≫ b) :
    a ≫ (∑ j, n j • f j) = (∑ j, n j • g j) ≫ b := by
  rw [comp_univ_sum, sum_univ_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, h j]

private lemma map_sum_zsmul {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive]
    {P Q : C} {J : Type*} [Fintype J] (n : J → ℤ) (f : J → (P ⟶ Q)) :
    G.map (∑ j, n j • f j) = ∑ j, n j • G.map (f j) := by
  rw [map_univ_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Functor.map_zsmul]

/-- **Per-coface square of the core comparison** (`lem:coreIso_comm_coface`): for each
degree `p` and coface index `k`, the object isos intertwine the individual cofaces.
Coordinatewise extensionality (`Pi.hom_ext`); the `σ'`-coordinate of the left side is the
face restriction by the defining `Pi.lift_π` of the section-Čech cosimplicial map, and the
right side is `coreIso_comm_leg`. -/
lemma coreIso_comm_coface (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (p : ℕ) (k : Fin (p + 2)) :
    (coreIso_objIso 𝒰 F p V).hom ≫
        (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F)).δ k =
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
            (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k)) ≫
        (coreIso_objIso 𝒰 F (p + 1) V).hom := by
  apply Limits.Pi.hom_ext
  intro σ'
  have hπ : (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F)).map (SimplexCategory.δ k) ≫
        Pi.π _ σ' =
      Pi.π _ (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫
        sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k :=
    Pi.lift_π _ σ'
  change (coreIso_objIso 𝒰 F p V).hom ≫
    ((sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F)).map (SimplexCategory.δ k) ≫
      Pi.π _ σ') = _
  calc
    _ = (coreIso_objIso 𝒰 F p V).hom ≫
        (Pi.π _ (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫
          sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
            ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k) :=
      congrArg (fun f => (coreIso_objIso 𝒰 F p V).hom ≫ f) hπ
    _ = ((coreIso_objIso 𝒰 F p V).hom ≫
        Pi.π _ (σ' ∘ (SimplexCategory.δ k).toOrderHom)) ≫
          sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
            ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k :=
      (Category.assoc _ _ _).symm
    _ = _ := (coreIso_comm_leg 𝒰 F V p k σ').symm

/-- **Alternating-sum assembly of the core comparison square** (`lem:coreIso_comm_sum`):
the full alternating-coface differentials are intertwined by the object isos. This follows
by distributing composition and the additive evaluation functors over the finite sum, then
applying `coreIso_comm_coface` to each summand. -/
lemma coreIso_comm_sum (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (p : ℕ) :
    (coreIso_objIso 𝒰 F p V).hom ≫
        AlgebraicTopology.AlternatingCofaceMapComplex.objD
          (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
            ((SheafOfModules.forget X.ringCatSheaf).obj F)) p =
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
            (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (AlgebraicTopology.AlternatingCofaceMapComplex.objD
              (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) p)) ≫
        (coreIso_objIso 𝒰 F (p + 1) V).hom := by
  haveI : (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).Additive := inferInstance
  haveI : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
      (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
        (Opposite.op V)).Additive := inferInstance
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  have hmap :
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
            (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
              (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
              (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k)) =
        ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
          (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
                (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
                  (Opposite.op V)).map
            ((SheafOfModules.forget X.ringCatSheaf ⋙
                PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
              ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k)) := by
    calc
      _ = (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
              (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
                (Opposite.op V)).map
            (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
              (SheafOfModules.forget X.ringCatSheaf ⋙
                  PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
                ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k)) :=
        congrArg _ (map_sum_zsmul
          (SheafOfModules.forget X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj))
          (fun k : Fin (p + 2) => (-1 : ℤ) ^ (k : ℕ))
          (fun k => (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k))
      _ = _ := map_sum_zsmul
        (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V))
        (fun k : Fin (p + 2) => (-1 : ℤ) ^ (k : ℕ))
        (fun k => (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k))
  calc
    _ = (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
          (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
                (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
                  (Opposite.op V)).map
            ((SheafOfModules.forget X.ringCatSheaf ⋙
                PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
              ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k))) ≫
        (coreIso_objIso 𝒰 F (p + 1) V).hom :=
      comp_sum_zsmul_eq_sum_zsmul_comp
        (coreIso_objIso 𝒰 F p V).hom (coreIso_objIso 𝒰 F (p + 1) V).hom
        (fun k : Fin (p + 2) => (-1 : ℤ) ^ (k : ℕ))
        (fun k => (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F)).δ k)
        (fun k => (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
              (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
                (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k)))
        (coreIso_comm_coface 𝒰 F V p)
    _ = _ := congrArg (fun f => f ≫ (coreIso_objIso 𝒰 F (p + 1) V).hom) hmap.symm

/-- **The core comparison intertwines the Čech differentials** (`lem:coreIso_comm`).  Under the
degreewise object isos `coreIso_objIso`, the alternating-coface differential of the evaluated
backbone complex `(G_V ∘ Ψ) Č•(𝒰, F)` matches the alternating-coface differential of the
concrete restricted section complex `Č•(𝒰', F)`.  The square is exactly the alternating-sum
assembly `coreIso_comm_sum` (built from the per-coface squares `coreIso_comm_coface`, in turn
from the per-leg naturality `coreIso_comm_leg`). -/
lemma coreIso_comm (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (coreIso_objIso 𝒰 F i V).hom ≫ (sectionCechComplexV 𝒰 F V).d i j =
      (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
            (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
              (Opposite.op V)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (cechComplexOnX 𝒰 F))).d i j ≫
        (coreIso_objIso 𝒰 F j V).hom := by
  obtain rfl : i + 1 = j := hij
  rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d]
  have hsec : (sectionCechComplexV 𝒰 F V).d i (i + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F)) i :=
    CochainComplex.of_d
      (fun n => (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F)).obj (SimplexCategory.mk n))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F))) i
  have hX : (cechComplexOnX 𝒰 F).d i (i + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) i :=
    CochainComplex.of_d
      (fun n => (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).obj
        (SimplexCategory.mk n))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F))) i
  rw [hsec, hX]
  exact coreIso_comm_sum 𝒰 F V i

end AlgebraicGeometry
