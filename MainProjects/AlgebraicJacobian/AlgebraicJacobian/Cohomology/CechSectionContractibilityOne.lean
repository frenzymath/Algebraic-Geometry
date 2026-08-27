/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionContractibilityCore

/-!
# Degree-one section Cech contraction

This file identifies the two coordinates in the augmentation-degree contracting identity and
combines them using the dependent combinatorial Cech homotopy.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

section ContractingHomotopy

variable (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (V : TopologicalSpace.Opens X)
variable (i_fix : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i_fix)

/-- The bottom differential of the augmented section Cech complex is its augmentation map. -/
lemma cechSectionAugComplex_d_zero_one :
    (cechSectionAugComplex 𝒰 F V).d 0 1 = sectionCechAugV 𝒰 F V :=
  rfl

/-- The degree-zero product coordinate, kept opaque so composition can be transported without
unfolding the full dependent product equivalence. -/
noncomputable def cechSectionZeroCoord (σ : Fin 1 → 𝒰.I₀)
    (t : ToType ((cechSectionAugComplex 𝒰 F V).X 1)) : cechSectionCoeff 𝒰 F V 1 σ :=
  sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) 0 t σ

/-- The opaque degree-zero coordinate agrees with the section product equivalence. -/
lemma cechSectionZeroCoord_eq (σ : Fin 1 → 𝒰.I₀)
    (t : ToType ((cechSectionAugComplex 𝒰 F V).X 1)) :
    cechSectionZeroCoord 𝒰 F V σ t =
      sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F) 0 t σ :=
  rfl

/-- The bottom homotopy followed by the augmentation, kept opaque for coordinate evaluation. -/
noncomputable def cechSectionHomotopyZeroAug :
    (cechSectionAugComplex 𝒰 F V).X 1 ⟶ (cechSectionAugComplex 𝒰 F V).X 1 :=
  AddCommGrpCat.ofHom ((sectionCechAugV 𝒰 F V).hom.comp
    (cechSectionHomotopyZero 𝒰 F V i_fix hiV).hom)

/-- The opaque bottom composite is the bottom homotopy followed by the augmentation. -/
lemma cechSectionHomotopyZeroAug_eq :
    cechSectionHomotopyZeroAug 𝒰 F V i_fix hiV =
      cechSectionHomotopyZero 𝒰 F V i_fix hiV ≫ sectionCechAugV 𝒰 F V :=
  rfl

/-- Evaluation of the opaque bottom composite is ordinary morphism composition. -/
lemma cechSectionHomotopyZeroAug_apply
    (t : ToType ((cechSectionAugComplex 𝒰 F V).X 1)) :
    ConcreteCategory.hom (cechSectionHomotopyZeroAug 𝒰 F V i_fix hiV) t =
      ConcreteCategory.hom (sectionCechAugV 𝒰 F V)
        (ConcreteCategory.hom (cechSectionHomotopyZero 𝒰 F V i_fix hiV) t) := by
  rfl

/-- The coordinate of the section Cech augmentation is its corresponding coface restriction. -/
lemma sectionCechAugV_coord
    (x : ToType ((cechSectionAugComplex 𝒰 F V).X 0)) (σ : Fin 1 → 𝒰.I₀) :
    cechSectionZeroCoord 𝒰 F V σ (ConcreteCategory.hom (sectionCechAugV 𝒰 F V) x) =
      cechSectionCoface 𝒰 F V 0 σ 0 x := by
  change sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) 0
    (ConcreteCategory.hom (sectionCechAugV 𝒰 F V) x) σ = _
  refine Eq.trans (sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) 0 _ σ) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ (Pi.π _ σ) _).symm ?_
  exact ConcreteCategory.congr_hom (sectionCechAugV_π 𝒰 F V σ) x

/-- Evaluating the bottom homotopy projects to the distinguished coordinate and applies the
prepend restriction. -/
lemma cechSectionHomotopyZero_apply (t : ToType ((cechSectionAugComplex 𝒰 F V).X 1)) :
    ConcreteCategory.hom (cechSectionHomotopyZero 𝒰 F V i_fix hiV) t =
      cechSectionPrepend 𝒰 F V i_fix hiV 0 Fin.elim0
        (sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F) 0 t
          (Fin.cons i_fix Fin.elim0)) := by
  refine Eq.trans (ConcreteCategory.comp_apply _ _ t) ?_
  exact DFunLike.congr_arg (cechSectionPrepend 𝒰 F V i_fix hiV 0 Fin.elim0)
    (sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) 0 t
      (Fin.cons i_fix Fin.elim0)).symm

omit [Finite 𝒰.I₀] in
/-- At the bottom level, the dependent differential of a prepended tuple is its unique coface
coordinate. -/
lemma cechSectionDepDiff_depHomotopy_zero
    (u : ∀ τ : Fin 1 → 𝒰.I₀, cechSectionCoeff 𝒰 F V 1 τ) (σ : Fin 1 → 𝒰.I₀) :
    CombinatorialCech.depDiff (A := cechSectionCoeff 𝒰 F V) (cechSectionCoface 𝒰 F V)
        (CombinatorialCech.depHomotopy i_fix (cechSectionPrepend 𝒰 F V i_fix hiV) u) σ
      = cechSectionCoface 𝒰 F V 0 σ 0
          (cechSectionPrepend 𝒰 F V i_fix hiV 0 Fin.elim0
            (u (Fin.cons i_fix Fin.elim0))) := by
  refine Eq.trans (cechSectionDepDiff_zero 𝒰 F V _ σ) ?_
  have htuple : ∀ ρ : Fin 0 → 𝒰.I₀,
      cechSectionPrepend 𝒰 F V i_fix hiV 0 ρ (u (Fin.cons i_fix ρ)) =
        cechSectionPrepend 𝒰 F V i_fix hiV 0 Fin.elim0
          (u (Fin.cons i_fix Fin.elim0)) := by
    intro ρ
    have hρ : ρ = Fin.elim0 := Subsingleton.elim _ _
    subst hρ
    rfl
  exact DFunLike.congr_arg (cechSectionCoface 𝒰 F V 0 σ 0)
    (htuple (σ ∘ (0 : Fin 1).succAbove))

/-- The augmentation coordinate of the bottom homotopy followed by the differential is the
corresponding coface restriction. -/
lemma cechSectionHomotopyZero_comp_d_restriction_coord
    (t : ToType ((cechSectionAugComplex 𝒰 F V).X 1)) (σ : Fin 1 → 𝒰.I₀) :
    cechSectionZeroCoord 𝒰 F V σ
        (ConcreteCategory.hom (cechSectionHomotopyZeroAug 𝒰 F V i_fix hiV) t)
      = cechSectionCoface 𝒰 F V 0 σ 0
          (ConcreteCategory.hom (cechSectionHomotopyZero 𝒰 F V i_fix hiV) t) := by
  refine Eq.trans (congrArg (cechSectionZeroCoord 𝒰 F V σ)
    (cechSectionHomotopyZeroAug_apply 𝒰 F V i_fix hiV t)) ?_
  exact sectionCechAugV_coord 𝒰 F V
    (ConcreteCategory.hom (cechSectionHomotopyZero 𝒰 F V i_fix hiV) t) σ

/-- The coordinate of the augmentation projection followed by the Cech differential is the
bottom-level dependent differential of the prepended tuple. -/
lemma cechSectionHomotopyZero_comp_d_coord
    (t : ToType ((cechSectionAugComplex 𝒰 F V).X 1)) (σ : Fin 1 → 𝒰.I₀) :
    sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F) 0
        (ConcreteCategory.hom (cechSectionHomotopyZero 𝒰 F V i_fix hiV ≫
          (cechSectionAugComplex 𝒰 F V).d 0 1) t) σ
      = CombinatorialCech.depDiff (A := cechSectionCoeff 𝒰 F V) (cechSectionCoface 𝒰 F V)
          (CombinatorialCech.depHomotopy i_fix (cechSectionPrepend 𝒰 F V i_fix hiV)
            (fun τ => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
              ((SheafOfModules.forget X.ringCatSheaf).obj F) 0 t τ)) σ := by
  refine Eq.trans (cechSectionZeroCoord_eq 𝒰 F V σ _).symm ?_
  refine Eq.trans (congrArg (fun d => cechSectionZeroCoord 𝒰 F V σ
      (ConcreteCategory.hom (cechSectionHomotopyZero 𝒰 F V i_fix hiV ≫ d) t))
    (cechSectionAugComplex_d_zero_one 𝒰 F V)) ?_
  refine Eq.trans (congrArg (cechSectionZeroCoord 𝒰 F V σ)
    (ConcreteCategory.congr_hom (cechSectionHomotopyZeroAug_eq
      𝒰 F V i_fix hiV).symm t)) ?_
  refine Eq.trans (cechSectionHomotopyZero_comp_d_restriction_coord
    𝒰 F V i_fix hiV t σ) ?_
  refine Eq.trans (DFunLike.congr_arg (cechSectionCoface 𝒰 F V 0 σ 0)
    (cechSectionHomotopyZero_apply 𝒰 F V i_fix hiV t)) ?_
  exact (cechSectionDepDiff_depHomotopy_zero 𝒰 F V i_fix hiV
    (fun τ => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) 0 t τ) σ).symm

/-- The coordinate of the first Cech differential followed by the prepend homotopy is the
dependent prepend map applied to the dependent differential. -/
lemma cechSectionD_comp_homotopyComp_zero_coord
    (t : ToType ((cechSectionAugComplex 𝒰 F V).X 1)) (σ : Fin 1 → 𝒰.I₀) :
    sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F) 0
        (ConcreteCategory.hom ((cechSectionAugComplex 𝒰 F V).d 1 2 ≫
          cechSectionHomotopyComp 𝒰 F V i_fix hiV 0) t) σ
      = CombinatorialCech.depHomotopy i_fix (cechSectionPrepend 𝒰 F V i_fix hiV)
          (CombinatorialCech.depDiff (A := cechSectionCoeff 𝒰 F V) (cechSectionCoface 𝒰 F V)
            (fun τ => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
              ((SheafOfModules.forget X.ringCatSheaf).obj F) 0 t τ)) σ := by
  refine Eq.trans (congrArg (fun y => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) 0 y σ)
    (ConcreteCategory.comp_apply _ _ t)) ?_
  refine Eq.trans (cechSectionHomotopyComp_coord 𝒰 F V i_fix hiV 0 _ σ) ?_
  exact DFunLike.congr_arg (cechSectionPrepend 𝒰 F V i_fix hiV 1 σ)
    (cechSectionD_coord 𝒰 F V 0 t (Fin.cons i_fix σ))

/-- **(I1)** The augmentation-node contracting identity:
`𝟙 = π_{i_fix} ≫ ε + d⁰ ≫ h₁` on `Č⁰`. -/
lemma cechSection_comm_one :
    𝟙 ((cechSectionAugComplex 𝒰 F V).X 1) =
      cechSectionHomotopyZero 𝒰 F V i_fix hiV ≫ (cechSectionAugComplex 𝒰 F V).d 0 1 +
        (cechSectionAugComplex 𝒰 F V).d 1 2 ≫ cechSectionHomotopyComp 𝒰 F V i_fix hiV 0 := by
  let E := sectionCechProductAddEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) 0
  ext t
  apply E.injective
  funext σ
  refine Eq.symm ?_
  have hsplit : ConcreteCategory.hom
      (cechSectionHomotopyZero 𝒰 F V i_fix hiV ≫ (cechSectionAugComplex 𝒰 F V).d 0 1 +
        (cechSectionAugComplex 𝒰 F V).d 1 2 ≫ cechSectionHomotopyComp 𝒰 F V i_fix hiV 0) t
      = ConcreteCategory.hom (cechSectionHomotopyZero 𝒰 F V i_fix hiV ≫
          (cechSectionAugComplex 𝒰 F V).d 0 1) t +
        ConcreteCategory.hom ((cechSectionAugComplex 𝒰 F V).d 1 2 ≫
          cechSectionHomotopyComp 𝒰 F V i_fix hiV 0) t := by
    rw [AddCommGrpCat.hom_add_apply]
  refine Eq.trans (congrArg (fun y => E y σ) hsplit) ?_
  refine Eq.trans (congrArg (fun y => y σ) (map_add E _ _)) ?_
  refine Eq.trans (congrArg₂ (· + ·)
    (cechSectionHomotopyZero_comp_d_coord 𝒰 F V i_fix hiV t σ)
    (cechSectionD_comp_homotopyComp_zero_coord 𝒰 F V i_fix hiV t σ)) ?_
  refine Eq.trans (CombinatorialCech.depHomotopy_spec i_fix (cechSectionCoface 𝒰 F V)
    (cechSectionPrepend 𝒰 F V i_fix hiV)
    (fun {m} σ' y => cechSection_hu 𝒰 F V i_fix hiV σ' y)
    (fun {m} σ' k y => cechSection_hsh 𝒰 F V i_fix hiV σ' k y)
    (fun τ => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) 0 t τ) σ) ?_
  exact congrArg (fun y => E y σ) (ConcreteCategory.id_apply t).symm

end ContractingHomotopy

end AlgebraicGeometry
