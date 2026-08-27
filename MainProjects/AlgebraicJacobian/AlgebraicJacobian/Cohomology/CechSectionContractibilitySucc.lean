/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionContractibilityCore

/-!
# Positive-degree section Čech contraction

This file proves the positive-degree contracting identity from the dependent combinatorial
Čech homotopy and the concrete section-complex coordinate formulas.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

section ContractingHomotopy

variable (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (V : TopologicalSpace.Opens X)
variable (i_fix : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i_fix)

/-- **(In)** The positive-degree contracting identities, from the dependent engine
(`CombinatorialCech.depHomotopy_spec`). -/
lemma cechSection_comm_succ (n : ℕ) :
    𝟙 ((cechSectionAugComplex 𝒰 F V).X (n + 2)) =
      cechSectionHomotopyComp 𝒰 F V i_fix hiV n ≫
          (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2) +
        (cechSectionAugComplex 𝒰 F V).d (n + 2) (n + 3) ≫
          cechSectionHomotopyComp 𝒰 F V i_fix hiV (n + 1) := by
  let E := sectionCechProductAddEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) (n + 1)
  ext t
  apply E.injective
  funext σ
  refine Eq.symm ?_
  have hsplit : ConcreteCategory.hom
      (cechSectionHomotopyComp 𝒰 F V i_fix hiV n ≫
          (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2) +
        (cechSectionAugComplex 𝒰 F V).d (n + 2) (n + 3) ≫
          cechSectionHomotopyComp 𝒰 F V i_fix hiV (n + 1)) t
      = ConcreteCategory.hom (cechSectionHomotopyComp 𝒰 F V i_fix hiV n ≫
          (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2)) t +
        ConcreteCategory.hom ((cechSectionAugComplex 𝒰 F V).d (n + 2) (n + 3) ≫
          cechSectionHomotopyComp 𝒰 F V i_fix hiV (n + 1)) t := by
    rw [AddCommGrpCat.hom_add_apply]
  refine Eq.trans (congrArg (fun y => E y σ) hsplit) ?_
  refine Eq.trans (congrArg (fun y => y σ) (map_add E _ _)) ?_
  -- piece 1: `h ≫ d` is `depDiff (depHomotopy t̃)`
  have hpiece1 : sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) (n + 1)
      (ConcreteCategory.hom (cechSectionHomotopyComp 𝒰 F V i_fix hiV n ≫
        (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2)) t) σ
      = CombinatorialCech.depDiff (A := cechSectionCoeff 𝒰 F V) (cechSectionCoface 𝒰 F V)
          (CombinatorialCech.depHomotopy i_fix (cechSectionPrepend 𝒰 F V i_fix hiV)
            (fun τ => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
              ((SheafOfModules.forget X.ringCatSheaf).obj F) (n + 1) t τ)) σ := by
    refine Eq.trans (congrArg (fun y => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) (n + 1) y σ)
      (ConcreteCategory.comp_apply _ _ t)) ?_
    refine Eq.trans (cechSectionD_coord 𝒰 F V n _ σ) ?_
    exact congrArg (fun u => CombinatorialCech.depDiff (A := cechSectionCoeff 𝒰 F V)
      (cechSectionCoface 𝒰 F V) u σ)
      (funext fun τ => cechSectionHomotopyComp_coord 𝒰 F V i_fix hiV n t τ)
  -- piece 2: `d ≫ h` is `depHomotopy (depDiff t̃)`
  have hpiece2 : sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) (n + 1)
      (ConcreteCategory.hom ((cechSectionAugComplex 𝒰 F V).d (n + 2) (n + 3) ≫
        cechSectionHomotopyComp 𝒰 F V i_fix hiV (n + 1)) t) σ
      = CombinatorialCech.depHomotopy i_fix (cechSectionPrepend 𝒰 F V i_fix hiV)
          (CombinatorialCech.depDiff (A := cechSectionCoeff 𝒰 F V) (cechSectionCoface 𝒰 F V)
            (fun τ => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
              ((SheafOfModules.forget X.ringCatSheaf).obj F) (n + 1) t τ)) σ := by
    refine Eq.trans (congrArg (fun y => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) (n + 1) y σ)
      (ConcreteCategory.comp_apply _ _ t)) ?_
    refine Eq.trans (cechSectionHomotopyComp_coord 𝒰 F V i_fix hiV (n + 1) _ σ) ?_
    exact DFunLike.congr_arg (cechSectionPrepend 𝒰 F V i_fix hiV (n + 2) σ)
      (cechSectionD_coord 𝒰 F V (n + 1) t (Fin.cons i_fix σ))
  refine Eq.trans (congrArg₂ (· + ·) hpiece1 hpiece2) ?_
  refine Eq.trans (CombinatorialCech.depHomotopy_spec i_fix (cechSectionCoface 𝒰 F V)
    (cechSectionPrepend 𝒰 F V i_fix hiV)
    (fun {m} σ' y => cechSection_hu 𝒰 F V i_fix hiV σ' y)
    (fun {m} σ' k y => cechSection_hsh 𝒰 F V i_fix hiV σ' k y)
    (fun τ => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) (n + 1) t τ) σ) ?_
  exact congrArg (fun y => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) (n + 1) y σ)
    (ConcreteCategory.id_apply t).symm

end ContractingHomotopy

end AlgebraicGeometry
