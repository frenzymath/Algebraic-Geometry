/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionContractibilityOne
import AlgebraicJacobian.Cohomology.CechSectionContractibilitySucc

/-!
# Contractibility of the concrete section Čech complex

This file packages the degreewise contracting identities into a contracting homotopy.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

section ContractingHomotopy

variable (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (V : TopologicalSpace.Opens X)
variable (i_fix : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i_fix)

/-- The coinductive step: given the previous homotopy condition, the corrected component
`h_{n+2} ≫ (𝟙 - p₂₁ ≫ d)` satisfies the next one (pure preadditive algebra from `(In)`
and `d ∘ d = 0`). -/
private lemma cechSection_succ_step (n : ℕ)
    {f : (cechSectionAugComplex 𝒰 F V).X (n + 1) ⟶ (cechSectionAugComplex 𝒰 F V).X n}
    {g : (cechSectionAugComplex 𝒰 F V).X (n + 2) ⟶ (cechSectionAugComplex 𝒰 F V).X (n + 1)}
    (hp : 𝟙 ((cechSectionAugComplex 𝒰 F V).X (n + 1)) =
      f ≫ (cechSectionAugComplex 𝒰 F V).d n (n + 1) +
        (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2) ≫ g) :
    𝟙 ((cechSectionAugComplex 𝒰 F V).X (n + 2)) =
      g ≫ (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2) +
        (cechSectionAugComplex 𝒰 F V).d (n + 2) (n + 3) ≫
          (cechSectionHomotopyComp 𝒰 F V i_fix hiV (n + 1) ≫
            (𝟙 ((cechSectionAugComplex 𝒰 F V).X (n + 2)) -
              g ≫ (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2))) := by
  have hIn := cechSection_comm_succ 𝒰 F V i_fix hiV n
  have hsub : (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2) =
      (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2) ≫ g ≫
        (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2) := by
    have h₀ := congrArg (fun m => m ≫ (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2)) hp
    simpa only [Category.id_comp, Preadditive.add_comp, Category.assoc,
      HomologicalComplex.d_comp_d, comp_zero, zero_add] using h₀
  have hd1E : (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2) ≫
      (𝟙 ((cechSectionAugComplex 𝒰 F V).X (n + 2)) -
        g ≫ (cechSectionAugComplex 𝒰 F V).d (n + 1) (n + 2)) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero]
    exact hsub
  have hdb := eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hIn.symm)
  rw [← Category.assoc ((cechSectionAugComplex 𝒰 F V).d (n + 2) (n + 3))
    (cechSectionHomotopyComp 𝒰 F V i_fix hiV (n + 1)) _, hdb, Preadditive.sub_comp,
    Category.id_comp, Category.assoc, hd1E, comp_zero, sub_zero]
  abel

end ContractingHomotopy

/-- The concrete augmented section Čech complex is contractible after choosing a cover member
that contains `V`. -/
noncomputable def cechSection_contractible (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (F : X.Modules) (V : TopologicalSpace.Opens X)
    (i_fix : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i_fix) :
    Homotopy (𝟙 (cechSectionAugComplex 𝒰 F V)) 0 := by
  let C := cechSectionAugComplex 𝒰 F V
  -- The prepend-`i_fix` contracting homotopy on the augmented concrete section complex,
  -- assembled by `Homotopy.mkCoinductive` from the explicit components (`π_{i_fix}` at the
  -- augmentation node, prepend-`i_fix` in the Čech degrees) and the three contracting
  -- identities (I0)/(I1)/(In) proved above via the dependent combinatorial engine.
  exact Homotopy.mkCoinductive (𝟙 C)
    (cechSectionHomotopyZero 𝒰 F V i_fix hiV)
    ((HomologicalComplex.id_f _ _).trans (cechSection_comm_zero 𝒰 F V i_fix hiV))
    (cechSectionHomotopyComp 𝒰 F V i_fix hiV 0)
    ((HomologicalComplex.id_f _ _).trans (cechSection_comm_one 𝒰 F V i_fix hiV))
    (fun n p =>
      ⟨cechSectionHomotopyComp 𝒰 F V i_fix hiV (n + 1) ≫
          (𝟙 (C.X (n + 2)) - p.2.1 ≫ C.d (n + 1) (n + 2)), by
        have hp := (HomologicalComplex.id_f _ _).symm.trans p.2.2
        exact (HomologicalComplex.id_f _ _).trans
          (cechSection_succ_step 𝒰 F V i_fix hiV n hp)⟩)

end AlgebraicGeometry
