/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionComplex

/-!
# Components of the concrete section Čech contraction

This file constructs the restriction maps and homotopy components for the augmented concrete
section Čech complex, together with the degree-zero contracting identity.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Additive product coordinates -/

/-- The additive form of the dependent product coordinates used by the concrete section Čech
complex.  Keeping the product equivalence bundled avoids repeating its additivity proof at each
coordinatewise contracting identity. -/
noncomputable def sectionCechProductAddEquiv {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) (F : X.PresheafOfModules) (p : ℕ) :
    ToType ((sectionCechCosimplicial U F).obj (SimplexCategory.mk p)) ≃+
      (∀ σ : Fin (p + 1) → ι,
        ToType (F.presheaf.obj (Opposite.op (⨅ k, U (σ k))))) where
  toFun := sectionCechProductEquiv U F p
  invFun := (sectionCechProductEquiv U F p).symm
  left_inv := (sectionCechProductEquiv U F p).left_inv
  right_inv := (sectionCechProductEquiv U F p).right_inv
  map_add' x y := by
    funext σ
    simp only [sectionCechProductEquiv_apply, Pi.add_apply]
    exact map_add _ x y

/-! ## Contracting homotopy on the augmented concrete section Čech complex -/

/-! ### Restriction engine

The dependent-coefficient combinatorial Čech engine (`CombinatorialCech.depHomotopy_spec`,
CechAcyclic.lean) is instantiated with the augmentation node `Γ(V, F)` as level `0` and the
restricted Čech coefficients `Γ(⨅ₖ (U_{σ k} ⊓ V), F)` as levels `≥ 1`.  The coface maps `δ`
are the presheaf face restrictions (level `0 → 1` is the augmentation restriction), and the
prepend maps `c` are genuine restrictions because `V ≤ coverOpen 𝒰 i_fix` forces
`U'_{i_fix·σ} = U'_σ`.  The `hu`/`hsh` compatibilities collapse to "two parallel restriction
chains between the same opens agree". -/

section RestrictionEngine

variable (𝒰 : X.OpenCover) (F : X.Modules) (V : TopologicalSpace.Opens X)


/-- Prepending `i_fix` does not shrink the restricted intersection (positive levels). -/
private lemma restrictedIntersection_le_cons {m : ℕ} (i_fix : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i_fix)
    (σ : Fin (m + 1) → 𝒰.I₀) :
    (⨅ k, (coverOpen 𝒰 (σ k) ⊓ V)) ≤
      ⨅ k, (coverOpen 𝒰 ((Fin.cons i_fix σ : Fin (m + 2) → 𝒰.I₀) k) ⊓ V) := by
  refine le_iInf fun k => ?_
  refine Fin.cases ?_ ?_ k
  · rw [Fin.cons_zero]
    exact le_trans (sectionCechV_intersection_le 𝒰 V σ) (le_inf hiV le_rfl)
  · intro j
    rw [Fin.cons_succ]
    exact iInf_le _ j

/-- Prepending `i_fix` to the empty tuple yields an intersection containing `V`
(the augmentation node case). -/
private lemma le_restrictedIntersection_cons_empty (i_fix : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i_fix)
    (σ : Fin 0 → 𝒰.I₀) :
    V ≤ ⨅ k, (coverOpen 𝒰 ((Fin.cons i_fix σ : Fin 1 → 𝒰.I₀) k) ⊓ V) := by
  refine le_iInf fun k => ?_
  rw [Fin.fin_one_eq_zero k, Fin.cons_zero]
  exact le_inf hiV le_rfl

/-- The open underlying the level-`m` contracting-homotopy coefficient: level `0` is `V` (the
augmentation node), level `m+1` is the restricted intersection `⨅ₖ (U_{σ k} ⊓ V)`. -/
private def homotopyOpen : (m : ℕ) → (Fin m → 𝒰.I₀) → TopologicalSpace.Opens ↥X
  | 0, _ => V
  | _ + 1, σ => ⨅ k, (coverOpen 𝒰 (σ k) ⊓ V)

/-- The coface inclusion of the contracting-homotopy opens. -/
private lemma homotopyOpen_le_coface : ∀ {m : ℕ} (σ : Fin (m + 1) → 𝒰.I₀) (j : Fin (m + 1)),
    homotopyOpen 𝒰 V (m + 1) σ ≤ homotopyOpen 𝒰 V m (σ ∘ j.succAbove)
  | 0, σ, _ => sectionCechV_intersection_le 𝒰 V σ
  | _ + 1, _, j => le_iInf fun l => iInf_le _ (j.succAbove l)

/-- The prepend inclusion of the contracting-homotopy opens (prepending `i_fix` does not shrink the
open, because `V ≤ coverOpen 𝒰 i_fix`). -/
private lemma homotopyOpen_le_prepend (i_fix : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i_fix) :
    ∀ {m : ℕ} (σ : Fin m → 𝒰.I₀),
      homotopyOpen 𝒰 V m σ ≤ homotopyOpen 𝒰 V (m + 1) (Fin.cons i_fix σ)
  | 0, σ => le_restrictedIntersection_cons_empty 𝒰 V i_fix hiV σ
  | _ + 1, σ => restrictedIntersection_le_cons 𝒰 V i_fix hiV σ

/-- Dependent coefficient family for the contracting-homotopy engine: the sections of `F` over
`homotopyOpen m σ`.  Kept as a reducible abbreviation so the `AddCommGroup` instance is the
generic one on `Ab`-objects (no bespoke match-instance). -/
noncomputable abbrev cechSectionCoeff (m : ℕ) (σ : Fin m → 𝒰.I₀) : Type u :=
  ToType (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
    (Opposite.op (homotopyOpen 𝒰 V m σ)))

/-- The engine coface maps: presheaf face restrictions (level `0 → 1` is the augmentation
restriction `Γ(V) → Γ(U'_σ)`). -/
noncomputable def cechSectionCoface (m : ℕ) (σ : Fin (m + 1) → 𝒰.I₀)
    (j : Fin (m + 1)) :
    cechSectionCoeff 𝒰 F V m (σ ∘ j.succAbove) →+ cechSectionCoeff 𝒰 F V (m + 1) σ :=
  ConcreteCategory.hom (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
    (homOfLE (homotopyOpen_le_coface 𝒰 V σ j)).op)

/-- The engine prepend maps: genuine restrictions (level `1 → 0` is the restriction
`Γ(U'_{(i_fix)}) → Γ(V)` along `V ≤ U'_{i_fix}`). -/
noncomputable def cechSectionPrepend (i_fix : 𝒰.I₀)
    (hiV : V ≤ coverOpen 𝒰 i_fix) (m : ℕ) (σ : Fin m → 𝒰.I₀) :
    cechSectionCoeff 𝒰 F V (m + 1) (Fin.cons i_fix σ) →+ cechSectionCoeff 𝒰 F V m σ :=
  ConcreteCategory.hom (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
    (homOfLE (homotopyOpen_le_prepend 𝒰 V i_fix hiV σ)).op)

/-- Transport of a Čech coefficient along an equality of index tuples is the canonical
restriction between the (equal) intersection opens. -/
private lemma cechSectionCoeff_transport {m : ℕ} {τ₁ τ₂ : Fin (m + 1) → 𝒰.I₀}
    (h : τ₁ = τ₂)
    (hle : homotopyOpen 𝒰 V (m + 1) τ₂ ≤ homotopyOpen 𝒰 V (m + 1) τ₁)
    (y : cechSectionCoeff 𝒰 F V (m + 1) τ₁) :
    (h ▸ y : cechSectionCoeff 𝒰 F V (m + 1) τ₂)
      = ConcreteCategory.hom
          (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map (homOfLE hle).op)
          y := by
  subst h
  rw [show homOfLE hle = 𝟙 _ from Subsingleton.elim _ _, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- Unit compatibility `hu` for the contracting-homotopy engine: deleting the prepended
`i_fix` and then applying the prepend restriction is the identity transport (both sides are
restriction chains between the same opens). -/
lemma cechSection_hu (i_fix : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i_fix)
    {m : ℕ} (σ : Fin (m + 1) → 𝒰.I₀)
    (y : cechSectionCoeff 𝒰 F V (m + 1)
      ((Fin.cons i_fix σ : Fin (m + 2) → 𝒰.I₀) ∘ (0 : Fin (m + 2)).succAbove)) :
    cechSectionPrepend 𝒰 F V i_fix hiV (m + 1) σ
        (cechSectionCoface 𝒰 F V (m + 1) (Fin.cons i_fix σ) 0 y)
      = (CombinatorialCech.cons_comp_zero_succAbove i_fix σ) ▸ y := by
  rw [cechSectionCoeff_transport 𝒰 F V (CombinatorialCech.cons_comp_zero_succAbove i_fix σ)
    (le_of_eq (by rw [CombinatorialCech.cons_comp_zero_succAbove i_fix σ]))]
  exact (presheaf_restriction_comp_apply _ _ _ y).trans
    (presheaf_restriction_eq_of_parallel _ _ _ y)

/-- Shift compatibility `hsh` for the contracting-homotopy engine: prepend commutes with the later
cofaces (both sides are restriction chains between the same opens). -/
lemma cechSection_hsh (i_fix : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i_fix)
    {m : ℕ} (σ : Fin (m + 1) → 𝒰.I₀) (k : Fin (m + 1))
    (y : cechSectionCoeff 𝒰 F V (m + 1)
      ((Fin.cons i_fix σ : Fin (m + 2) → 𝒰.I₀) ∘ (k.succ).succAbove)) :
    cechSectionPrepend 𝒰 F V i_fix hiV (m + 1) σ
        (cechSectionCoface 𝒰 F V (m + 1) (Fin.cons i_fix σ) k.succ y)
      = cechSectionCoface 𝒰 F V m σ k
          (cechSectionPrepend 𝒰 F V i_fix hiV m (σ ∘ k.succAbove)
            ((CombinatorialCech.cons_comp_succAbove_succ i_fix σ k) ▸ y)) := by
  have hle : homotopyOpen 𝒰 V (m + 1) (Fin.cons i_fix (σ ∘ k.succAbove)) ≤
      homotopyOpen 𝒰 V (m + 1) ((Fin.cons i_fix σ : Fin (m + 2) → 𝒰.I₀) ∘ (k.succ).succAbove) :=
    le_of_eq (by rw [CombinatorialCech.cons_comp_succAbove_succ i_fix σ k])
  rw [cechSectionCoeff_transport 𝒰 F V
    (CombinatorialCech.cons_comp_succAbove_succ i_fix σ k) hle]
  refine Eq.trans (presheaf_restriction_comp_apply _
    (homotopyOpen_le_prepend 𝒰 V i_fix hiV σ)
    (homotopyOpen_le_coface 𝒰 V (Fin.cons i_fix σ) k.succ) y) ?_
  refine Eq.trans (presheaf_restriction_eq_of_parallel _ _
    (homOfLE ((homotopyOpen_le_coface 𝒰 V σ k).trans
    ((homotopyOpen_le_prepend 𝒰 V i_fix hiV (σ ∘ k.succAbove)).trans hle))).op y) ?_
  refine Eq.symm ?_
  refine Eq.trans (DFunLike.congr_arg (cechSectionCoface 𝒰 F V m σ k)
    (presheaf_restriction_comp_apply _
      (homotopyOpen_le_prepend 𝒰 V i_fix hiV (σ ∘ k.succAbove)) hle y)) ?_
  exact presheaf_restriction_comp_apply _ (homotopyOpen_le_coface 𝒰 V σ k)
    ((homotopyOpen_le_prepend 𝒰 V i_fix hiV (σ ∘ k.succAbove)).trans hle) y

end RestrictionEngine

section ContractingHomotopy

variable (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (V : TopologicalSpace.Opens X)
variable (i_fix : 𝒰.I₀) (hiV : V ≤ coverOpen 𝒰 i_fix)

/-- The augmented concrete section Čech complex of section Čech, as a reducible abbreviation. -/
noncomputable abbrev cechSectionAugComplex : CochainComplex Ab.{u} ℕ :=
  (sectionCechComplexV 𝒰 F V).augment (sectionCechAugV 𝒰 F V) (sectionCechAugV_comp_d 𝒰 F V)

/-- The bottom homotopy component `Č⁰ ⟶ Γ(V, F)`: project onto the `i_fix`-coordinate and
restrict along `V ≤ U'_{i_fix}` (the `π_{i_fix}` of the Stacks projection homotopy). -/
noncomputable def cechSectionHomotopyZero :
    (cechSectionAugComplex 𝒰 F V).X 1 ⟶ (cechSectionAugComplex 𝒰 F V).X 0 :=
  Pi.π (fun τ : Fin 1 → 𝒰.I₀ =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
        (Opposite.op (⨅ l, (coverOpen 𝒰 (τ l) ⊓ V)))) (Fin.cons i_fix Fin.elim0) ≫
    ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
      (homOfLE (homotopyOpen_le_prepend 𝒰 V i_fix hiV Fin.elim0)).op

/-- The Čech-degree homotopy components `Čᵐ⁺¹ ⟶ Čᵐ`: prepend `i_fix` to the multi-index
and restrict (the identity on coefficients, since prepending does not shrink the open). -/
noncomputable def cechSectionHomotopyComp (m : ℕ) :
    (cechSectionAugComplex 𝒰 F V).X (m + 2) ⟶ (cechSectionAugComplex 𝒰 F V).X (m + 1) :=
  Pi.lift fun τ : Fin (m + 1) → 𝒰.I₀ =>
    Pi.π (fun ρ : Fin (m + 2) → 𝒰.I₀ =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op (⨅ l, (coverOpen 𝒰 (ρ l) ⊓ V)))) (Fin.cons i_fix τ) ≫
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
        (homOfLE (homotopyOpen_le_prepend 𝒰 V i_fix hiV τ)).op

/-- Coordinatewise value of the homotopy component: the `τ`-coordinate of `h(t)` is the
engine prepend map applied to the `(i_fix :: τ)`-coordinate of `t`. -/
lemma cechSectionHomotopyComp_coord (m : ℕ)
    (t : ToType ((sectionCechComplexV 𝒰 F V).X (m + 1))) (τ : Fin (m + 1) → 𝒰.I₀) :
    sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F) m
        (ConcreteCategory.hom (cechSectionHomotopyComp 𝒰 F V i_fix hiV m) t) τ
      = cechSectionPrepend 𝒰 F V i_fix hiV (m + 1) τ
          (sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
            ((SheafOfModules.forget X.ringCatSheaf).obj F) (m + 1) t (Fin.cons i_fix τ)) := by
  refine Eq.trans (sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) m _ τ) ?_
  refine Eq.trans (ConcreteCategory.comp_apply
    (cechSectionHomotopyComp 𝒰 F V i_fix hiV m) (Pi.π _ τ) t).symm ?_
  refine Eq.trans (ConcreteCategory.congr_hom (Pi.lift_π _ τ) t) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ t) ?_
  exact DFunLike.congr_arg (cechSectionPrepend 𝒰 F V i_fix hiV (m + 1) τ)
    (sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) (m + 1) t (Fin.cons i_fix τ)).symm

/-- Coordinatewise value of the section Čech differential: the engine `depDiff`. -/
lemma cechSectionD_coord (m : ℕ)
    (t : ToType ((sectionCechComplexV 𝒰 F V).X m)) (σ : Fin (m + 2) → 𝒰.I₀) :
    sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F) (m + 1)
        (ConcreteCategory.hom ((sectionCechComplexV 𝒰 F V).d m (m + 1)) t) σ
      = CombinatorialCech.depDiff (A := cechSectionCoeff 𝒰 F V) (cechSectionCoface 𝒰 F V)
          (fun τ => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
            ((SheafOfModules.forget X.ringCatSheaf).obj F) m t τ) σ := by
  have hd : (sectionCechComplexV 𝒰 F V).d m (m + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F)) m :=
    CochainComplex.of_d
      (fun n => (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F)).obj (SimplexCategory.mk n))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F))) m
  refine Eq.trans (congrArg (fun y => sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) (m + 1) y σ)
    (ConcreteCategory.congr_hom hd t)) ?_
  refine Eq.trans (sectionCech_objD_apply (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) m t σ) ?_
  exact Finset.sum_congr rfl fun j _ => rfl

omit [Finite 𝒰.I₀] in
/-- The `m = 0` engine differential is the single augmentation restriction. -/
lemma cechSectionDepDiff_zero
    (u : ∀ ρ : Fin 0 → 𝒰.I₀, cechSectionCoeff 𝒰 F V 0 ρ) (σ : Fin 1 → 𝒰.I₀) :
    CombinatorialCech.depDiff (A := cechSectionCoeff 𝒰 F V) (cechSectionCoface 𝒰 F V) u σ
      = cechSectionCoface 𝒰 F V 0 σ 0 (u (σ ∘ (0 : Fin 1).succAbove)) := by
  simp only [CombinatorialCech.depDiff]
  refine Eq.trans (Fin.sum_univ_one _) ?_
  simp only [Fin.val_zero, pow_zero]
  exact one_zsmul _

/-- **(I0)** The degree-`0` contracting identity: `ε ≫ π_{i_fix} = 𝟙` on `Γ(V, F)`. -/
lemma cechSection_comm_zero :
    𝟙 ((cechSectionAugComplex 𝒰 F V).X 0) =
      (cechSectionAugComplex 𝒰 F V).d 0 1 ≫ cechSectionHomotopyZero 𝒰 F V i_fix hiV := by
  refine Eq.symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (· ≫ ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
      (homOfLE (homotopyOpen_le_prepend 𝒰 V i_fix hiV Fin.elim0)).op)
    (sectionCechAugV_π 𝒰 F V (Fin.cons i_fix Fin.elim0))) ?_
  refine Eq.trans ((((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map_comp
    (homOfLE (sectionCechV_intersection_le 𝒰 V (Fin.cons i_fix Fin.elim0))).op
    (homOfLE (homotopyOpen_le_prepend 𝒰 V i_fix hiV Fin.elim0)).op).symm) ?_
  refine Eq.trans (congrArg (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map)
    (op_comp (f := homOfLE (homotopyOpen_le_prepend 𝒰 V i_fix hiV Fin.elim0))
      (g := homOfLE
        (sectionCechV_intersection_le 𝒰 V (Fin.cons i_fix Fin.elim0)))).symm) ?_
  refine Eq.trans (congrArg
    (fun m => ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map m.op)
    (Subsingleton.elim (homOfLE (homotopyOpen_le_prepend 𝒰 V i_fix hiV Fin.elim0) ≫
      homOfLE (sectionCechV_intersection_le 𝒰 V (Fin.cons i_fix Fin.elim0))) (𝟙 V))) ?_
  exact (congrArg (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map)
    (op_id (X := V))).trans
    (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map_id (Opposite.op V))

end ContractingHomotopy

end AlgebraicGeometry
