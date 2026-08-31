/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeEpsCarveKit
import AlgebraicJacobian.Picard.DivSchemeFamilySide

/-!
# Multiplication compatibility for arbitrary theta windows

The original divisor-scheme carve uses only the multiplication step `M -> M + S`.
The high-window relation tower needs the same calculation at every pair of exponents.
This file packages multiplication

`H^0(O(pF)) x H^0(O(qF)) -> H^0(O((p+q)F))`

and proves that both components of the theta presentation multiply on the nose, first
over the base field and then after relative base change.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

noncomputable local instance instOverCleftWindowMulGeneral :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))] [IsDominant pi]

section FieldMultiplication

/-- Multiplication between arbitrary fibre-divisor windows, reindexed by
`p • F + q • F = (p + q) • F`. -/
noncomputable def thetaWindowMul (p q : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤)) :
    ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤) →ₗ[k]
      ↥(divisorSections k ((p + q) • fiberWeilDivisor pi) ⊤) :=
  (LinearEquiv.ofEq _ _ (congrArg (fun D => divisorSections k D ⊤)
    (add_nsmul (fiberWeilDivisor pi) p q).symm)).toLinearMap.comp
      (sectionMulBilin k (p • fiberWeilDivisor pi) (q • fiberWeilDivisor pi) a)

omit [IsFinite pi] in
@[simp]
theorem thetaWindowMul_coe (p q : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤))
    (m : ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) :
    ((thetaWindowMul (C := C) (pi := pi) p q a m :
        ↥(divisorSections k ((p + q) • fiberWeilDivisor pi) ⊤)) :
      C.left.functionField) =
      (a : C.left.functionField) * (m : C.left.functionField) := by
  rw [thetaWindowMul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_ofEq_apply, sectionMulBilin_apply_coe]

omit [IsFinite pi] in
/-- Arbitrary-exponent field-pair multiplication on the first theta chart. -/
theorem thetaSectionPair_thetaWindowMul_fst (p q : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤))
    (m : ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) :
    (thetaSectionPair C pi (p + q) (thetaWindowMul (C := C) (pi := pi) p q a m)).val.1 =
      (thetaSectionPair C pi p a).val.1 * (thetaSectionPair C pi q m).val.1 := by
  apply germ_injective_of_isIntegral C.left (genericPoint C.left)
    (⟨trivial, (genericPoint_mem_preimage_inf pi).1⟩ :
      genericPoint C.left ∈ ⊤ ⊓ fiberChart₀ pi)
  rw [map_mul, germ_thetaSectionPair_fst, germ_thetaSectionPair_fst,
    germ_thetaSectionPair_fst, thetaWindowMul_coe, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_add]
  ring

omit [IsFinite pi] in
/-- Arbitrary-exponent field-pair multiplication on the second theta chart. -/
theorem thetaSectionPair_thetaWindowMul_snd (p q : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤))
    (m : ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) :
    (thetaSectionPair C pi (p + q) (thetaWindowMul (C := C) (pi := pi) p q a m)).val.2 =
      (thetaSectionPair C pi p a).val.2 * (thetaSectionPair C pi q m).val.2 := by
  apply germ_injective_of_isIntegral C.left (genericPoint C.left)
    (⟨trivial, (genericPoint_mem_preimage_inf pi).2⟩ :
      genericPoint C.left ∈ ⊤ ⊓ fiberChart₁ pi)
  rw [map_mul, germ_thetaSectionPair_snd, germ_thetaSectionPair_snd,
    germ_thetaSectionPair_snd, thetaWindowMul_coe]

end FieldMultiplication

section BaseFieldMultiplication

/-- Arbitrary-exponent multiplication for base-field relative theta sections, chart 0. -/
theorem resHom_relThetaFieldSection_thetaWindowMul_fst (p q : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤))
    (m : ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) :
    (relCurve C k).resHom (le_inf le_top le_rfl)
        ((relThetaFieldSection C pi (p + q)
          (thetaWindowMul (C := C) (pi := pi) p q a m)).val.1) =
      (relCurve C k).resHom (le_inf le_top le_rfl)
          ((relThetaFieldSection C pi p a).val.1) *
        (relCurve C k).resHom (le_inf le_top le_rfl)
          ((relThetaFieldSection C pi q m).val.1) := by
  rw [resHom_relThetaFieldSection_fst, resHom_relThetaFieldSection_fst,
    resHom_relThetaFieldSection_fst, thetaSectionPair_thetaWindowMul_fst, map_mul,
    sectionsCollapse_mul]

/-- Arbitrary-exponent multiplication for base-field relative theta sections, chart 1. -/
theorem resHom_relThetaFieldSection_thetaWindowMul_snd (p q : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤))
    (m : ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) :
    (relCurve C k).resHom (le_inf le_top le_rfl)
        ((relThetaFieldSection C pi (p + q)
          (thetaWindowMul (C := C) (pi := pi) p q a m)).val.2) =
      (relCurve C k).resHom (le_inf le_top le_rfl)
          ((relThetaFieldSection C pi p a).val.2) *
        (relCurve C k).resHom (le_inf le_top le_rfl)
          ((relThetaFieldSection C pi q m).val.2) := by
  rw [resHom_relThetaFieldSection_snd, resHom_relThetaFieldSection_snd,
    resHom_relThetaFieldSection_snd, thetaSectionPair_thetaWindowMul_snd, map_mul,
    sectionsCollapse_mul]

end BaseFieldMultiplication

section RelativeMultiplication

variable (R : Type u) [CommRing R] [Algebra k R]

/-- The first-chart component of a base-field theta multiplier after extension to `R`. -/
noncomputable def thetaWindowMulSectionFst (p : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤)) :
    Γ(relCurve C R, (relCover C R (fiberTwoCover pi)).V₀) :=
  relSectionsMap C k R (fiberTwoCover pi).V₀
    ((relCurve C k).resHom (le_inf le_top le_rfl)
      ((relThetaFieldSection C pi p a).val.1))

/-- The second-chart component of a base-field theta multiplier after extension to `R`. -/
noncomputable def thetaWindowMulSectionSnd (p : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤)) :
    Γ(relCurve C R, (relCover C R (fiberTwoCover pi)).V₁) :=
  relSectionsMap C k R (fiberTwoCover pi).V₁
    ((relCurve C k).resHom (le_inf le_top le_rfl)
      ((relThetaFieldSection C pi p a).val.2))

set_option maxHeartbeats 1000000 in
-- Mixed relative-curve and tensor spellings make the pure-tensor reduction expensive.
set_option synthInstance.maxHeartbeats 400000 in
/-- Arbitrary-exponent relative multiplication on the first theta chart. -/
theorem relThetaWindowEquiv_thetaWindowMul_fst (p q : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤))
    (hH1q : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi q)).H1)
    (hH1pq : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi (p + q))).H1)
    (x : R ⊗[k] ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) :
    (relCurve C R).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C R pi (p + q) hH1pq
          (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) x)).val.1) =
      thetaWindowMulSectionFst (C := C) (pi := pi) R p a *
        (relCurve C R).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C R pi q hH1q x).val.1) := by
  induction x with
  | zero => simp only [map_zero, Submodule.coe_zero, Prod.fst_zero, mul_zero]
  | add x y hx hy =>
      have h2 : (relThetaWindowEquiv C R pi (p + q) hH1pq
            (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) x +
              LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) y)).val.1 =
          (relThetaWindowEquiv C R pi (p + q) hH1pq
            (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) x)).val.1 +
          (relThetaWindowEquiv C R pi (p + q) hH1pq
            (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) y)).val.1 := by
        rw [map_add]
        rfl
      have h3 : (relThetaWindowEquiv C R pi q hH1q (x + y)).val.1 =
          (relThetaWindowEquiv C R pi q hH1q x).val.1 +
            (relThetaWindowEquiv C R pi q hH1q y).val.1 := by
        rw [map_add]
        rfl
      rw [map_add, h2, map_add, hx, hy, h3, map_add, mul_add]
  | tmul r m =>
      have hone : (relCurve C R).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C R pi (p + q) hH1pq
            (1 ⊗ₜ thetaWindowMul (C := C) (pi := pi) p q a m)).val.1) =
          thetaWindowMulSectionFst (C := C) (pi := pi) R p a *
            (relCurve C R).resHom (le_inf le_top le_rfl)
              ((relThetaWindowEquiv C R pi q hH1q (1 ⊗ₜ m)).val.1) :=
        ((resHom_relThetaWindowEquiv_one_tmul_fst C pi R (p + q) hH1pq
            (thetaWindowMul (C := C) (pi := pi) p q a m)).trans
          ((congrArg (relSectionsMap C k R (fiberTwoCover pi).V₀)
              (resHom_relThetaFieldSection_thetaWindowMul_fst C pi p q a m)).trans
            (map_mul (relSectionsMap C k R (fiberTwoCover pi).V₀) _ _))).trans
          (congrArg (thetaWindowMulSectionFst (C := C) (pi := pi) R p a * ·)
            (resHom_relThetaWindowEquiv_one_tmul_fst C pi R q hH1q m).symm)
      have hbc : LinearMap.baseChange R
          (thetaWindowMul (C := C) (pi := pi) p q a) (r ⊗ₜ m) =
          r • ((1 : R) ⊗ₜ thetaWindowMul (C := C) (pi := pi) p q a m) := by
        rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hsm : (r ⊗ₜ m : R ⊗[k]
          ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) = r • ((1 : R) ⊗ₜ m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e1 : (relThetaWindowEquiv C R pi (p + q) hH1pq
            (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a)
              (r ⊗ₜ m))).val.1 =
          r • (relThetaWindowEquiv C R pi (p + q) hH1pq
            (1 ⊗ₜ thetaWindowMul (C := C) (pi := pi) p q a m)).val.1 := by
        rw [hbc, map_smul]
        rfl
      have e2 : (relThetaWindowEquiv C R pi q hH1q (r ⊗ₜ m)).val.1 =
          r • (relThetaWindowEquiv C R pi q hH1q (1 ⊗ₜ m)).val.1 := by
        rw [hsm, map_smul]
        rfl
      have e2' : (relCurve C R).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C R pi q hH1q (r ⊗ₜ m)).val.1) =
          r • (relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R pi q hH1q (1 ⊗ₜ m)).val.1) :=
        (congrArg ((relCurve C R).resHom (le_inf le_top le_rfl)) e2).trans
          (resHom_smul_rel' C R _ _ _)
      refine ((congrArg ((relCurve C R).resHom (le_inf le_top le_rfl)) e1).trans
        (resHom_smul_rel' C R _ _ _)).trans ?_
      refine (congrArg (r • ·) hone).trans ?_
      refine Eq.trans ?_
        (congrArg (thetaWindowMulSectionFst (C := C) (pi := pi) R p a * ·) e2'.symm)
      rw [Scheme.overModule_smul_def, Scheme.overModule_smul_def, mul_left_comm]

set_option maxHeartbeats 1000000 in
-- Mixed relative-curve and tensor spellings make the pure-tensor reduction expensive.
set_option synthInstance.maxHeartbeats 400000 in
/-- Arbitrary-exponent relative multiplication on the second theta chart. -/
theorem relThetaWindowEquiv_thetaWindowMul_snd (p q : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤))
    (hH1q : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi q)).H1)
    (hH1pq : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi (p + q))).H1)
    (x : R ⊗[k] ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) :
    (relCurve C R).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C R pi (p + q) hH1pq
          (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) x)).val.2) =
      thetaWindowMulSectionSnd (C := C) (pi := pi) R p a *
        (relCurve C R).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C R pi q hH1q x).val.2) := by
  induction x with
  | zero => simp only [map_zero, Submodule.coe_zero, Prod.snd_zero, mul_zero]
  | add x y hx hy =>
      have h2 : (relThetaWindowEquiv C R pi (p + q) hH1pq
            (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) x +
              LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) y)).val.2 =
          (relThetaWindowEquiv C R pi (p + q) hH1pq
            (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) x)).val.2 +
          (relThetaWindowEquiv C R pi (p + q) hH1pq
            (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) y)).val.2 := by
        rw [map_add]
        rfl
      have h3 : (relThetaWindowEquiv C R pi q hH1q (x + y)).val.2 =
          (relThetaWindowEquiv C R pi q hH1q x).val.2 +
            (relThetaWindowEquiv C R pi q hH1q y).val.2 := by
        rw [map_add]
        rfl
      rw [map_add, h2, map_add, hx, hy, h3, map_add, mul_add]
  | tmul r m =>
      have hone : (relCurve C R).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C R pi (p + q) hH1pq
            (1 ⊗ₜ thetaWindowMul (C := C) (pi := pi) p q a m)).val.2) =
          thetaWindowMulSectionSnd (C := C) (pi := pi) R p a *
            (relCurve C R).resHom (le_inf le_top le_rfl)
              ((relThetaWindowEquiv C R pi q hH1q (1 ⊗ₜ m)).val.2) :=
        ((resHom_relThetaWindowEquiv_one_tmul_snd C pi R (p + q) hH1pq
            (thetaWindowMul (C := C) (pi := pi) p q a m)).trans
          ((congrArg (relSectionsMap C k R (fiberTwoCover pi).V₁)
              (resHom_relThetaFieldSection_thetaWindowMul_snd C pi p q a m)).trans
            (map_mul (relSectionsMap C k R (fiberTwoCover pi).V₁) _ _))).trans
          (congrArg (thetaWindowMulSectionSnd (C := C) (pi := pi) R p a * ·)
            (resHom_relThetaWindowEquiv_one_tmul_snd C pi R q hH1q m).symm)
      have hbc : LinearMap.baseChange R
          (thetaWindowMul (C := C) (pi := pi) p q a) (r ⊗ₜ m) =
          r • ((1 : R) ⊗ₜ thetaWindowMul (C := C) (pi := pi) p q a m) := by
        rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hsm : (r ⊗ₜ m : R ⊗[k]
          ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) = r • ((1 : R) ⊗ₜ m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e1 : (relThetaWindowEquiv C R pi (p + q) hH1pq
            (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a)
              (r ⊗ₜ m))).val.2 =
          r • (relThetaWindowEquiv C R pi (p + q) hH1pq
            (1 ⊗ₜ thetaWindowMul (C := C) (pi := pi) p q a m)).val.2 := by
        rw [hbc, map_smul]
        rfl
      have e2 : (relThetaWindowEquiv C R pi q hH1q (r ⊗ₜ m)).val.2 =
          r • (relThetaWindowEquiv C R pi q hH1q (1 ⊗ₜ m)).val.2 := by
        rw [hsm, map_smul]
        rfl
      have e2' : (relCurve C R).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C R pi q hH1q (r ⊗ₜ m)).val.2) =
          r • (relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R pi q hH1q (1 ⊗ₜ m)).val.2) :=
        (congrArg ((relCurve C R).resHom (le_inf le_top le_rfl)) e2).trans
          (resHom_smul_rel' C R _ _ _)
      refine ((congrArg ((relCurve C R).resHom (le_inf le_top le_rfl)) e1).trans
        (resHom_smul_rel' C R _ _ _)).trans ?_
      refine (congrArg (r • ·) hone).trans ?_
      refine Eq.trans ?_
        (congrArg (thetaWindowMulSectionSnd (C := C) (pi := pi) R p a * ·) e2'.symm)
      rw [Scheme.overModule_smul_def, Scheme.overModule_smul_def, mul_left_comm]

set_option maxHeartbeats 1000000 in
-- Side-uniform reduction unfolds the two dependent pinned-chart restrictions.
/-- Arbitrary-exponent multiplication, stated uniformly on either pinned chart. -/
theorem relThetaResSide_relThetaWindowEquiv_thetaWindowMul (p q : Nat)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤))
    (hH1p : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi p)).H1)
    (hH1q : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi q)).H1)
    (hH1pq : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi (p + q))).H1)
    (side : Bool)
    (x : R ⊗[k] ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) :
    relThetaResSide (p + q) side le_rfl
        (relThetaWindowEquiv C R pi (p + q) hH1pq
          (LinearMap.baseChange R (thetaWindowMul (C := C) (pi := pi) p q a) x)) =
      relThetaResSide p side le_rfl
          (relThetaWindowEquiv C R pi p hH1p (1 ⊗ₜ a)) *
        relThetaResSide q side le_rfl (relThetaWindowEquiv C R pi q hH1q x) := by
  cases side
  · simp only [relThetaResSide_false]
    calc
      _ = thetaWindowMulSectionFst (C := C) (pi := pi) R p a *
          (relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R pi q hH1q x).val.1) :=
        relThetaWindowEquiv_thetaWindowMul_fst C pi R p q a hH1q hH1pq x
      _ = _ := congrArg
        (· * (relCurve C R).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C R pi q hH1q x).val.1))
        (resHom_relThetaWindowEquiv_one_tmul_fst C pi R p hH1p a).symm
  · simp only [relThetaResSide_true]
    calc
      _ = thetaWindowMulSectionSnd (C := C) (pi := pi) R p a *
          (relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R pi q hH1q x).val.2) :=
        relThetaWindowEquiv_thetaWindowMul_snd C pi R p q a hH1q hH1pq x
      _ = _ := congrArg
        (· * (relCurve C R).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C R pi q hH1q x).val.2))
        (resHom_relThetaWindowEquiv_one_tmul_snd C pi R p hH1p a).symm

end RelativeMultiplication

end AlgebraicGeometry
