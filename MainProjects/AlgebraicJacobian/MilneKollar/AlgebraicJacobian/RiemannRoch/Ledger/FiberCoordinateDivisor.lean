/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.FiberCoordinateData

/-!
# The divisor intrinsic to source-side fiber coordinates

A `FiberCoordinateData` carries enough information to recover the fiber unit in the function
field and the effective divisor of its zeros.  This file makes those constructions independent
of a chosen model of the projective line.  The compatibility lemmas at the end identify them
with the existing `fiberCoordUnit` and `fiberWeilDivisor` for data obtained from a map to
Ledger's `P1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace FiberCoordinateData

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (D : FiberCoordinateData Y)

/-! ## The coordinate unit -/

omit [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
private theorem germ_x_mul_germ_y :
    (Y.presheaf.germ D.V₀ (genericPoint Y) (D.genericPoint_mem_inf).1).hom D.x *
      (Y.presheaf.germ D.V₁ (genericPoint Y) (D.genericPoint_mem_inf).2).hom D.y = 1 := by
  have hη : genericPoint Y ∈ D.V₀ ⊓ D.V₁ := D.genericPoint_mem_inf
  rw [← Y.presheaf.germ_res_apply (homOfLE inf_le_left) (genericPoint Y) hη D.x,
    ← Y.presheaf.germ_res_apply (homOfLE inf_le_right) (genericPoint Y) hη D.y,
    ← map_mul, D.res_x_mul_res_y, map_one]

/-- The function-field unit represented by the first coordinate and inverted by the second. -/
noncomputable def coordinateUnit : Y.functionFieldˣ where
  val := (Y.presheaf.germ D.V₀ (genericPoint Y) (D.genericPoint_mem_inf).1).hom D.x
  inv := (Y.presheaf.germ D.V₁ (genericPoint Y) (D.genericPoint_mem_inf).2).hom D.y
  val_inv := germ_x_mul_germ_y D
  inv_val := by rw [mul_comm]; exact germ_x_mul_germ_y D

omit [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
lemma coordinateUnit_val : (D.coordinateUnit : Y.functionField) =
    (Y.presheaf.germ D.V₀ (genericPoint Y) (D.genericPoint_mem_inf).1).hom D.x := rfl

omit [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
lemma coordinateUnit_inv_val : (D.coordinateUnit⁻¹).val =
    (Y.presheaf.germ D.V₁ (genericPoint Y) (D.genericPoint_mem_inf).2).hom D.y := rfl

/-! ## The order table -/

private lemma divisorBound_le_iff {A B : Y.CurveDivisor} {x : Y}
    (hx : x ≠ genericPoint Y) :
    Scheme.divisorBound A hx ≤ Scheme.divisorBound B hx ↔ coeffAt hx A ≤ coeffAt hx B := by
  simp only [Scheme.divisorBound, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  rfl

private lemma zero_le_coeffAt_divOf_iff_ord_le_one (w : Y.functionFieldˣ) {x : Y}
    (hx : x ≠ genericPoint Y) :
    (0 : ℤ) ≤ coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) w) ↔
      Scheme.ord (Y ↘ Spec (CommRingCat.of K)) hx (w : Y.functionField) ≤ 1 := by
  rw [Scheme.ord_val_eq K w hx, ← Scheme.divisorBound_zero hx, divisorBound_le_iff hx,
    CurveDivisor.coeffAt_zero, CurveDivisor.coeffAt_neg, neg_nonpos]

private lemma zero_le_coeffAt_divOf_of_val_eq_germ {w : Y.functionFieldˣ} {W : Y.Opens}
    (hηW : genericPoint Y ∈ W) {x : Y} (hx : x ≠ genericPoint Y) (hxW : x ∈ W)
    (s : Γ(Y, W))
    (hws : (w : Y.functionField) = (Y.presheaf.germ W (genericPoint Y) hηW).hom s) :
    (0 : ℤ) ≤ coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) w) := by
  rw [zero_le_coeffAt_divOf_iff_ord_le_one w hx, hws,
    germ_generic_eq_algebraMap_germ hηW hxW s]
  exact Scheme.ord_algebraMap_stalk_le_one K hx _

/-- The coordinate unit has nonnegative order on its regular chart. -/
theorem coordinateUnit_coeffAt_divOf_nonneg_of_mem_V0 {x : Y}
    (hx : x ≠ genericPoint Y) (hxV0 : x ∈ D.V₀) :
    (0 : ℤ) ≤ coeffAt hx
      (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) D.coordinateUnit) :=
  zero_le_coeffAt_divOf_of_val_eq_germ (D.genericPoint_mem_inf).1 hx hxV0 D.x
    D.coordinateUnit_val

private lemma coeffAt_divOf_inv {x : Y} (hx : x ≠ genericPoint Y) :
    coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) D.coordinateUnit⁻¹) =
      -coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) D.coordinateUnit) := by
  have h : Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) D.coordinateUnit⁻¹ +
      Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) D.coordinateUnit = 0 := by
    rw [← Scheme.divOf_mul (Y ↘ Spec (CommRingCat.of K)), inv_mul_cancel,
      Scheme.divOf_one (Y ↘ Spec (CommRingCat.of K))]
  have hc := congrArg (coeffAt hx) h
  rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_zero] at hc
  linarith

/-- The coordinate unit has nonpositive order on the chart where its inverse is regular. -/
theorem coordinateUnit_coeffAt_divOf_nonpos_of_mem_V1 {x : Y}
    (hx : x ≠ genericPoint Y) (hxV1 : x ∈ D.V₁) :
    coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) D.coordinateUnit) ≤ 0 := by
  have hinv := zero_le_coeffAt_divOf_of_val_eq_germ
    (K := K) (w := D.coordinateUnit⁻¹) (D.genericPoint_mem_inf).2 hx hxV1 D.y
      D.coordinateUnit_inv_val
  rw [coeffAt_divOf_inv D hx, neg_nonneg] at hinv
  exact hinv

/-! ## The positive divisor -/

/-- The effective divisor of zeros of the source-side coordinate unit. -/
noncomputable def coordinateWeilDivisor : Y.CurveDivisor :=
  Finsupp.mapRange (fun n => max n 0) (max_self 0)
    (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) D.coordinateUnit)

lemma coordinateWeilDivisor_coeffAt {x : Y} (hx : x ≠ genericPoint Y) :
    coeffAt hx (D.coordinateWeilDivisor (K := K)) =
      max (coeffAt hx
        (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) D.coordinateUnit)) 0 := by
  simp only [coeffAt, toFinsupp, coordinateWeilDivisor, Finsupp.mapRange_apply]

/-- The coordinate divisor is effective. -/
theorem coordinateWeilDivisor_nonneg : 0 ≤ D.coordinateWeilDivisor (K := K) := by
  refine Finsupp.le_def.mpr (fun p => ?_)
  change (0 : ℤ) ≤ coeffAt p.2 (D.coordinateWeilDivisor (K := K))
  rw [D.coordinateWeilDivisor_coeffAt (K := K) p.2]
  exact le_max_right _ _

/-- The coordinate divisor vanishes on the inverse-coordinate chart. -/
theorem coordinateWeilDivisor_coeffAt_of_mem_V1 {x : Y} (hx : x ≠ genericPoint Y)
    (hxV1 : x ∈ D.V₁) : coeffAt hx (D.coordinateWeilDivisor (K := K)) = 0 := by
  rw [D.coordinateWeilDivisor_coeffAt (K := K) hx,
    max_eq_right (D.coordinateUnit_coeffAt_divOf_nonpos_of_mem_V1 hx hxV1)]

/-- On the regular-coordinate chart, the coordinate divisor equals the principal order. -/
theorem coordinateWeilDivisor_coeffAt_of_mem_V0 {x : Y} (hx : x ≠ genericPoint Y)
    (hxV0 : x ∈ D.V₀) :
    coeffAt hx (D.coordinateWeilDivisor (K := K)) =
      coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) D.coordinateUnit) := by
  rw [D.coordinateWeilDivisor_coeffAt (K := K) hx,
    max_eq_left (D.coordinateUnit_coeffAt_divOf_nonneg_of_mem_V0 hx hxV0)]

/-! ## Compatibility with the map-based construction -/

section OfMap

variable (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]

omit [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
/-- The intrinsic unit of map-derived coordinates is the existing fiber coordinate unit. -/
lemma coordinateUnit_ofMap : (ofMap π).coordinateUnit = fiberCoordUnit π := by
  apply Units.ext
  rfl

/-- The intrinsic positive divisor of map-derived coordinates is the existing fiber divisor. -/
lemma coordinateWeilDivisor_ofMap :
    (ofMap π).coordinateWeilDivisor (K := K) = fiberWeilDivisor π := by
  unfold coordinateWeilDivisor fiberWeilDivisor
  rw [coordinateUnit_ofMap π]

end OfMap

end FiberCoordinateData

end AlgebraicGeometry
