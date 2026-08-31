/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowTransitions
import AlgebraicJacobian.Cohomology.RigidEngine5Toolkit

/-!
# Eventual kernel killing for side-preserving theta transitions

A global relative theta section can vanish on one pinned chart without vanishing on
the other when the base ring is nonreduced.  The matching equation nevertheless makes
the opposite component vanish on the chart overlap.  Since that overlap is the basic
open of the opposite chart coordinate, affine denominator clearing kills the opposite
component by a power of that coordinate.

The canonical side-preserving transition has component `1` on the selected chart and
the corresponding coordinate power on the opposite chart.  It therefore kills every
chosen-side read-zero section after all sufficiently large shifts.  In particular, a
killing shift can be chosen to be a multiple of any positive high-window step.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

section CoordinatePowers

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

/-- The manufactured chart-0 coordinate power is the power of the relative
chart-0 coordinate. -/
theorem relFiberCoordPow_eq_pow (a : Nat) :
    relFiberCoordPow C R pi a = relFiberCoord₀ C R pi ^ a := by
  change relPullbackSection C R (fiberChart₀ pi) (fiberCoord pi ^ a) =
    relPullbackSection C R (fiberChart₀ pi) (fiberCoord pi) ^ a
  induction a with
  | zero =>
      rw [pow_zero, pow_zero]
      exact map_one _
  | succ a ih => rw [pow_succ, pow_succ, relPullbackSection_mul, ih]

/-- The manufactured chart-1 coordinate power is the power of the relative
chart-1 coordinate. -/
theorem relFiberCoordOnePow_eq_pow (a : Nat) :
    relFiberCoordOnePow C R pi a = relFiberCoord₁ C R pi ^ a := by
  change relPullbackSection C R (fiberChart₁ pi) (fiberCoord₁ pi ^ a) =
    relPullbackSection C R (fiberChart₁ pi) (fiberCoord₁ pi) ^ a
  induction a with
  | zero =>
      rw [pow_zero, pow_zero]
      exact map_one _
  | succ a ih => rw [pow_succ, pow_succ, relPullbackSection_mul, ih]

/-- On the chart opposite side `false`, the false-side unit section reads as
the chart-1 coordinate power. -/
@[simp]
theorem relThetaResSide_relThetaSideUnit_false_true (a : Nat) :
    relThetaResSide a true le_rfl
        (relThetaSideUnitSection C R pi false a) =
      relFiberCoord₁ C R pi ^ a := by
  change (relCurve C R).resHom (le_inf le_top le_rfl)
      ((relThetaSectionSnd C R pi a).val.2) = relFiberCoord₁ C R pi ^ a
  rw [relThetaSectionSnd_val_snd, Scheme.resHom_resHom, Scheme.resHom_self,
    relFiberCoordOnePow_eq_pow]

/-- On the chart opposite side `true`, the true-side unit section reads as
the chart-0 coordinate power. -/
@[simp]
theorem relThetaResSide_relThetaSideUnit_true_false (a : Nat) :
    relThetaResSide a false le_rfl
        (relThetaSideUnitSection C R pi true a) =
      relFiberCoord₀ C R pi ^ a := by
  change (relCurve C R).resHom (le_inf le_top le_rfl)
      ((relThetaSectionFst C R pi a).val.1) = relFiberCoord₀ C R pi ^ a
  rw [relThetaSectionFst_val_fst, Scheme.resHom_resHom, Scheme.resHom_self,
    relFiberCoordPow_eq_pow]

end CoordinatePowers

section KernelKill

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

local notation "X" => relCurve C R
local notation "V₀" => relPinnedChart C R pi false
local notation "V₁" => relPinnedChart C R pi true

/-- A theta section whose full readings on both pinned charts vanish is zero.
This is valid over an arbitrary base ring: the two readings are restrictions
along the equalities `Vᵢ = ⊤ ⊓ Vᵢ`, so together they recover both components. -/
theorem relThetaSections_eq_zero_of_both_side_reads (a : Nat)
    (x : relThetaSections C R pi a)
    (hfalse : relThetaResSide a false le_rfl x = 0)
    (htrue : relThetaResSide a true le_rfl x = 0) : x = 0 := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [relPinnedChart] at hfalse
    rw [relThetaResSide_false] at hfalse
    let hsource : (relCover C R (fiberTwoCover pi)).V₀ ≤
        ⊤ ⊓ (relCover C R (fiberTwoCover pi)).V₀ := le_inf le_top le_rfl
    let hback : ⊤ ⊓ (relCover C R (fiberTwoCover pi)).V₀ ≤
        (relCover C R (fiberTwoCover pi)).V₀ := inf_le_right
    have hread : (relCurve C R).resHom hsource x.val.1 = 0 := hfalse
    have hzero : (relCurve C R).resHom hback
        ((relCurve C R).resHom hsource x.val.1) = 0 := by
      simpa only [map_zero] using
        congrArg ((relCurve C R).resHom hback) hread
    have hxzero : x.val.1 = 0 := by
      calc
        x.val.1 = (relCurve C R).resHom (hback.trans hsource) x.val.1 :=
          (Scheme.resHom_self _ _).symm
        _ = (relCurve C R).resHom hback
            ((relCurve C R).resHom hsource x.val.1) :=
          (Scheme.resHom_resHom _ _ _).symm
        _ = 0 := hzero
    simpa only [Submodule.coe_zero, Prod.fst_zero] using hxzero
  · simp only [relPinnedChart] at htrue
    rw [relThetaResSide_true] at htrue
    let hsource : (relCover C R (fiberTwoCover pi)).V₁ ≤
        ⊤ ⊓ (relCover C R (fiberTwoCover pi)).V₁ := le_inf le_top le_rfl
    let hback : ⊤ ⊓ (relCover C R (fiberTwoCover pi)).V₁ ≤
        (relCover C R (fiberTwoCover pi)).V₁ := inf_le_right
    have hread : (relCurve C R).resHom hsource x.val.2 = 0 := htrue
    have hzero : (relCurve C R).resHom hback
        ((relCurve C R).resHom hsource x.val.2) = 0 := by
      simpa only [map_zero] using
        congrArg ((relCurve C R).resHom hback) hread
    have hxzero : x.val.2 = 0 := by
      calc
        x.val.2 = (relCurve C R).resHom (hback.trans hsource) x.val.2 :=
          (Scheme.resHom_self _ _).symm
        _ = (relCurve C R).resHom hback
            ((relCurve C R).resHom hsource x.val.2) :=
          (Scheme.resHom_resHom _ _ _).symm
        _ = 0 := hzero
    simpa only [Submodule.coe_zero, Prod.snd_zero] using hxzero

/-- **Eventual kernel killing.** If a theta section reads as zero on the selected
pinned chart, then every sufficiently large selected-side unit transition kills it.

For side `false`, matching makes the chart-1 component vanish on `D(t₁)` and a
power of `t₁` kills it on `V₁`.  The side `true` case is the chart-0 mirror. -/
theorem exists_forall_ge_relThetaSideTransition_eq_zero (side : Bool) (p : Nat)
    (x : relThetaSections C R pi p)
    (hx : relThetaResSide p side le_rfl x = 0) :
    ∃ m : Nat, ∀ s : Nat, m ≤ s →
      relThetaSideTransition C R pi side p s x = 0 := by
  cases side with
  | false =>
      let hW : V₀ ⊓ V₁ ≤ V₀ ⊓ V₁ := le_rfl
      have hmatch := relThetaResSide_matching (C := C) (R := R) (π := pi)
        p false true hW x
      have hselected : relThetaResSide p false (hW.trans inf_le_left) x = 0 := by
        have hres : (relCurve C R).resHom
            (inf_le_left : V₀ ⊓ V₁ ≤ V₀)
            (relThetaResSide p false le_rfl x) = 0 := by
          have h := congrArg
            ((relCurve C R).resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀)) hx
          rw [map_zero] at h
          exact h
        exact (resHom_relThetaResSide p false le_rfl inf_le_left x).symm.trans hres
      rw [hselected] at hmatch
      have hoverlap : relThetaResSide p true (hW.trans inf_le_right) x = 0 :=
        (relThetaSideUnit (C := C) (R := R) (π := pi)
          p false true hW).mul_right_eq_zero.mp
            hmatch.symm
      have hopp : (relCurve C R).resHom
          (inf_le_right : V₀ ⊓ V₁ ≤ V₁)
          (relThetaResSide p true le_rfl x) = 0 := by
        exact (resHom_relThetaResSide p true le_rfl
          (inf_le_right : V₀ ⊓ V₁ ≤ V₁) x).trans hoverlap
      let rx : Γ(X, (relCover C R (fiberTwoCover pi)).V₁) := by
        simpa only [relPinnedChart] using relThetaResSide p true le_rfl x
      have hopp' : (relCurve C R).resHom
          (inf_le_right :
            (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁ ≤
              (relCover C R (fiberTwoCover pi)).V₁) rx = 0 := by
        simpa only [rx, relPinnedChart] using hopp
      obtain ⟨m, hm⟩ :=
        (relCover_isAffineOpen₁ C R (fiberTwoCover pi)).exists_pow_mul_eq_zero_of_resHom_eq_zero
          (relFiberCoord₁ C R pi)
          (relCover_fiberTwoCover_inf_eq_basicOpen₁ C R pi)
          (inf_le_right :
            (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁ ≤
              (relCover C R (fiberTwoCover pi)).V₁)
          rx hopp'
      refine ⟨m, fun s hms => ?_⟩
      have hpow : relFiberCoord₁ C R pi ^ s * rx = 0 := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hms
        calc
          relFiberCoord₁ C R pi ^ (m + d) *
                rx =
              relFiberCoord₁ C R pi ^ d *
                (relFiberCoord₁ C R pi ^ m *
                  rx) := by ring
          _ = 0 := by rw [hm, mul_zero]
      have hfalse : relThetaResSide (s + p) false le_rfl
          (relThetaSideTransition C R pi false p s x) = 0 := by
        rw [relThetaResSide_relThetaSideTransition, hx]
      have htrue : relThetaResSide (s + p) true le_rfl
          (relThetaSideTransition C R pi false p s x) = 0 := by
        rw [relThetaSideTransition, relThetaSectionsMulLeft_apply,
          relThetaResSide_relThetaSectionsMul,
          relThetaResSide_relThetaSideUnit_false_true]
        simpa only [rx, relPinnedChart] using hpow
      exact relThetaSections_eq_zero_of_both_side_reads C R pi (s + p)
        (relThetaSideTransition C R pi false p s x) hfalse htrue
  | true =>
      have hswap : V₀ ⊓ V₁ ≤ V₁ ⊓ V₀ := le_inf inf_le_right inf_le_left
      have hmatch := relThetaResSide_matching (C := C) (R := R) (π := pi)
        p true false hswap x
      have hselected : relThetaResSide p true (hswap.trans inf_le_left) x = 0 := by
        have hres : (relCurve C R).resHom
            (inf_le_right : V₀ ⊓ V₁ ≤ V₁)
            (relThetaResSide p true le_rfl x) = 0 := by
          have h := congrArg
            ((relCurve C R).resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁)) hx
          rw [map_zero] at h
          exact h
        exact (resHom_relThetaResSide p true le_rfl inf_le_right x).symm.trans hres
      rw [hselected] at hmatch
      have hoverlap : relThetaResSide p false (hswap.trans inf_le_right) x = 0 :=
        (relThetaSideUnit (C := C) (R := R) (π := pi)
          p true false hswap).mul_right_eq_zero.mp hmatch.symm
      have hopp : (relCurve C R).resHom
          (inf_le_left : V₀ ⊓ V₁ ≤ V₀)
          (relThetaResSide p false le_rfl x) = 0 := by
        exact (resHom_relThetaResSide p false le_rfl
          (inf_le_left : V₀ ⊓ V₁ ≤ V₀) x).trans hoverlap
      let rx : Γ(X, (relCover C R (fiberTwoCover pi)).V₀) := by
        simpa only [relPinnedChart] using relThetaResSide p false le_rfl x
      have hopp' : (relCurve C R).resHom
          (inf_le_left :
            (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁ ≤
              (relCover C R (fiberTwoCover pi)).V₀) rx = 0 := by
        simpa only [rx, relPinnedChart] using hopp
      obtain ⟨m, hm⟩ :=
        (relCover_isAffineOpen₀ C R (fiberTwoCover pi)).exists_pow_mul_eq_zero_of_resHom_eq_zero
          (relFiberCoord₀ C R pi)
          (relCover_fiberTwoCover_inf_eq_basicOpen₀ C R pi)
          (inf_le_left :
            (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁ ≤
              (relCover C R (fiberTwoCover pi)).V₀)
          rx hopp'
      refine ⟨m, fun s hms => ?_⟩
      have hpow : relFiberCoord₀ C R pi ^ s * rx = 0 := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hms
        calc
          relFiberCoord₀ C R pi ^ (m + d) *
                rx =
              relFiberCoord₀ C R pi ^ d *
                (relFiberCoord₀ C R pi ^ m *
                  rx) := by ring
          _ = 0 := by rw [hm, mul_zero]
      have hfalse : relThetaResSide (s + p) false le_rfl
          (relThetaSideTransition C R pi true p s x) = 0 := by
        rw [relThetaSideTransition, relThetaSectionsMulLeft_apply,
          relThetaResSide_relThetaSectionsMul,
          relThetaResSide_relThetaSideUnit_true_false]
        simpa only [rx, relPinnedChart] using hpow
      have htrue : relThetaResSide (s + p) true le_rfl
          (relThetaSideTransition C R pi true p s x) = 0 := by
        rw [relThetaResSide_relThetaSideTransition, hx]
      exact relThetaSections_eq_zero_of_both_side_reads C R pi (s + p)
        (relThetaSideTransition C R pi true p s x) hfalse htrue

/-- A chosen-side read-zero section is killed by some side-unit transition. -/
theorem exists_relThetaSideTransition_eq_zero (side : Bool) (p : Nat)
    (x : relThetaSections C R pi p)
    (hx : relThetaResSide p side le_rfl x = 0) :
    ∃ s : Nat, relThetaSideTransition C R pi side p s x = 0 := by
  obtain ⟨m, hm⟩ := exists_forall_ge_relThetaSideTransition_eq_zero
    C R pi side p x hx
  exact ⟨m, hm m le_rfl⟩

/-- Killing exponents meet every positive arithmetic progression. -/
theorem exists_arithmeticProgression_relThetaSideTransition_eq_zero
    (start step : Nat) (hstep : 0 < step) (side : Bool) (p : Nat)
    (x : relThetaSections C R pi p)
    (hx : relThetaResSide p side le_rfl x = 0) :
    ∃ n : Nat,
      relThetaSideTransition C R pi side p (start + n * step) x = 0 := by
  obtain ⟨m, hm⟩ := exists_forall_ge_relThetaSideTransition_eq_zero
    C R pi side p x hx
  have hmstep : m ≤ start + m * step := by
    have hle : m ≤ m * step := Nat.le_mul_of_pos_right m hstep
    exact hle.trans (Nat.le_add_left _ _)
  exact ⟨m, hm _ hmstep⟩

/-- In particular, for every positive step `S`, a killing exponent can be chosen
to be a multiple of `S`. -/
theorem exists_mul_relThetaSideTransition_eq_zero (S : Nat) (hS : 0 < S)
    (side : Bool) (p : Nat) (x : relThetaSections C R pi p)
    (hx : relThetaResSide p side le_rfl x = 0) :
    ∃ q : Nat, relThetaSideTransition C R pi side p (q * S) x = 0 := by
  obtain ⟨m, hm⟩ := exists_forall_ge_relThetaSideTransition_eq_zero
    C R pi side p x hx
  exact ⟨m, hm (m * S) (Nat.le_mul_of_pos_right m hS)⟩

end KernelKill

end AlgebraicGeometry
