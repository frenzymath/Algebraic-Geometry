/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowH1
import AlgebraicJacobian.Picard.DivisorFamilyThetaSections
import AlgebraicJacobian.Picard.DivSchemeSeedUnivAssemble
import AlgebraicJacobian.Picard.DivSchemeFamilySide
import AlgebraicJacobian.Picard.DivisorThetaPairing
import AlgebraicJacobian.Cohomology.RigidEngine5Toolkit

/-!
# Exhaustion of pinned chart sections by high theta windows

Every section on either pinned affine chart extends to a global relative theta section
after a sufficiently large twist.  Denominator clearing on the opposite affine chart
produces one extension exponent.  Multiplication by the canonical theta section whose
chosen-side component is `1` then promotes that extension to every larger exponent.

Consequently every pinned-chart section is read by a theta section at one of the
cofinal divisor-scheme exponents `M + n * S` whenever `S > 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

section WindowStep

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
  (pi : Y ⟶ P1 K) [IsFinite pi] [IsDominant pi]
  (hpi : pi ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))

/-- A positive vanishing bound forces the multiplier-window exponent to be positive. -/
theorem windowS_choice_pos_of_windowBound_pos (g : Nat)
    (hb : 0 < windowBound pi hpi) : 0 < windowS_choice pi hpi g := by
  by_contra hS
  have hS0 : windowS_choice pi hpi g = 0 := Nat.eq_zero_of_not_pos hS
  have hspec := windowS_spec_three pi hpi g
  have hdelta := one_le_windowδ pi
  have hg : (0 : Int) ≤ g := Int.natCast_nonneg g
  rw [hS0] at hspec
  norm_num at hspec
  linarith

end WindowStep

section ThetaMultiplication

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

/-- Componentwise multiplication of global theta sections adds their exponents. -/
noncomputable def relThetaSectionsMul (a b : Nat)
    (x : relThetaSections C R pi a) (y : relThetaSections C R pi b) :
    relThetaSections C R pi (a + b) := by
  refine ⟨(x.1.1 * y.1.1, x.1.2 * y.1.2), ?_⟩
  rw [mem_twistSubmodule_iff]
  have hx := (mem_twistSubmodule_iff R
    (relCover C R (fiberTwoCover pi)).V₀
    (relCover C R (fiberTwoCover pi)).V₁
    (relThetaCocycle C R pi a) x.1).mp x.2
  have hy := (mem_twistSubmodule_iff R
    (relCover C R (fiberTwoCover pi)).V₀
    (relCover C R (fiberTwoCover pi)).V₁
    (relThetaCocycle C R pi b) y.1).mp y.2
  rw [map_mul, map_mul, relThetaCocycle_add, Units.val_mul, map_mul, hx, hy]
  ring

@[simp]
theorem relThetaResSide_relThetaSectionsMul (a b : Nat) (side : Bool)
    (x : relThetaSections C R pi a) (y : relThetaSections C R pi b) :
    relThetaResSide (a + b) side le_rfl (relThetaSectionsMul C R pi a b x y) =
      relThetaResSide a side le_rfl x * relThetaResSide b side le_rfl y := by
  cases side <;> simp [relThetaSectionsMul, map_mul]

end ThetaMultiplication

section EventualExhaustion

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

private theorem relFiberCoordPow_eq_pow (a : Nat) :
    relFiberCoordPow C R pi a = relFiberCoord₀ C R pi ^ a := by
  change relPullbackSection C R (fiberChart₀ pi) (fiberCoord pi ^ a) =
    relPullbackSection C R (fiberChart₀ pi) (fiberCoord pi) ^ a
  induction a with
  | zero =>
      rw [pow_zero, pow_zero]
      exact map_one _
  | succ a ih => rw [pow_succ, pow_succ, relPullbackSection_mul, ih]

private theorem relFiberCoordOnePow_eq_pow (a : Nat) :
    relFiberCoordOnePow C R pi a = relFiberCoord₁ C R pi ^ a := by
  change relPullbackSection C R (fiberChart₁ pi) (fiberCoord₁ pi ^ a) =
    relPullbackSection C R (fiberChart₁ pi) (fiberCoord₁ pi) ^ a
  induction a with
  | zero =>
      rw [pow_zero, pow_zero]
      exact map_one _
  | succ a ih => rw [pow_succ, pow_succ, relPullbackSection_mul, ih]

/-- A section on either pinned affine chart is the chosen-side reading of a global
theta section at every sufficiently large exponent. -/
theorem exists_forall_ge_exists_relThetaResSide_eq (side : Bool)
    (x : Γ(relCurve C R, relPinnedChart C R pi side)) :
    ∃ m : Nat, ∀ a : Nat, m ≤ a → ∃ s : relThetaSections C R pi a,
      relThetaResSide a side le_rfl s = x := by
  cases side with
  | false =>
      obtain ⟨y, m, hy⟩ :=
        (relCover_isAffineOpen₁ C R (fiberTwoCover pi)).exists_pow_mul_eq_resHom
          (relFiberCoord₁ C R pi)
          (relCover_fiberTwoCover_inf_eq_basicOpen₁ C R pi)
          (inf_le_right :
            (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁ ≤
              (relCover C R (fiberTwoCover pi)).V₁)
          ((relCurve C R).resHom inf_le_left x)
      refine ⟨m, fun a hma => ?_⟩
      let sm : relThetaSections C R pi m := by
        refine ⟨((relCurve C R).resHom inf_le_right x,
          (relCurve C R).resHom inf_le_right y), ?_⟩
        rw [mem_twistSubmodule_iff]
        have hcoord : (relCurve C R).resHom inf_le_right
            (relFiberCoord₁ C R pi) ^ m =
              (((relThetaCocycle C R pi m)⁻¹ :
                Γ(relCurve C R,
                  (relCover C R (fiberTwoCover pi)).V₀ ⊓
                    (relCover C R (fiberTwoCover pi)).V₁)ˣ) :
                Γ(relCurve C R,
                  (relCover C R (fiberTwoCover pi)).V₀ ⊓
                    (relCover C R (fiberTwoCover pi)).V₁)) := by
          rw [← map_pow, ← relFiberCoordOnePow_eq_pow C R pi,
            resHom_relFiberCoordOnePow]
        have hmatch : (relCurve C R).resHom inf_le_left x =
            ((relThetaCocycle C R pi m :
            Γ(relCurve C R,
              (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁)ˣ) :
            Γ(relCurve C R,
              (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁)) *
              (relCurve C R).resHom inf_le_right y := by
          rw [← hy, hcoord, ← mul_assoc, Units.mul_inv, one_mul]
          rfl
        have hmatch' := congrArg ((relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            ⊤ ⊓ (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁ ≤
                (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁)) hmatch
        rw [map_mul] at hmatch'
        convert hmatch' using 1 <;>
          try simp only [Scheme.resHom_resHom]
        all_goals exact (Scheme.resHom_resHom _ _ _).symm
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hma
      let oneSide : relThetaSections C R pi d := relThetaSectionSnd C R pi d
      refine ⟨relThetaSectionsMul C R pi m d sm oneSide, ?_⟩
      rw [relThetaResSide_relThetaSectionsMul]
      simp [sm, oneSide]
  | true =>
      obtain ⟨y, m, hy⟩ :=
        (relCover_isAffineOpen₀ C R (fiberTwoCover pi)).exists_pow_mul_eq_resHom
          (relFiberCoord₀ C R pi)
          (relCover_fiberTwoCover_inf_eq_basicOpen₀ C R pi)
          (inf_le_left :
            (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁ ≤
              (relCover C R (fiberTwoCover pi)).V₀)
          ((relCurve C R).resHom inf_le_right x)
      refine ⟨m, fun a hma => ?_⟩
      let sm : relThetaSections C R pi m := by
        refine ⟨((relCurve C R).resHom inf_le_right y,
          (relCurve C R).resHom inf_le_right x), ?_⟩
        rw [mem_twistSubmodule_iff]
        have hcoord : (relCurve C R).resHom inf_le_left
            (relFiberCoord₀ C R pi) ^ m =
              ((relThetaCocycle C R pi m :
                Γ(relCurve C R,
                  (relCover C R (fiberTwoCover pi)).V₀ ⊓
                    (relCover C R (fiberTwoCover pi)).V₁)ˣ) :
                Γ(relCurve C R,
                  (relCover C R (fiberTwoCover pi)).V₀ ⊓
                    (relCover C R (fiberTwoCover pi)).V₁)) := by
          rw [← map_pow, ← relFiberCoordPow_eq_pow C R pi,
            resHom_relFiberCoordPow]
        have hmatch : (relCurve C R).resHom inf_le_left y =
            ((relThetaCocycle C R pi m :
            Γ(relCurve C R,
              (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁)ˣ) :
            Γ(relCurve C R,
              (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁)) *
              (relCurve C R).resHom inf_le_right x := by
          rw [← hy, hcoord]
          rfl
        have hmatch' := congrArg ((relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            ⊤ ⊓ (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁ ≤
                (relCover C R (fiberTwoCover pi)).V₀ ⊓
                (relCover C R (fiberTwoCover pi)).V₁)) hmatch
        rw [map_mul] at hmatch'
        convert hmatch' using 1 <;>
          try simp only [Scheme.resHom_resHom]
        all_goals
          congr 1
          exact (Scheme.resHom_resHom _ _ _).symm
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hma
      let oneSide : relThetaSections C R pi d := relThetaSectionFst C R pi d
      refine ⟨relThetaSectionsMul C R pi m d sm oneSide, ?_⟩
      rw [relThetaResSide_relThetaSectionsMul]
      simp [sm, oneSide]

/-- Cofinal arithmetic-progressions exhaust either pinned chart. -/
theorem exists_arithmeticProgression_relThetaResSide_eq (start step : Nat)
    (hstep : 0 < step) (side : Bool)
    (x : Γ(relCurve C R, relPinnedChart C R pi side)) :
    ∃ n : Nat, ∃ s : relThetaSections C R pi (start + n * step),
      relThetaResSide (start + n * step) side le_rfl s = x := by
  obtain ⟨m, hm⟩ := exists_forall_ge_exists_relThetaResSide_eq C R pi side x
  have hmstep : m ≤ start + m * step := by
    have hle : m ≤ m * step := by
      exact Nat.le_mul_of_pos_right m hstep
    exact hle.trans (Nat.le_add_left _ _)
  exact ⟨m, hm _ hmstep⟩

end EventualExhaustion

section HighWindowExhaustion

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (pi : C.left ⟶ P1 k) [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowChartExhaustion :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (R : Type u) [CommRing R] [Algebra k R]

/-- Every pinned-chart section occurs as a reading at some `M + n*S` window. -/
theorem exists_highWindow_relThetaResSide_eq (g : Nat)
    (hS : 0 < windowS_choice pi hpi g)
    (side : Bool) (x : Γ(relCurve C R, relPinnedChart C R pi side)) :
    ∃ n : Nat, ∃ s : relThetaSections C R pi
        (windowM_choice pi hpi g + n * windowS_choice pi hpi g),
      relThetaResSide
        (windowM_choice pi hpi g + n * windowS_choice pi hpi g)
        side le_rfl s = x :=
  exists_arithmeticProgression_relThetaResSide_eq C R pi
    (windowM_choice pi hpi g) (windowS_choice pi hpi g) hS side x

/-- Campaign form: the standard positive window-bound hypothesis discharges `S > 0`. -/
theorem exists_highWindow_relThetaResSide_eq_of_windowBound_pos (g : Nat)
    (hb : 0 < windowBound pi hpi) (side : Bool)
    (x : Γ(relCurve C R, relPinnedChart C R pi side)) :
    ∃ n : Nat, ∃ s : relThetaSections C R pi
        (windowM_choice pi hpi g + n * windowS_choice pi hpi g),
      relThetaResSide
        (windowM_choice pi hpi g + n * windowS_choice pi hpi g)
        side le_rfl s = x :=
  exists_highWindow_relThetaResSide_eq C pi hpi R g
    (windowS_choice_pos_of_windowBound_pos pi hpi g hb) side x

end HighWindowExhaustion

end AlgebraicGeometry
