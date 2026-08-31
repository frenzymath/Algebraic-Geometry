/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeThetaCoordinateMulSpan
import AlgebraicJacobian.Picard.DivSchemeHighWindowRelationReadSuccessor

/-!
# Pure-window coefficient readings

This file packages the arithmetic-progression coefficient windows used by
high-window saturation.  The product formula combines field normal generation
with the relative theta multiplication and exponent-reindexing identities.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowTransitionSaturationCoefficient

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowTransitionSaturationCoefficient :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k ((windowS_choice pi hpi g • fiberWeilDivisor pi)
    + (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)
variable (side : Bool)

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
local notation "S" => windowS_choice pi hpi g
local notation "F" => fiberWeilDivisor pi
local notation "HS" => ↥(Scheme.divisorSections k (S • F) ⊤)
local notation "HP" q => ↥(Scheme.divisorSections k ((S + q * S) • F) ⊤)
local notation "B" => Γ(relCurve C RZ, relPinnedChart C RZ pi side)

/-- Reading a coefficient in the pure arithmetic-progression window
`S + q*S` on the selected pinned chart. -/
noncomputable def divUniversalPureWindowCoefficientRead (q : Nat) :
    (RZ ⊗[k] HP(q)) →ₗ[RZ] B :=
  (relThetaResSide (S + q * S) side le_rfl).comp
    (relThetaWindowEquiv C RZ pi (S + q * S)
      (relThetaPairH1_windowS_add_mulS C pi hpi g q)).toLinearMap

/-- The multiplier-window tensor, reindexed as the zeroth pure window. -/
noncomputable def divUniversalPureWindowZeroTensor (a : HS) : RZ ⊗[k] HP(0) :=
  LinearMap.baseChange RZ
    (divisorWindowExponentEquiv (C := C) (pi := pi)
      (by simp : S = S + 0 * S)).toLinearMap (1 ⊗ₜ a)

/-- Reading the reindexed zeroth pure tensor is the ordinary `S`-window read. -/
theorem divUniversalPureWindowCoefficientRead_zeroTensor (a : HS) :
    divUniversalPureWindowCoefficientRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j side 0
        (divUniversalPureWindowZeroTensor (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j a) =
      relThetaResSide S side le_rfl
        (relThetaWindowEquiv C RZ pi S (relThetaPairH1_windowS C hpi g)
          (1 ⊗ₜ a)) := by
  exact relThetaResSide_relThetaWindowEquiv_baseChange_ofEq
    (C := C) (pi := pi) (by simp : S = S + 0 * S)
      (relThetaPairH1_windowS C hpi g)
      (relThetaPairH1_windowS_add_mulS C pi hpi g 0) RZ side (1 ⊗ₜ a)

/-- Reindexing an arbitrary zeroth pure-window tensor back to the `S` window
does not change its selected chart reading. -/
theorem divUniversalPureWindowCoefficientRead_zero (z : RZ ⊗[k] HP(0)) :
    divUniversalPureWindowCoefficientRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j side 0 z =
      relThetaResSide S side le_rfl
        (relThetaWindowEquiv C RZ pi S (relThetaPairH1_windowS C hpi g)
          (LinearMap.baseChange RZ
            (divisorWindowExponentEquiv (C := C) (pi := pi)
              (by simp : S + 0 * S = S)).toLinearMap z)) := by
  exact (relThetaResSide_relThetaWindowEquiv_baseChange_ofEq
    (C := C) (pi := pi) (by simp : S + 0 * S = S)
      (relThetaPairH1_windowS_add_mulS C pi hpi g 0)
      (relThetaPairH1_windowS C hpi g) RZ side z).symm

/-- Reindex a product into the next pure arithmetic-progression window. -/
noncomputable def divUniversalPureWindowProduct (q : Nat) (a : HS) (b : HP(q)) :
    HP(q + 1) :=
  divisorWindowExponentEquiv (C := C) (pi := pi) (by ring :
      S + (S + q * S) = S + (q + 1) * S)
    (thetaWindowMul (C := C) (pi := pi) S (S + q * S) a b)

@[simp]
theorem coe_divUniversalPureWindowProduct (q : Nat) (a : HS) (b : HP(q)) :
    (divUniversalPureWindowProduct (C := C) (pi := pi) hpi g q a b :
      C.left.functionField) =
      (a : C.left.functionField) * (b : C.left.functionField) := by
  rw [divUniversalPureWindowProduct, coe_divisorWindowExponentEquiv,
    thetaWindowMul_coe]

set_option maxHeartbeats 2400000 in
-- Reindexing both base-changed pure-window factors is elaboration-heavy.
set_option synthInstance.maxHeartbeats 800000 in
/-- Pure-window coefficient readings respect the product decomposition used by
the two-coordinate normal-generation theorem. -/
theorem divUniversalPureWindowCoefficientRead_product (q : Nat)
    (a : HS) (b : HP(q)) :
    divUniversalPureWindowCoefficientRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j side (q + 1)
        (1 ⊗ₜ divUniversalPureWindowProduct (C := C) (pi := pi) hpi g q a b) =
      divUniversalPureWindowCoefficientRead (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j side 0
            (divUniversalPureWindowZeroTensor (C := C) (pi := pi)
              hpi g r1 r2 b1 b2 i j a) *
        divUniversalPureWindowCoefficientRead (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j side q (1 ⊗ₜ b) := by
  let e : S + (S + q * S) = S + (q + 1) * S := by ring
  have hH1sum : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi (S + (S + q * S)))).H1 := by
    rw [e]
    exact relThetaPairH1_windowS_add_mulS C pi hpi g (q + 1)
  have htensor :
      (1 ⊗ₜ divUniversalPureWindowProduct (C := C) (pi := pi) hpi g q a b :
        RZ ⊗[k] HP(q + 1)) =
        LinearMap.baseChange RZ
          (divisorWindowExponentEquiv (C := C) (pi := pi) e).toLinearMap
          (LinearMap.baseChange RZ
            (thetaWindowMul (C := C) (pi := pi) S (S + q * S) a) (1 ⊗ₜ b)) := by
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    rfl
  rw [htensor]
  change relThetaResSide (S + (q + 1) * S) side le_rfl
      (relThetaWindowEquiv C RZ pi (S + (q + 1) * S)
        (relThetaPairH1_windowS_add_mulS C pi hpi g (q + 1))
        (LinearMap.baseChange RZ
          (divisorWindowExponentEquiv (C := C) (pi := pi) e).toLinearMap
          (LinearMap.baseChange RZ
            (thetaWindowMul (C := C) (pi := pi) S (S + q * S) a) (1 ⊗ₜ b)))) = _
  rw [relThetaResSide_relThetaWindowEquiv_baseChange_ofEq
    (C := C) (pi := pi) e hH1sum
      (relThetaPairH1_windowS_add_mulS C pi hpi g (q + 1)) RZ side]
  rw [divUniversalPureWindowCoefficientRead_zeroTensor]
  exact relThetaResSide_relThetaWindowEquiv_thetaWindowMul
    C pi RZ S (S + q * S) a
      (relThetaPairH1_windowS C hpi g)
      (relThetaPairH1_windowS_add_mulS C pi hpi g q) hH1sum side (1 ⊗ₜ b)

end HighWindowTransitionSaturationCoefficient

end AlgebraicGeometry
