/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowTransitionRelation
import AlgebraicJacobian.Picard.DivSchemeThetaKernelKill

/-!
# Shifted high-window transition read formulas

The transition relation records the arbitrary-side chart-reading formula, so
its iterates multiply each chart reading by a fixed unit-section reading.  The
unit-read calculations are kept here; the eventual theta-kernel argument lives
in the companion `DivSchemeHighWindowTransitionKernelKill` module.
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

section HighWindowTransitionKernel

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowTransitionKernel :
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

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
local notation "G" n => divUniversalHighWindowAmbient (C := C) (pi := pi)
  (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
  (i := i) (j := j) n
local notation "CR" => divUniversalHighWindowChartRead (C := C)
  (pi := pi) hpi g r1 r2 b1 b2 i j

/-! ## The fixed multiplier read -/

/-- The reading of the canonical multiplier used by a side-preserving transition. -/
noncomputable def divUniversalHighWindowUnitRead
    (transitionSide readSide : Bool) :
    Γ(relCurve C RZ, relPinnedChart C RZ pi readSide) :=
  relThetaResSide (windowS_choice pi hpi g) readSide le_rfl
    (relThetaSideUnitSection C RZ pi transitionSide
      (windowS_choice pi hpi g))

/-! ## One-step and iterated chart readings -/

set_option maxHeartbeats 4800000 in
-- The arbitrary-side transition formula unfolds the dependent theta dictionary.
set_option synthInstance.maxHeartbeats 1200000 in
/-- A side-preserving one-step transition multiplies every chart reading by the
reading of its canonical multiplier. -/
theorem divUniversalHighWindowRelationTransition_chartRead_mul
    (transitionSide readSide : Bool) (n : Nat) (x : G(n + 1)) :
    (CR (n + 2) readSide)
        (divUniversalHighWindowRelationTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j transitionSide (n + 1) x) =
      divUniversalHighWindowUnitRead (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
          transitionSide readSide * (CR (n + 1) readSide) x := by
  rw [divUniversalHighWindowRelationTransition,
    divUniversalHighWindowTensorMultiplierTransition_chartRead,
    divUniversalHighWindowSideMultiplierTensor_theta]
  rfl

set_option maxHeartbeats 1600000 in
-- The induction repeatedly re-elaborates the shifted dependent ambient.
set_option synthInstance.maxHeartbeats 1200000 in
-- Each induction branch synthesizes the module structure of a shifted stage family.
/-- Iterated shifted transitions multiply an arbitrary chart reading by a power
of the fixed canonical multiplier reading. -/
theorem divUniversalHighWindowShiftedRelationTransitionOfLE_chartRead_pow
    (transitionSide readSide : Bool) (n m : Nat) (h : n ≤ m) (x : G(n + 1)) :
    (CR (m + 1) readSide)
        (divUniversalHighWindowShiftedRelationTransitionOfLE (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j transitionSide n m h x) =
      (divUniversalHighWindowUnitRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j transitionSide readSide) ^ (m - n) *
        (CR (n + 1) readSide) x := by
  induction h with
  | refl =>
      simp [divUniversalHighWindowShiftedRelationTransitionOfLE,
        HighWindowTransitionKit.transitionOfLE_self]
  | @step m h ih =>
      rw [divUniversalHighWindowShiftedRelationTransitionOfLE,
        HighWindowTransitionKit.transitionOfLE_succ
          (fun q => G(q + 1))
          (fun q => divUniversalHighWindowRelationTransition
            (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j transitionSide (q + 1))
          n m h,
        LinearMap.comp_apply,
        divUniversalHighWindowRelationTransition_chartRead_mul]
      have ih' :
          (CR (m + 1) readSide)
              (HighWindowTransitionKit.transitionOfLE
                (fun q => G (q + 1))
                (fun q => divUniversalHighWindowRelationTransition
                  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
                  transitionSide (q + 1)) n m h x) =
            (divUniversalHighWindowUnitRead (C := C) (pi := pi)
              hpi g r1 r2 b1 b2 i j transitionSide readSide) ^ (m - n) *
              (CR (n + 1) readSide) x := by
        simpa only [divUniversalHighWindowShiftedRelationTransitionOfLE] using ih
      rw [ih']
      have hsub : m + 1 - n = (m - n) + 1 := Nat.sub_add_comm h
      rw [hsub, pow_succ]
      ring

/-! ## Unit-read powers -/

set_option maxHeartbeats 1600000 in
-- The four side combinations unfold dependent relative-chart section rings.
set_option synthInstance.maxHeartbeats 800000 in
-- Same-side unit reads and opposite coordinate powers use different chart presentations.
/-- The opposite pinned-chart reading of a `q*S` side unit is the `q`-th power
of the one-step opposite reading. -/
theorem divUniversalHighWindowUnitRead_pow
    (transitionSide readSide : Bool) (q : Nat) :
    (divUniversalHighWindowUnitRead (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
      transitionSide readSide) ^ q =
      relThetaResSide (q * windowS_choice pi hpi g) readSide le_rfl
        (relThetaSideUnitSection C RZ pi transitionSide
          (q * windowS_choice pi hpi g)) := by
  unfold divUniversalHighWindowUnitRead
  cases transitionSide with
  | false =>
      cases readSide with
      | false =>
          rw [relThetaResSide_relThetaSideUnit,
            relThetaResSide_relThetaSideUnit, one_pow]
      | true =>
          rw [relThetaResSide_relThetaSideUnit_false_true,
            relThetaResSide_relThetaSideUnit_false_true]
          simpa [Nat.mul_comm] using
            (pow_mul (relFiberCoord₁ C RZ pi)
              (windowS_choice pi hpi g) q).symm
  | true =>
      cases readSide with
      | false =>
          rw [relThetaResSide_relThetaSideUnit_true_false,
            relThetaResSide_relThetaSideUnit_true_false]
          simpa [Nat.mul_comm] using
            (pow_mul (relFiberCoord₀ C RZ pi)
              (windowS_choice pi hpi g) q).symm
      | true =>
          rw [relThetaResSide_relThetaSideUnit,
            relThetaResSide_relThetaSideUnit, one_pow]

end HighWindowTransitionKernel

end AlgebraicGeometry
