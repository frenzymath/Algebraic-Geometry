/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowTransitionKernel

/-!
# Kernel killing for the shifted high-window transition system

The relative theta kernel-killing theorem applies to a high-window ambient
after transporting it through `divUniversalHighWindowThetaEquiv`.  The
transition relation already records the arbitrary-side chart-reading formula,
so its iterates multiply each chart reading by a fixed unit-section reading.
The two unit-read calculations turn the relative theta killing exponent
`q * S` into a `q`-step shifted transition.  Finally both pinned-chart reads
of the transported output vanish, and the two-side theta injectivity lemma
returns the ambient equality.
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

section HighWindowTransitionKernelKill

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowTransitionKernelKill :
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

set_option maxHeartbeats 2400000 in
-- Both chart readings of the transported output are compared before injectivity.
set_option synthInstance.maxHeartbeats 800000 in
/-- A shifted high-window ambient section with selected chart read zero is killed
by some later side-preserving transition. -/
theorem exists_divUniversalHighWindowShiftedRelationTransitionOfLE_eq_zero_of_chartRead_eq_zero
    (hb : 0 < windowBound pi hpi) (transitionSide : Bool) (n : Nat)
    (x : G(n + 1))
    (hx : (CR (n + 1) transitionSide) x = 0) :
    ∃ m : Nat, ∃ h : n ≤ m,
      divUniversalHighWindowShiftedRelationTransitionOfLE (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j transitionSide n m h x = 0 := by
  let p := divUniversalHighWindowExponent (C := C) (pi := pi) hpi g (n + 1)
  let thetaX := (divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j (n + 1)) x
  have hx' : relThetaResSide p transitionSide le_rfl thetaX = 0 := by
    change relThetaResSide
      (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g (n + 1))
      transitionSide le_rfl
      ((divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1)) x) = 0
    exact hx
  have hS : 0 < windowS_choice pi hpi g :=
    windowS_choice_pos_of_windowBound_pos pi hpi g hb
  obtain ⟨q, hkill⟩ := exists_mul_relThetaSideTransition_eq_zero
    C RZ pi (windowS_choice pi hpi g) hS transitionSide p thetaX hx'
  let h : n ≤ n + q := Nat.le_add_right n q
  have hkill_read (readSide : Bool) :
      relThetaResSide (q * windowS_choice pi hpi g) readSide le_rfl
          (relThetaSideUnitSection C RZ pi transitionSide
            (q * windowS_choice pi hpi g)) *
        relThetaResSide p readSide le_rfl thetaX = 0 := by
    have hread := congrArg
      (relThetaResSide (q * windowS_choice pi hpi g + p) readSide le_rfl)
      hkill
    rw [relThetaSideTransition, relThetaSectionsMulLeft_apply,
      relThetaResSide_relThetaSectionsMul, map_zero] at hread
    exact hread
  have hzero_read (readSide : Bool) :
      (CR (n + q + 1) readSide)
          (divUniversalHighWindowShiftedRelationTransitionOfLE (C := C)
            (pi := pi) hpi g r1 r2 b1 b2 i j transitionSide n (n + q) h x) = 0 := by
    calc
      _ = (divUniversalHighWindowUnitRead (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j transitionSide readSide) ^
            ((n + q) - n) * (CR (n + 1) readSide) x :=
        divUniversalHighWindowShiftedRelationTransitionOfLE_chartRead_pow
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j transitionSide readSide
          n (n + q) h x
      _ = (divUniversalHighWindowUnitRead (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j transitionSide readSide) ^ q *
          relThetaResSide p readSide le_rfl thetaX := by
        rw [Nat.add_sub_cancel_left]
        rfl
      _ = relThetaResSide (q * windowS_choice pi hpi g) readSide le_rfl
            (relThetaSideUnitSection C RZ pi transitionSide
              (q * windowS_choice pi hpi g)) *
          relThetaResSide p readSide le_rfl thetaX := by
        rw [divUniversalHighWindowUnitRead_pow]
      _ = 0 := hkill_read readSide
  have hthetaY :
      (divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + q + 1))
          (divUniversalHighWindowShiftedRelationTransitionOfLE (C := C)
            (pi := pi) hpi g r1 r2 b1 b2 i j transitionSide n (n + q) h x) = 0 := by
    refine relThetaSections_eq_zero_of_both_side_reads C RZ pi _ _ ?_ ?_
    · change (CR (n + q + 1) false)
        (divUniversalHighWindowShiftedRelationTransitionOfLE (C := C)
          (pi := pi) hpi g r1 r2 b1 b2 i j transitionSide n (n + q) h x) = 0
      exact hzero_read false
    · change (CR (n + q + 1) true)
        (divUniversalHighWindowShiftedRelationTransitionOfLE (C := C)
          (pi := pi) hpi g r1 r2 b1 b2 i j transitionSide n (n + q) h x) = 0
      exact hzero_read true
  refine ⟨n + q, h, ?_⟩
  apply (divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j (n + q + 1)).injective
  simpa using hthetaY

set_option maxHeartbeats 1600000 in
-- The wrapper re-elaborates the dependent transition witness and relation stage.
set_option synthInstance.maxHeartbeats 800000 in
-- Relation membership at the existential target requires the full shifted module graph.
/-- The zero-killing theorem gives the eventual relation-membership statement
used by the varying-ambient saturation criterion. -/
theorem exists_divUniversalHighWindowShiftedRelationTransitionOfLE_mem_relation_of_chartRead_eq_zero
    (hb : 0 < windowBound pi hpi) (transitionSide : Bool) (n : Nat)
    (x : G(n + 1))
    (hx : (CR (n + 1) transitionSide) x = 0) :
    ∃ m : Nat, ∃ h : n ≤ m,
      divUniversalHighWindowShiftedRelationTransitionOfLE (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j transitionSide n m h x ∈
      divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (m + 1) := by
  obtain ⟨m, h, hm⟩ :=
    exists_divUniversalHighWindowShiftedRelationTransitionOfLE_eq_zero_of_chartRead_eq_zero
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hb transitionSide n x hx
  refine ⟨m, h, ?_⟩
  rw [hm]
  exact Submodule.zero_mem _

end HighWindowTransitionKernelKill

end AlgebraicGeometry
