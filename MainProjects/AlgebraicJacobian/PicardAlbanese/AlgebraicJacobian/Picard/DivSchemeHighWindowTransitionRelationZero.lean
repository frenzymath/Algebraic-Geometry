/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowTransitionRelation

/-!
# Stage-zero compatibility for high-window transitions

This file supplies the initial step omitted by the recursive successor theorem:
multiplication by any base-field section of the multiplier window sends the
transported first universal window into the transported universal multiplication
span at stage one.
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

section HighWindowTransitionRelationZero

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowTransitionRelationZero :
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
local notation "HS" => ↥(Scheme.divisorSections k
  (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)
local notation "HM" => ↥(Scheme.divisorSections k
  (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤)

set_option maxHeartbeats 500000 in
-- Reducing the stage-zero reindexing traverses a dependent divisor-section subtype.
private theorem coe_divUniversalHighWindowZeroEquiv (x : HM) :
    (((divUniversalHighWindowZeroEquiv (C := C) (pi := pi) hpi g).toLinearMap x :
      divUniversalHighWindowSections (C := C) (pi := pi) hpi g 0) :
      C.left.functionField) = (x : C.left.functionField) := by
  rw [divUniversalHighWindowZeroEquiv, LinearEquiv.coe_coe,
    LinearEquiv.coe_ofEq_apply]

set_option maxHeartbeats 500000 in
-- Reducing the stage-one reindexing traverses its dependent divisor-section subtype.
private theorem coe_divUniversalHighWindowOneEquiv
    (x : ↥(Scheme.divisorSections k
      ((windowM_choice pi hpi g + windowS_choice pi hpi g) •
        fiberWeilDivisor pi) ⊤)) :
    (((divUniversalHighWindowOneEquiv (C := C) (pi := pi) hpi g).toLinearMap x :
      divUniversalHighWindowSections (C := C) (pi := pi) hpi g 1) :
      C.left.functionField) = (x : C.left.functionField) := by
  rw [divUniversalHighWindowOneEquiv, LinearEquiv.coe_coe,
    LinearEquiv.coe_ofEq_apply]

set_option maxHeartbeats 500000 in
-- The shifted seed product has the expected underlying function-field value.
private theorem coe_windowShiftMul_zero (a : HS) (x : HM) :
    ((windowShiftMul hpi g a x : ↥(Scheme.divisorSections k
      ((windowM_choice pi hpi g + windowS_choice pi hpi g) •
        fiberWeilDivisor pi) ⊤)) : C.left.functionField) =
      (a : C.left.functionField) * (x : C.left.functionField) := by
  rw [windowShiftMul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_ofEq_apply, sectionMulBilin_apply_coe]

set_option maxHeartbeats 500000 in
-- The two seed-window reindexings carry the same product in the function field.
private theorem divUniversalHighWindowShiftMul_zero_comp_zeroEquiv
    (a : HS) :
    (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g 0 a).comp
        (divUniversalHighWindowZeroEquiv (C := C) (pi := pi) hpi g).toLinearMap =
      (divUniversalHighWindowOneEquiv (C := C) (pi := pi) hpi g).toLinearMap.comp
        (windowShiftMul hpi g a) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply]
  rw [coe_divUniversalHighWindowShiftMul,
    coe_divUniversalHighWindowZeroEquiv,
    coe_divUniversalHighWindowOneEquiv, coe_windowShiftMul_zero]

set_option maxHeartbeats 500000 in
-- Base change preserves the seed-window multiplication square.
private theorem divUniversalHighWindowBaseChangeShiftMul_zero_zeroEquiv
    (a : HS) (x : RZ ⊗[k] HM) :
    (LinearMap.baseChange RZ
      (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g 0 a))
        (LinearMap.baseChange RZ
          (divUniversalHighWindowZeroEquiv (C := C) (pi := pi) hpi g).toLinearMap x) =
      (LinearMap.baseChange RZ
        (divUniversalHighWindowOneEquiv (C := C) (pi := pi) hpi g).toLinearMap)
        (LinearMap.baseChange RZ (windowShiftMul hpi g a) x) := by
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using
    congrArg (fun f => (LinearMap.baseChange RZ f) x)
      (divUniversalHighWindowShiftMul_zero_comp_zeroEquiv
        (C := C) (pi := pi) hpi g a)

set_option maxHeartbeats 1600000 in
-- Associating the first-window inclusion with each finite projection is expensive.
set_option synthInstance.maxHeartbeats 400000 in
-- The finite function source uses the dependent carve-chart tensor module.
/-- The seed universal multiplication map is its finite component sum. -/
private theorem universalMulMap_eq_finiteComponentSum :
    universalMulMap (hπ := hpi) g r1 r2 b1 b2 i j =
      finiteComponentSum (fun t =>
        (LinearMap.baseChange RZ
          (windowShiftMul hpi g ((Module.finBasis k HS) t))).comp
            (divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule.subtype) := by
  classical
  simp only [universalMulMap, finiteComponentSum, LinearMap.comp_assoc]

set_option maxHeartbeats 1600000 in
-- Evaluating the dependent universal map first requires its component-sum normal form.
set_option synthInstance.maxHeartbeats 400000 in
-- The supported source uses the finite function module over the carve chart.
private theorem universalMulMap_piSingle
    (t : Fin (Module.finrank k HS))
    (x : ↥(divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule) :
    universalMulMap (hπ := hpi) g r1 r2 b1 b2 i j (Pi.single t x) =
      LinearMap.baseChange RZ
        (windowShiftMul hpi g ((Module.finBasis k HS) t)) x.1 := by
  classical
  rw [universalMulMap_eq_finiteComponentSum
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j,
    finiteComponentSum_piSingle]
  rfl

set_option maxHeartbeats 1600000 in
-- A single basis product is one coordinate of the universal multiplication map.
set_option synthInstance.maxHeartbeats 400000 in
-- Constructing the supported finite source requires the carve-chart module instance.
private theorem baseChange_windowShiftMul_finBasis_mem_universalMulSpan
    (t : Fin (Module.finrank k HS))
    (x : ↥(divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule) :
    LinearMap.baseChange RZ
        (windowShiftMul hpi g ((Module.finBasis k HS) t)) x.1 ∈
      universalMulSpan (hπ := hpi) g r1 r2 b1 b2 i j := by
  classical
  exact ⟨Pi.single t x, universalMulMap_piSingle
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j t x⟩

set_option maxHeartbeats 1600000 in
-- One relation coordinate traverses both transported seed-window submodules.
private theorem baseChange_highWindowShiftMul_finBasis_relation_zero_mem_one
    (t : Fin (Module.finrank k HS))
    (z : ↥(divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j 0)) :
    LinearMap.baseChange RZ
        (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g 0
          ((Module.finBasis k HS) t)) z.1 ∈
      divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1 := by
  rw [divUniversalHighWindowRelation_one_transport]
  let y : divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
      (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) 0 := z
  have hy : y ∈ divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j 0 := z.2
  have hy' : y ∈ Submodule.map
      (LinearMap.baseChange RZ
        (divUniversalHighWindowZeroEquiv (C := C) (pi := pi) hpi g).toLinearMap)
      (divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule := by
    rw [← divUniversalHighWindowRelation_zero_eq_firstWindow
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j]
    exact hy
  rcases hy' with ⟨x, hx, hxv⟩
  let x' : ↥(divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule :=
    ⟨x, hx⟩
  refine ⟨LinearMap.baseChange RZ
      (windowShiftMul hpi g ((Module.finBasis k HS) t)) x,
    baseChange_windowShiftMul_finBasis_mem_universalMulSpan
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j t x', ?_⟩
  change _ = LinearMap.baseChange RZ
    (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g 0
      ((Module.finBasis k HS) t)) y
  rw [← hxv]
  exact (divUniversalHighWindowBaseChangeShiftMul_zero_zeroEquiv
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
      ((Module.finBasis k HS) t) x).symm

set_option maxHeartbeats 1600000 in
-- The generic stage-zero span is transported from the seed multiplication span.
private theorem divUniversalHighWindowMulSpan_zero_relation_le_one :
    divUniversalHighWindowMulSpan (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 0
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j 0) ≤
      divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1 := by
  classical
  rintro _ ⟨v, rfl⟩
  rw [divUniversalHighWindowMulMap, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro t ht
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  exact baseChange_highWindowShiftMul_finBasis_relation_zero_mem_one
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j t (v t)

set_option maxHeartbeats 1600000 in
-- Unfolding both transported seed stages is definitionally expensive.
/-- Multiplication by any base-field multiplier preserves the relation tower at
its initial transition. -/
theorem map_divUniversalHighWindowBaseMultiplierTransition_relation_zero_le
    (a : HS) :
    Submodule.map
        (divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j 0 a)
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j 0) ≤
      divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1 :=
  (map_divUniversalHighWindowBaseMultiplierTransition_le_mulSpan
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j 0
      (divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 0) a).trans
    (divUniversalHighWindowMulSpan_zero_relation_le_one
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j)

set_option maxHeartbeats 1600000 in
-- The zero branch unfolds the transported seed multiplication span.
/-- Multiplication by any base-field multiplier preserves the recursive
high-window relation tower at every stage. -/
theorem map_divUniversalHighWindowBaseMultiplierTransition_relation_le
    (n : Nat) (a : HS) :
    Submodule.map
        (divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n a)
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n) ≤
      divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) := by
  cases n with
  | zero =>
      exact map_divUniversalHighWindowBaseMultiplierTransition_relation_zero_le
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j a
  | succ n =>
      exact map_divUniversalHighWindowBaseMultiplierTransition_relation_succ_le
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n a

end HighWindowTransitionRelationZero

end AlgebraicGeometry
