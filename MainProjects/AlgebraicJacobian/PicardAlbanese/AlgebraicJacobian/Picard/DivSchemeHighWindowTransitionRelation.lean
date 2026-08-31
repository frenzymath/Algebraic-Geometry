/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowTransitions
import AlgebraicJacobian.Picard.DivSchemeHighWindowRelationReadSuccessor

/-!
# Relation compatibility for high-window transitions

The recursive successor relation is the range of multiplication by a finite
basis of the multiplier window.  Consequently multiplication by every
base-field multiplier sends an arbitrary relation submodule into that successor:
expand the multiplier in the finite basis and use the corresponding coordinate
of `DivUniversalHighWindowMulSource`.

This is a genuine submodule inclusion over the nonreduced carve-chart ring.  It
does not use residue fibres or a saturation hypothesis.
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

section HighWindowTransitionRelation

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowTransitionRelation :
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
local notation "H" n => divUniversalHighWindowSections
  (C := C) (pi := pi) hpi g n
local notation "G" n => divUniversalHighWindowAmbient (C := C) (pi := pi)
  (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
  (i := i) (j := j) n

/-- Multiplication into the next high window, linear in the multiplier. -/
noncomputable def divUniversalHighWindowShiftMulLinear (n : Nat) :
    HS →ₗ[k] ((H n) →ₗ[k] (H (n + 1))) :=
  (LinearMap.llcomp k _ _ _
    (divUniversalHighWindowSuccEquiv (C := C) (pi := pi) hpi g n).toLinearMap).comp
      (sectionMulBilin k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n •
          fiberWeilDivisor pi))

@[simp]
theorem divUniversalHighWindowShiftMulLinear_apply (n : Nat) (a : HS) :
    divUniversalHighWindowShiftMulLinear (C := C) (pi := pi) hpi g n a =
      divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n a := rfl

set_option maxHeartbeats 1600000 in
-- Base change over the dependent high-window ambient needs extended reduction.
set_option synthInstance.maxHeartbeats 1200000 in
-- The base-change typeclass graph is dependent on both window stages.
/-- The scalar-extended transition attached to a base-field multiplier. -/
noncomputable def divUniversalHighWindowBaseMultiplierTransition
    (n : Nat) (a : HS) : (G n) →ₗ[RZ] (G (n + 1)) :=
  LinearMap.baseChange RZ
    (divUniversalHighWindowShiftMulLinear (C := C) (pi := pi) hpi g n a)

set_option maxHeartbeats 4800000 in
-- The tensor-lifted multiplier carries both dependent high-window stages.
set_option synthInstance.maxHeartbeats 1200000 in
-- The lift also re-elaborates the base-change homomorphism.
/-- Multiplication by an arbitrary scalar-extended multiplier, linear in that
multiplier. -/
noncomputable def divUniversalHighWindowTensorMultiplierTransition (n : Nat) :
    (RZ ⊗[k] HS) →ₗ[RZ] ((G n) →ₗ[RZ] (G (n + 1))) :=
  LinearMap.liftBaseChange RZ
    ((LinearMap.baseChangeHom k RZ (H n) (H (n + 1))).comp
      (divUniversalHighWindowShiftMulLinear (C := C) (pi := pi) hpi g n))

set_option maxHeartbeats 4800000 in
-- Tensor scalar-action reduction traverses both dependent stages.
set_option synthInstance.maxHeartbeats 1200000 in
-- Tensor scalar-action inference traverses the dependent ambient modules.
@[simp]
theorem divUniversalHighWindowTensorMultiplierTransition_tmul
    (n : Nat) (r : RZ) (a : HS) :
    divUniversalHighWindowTensorMultiplierTransition (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n (r ⊗ₜ a) =
      r • divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n a := by
  rw [divUniversalHighWindowTensorMultiplierTransition,
    LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
    LinearMap.baseChangeHom_apply,
    divUniversalHighWindowBaseMultiplierTransition]

set_option maxHeartbeats 4800000 in
-- The finite dependent source and high-window ambient require extended reduction.
set_option synthInstance.maxHeartbeats 1200000 in
-- Basis coordinates require dependent module and zero-map instances.
/-- A transition by one multiplier-basis vector lands in the finite successor span. -/
theorem divUniversalHighWindowBaseMultiplierTransition_finBasis_mem_mulSpan
    (n : Nat) (K : Submodule RZ (G n))
    (t : Fin (Module.finrank k HS)) (x : G n) (hx : x ∈ K) :
    divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n ((Module.finBasis k HS) t) x ∈
      divUniversalHighWindowMulSpan (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K := by
  classical
  let xt : K := ⟨x, hx⟩
  refine ⟨Pi.single t xt, ?_⟩
  rw [divUniversalHighWindowMulMap, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single t]
  · rw [Pi.single_eq_same]
    rfl
  · intro s _ hst
    rw [Pi.single_eq_of_ne hst, map_zero]
    exact (LinearMap.baseChange RZ
      (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n
        ((Module.finBasis k HS) s))).map_zero
  · intro ht
    exact (ht (Finset.mem_univ t)).elim

set_option maxHeartbeats 4800000 in
-- Basis expansion traverses scalar extension of a dependent family of linear maps.
set_option synthInstance.maxHeartbeats 1200000 in
-- The composite base-change map elaborates the full dependent ambient family.
/-- Every base-field multiplier transition lands in the finite successor span. -/
theorem divUniversalHighWindowBaseMultiplierTransition_mem_mulSpan
    (n : Nat) (K : Submodule RZ (G n)) (a : HS)
    (x : G n) (hx : x ∈ K) :
    divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n a x ∈
      divUniversalHighWindowMulSpan (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K := by
  classical
  let basis := Module.finBasis k HS
  have ha : a = ∑ t, (basis.repr a t) • basis t := (basis.sum_repr a).symm
  have htransition :
      divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n a x =
        ∑ t, (basis.repr a t) •
          divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n (basis t) x := by
    let T : HS →ₗ[k] ((G n) →ₗ[RZ] (G (n + 1))) :=
      (LinearMap.baseChangeHom k RZ (H n) (H (n + 1))).comp
        (divUniversalHighWindowShiftMulLinear (C := C) (pi := pi) hpi g n)
    change
      (T a) x =
        ∑ t, (basis.repr a t) •
          (T (basis t)) x
    conv_lhs => rw [ha]
    rw [map_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    rw [map_smul, LinearMap.smul_apply]
  rw [htransition]
  apply Submodule.sum_mem
  intro t _
  rw [← IsScalarTower.algebraMap_smul RZ (basis.repr a t)]
  exact (divUniversalHighWindowMulSpan (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j n K).smul_mem _
      (divUniversalHighWindowBaseMultiplierTransition_finBasis_mem_mulSpan
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K t x hx)

set_option maxHeartbeats 1600000 in
-- Tensor induction elaborates the dependent transition codomain at every constructor.
set_option synthInstance.maxHeartbeats 1200000 in
-- Tensor induction also resolves scalar and zero-map instances at each branch.
/-- Every scalar-extended multiplier transition lands in the finite successor span. -/
theorem divUniversalHighWindowTensorMultiplierTransition_mem_mulSpan
    (n : Nat) (K : Submodule RZ (G n)) (z : RZ ⊗[k] HS)
    (x : G n) (hx : x ∈ K) :
    divUniversalHighWindowTensorMultiplierTransition (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n z x ∈
      divUniversalHighWindowMulSpan (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K := by
  induction z with
  | zero =>
      rw [map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
  | add z w hz hw =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hz hw
  | tmul r a =>
      rw [divUniversalHighWindowTensorMultiplierTransition_tmul,
        LinearMap.smul_apply]
      exact (divUniversalHighWindowMulSpan (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K).smul_mem r
          (divUniversalHighWindowBaseMultiplierTransition_mem_mulSpan
            (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K a x hx)

set_option maxHeartbeats 4800000 in
-- The chart-reading formula traverses three relative theta-window dictionaries.
set_option synthInstance.maxHeartbeats 1200000 in
/-- Reading multiplication by an arbitrary scalar-extended multiplier is the
product of its multiplier-window reading and the predecessor reading. -/
theorem divUniversalHighWindowTensorMultiplierTransition_chartRead
    (n : Nat) (side : Bool) (z : RZ ⊗[k] HS) (x : G n) :
    divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side
        (divUniversalHighWindowTensorMultiplierTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n z x) =
      relThetaResSide (windowS_choice pi hpi g) side le_rfl
          (relThetaWindowEquiv C RZ pi (windowS_choice pi hpi g)
            (relThetaPairH1_windowS C hpi g) z) *
        divUniversalHighWindowChartRead (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n side x := by
  induction z with
  | zero => simp
  | add z w hz hw =>
      simp only [map_add, LinearMap.add_apply, hz, hw, add_mul]
  | tmul r a =>
      rw [divUniversalHighWindowTensorMultiplierTransition_tmul,
        LinearMap.smul_apply, map_smul,
        divUniversalHighWindowBaseMultiplierTransition,
        divUniversalHighWindowShiftMulLinear_apply,
        divUniversalHighWindowShiftMul_chartRead]
      have htmul : (r ⊗ₜ a : RZ ⊗[k] HS) = r • ((1 : RZ) ⊗ₜ a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [htmul, map_smul, map_smul,
        divUniversalHighWindowMultiplierChartRead]
      rw [Scheme.overModule_smul_def, Scheme.overModule_smul_def]
      ring

/-- The tensor multiplier corresponding, through the multiplier-window theta
equivalence, to the canonical section whose selected-side reading is `1`. -/
noncomputable def divUniversalHighWindowSideMultiplierTensor (side : Bool) :
    RZ ⊗[k] HS :=
  (relThetaWindowEquiv C RZ pi (windowS_choice pi hpi g)
    (relThetaPairH1_windowS C hpi g)).symm
      (relThetaSideUnitSection C RZ pi side (windowS_choice pi hpi g))

@[simp]
theorem divUniversalHighWindowSideMultiplierTensor_theta (side : Bool) :
    relThetaWindowEquiv C RZ pi (windowS_choice pi hpi g)
        (relThetaPairH1_windowS C hpi g)
        (divUniversalHighWindowSideMultiplierTensor (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j side) =
      relThetaSideUnitSection C RZ pi side (windowS_choice pi hpi g) := by
  exact LinearEquiv.apply_symm_apply _ _

/-- The relation-compatible selected-side successor transition. -/
noncomputable def divUniversalHighWindowRelationTransition
    (side : Bool) (n : Nat) : (G n) →ₗ[RZ] (G (n + 1)) :=
  divUniversalHighWindowTensorMultiplierTransition (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j n
      (divUniversalHighWindowSideMultiplierTensor (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j side)

set_option maxHeartbeats 1600000 in
-- The concrete side transition unfolds the dependent tensor chart formula.
set_option synthInstance.maxHeartbeats 1200000 in
-- The side-unit theta equivalence drives a large instance graph.
@[simp]
theorem divUniversalHighWindowRelationTransition_chartRead
    (side : Bool) (n : Nat) (x : G n) :
    divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side
        (divUniversalHighWindowRelationTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j side n x) =
      divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n side x := by
  rw [divUniversalHighWindowRelationTransition,
    divUniversalHighWindowTensorMultiplierTransition_chartRead,
    divUniversalHighWindowSideMultiplierTensor_theta,
    relThetaResSide_relThetaSideUnit, one_mul]

/-- Uniform submodule form of base-field multiplier compatibility. -/
theorem map_divUniversalHighWindowBaseMultiplierTransition_le_mulSpan
    (n : Nat) (K : Submodule RZ (G n)) (a : HS) :
    Submodule.map
        (divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n a) K ≤
      divUniversalHighWindowMulSpan (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K := by
  rintro _ ⟨x, hx, rfl⟩
  exact divUniversalHighWindowBaseMultiplierTransition_mem_mulSpan
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K a x hx

/-- Uniform submodule form of scalar-extended multiplier compatibility. -/
theorem map_divUniversalHighWindowTensorMultiplierTransition_le_mulSpan
    (n : Nat) (K : Submodule RZ (G n)) (z : RZ ⊗[k] HS) :
    Submodule.map
        (divUniversalHighWindowTensorMultiplierTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n z) K ≤
      divUniversalHighWindowMulSpan (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K := by
  rintro _ ⟨x, hx, rfl⟩
  exact divUniversalHighWindowTensorMultiplierTransition_mem_mulSpan
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K z x hx

set_option maxHeartbeats 1600000 in
-- Rewriting the recursive dependent relation at `n+2` needs extended reduction.
/-- From stage one onward, every base-field multiplier transition preserves the
recursive relation tower. -/
theorem map_divUniversalHighWindowBaseMultiplierTransition_relation_succ_le
    (n : Nat) (a : HS) :
    Submodule.map
        (divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1) a)
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1)) ≤
      divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 2) := by
  rw [divUniversalHighWindowRelation_succ_succ]
  exact map_divUniversalHighWindowBaseMultiplierTransition_le_mulSpan
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1)
      (divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1)) a

set_option maxHeartbeats 1600000 in
-- Rewriting the recursive dependent relation at `n+2` needs extended reduction.
/-- From stage one onward, every scalar-extended multiplier transition preserves
the recursive relation tower. -/
theorem map_divUniversalHighWindowTensorMultiplierTransition_relation_succ_le
    (n : Nat) (z : RZ ⊗[k] HS) :
    Submodule.map
        (divUniversalHighWindowTensorMultiplierTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1) z)
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1)) ≤
      divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 2) := by
  rw [divUniversalHighWindowRelation_succ_succ]
  exact map_divUniversalHighWindowTensorMultiplierTransition_le_mulSpan
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1)
      (divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1)) z

set_option maxHeartbeats 1600000 in
-- The selected-side tensor retains the full dependent multiplier dictionary.
/-- From stage one onward, the selected-side relation transition preserves the
recursive relation tower. -/
theorem map_divUniversalHighWindowRelationTransition_relation_succ_le
    (n : Nat) (side : Bool) :
    Submodule.map
        (divUniversalHighWindowRelationTransition (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j side (n + 1))
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1)) ≤
      divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 2) := by
  exact map_divUniversalHighWindowTensorMultiplierTransition_relation_succ_le
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n
      (divUniversalHighWindowSideMultiplierTensor (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j side)

/-! ## The shifted relation-preserving directed system -/

set_option maxHeartbeats 1600000 in
-- Reindexing the shifted dependent ambient needs extended definitional reduction.
set_option synthInstance.maxHeartbeats 1200000 in
-- The generic transition kit specializes through the full high-window family.
/-- Arbitrary comparable-index transition on the shifted family `G'(n)=G(n+1)`. -/
noncomputable def divUniversalHighWindowShiftedRelationTransitionOfLE
    (side : Bool) (n m : Nat) (h : n ≤ m) :
      (G (n + 1)) →ₗ[RZ] (G (m + 1)) :=
  HighWindowTransitionKit.transitionOfLE
    (fun q => G (q + 1))
    (fun q => divUniversalHighWindowRelationTransition (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j side (q + 1)) n m h

set_option maxHeartbeats 1600000 in
-- The directed-system instance re-elaborates the shifted dependent family.
set_option synthInstance.maxHeartbeats 1200000 in
-- The generic coherence proof traverses all successor maps.
noncomputable instance directedSystem_divUniversalHighWindowShiftedRelationTransition
    (side : Bool) :
    DirectedSystem (fun n => G (n + 1))
      (divUniversalHighWindowShiftedRelationTransitionOfLE
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side · · ·) :=
  HighWindowTransitionKit.directedSystem_transitionOfLE
    (fun q => G (q + 1))
    (fun q => divUniversalHighWindowRelationTransition (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j side (q + 1))

set_option maxHeartbeats 1600000 in
-- Read invariance specializes the iterated transition to dependent chart maps.
set_option synthInstance.maxHeartbeats 1200000 in
-- Every shifted stage carries the full carve-chart module graph.
/-- The shifted arbitrary-index transition preserves pinned-chart readings. -/
@[simp]
theorem divUniversalHighWindowShiftedRelationTransitionOfLE_chartRead
    (side : Bool) (n m : Nat) (h : n ≤ m) (x : G(n + 1)) :
    divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (m + 1) side
        (divUniversalHighWindowShiftedRelationTransitionOfLE
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n m h x) =
      divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side x := by
  exact HighWindowTransitionKit.transitionOfLE_read
    (fun q => G (q + 1))
    (fun q => divUniversalHighWindowRelationTransition (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j side (q + 1))
    (fun q => divUniversalHighWindowChartRead (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (q + 1) side)
    (fun q y => divUniversalHighWindowRelationTransition_chartRead
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side (q + 1) y)
    n m h x

set_option maxHeartbeats 1600000 in
-- Relation preservation elaborates the dependent submodule family at each stage.
set_option synthInstance.maxHeartbeats 1200000 in
-- The generic transition lemma resolves the shifted module instances repeatedly.
/-- The shifted arbitrary-index transition preserves the recursive relation modules. -/
theorem map_divUniversalHighWindowShiftedRelationTransitionOfLE_relation_le
    (side : Bool) (n m : Nat) (h : n ≤ m) :
    Submodule.map
        (divUniversalHighWindowShiftedRelationTransitionOfLE
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n m h)
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1)) ≤
      divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (m + 1) := by
  exact HighWindowTransitionKit.map_transitionOfLE_le
    (fun q => G (q + 1))
    (fun q => divUniversalHighWindowRelationTransition (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j side (q + 1))
    (fun q => divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (q + 1))
    (fun q y hy => map_divUniversalHighWindowRelationTransition_relation_succ_le
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j q side ⟨y, hy, rfl⟩)
    n m h

end HighWindowTransitionRelation

end AlgebraicGeometry
