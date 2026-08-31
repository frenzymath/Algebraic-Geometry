/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowTransitionRelation

/-!
# Quotient and colimit interfaces for high-window transitions

This module packages the shifted relation system into quotient and colimit
interfaces, together with the stabilized pinned-chart reading ideals.
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

section HighWindowTransitionQuotient

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowTransitionQuotient :
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


set_option maxHeartbeats 1600000 in
-- The quotient map specializes the dependent shifted ambient at both endpoints.
set_option synthInstance.maxHeartbeats 1200000 in
-- Compatibility transports the recursive relation through the quotient.
/-- The quotient transition on the shifted recursive relation family. -/
noncomputable def divUniversalHighWindowShiftedRelationQuotientTransition
    (side : Bool) (n m : Nat) (h : n ≤ m) :
    ((G(n + 1)) ⧸ divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1)) →ₗ[RZ]
    ((G(m + 1)) ⧸ divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (m + 1)) :=
  Submodule.directedQuotientMapOfCompatible
    (f := divUniversalHighWindowShiftedRelationTransitionOfLE
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side)
    (K := fun q => divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (q + 1))
    (hK := fun q r hr =>
      map_divUniversalHighWindowShiftedRelationTransitionOfLE_relation_le
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side q r hr)
    n m h

set_option maxHeartbeats 1600000 in
-- Quotient evaluation unfolds compatibility at both dependent endpoints.
set_option synthInstance.maxHeartbeats 1200000 in
-- The quotient-map simplification requires both shifted relation instances.
@[simp]
theorem divUniversalHighWindowShiftedRelationQuotientTransition_mk
    (side : Bool) (n m : Nat) (h : n ≤ m) (x : G(n + 1)) :
    divUniversalHighWindowShiftedRelationQuotientTransition
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n m h
      (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (divUniversalHighWindowShiftedRelationTransitionOfLE
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n m h x) := by
  rw [divUniversalHighWindowShiftedRelationQuotientTransition,
    Submodule.directedQuotientMapOfCompatible_mk]

/-- The shifted high-window ambients still exhaust either pinned chart: shift an
arbitrary exhaustion witness once using the read-invariant relation transition. -/
theorem exists_divUniversalHighWindowShiftedChartRead_eq
    (hb : 0 < windowBound pi hpi) (side : Bool)
    (x : Γ(relCurve C RZ, relPinnedChart C RZ pi side)) :
    ∃ n : Nat, ∃ y : G(n + 1),
      divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side y = x := by
  obtain ⟨n, y, hy⟩ := exists_divUniversalHighWindowChartRead_eq
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hb side x
  refine ⟨n, divUniversalHighWindowRelationTransition (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j side n y, ?_⟩
  rw [divUniversalHighWindowRelationTransition_chartRead, hy]

/-! ## Conditional shifted colimit interface -/

set_option maxHeartbeats 4800000 in
-- The generic varying-ambient colimit theorem re-elaborates all dependent stages.
set_option synthInstance.maxHeartbeats 1200000 in
-- The direct-limit family carries a dependent module instance at every stage.
/-- The shifted quotient colimit is flat once the finite-stage quotients are flat
and the explicit read-kernel saturation condition is supplied. -/
theorem flat_shifted_highWindow_relation_quotient_of_saturation
    {B : Type u} [CommRing B] [Algebra RZ B]
    (side : Bool)
    (read : ∀ n, (G(n + 1)) →ₗ[RZ] B) (J : Ideal B)
    (hreadK : ∀ n,
      divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1) ≤
        LinearMap.ker
          ((Ideal.Quotient.mkₐ RZ J).toLinearMap.comp (read n)))
    (hread : ∀ n m (h : n ≤ m) (x : G(n + 1)),
      read m
          (divUniversalHighWindowShiftedRelationTransitionOfLE
            (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n m h x) =
        read n x)
    (hcover : ∀ b : B, ∃ n : Nat, ∃ x : G(n + 1), read n x = b)
    (hsaturation : ∀ n (x : G(n + 1)), read n x ∈ J →
      ∃ m : Nat, ∃ h : n ≤ m,
        divUniversalHighWindowShiftedRelationTransitionOfLE
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n m h x ∈
        divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (m + 1))
    [∀ n, Module.Flat RZ
      ((G(n + 1)) ⧸ divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1))] :
    Module.Flat RZ (B ⧸ J) := by
  exact Submodule.flat_quotient_of_directLimit
    (f := divUniversalHighWindowShiftedRelationTransitionOfLE
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side)
    (K := fun n => divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1))
    (hK := fun n m h =>
      map_divUniversalHighWindowShiftedRelationTransitionOfLE_relation_le
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n m h)
    read J hreadK hread hcover hsaturation

/-- All shifted relation stages have the same pinned-chart reading ideal as
stage one. -/
theorem divUniversalHighWindowRelationReadIdeal_shifted_eq
    (side : Bool) (n : Nat) :
    divUniversalHighWindowRelationReadIdeal (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side =
      divUniversalHighWindowRelationReadIdeal (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1 side := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n.succ + 1 = n + 2 by omega,
        divUniversalHighWindowRelationReadIdeal_succ_succ_eq
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n side, ih]

set_option maxHeartbeats 4800000 in
-- The shifted section-to-ideal map unfolds the dependent relation subtype.
set_option synthInstance.maxHeartbeats 1200000 in
-- The chart-read ideal carries the full carve-chart instance graph.
/-- Every shifted relation section reads into the fixed stage-one chart ideal. -/
theorem divUniversalHighWindowShiftedRelation_read_mem_stageOneIdeal
    (side : Bool) (n : Nat)
    (x : G(n + 1))
    (hx : x ∈ divUniversalHighWindowRelation (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1)) :
    divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side x ∈
      divUniversalHighWindowRelationReadIdeal (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j 1 side := by
  have hmem : divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side x ∈
      divUniversalHighWindowRelationReadIdeal (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side := by
    rw [divUniversalHighWindowRelationReadIdeal_eq_submodule]
    exact Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩
  rw [divUniversalHighWindowRelationReadIdeal_shifted_eq
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n] at hmem
  exact hmem

set_option maxHeartbeats 4800000 in
-- The kernel inclusion traverses the stage-one ideal and quotient map.
set_option synthInstance.maxHeartbeats 1200000 in
-- The dependent chart map and relation subtype require extended synthesis.
/-- The concrete kernel hypothesis for the fixed stage-one chart ideal. -/
theorem divUniversalHighWindowShiftedRelation_read_ker_stageOneIdeal
    (side : Bool) (n : Nat) :
    divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) ≤
      LinearMap.ker
        ((Ideal.Quotient.mkₐ RZ
          (divUniversalHighWindowRelationReadIdeal (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j 1 side)).toLinearMap.comp
          (divUniversalHighWindowChartRead (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j (n + 1) side)) := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact divUniversalHighWindowShiftedRelation_read_mem_stageOneIdeal
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n x hx

set_option maxHeartbeats 4800000 in
-- The concrete chart specialization re-elaborates the dependent stage family.
set_option synthInstance.maxHeartbeats 1200000 in
-- The chart quotient combines the stabilized reading ideal with direct-limit flatness.
/-- Concrete chart form: after stage-one shifting, only bounded-stage flatness
and eventual saturation remain in the colimit flatness criterion. -/
theorem flat_shifted_highWindow_chart_quotient_of_saturation
    (hb : 0 < windowBound pi hpi) (side : Bool)
    (hsaturation : ∀ n (x : G(n + 1)),
      divUniversalHighWindowChartRead (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1) side x ∈
        divUniversalHighWindowRelationReadIdeal (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j 1 side →
      ∃ m : Nat, ∃ h : n ≤ m,
        divUniversalHighWindowShiftedRelationTransitionOfLE
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n m h x ∈
        divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (m + 1))
    [∀ n, Module.Flat RZ
      ((G(n + 1)) ⧸ divUniversalHighWindowRelation (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1))] :
    Module.Flat RZ
      (Γ(relCurve C RZ, relPinnedChart C RZ pi side) ⧸
        divUniversalHighWindowRelationReadIdeal (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j 1 side) := by
  apply flat_shifted_highWindow_relation_quotient_of_saturation
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side
    (read := fun n => divUniversalHighWindowChartRead (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) side)
    (J := divUniversalHighWindowRelationReadIdeal (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j 1 side)
    (hreadK := fun n => divUniversalHighWindowShiftedRelation_read_ker_stageOneIdeal
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n)
    (hread := fun n m h x =>
      divUniversalHighWindowShiftedRelationTransitionOfLE_chartRead
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side n m h x)
    (hcover := by
      intro b
      obtain ⟨n, x, hx⟩ := exists_divUniversalHighWindowShiftedChartRead_eq
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hb side b
      exact ⟨n, x, hx⟩)
    hsaturation

end HighWindowTransitionQuotient

end AlgebraicGeometry
