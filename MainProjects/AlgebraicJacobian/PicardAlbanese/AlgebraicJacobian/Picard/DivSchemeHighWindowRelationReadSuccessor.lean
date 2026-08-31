/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowRelationRead

/-!
# Successor chart readings for high-window relation modules

This module contains the successor-reading compatibility layer.  The seed
anchors and their chart-ideal identifications remain in
`DivSchemeHighWindowRelationRead`; keeping this dependent multiplication layer
separate keeps the transition module's elaboration budget local.
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

section HighWindowRelationReadSuccessor

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowRelationReadSuccessor :
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

set_option maxHeartbeats 800000 in
-- The equality transport unfolds a relative theta equivalence on both sides.
set_option synthInstance.maxHeartbeats 400000 in
-- The arbitrary coefficient ring requires the full relative-curve instance chain.
/-- Reindexing a base-field section space does not change its pinned-chart reading. -/
theorem relThetaResSide_relThetaWindowEquiv_baseChange_ofEq
    {p q : Nat} (h : p = q)
    (hp : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi p)).H1)
    (hq : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi q)).H1)
    (R : Type u) [CommRing R] [Algebra k R] (side : Bool)
    (x : R ⊗[k] ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤)) :
    relThetaResSide q side le_rfl
        (relThetaWindowEquiv C R pi q hq
          (LinearMap.baseChange R
            (divisorWindowExponentEquiv (C := C) (pi := pi) h).toLinearMap x)) =
      relThetaResSide p side le_rfl
        (relThetaWindowEquiv C R pi p hp x) := by
  subst q
  have heq :
      (divisorWindowExponentEquiv (C := C) (pi := pi) (rfl : p = p)).toLinearMap =
        LinearMap.id := by
    apply LinearMap.ext
    intro y
    rfl
  rw [heq, LinearMap.baseChange_id, LinearMap.id_apply]

/-- The chart reading of a multiplier-window basis section. -/
noncomputable def divUniversalHighWindowMultiplierChartRead (side : Bool) (a : HS) :
    Γ(relCurve C RZ, relPinnedChart C RZ pi side) :=
  relThetaResSide (windowS_choice pi hpi g) side le_rfl
    (relThetaWindowEquiv C RZ pi (windowS_choice pi hpi g)
      (relThetaPairH1_windowS C hpi g) (1 ⊗ₜ a))

/-- The multiplier-window basis readings generate the unit ideal on either pinned chart. -/
theorem exists_divUniversalHighWindowMultiplierChartRead_mul_eq_one (side : Bool) :
    ∃ c : Fin (Module.finrank k HS) →
        Γ(relCurve C RZ, relPinnedChart C RZ pi side),
      ∑ t, c t * divUniversalHighWindowMultiplierChartRead
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side
          ((Module.finBasis k HS) t) = 1 := by
  simpa only [divUniversalHighWindowMultiplierChartRead,
    relThetaWindowChartRead, LinearMap.comp_apply, LinearEquiv.coe_coe] using
      (exists_basis_relThetaWindowChartRead_mul_eq_one C RZ pi
        (windowS_choice pi hpi g) (Module.finBasis k HS)
        (relThetaPairH1_windowS C hpi g) side)

set_option maxHeartbeats 4800000 in
-- Successor reading compatibility unfolds two high-window theta dictionaries.
set_option synthInstance.maxHeartbeats 1200000 in
-- The carve-chart ring and both dependent tensor ambients make instance search expensive.
/-- The generic multiplication theorem specializes to one high-window successor. -/
theorem divUniversalHighWindowShiftMul_chartRead
    (n : Nat) (side : Bool) (a : HS)
    (x : divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi)
      (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n) :
    divUniversalHighWindowChartRead (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
        (n + 1) side
        ((LinearMap.baseChange RZ
          (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n a)) x) =
      divUniversalHighWindowMultiplierChartRead (C := C) (pi := pi) hpi g r1 r2
          b1 b2 i j side a *
      divUniversalHighWindowChartRead (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
          n side x := by
  let hsum : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi
        (windowS_choice pi hpi g +
          divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n))).H1 := by
    rw [divUniversalHighWindowExponent_succ (C := C) (pi := pi) hpi g n]
    exact relThetaPairH1_windowM_add_mulS C pi hpi g (n + 1)
  change relThetaResSide
      (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g (n + 1))
      side le_rfl
      ((divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1))
        (LinearMap.baseChange RZ
          (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n a) x)) =
    relThetaResSide (windowS_choice pi hpi g) side le_rfl
        (relThetaWindowEquiv C RZ pi (windowS_choice pi hpi g)
          (relThetaPairH1_windowS C hpi g) (1 ⊗ₜ a)) *
      relThetaResSide
        (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n)
        side le_rfl
        ((divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n) x)
  rw [divUniversalHighWindowShiftMul_eq, LinearMap.baseChange_comp,
    LinearMap.comp_apply]
  calc
    _ = relThetaResSide
          (windowS_choice pi hpi g +
            divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n)
          side le_rfl
          (relThetaWindowEquiv C RZ pi
            (windowS_choice pi hpi g +
              divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n)
            hsum
            (LinearMap.baseChange RZ
              (thetaWindowMul (C := C) (pi := pi)
                (windowS_choice pi hpi g)
                (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) a) x)) := by
        simpa only [divUniversalHighWindowSuccExponentEquiv,
          divUniversalHighWindowThetaEquiv] using
          relThetaResSide_relThetaWindowEquiv_baseChange_ofEq
            (C := C) (pi := pi)
            (divUniversalHighWindowExponent_succ (C := C) (pi := pi) hpi g n)
            hsum (relThetaPairH1_windowM_add_mulS C pi hpi g (n + 1))
            RZ side
            (LinearMap.baseChange RZ
              (thetaWindowMul (C := C) (pi := pi)
                (windowS_choice pi hpi g)
                (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) a) x)
    _ = _ := by
      simpa only [divUniversalHighWindowThetaEquiv] using
        (relThetaResSide_relThetaWindowEquiv_thetaWindowMul
          C pi RZ
          (windowS_choice pi hpi g)
          (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) a
          (relThetaPairH1_windowS C hpi g)
          (relThetaPairH1_windowM_add_mulS C pi hpi g n)
          hsum side x)

set_option maxHeartbeats 1600000 in
-- Expanding the finite sum repeats the dependent successor-reading calculation.
set_option synthInstance.maxHeartbeats 600000 in
-- Each finite component carries the full high-window ambient instance chain.
/-- Reading the finite successor multiplication map is the expected finite sum of
multiplier readings times predecessor readings. -/
theorem divUniversalHighWindowMulMap_chartRead
    (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (side : Bool)
    (x : DivUniversalHighWindowMulSource (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K) :
    divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side
        (divUniversalHighWindowMulMap (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K x) =
      ∑ t, divUniversalHighWindowMultiplierChartRead
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side
            ((Module.finBasis k HS) t) *
        divUniversalHighWindowChartRead (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n side (x t : _) := by
  rw [divUniversalHighWindowMulMap, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  exact divUniversalHighWindowShiftMul_chartRead
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n side
      ((Module.finBasis k HS) t) (x t)

set_option maxHeartbeats 1600000 in
-- The finite ideal bridge elaborates two dependent range-restricted maps.
set_option synthInstance.maxHeartbeats 600000 in
-- Source and range modules are indexed by the concrete carve-chart data.
/-- Multiplying an arbitrary high-window relation submodule by the full multiplier
window preserves its genuine chart-reading ideal. -/
theorem divUniversalHighWindowMulSpanReadIdeal_eq
    (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (side : Bool) :
    divUniversalHighWindowSubmoduleReadIdeal (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1)
        (divUniversalHighWindowMulSpan (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K) side =
      divUniversalHighWindowSubmoduleReadIdeal (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K side := by
  classical
  unfold divUniversalHighWindowSubmoduleReadIdeal
  refine IdealPurity.span_range_read_eq_of_surjective_finite_mul_of_unit
    (R := RZ)
    (B := Γ(relCurve C RZ, relPinnedChart C RZ pi side))
    (K := ↥K)
    (K' := ↥(divUniversalHighWindowMulSpan (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K))
    (ι := Fin (Module.finrank k HS))
    (m := fun t => divUniversalHighWindowMultiplierChartRead
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side
        ((Module.finBasis k HS) t))
    (r := (divUniversalHighWindowChartRead (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n side).comp K.subtype)
    (r' := (divUniversalHighWindowChartRead (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) side).comp
        (divUniversalHighWindowMulSpan (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K).subtype)
    (μ := (divUniversalHighWindowMulMap (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K).rangeRestrict)
    (divUniversalHighWindowMulMap (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K).surjective_rangeRestrict ?_ ?_
  · intro x
    change divUniversalHighWindowChartRead (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side
        (divUniversalHighWindowMulMap (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K x) = _
    exact divUniversalHighWindowMulMap_chartRead
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K side x
  · exact exists_divUniversalHighWindowMultiplierChartRead_mul_eq_one
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side

set_option maxHeartbeats 4800000 in
-- Rewriting the recursive dependent ambient at `n + 2` needs extended reduction.
set_option synthInstance.maxHeartbeats 1200000 in
-- The specialized relation module retains the full high-window instance chain.
/-- From stage one onward, consecutive recursive relation modules define the same
genuine reading ideal on each pinned chart. -/
theorem divUniversalHighWindowRelationReadIdeal_succ_succ_eq
    (n : Nat) (side : Bool) :
    divUniversalHighWindowRelationReadIdeal (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 2) side =
      divUniversalHighWindowRelationReadIdeal (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) side := by
  rw [divUniversalHighWindowRelationReadIdeal_eq_submodule,
    divUniversalHighWindowRelationReadIdeal_eq_submodule,
    divUniversalHighWindowRelation_succ_succ]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    divUniversalHighWindowMulSpanReadIdeal_eq
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1)
        (divUniversalHighWindowRelation (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1)) side

end HighWindowRelationReadSuccessor

end AlgebraicGeometry
