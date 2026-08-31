/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowKoszul
import AlgebraicJacobian.Picard.DivSchemeHighWindowMulCompatibility
import AlgebraicJacobian.Picard.DivSchemeHighWindowTransitionRelation

/-!
# A relative Koszul boundary for high-window relations

Multiplication by the fixed basis of the `S`-window carries a submodule in
high window `n` toward high window `n + 1`.  Given a target submodule which
contains these products, this file corestricts each basis multiplication to
a step between the two submodules and forms the finite rows-minus-columns
Koszul boundary.

The next high-window multiplication map kills this boundary.  This is the
relative `range <= kernel` half of the finite-stage relation theorem; the
reverse inclusion on residue-field fibres is the geometric pencil input.
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

section HighWindowRelativeKoszul

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowRelativeKoszul :
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
local notation "HI" => Fin (Module.finrank k HS)

set_option maxHeartbeats 1600000 in
-- The dependent source and successor submodules are expensive to elaborate.
/-- The basis multiplications from `K` land in the chosen successor
submodule `Knext`.  Keeping this as a hypothesis also covers the exceptional
seed transition, whose target is not definitionally the recursive range. -/
def DivUniversalHighWindowMulPreserves (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (Knext : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1))) :
    Prop :=
  ∀ (t : HI) (z : K),
    divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n ((Module.finBasis k HS) t)
        (K.subtype z) ∈ Knext

set_option maxHeartbeats 1600000 in
-- The supported source vector unfolds the dependent multiplication map.
/-- The canonical multiplication-span successor satisfies the preservation
condition by taking a vector supported at the chosen basis index. -/
theorem divUniversalHighWindowMulPreserves_mulSpan (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n)) :
    DivUniversalHighWindowMulPreserves (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K
      (divUniversalHighWindowMulSpan (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K) := by
  intro t z
  exact divUniversalHighWindowBaseMultiplierTransition_finBasis_mem_mulSpan
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K t
      (K.subtype z) z.property

set_option maxHeartbeats 1600000 in
-- Corestricting traverses both dependent high-window ambient types.
/-- Multiplication by one `S`-window basis vector, corestricted from `K` to
a successor submodule known to contain all such products. -/
noncomputable def divUniversalHighWindowBasisStep (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (Knext : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1)))
    (hpres : DivUniversalHighWindowMulPreserves (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K Knext) (t : HI) : K →ₗ[RZ] Knext :=
  ((divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n ((Module.finBasis k HS) t)).comp
    K.subtype).codRestrict Knext (hpres t)

set_option maxHeartbeats 1600000 in
-- Reducing the dependent corestriction needs the larger elaboration budget.
@[simp]
theorem coe_divUniversalHighWindowBasisStep (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (Knext : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1)))
    (hpres : DivUniversalHighWindowMulPreserves (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K Knext) (t : HI) (z : K) :
    ((divUniversalHighWindowBasisStep (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K Knext hpres t z : Knext) :
      divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
        (i := i) (j := j) (n + 1)) =
      divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n ((Module.finBasis k HS) t) (K.subtype z) :=
  rfl

set_option maxHeartbeats 1600000 in
-- The finite function modules retain both dependent relation subtypes.
/-- The relative finite Koszul boundary between consecutive high-window
submodules. -/
noncomputable def divUniversalHighWindowKoszulBoundary (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (Knext : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1)))
    (hpres : DivUniversalHighWindowMulPreserves (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K Knext) :
    (HI × HI → K) →ₗ[RZ] (HI → Knext) :=
  finiteKoszulBoundary (fun t =>
    divUniversalHighWindowBasisStep (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K Knext hpres t)

set_option maxHeartbeats 1600000 in
-- Naming the dependent step family avoids re-elaborating both relation subtypes.
/-- The relative boundary is the generic finite Koszul boundary on its
basis-indexed multiplication steps. -/
theorem divUniversalHighWindowKoszulBoundary_eq_finite (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (Knext : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1)))
    (hpres : DivUniversalHighWindowMulPreserves (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K Knext) :
    divUniversalHighWindowKoszulBoundary (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K Knext hpres =
      finiteKoszulBoundary (fun t =>
        divUniversalHighWindowBasisStep (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n K Knext hpres t) :=
  rfl

set_option maxHeartbeats 1600000 in
-- The row type contains the dependent ambient and relation subtype at one stage.
/-- One component row of the high-window multiplication map. -/
noncomputable def divUniversalHighWindowMulRow (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (t : HI) : K →ₗ[RZ]
      divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
        (i := i) (j := j) (n + 1) :=
  (LinearMap.baseChange RZ
    (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n
      ((Module.finBasis k HS) t))).comp K.subtype

set_option maxHeartbeats 1600000 in
-- Associating the dependent inclusion with each finite projection is expensive.
/-- The high-window multiplication map is the finite sum of its component rows. -/
theorem divUniversalHighWindowMulMap_eq_finiteComponentSum (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n)) :
    divUniversalHighWindowMulMap (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K =
      finiteComponentSum (divUniversalHighWindowMulRow (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K) := by
  classical
  simp only [divUniversalHighWindowMulMap, finiteComponentSum,
    divUniversalHighWindowMulRow, LinearMap.comp_assoc]

set_option maxHeartbeats 1600000 in
-- Expanding both dependent successor reindexings is elaboration-heavy.
/-- Consecutive high-window basis multiplications commute over the base
field. -/
theorem divUniversalHighWindowShiftMul_comp_comm (n : Nat) (a b : HS) :
    (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g (n + 1) a).comp
        (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n b) =
      (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g (n + 1) b).comp
  (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n a) := by
  ext z
  simp only [LinearMap.comp_apply, coe_divUniversalHighWindowShiftMul]
  ring

set_option maxHeartbeats 1600000 in
-- Base change traverses two consecutive dependent high-window maps.
/-- Consecutive high-window basis multiplications still commute after scalar
extension to the carve-chart ring. -/
theorem divUniversalHighWindowBaseChangeShiftMul_comm (n : Nat) (a b : HS)
    (z : divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
      (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n) :
    LinearMap.baseChange RZ
        (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g (n + 1) a)
        (LinearMap.baseChange RZ
          (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n b) z) =
      LinearMap.baseChange RZ
        (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g (n + 1) b)
        (LinearMap.baseChange RZ
          (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n a) z) := by
  change
    ((LinearMap.baseChange RZ
      (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g (n + 1) a)).comp
        (LinearMap.baseChange RZ
          (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n b))) z = _
  rw [← LinearMap.baseChange_comp,
    divUniversalHighWindowShiftMul_comp_comm (C := C) (pi := pi) hpi g n a b,
    LinearMap.baseChange_comp, LinearMap.comp_apply]

set_option maxHeartbeats 1600000 in
-- The generic cancellation lemma is instantiated with two dependent relation stages.
set_option synthInstance.maxHeartbeats 400000 in
-- The congruence map synthesizes the dependent carve-ring linear-map module.
/-- The finite component sum of the successor rows kills the relative Koszul
boundary. -/
theorem finiteComponentSum_divUniversalHighWindowMulRow_comp_koszulBoundary_eq_zero
    (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (Knext : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1)))
    (hpres : DivUniversalHighWindowMulPreserves (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K Knext) :
    (finiteComponentSum
        (divUniversalHighWindowMulRow (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1) Knext)).comp
      (divUniversalHighWindowKoszulBoundary (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K Knext hpres) = 0 := by
  let step : HI → K →ₗ[RZ] Knext := fun t =>
    divUniversalHighWindowBasisStep (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K Knext hpres t
  have hzero := finiteComponentSum_comp_finiteKoszulBoundary_eq_zero
    (divUniversalHighWindowMulRow (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) Knext) step (by
        intro a b z
        change
          LinearMap.baseChange RZ
              (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g (n + 1)
                ((Module.finBasis k HS) a))
              (LinearMap.baseChange RZ
                (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n
                  ((Module.finBasis k HS) b)) (K.subtype z)) =
            LinearMap.baseChange RZ
              (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g (n + 1)
                ((Module.finBasis k HS) b))
              (LinearMap.baseChange RZ
                (divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n
                  ((Module.finBasis k HS) a)) (K.subtype z))
        exact divUniversalHighWindowBaseChangeShiftMul_comm
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n
            ((Module.finBasis k HS) a) ((Module.finBasis k HS) b) (K.subtype z))
  have hboundary := divUniversalHighWindowKoszulBoundary_eq_finite
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K Knext hpres
  exact (congrArg (fun d =>
    (finiteComponentSum
      (divUniversalHighWindowMulRow (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) Knext)).comp d) hboundary).trans hzero

set_option maxHeartbeats 1600000 in
-- The dependent stages and their two consecutive multiplication maps are large.
set_option synthInstance.maxHeartbeats 400000 in
-- The final composition congruence uses the dependent boundary map module.
/-- The multiplication map out of `Knext` kills the relative Koszul boundary
formed one stage earlier. -/
theorem divUniversalHighWindowMulMap_comp_koszulBoundary_eq_zero (n : Nat)
    (K : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n))
    (Knext : Submodule RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) (n + 1)))
    (hpres : DivUniversalHighWindowMulPreserves (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K Knext) :
    (divUniversalHighWindowMulMap (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) Knext).comp
      (divUniversalHighWindowKoszulBoundary (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n K Knext hpres) = 0 := by
  have hmul := divUniversalHighWindowMulMap_eq_finiteComponentSum
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1) Knext
  have hzero :=
    finiteComponentSum_divUniversalHighWindowMulRow_comp_koszulBoundary_eq_zero
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n K Knext hpres
  exact (congrArg (fun f => f.comp
    (divUniversalHighWindowKoszulBoundary (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n K Knext hpres)) hmul).trans hzero

end HighWindowRelativeKoszul

end AlgebraicGeometry
