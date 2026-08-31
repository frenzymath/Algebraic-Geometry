/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowH1
import AlgebraicJacobian.Picard.DivSchemeSeedUniv
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Projective stages at every high divisor-scheme window

The saturation route to flatness uses the windows with exponents `M + n * s`, not
only the two carve windows `M` and `M + s`.  This file fixes the types of those stages
over a carve-chart ring and records the formal algebra which is already available:

* every high-window ambient is finite free, hence projective and flat;
* `relThetaWindowEquiv` identifies it with the corresponding relative theta sections,
  using the uniform `H^1` vanishing from `DivSchemeHighWindowH1`;
* a projective high-window quotient is exactly a Grassmannian point, and its quotient
  remains finite, projective, and flat after transporting to relative theta sections;
* the two universal carve windows give the stages at indices zero and one.

Constructing compatible stages at every later index, and identifying their directed
limit with the genuine chart-reading quotient, remain the geometric saturation step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

section HighWindowStage

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowStage :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
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

/-- The exponent of the `n`-th high window.  Thus index zero is `M` and index one is
the shifted carve window `M + s`. -/
noncomputable abbrev divUniversalHighWindowExponent (n : Nat) : Nat :=
  windowM_choice pi hpi g + n * windowS_choice pi hpi g

/-- The base-field section space at the `n`-th high window. -/
noncomputable abbrev divUniversalHighWindowSections (n : Nat) : Type u :=
  ↥(Scheme.divisorSections k
    (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n •
      fiberWeilDivisor pi) ⊤)

/-- The scalar-extended ambient module at the `n`-th high window. -/
noncomputable abbrev divUniversalHighWindowAmbient (n : Nat) : Type u :=
  RZ ⊗[k] divUniversalHighWindowSections (C := C) (pi := pi) hpi g n

/-- Uniform high-window identification with relative theta sections. -/
noncomputable def divUniversalHighWindowThetaEquiv (n : Nat) :
    divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n ≃ₗ[RZ]
      relThetaSections C RZ pi
        (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) :=
  relThetaWindowEquiv C RZ pi
    (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n)
    (relThetaPairH1_windowM_add_mulS C pi hpi g n)

set_option synthInstance.maxHeartbeats 400000 in
-- The dependent carve-chart tensor instance exceeds the default synthesis budget.
/-- Every high-window ambient is finite over the carve-chart ring. -/
theorem finite_divUniversalHighWindowAmbient (n : Nat) :
    Module.Finite RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n) := by
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
-- The dependent carve-chart tensor instance exceeds the default synthesis budget.
/-- Every high-window ambient is free over the carve-chart ring. -/
theorem free_divUniversalHighWindowAmbient (n : Nat) :
    Module.Free RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n) := by
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
-- Reusing the finite-dimensional base-change basis requires the larger chart budget.
/-- Every high-window ambient is projective over the carve-chart ring. -/
theorem projective_divUniversalHighWindowAmbient (n : Nat) :
    Module.Projective RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n) := by
  letI := free_divUniversalHighWindowAmbient (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n
  infer_instance

/-- Every high-window ambient is flat over the carve-chart ring. -/
theorem flat_divUniversalHighWindowAmbient (n : Nat) :
    Module.Flat RZ
      (divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n) := by
  letI := projective_divUniversalHighWindowAmbient
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n
  exact Module.Flat.of_projective

/-- A projective quotient stage at the `n`-th high window.  This is deliberately the
existing Grassmannian datum: later saturation work only has to construct these points
and their transition compatibility. -/
abbrev DivUniversalHighWindowStage (n : Nat) : Type u :=
  Grassmannian.grFunctorAff k
    (divUniversalHighWindowSections (C := C) (pi := pi) hpi g n) g RZ

/-- The quotient module carried by a high-window stage. -/
abbrev divUniversalHighWindowQuotient (n : Nat)
    (x : DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n) :
    Type u :=
  divUniversalHighWindowAmbient (C := C) (pi := pi) (hpi := hpi) (g := g)
    (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n ⧸
      x.toSubmodule

set_option maxHeartbeats 1600000 in
-- Unfolding the dependent high-window ambient and Grassmannian quotient is expensive.
/-- A high-window stage has finite quotient. -/
theorem finite_divUniversalHighWindowQuotient (n : Nat)
    (x : DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n) :
    Module.Finite RZ
      (divUniversalHighWindowQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n x) :=
  x.finite_quotient

set_option maxHeartbeats 1600000 in
-- Unfolding the dependent high-window ambient and Grassmannian quotient is expensive.
/-- A high-window stage has projective quotient. -/
theorem projective_divUniversalHighWindowQuotient (n : Nat)
    (x : DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n) :
    Module.Projective RZ
      (divUniversalHighWindowQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n x) :=
  x.projective_quotient

set_option maxHeartbeats 1600000 in
-- The projective-to-flat transport re-elaborates the dependent quotient type.
/-- A high-window stage has flat quotient. -/
theorem flat_divUniversalHighWindowQuotient (n : Nat)
    (x : DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n) :
    Module.Flat RZ
      (divUniversalHighWindowQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n x) := by
  letI := projective_divUniversalHighWindowQuotient
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n x
  exact Module.Flat.of_projective

/-- The stage submodule transported into relative theta sections. -/
noncomputable def divUniversalHighWindowThetaSubmodule (n : Nat)
    (x : DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n) :
    Submodule RZ
      (relThetaSections C RZ pi
        (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n)) :=
  Submodule.map
    (divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n).toLinearMap
    x.toSubmodule

set_option maxHeartbeats 1600000 in
-- Both sides unfold the relative-theta transport over the dependent carve-chart ring.
/-- Quotient comparison after reading a high-window stage as relative theta sections. -/
noncomputable def divUniversalHighWindowThetaQuotientEquiv (n : Nat)
    (x : DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n) :
    divUniversalHighWindowQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n x ≃ₗ[RZ]
      (relThetaSections C RZ pi
          (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) ⧸
        divUniversalHighWindowThetaSubmodule (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n x) :=
  Submodule.Quotient.equiv x.toSubmodule _
    (divUniversalHighWindowThetaEquiv (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n) rfl

set_option maxHeartbeats 1600000 in
-- Transporting finiteness re-elaborates the dependent theta quotient equivalence.
/-- The relative-theta quotient of a stage is finite. -/
theorem finite_divUniversalHighWindowThetaQuotient (n : Nat)
    (x : DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n) :
    Module.Finite RZ
      (relThetaSections C RZ pi
          (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) ⧸
        divUniversalHighWindowThetaSubmodule (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n x) := by
  letI := finite_divUniversalHighWindowQuotient
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n x
  exact Module.Finite.equiv
    (divUniversalHighWindowThetaQuotientEquiv (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n x)

set_option maxHeartbeats 1600000 in
-- Transporting projectivity re-elaborates the dependent theta quotient equivalence.
/-- The relative-theta quotient of a stage is projective. -/
theorem projective_divUniversalHighWindowThetaQuotient (n : Nat)
    (x : DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n) :
    Module.Projective RZ
      (relThetaSections C RZ pi
          (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) ⧸
        divUniversalHighWindowThetaSubmodule (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n x) := by
  letI := projective_divUniversalHighWindowQuotient
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n x
  exact Module.Projective.of_equiv
    (divUniversalHighWindowThetaQuotientEquiv (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n x)

set_option maxHeartbeats 1600000 in
-- The projective-to-flat transport re-elaborates the dependent theta quotient.
/-- The relative-theta quotient of a stage is flat. -/
theorem flat_divUniversalHighWindowThetaQuotient (n : Nat)
    (x : DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n) :
    Module.Flat RZ
      (relThetaSections C RZ pi
          (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) ⧸
        divUniversalHighWindowThetaSubmodule (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n x) := by
  letI := projective_divUniversalHighWindowThetaQuotient
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n x
  exact Module.Flat.of_projective

/-! ## The two landed seed stages -/

/-- Reindex the first universal window as high-window stage zero. -/
noncomputable def divUniversalHighWindowZeroEquiv :
    ↥(Scheme.divisorSections k
        (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤) ≃ₗ[k]
      divUniversalHighWindowSections (C := C) (pi := pi) hpi g 0 :=
  LinearEquiv.ofEq _ _ (congrArg (fun D => Scheme.divisorSections k D ⊤) (by
    simp [divUniversalHighWindowExponent]))

/-- Reindex the shifted universal window as high-window stage one. -/
noncomputable def divUniversalHighWindowOneEquiv :
    ↥(Scheme.divisorSections k
        ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤)
      ≃ₗ[k] divUniversalHighWindowSections (C := C) (pi := pi) hpi g 1 :=
  LinearEquiv.ofEq _ _ (congrArg (fun D => Scheme.divisorSections k D ⊤) (by
    simp [divUniversalHighWindowExponent]))

/-- The universal first carve window, placed at index zero of the high-window tower. -/
noncomputable def divUniversalHighWindowStageZero :
    DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j 0 :=
  Grassmannian.congrAmbient
    (divUniversalHighWindowZeroEquiv (C := C) (pi := pi) hpi g)
    (divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j)

/-- The universal second carve window, placed at index one of the high-window tower. -/
noncomputable def divUniversalHighWindowStageOne :
    DivUniversalHighWindowStage (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j 1 :=
  Grassmannian.congrAmbient
    (divUniversalHighWindowOneEquiv (C := C) (pi := pi) hpi g)
    (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j)

@[simp]
theorem divUniversalHighWindowStageZero_toSubmodule :
    (divUniversalHighWindowStageZero (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j).toSubmodule =
      Submodule.map
        (LinearMap.baseChange RZ
          (divUniversalHighWindowZeroEquiv (C := C) (pi := pi) hpi g).toLinearMap)
        (divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule :=
  rfl

@[simp]
theorem divUniversalHighWindowStageOne_toSubmodule :
    (divUniversalHighWindowStageOne (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j).toSubmodule =
      Submodule.map
        (LinearMap.baseChange RZ
          (divUniversalHighWindowOneEquiv (C := C) (pi := pi) hpi g).toLinearMap)
        (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule :=
  rfl

end HighWindowStage

end AlgebraicGeometry
