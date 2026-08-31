/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeWindowMulGeneral
import AlgebraicJacobian.Picard.DivSchemeHighWindowRelations

/-!
# Multiplication compatibility for the recursive high-window map

This specializes arbitrary theta-window multiplication to the arithmetic progression
`M + n*S`.  It identifies the multiplication map used to define the recursive relation
tower with the generic multiplication map, up to the canonical exponent reindexing.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000
-- Arithmetic/cast declarations retain the standing curve pack through synthesized instances.
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowMulCompatibility

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowMulCompatibility :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : Nat)

/-- The successor arithmetic identity for the high-window exponents. -/
theorem divUniversalHighWindowExponent_succ (n : Nat) :
    windowS_choice pi hpi g +
        divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n =
      divUniversalHighWindowExponent (C := C) (pi := pi) hpi g (n + 1) := by
  simp only [divUniversalHighWindowExponent, Nat.succ_mul]
  omega

/-- Reindex divisor-section windows along an equality of exponents. -/
noncomputable def divisorWindowExponentEquiv {p q : Nat} (h : p = q) :
    ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤) ≃ₗ[k]
      ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤) :=
  LinearEquiv.ofEq _ _ (congrArg
    (fun e : Nat => divisorSections k (e • fiberWeilDivisor pi) ⊤) h)

@[simp]
theorem coe_divisorWindowExponentEquiv {p q : Nat} (h : p = q)
    (x : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤)) :
    ((divisorWindowExponentEquiv (C := C) (pi := pi) h x :
        ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) : C.left.functionField) =
      (x : C.left.functionField) := by
  subst q
  rfl

/-- Reindex the generic sum exponent to the next campaign high window. -/
noncomputable def divUniversalHighWindowSuccExponentEquiv (n : Nat) :
    ↥(divisorSections k
        ((windowS_choice pi hpi g +
          divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) •
            fiberWeilDivisor pi) ⊤) ≃ₗ[k]
      divUniversalHighWindowSections (C := C) (pi := pi) hpi g (n + 1) :=
  divisorWindowExponentEquiv (C := C) (pi := pi)
    (divUniversalHighWindowExponent_succ (C := C) (pi := pi) hpi g n)

@[simp]
theorem coe_divUniversalHighWindowSuccExponentEquiv (n : Nat)
    (x : ↥(divisorSections k
      ((windowS_choice pi hpi g +
        divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) •
          fiberWeilDivisor pi) ⊤)) :
    (((divUniversalHighWindowSuccExponentEquiv (C := C) (pi := pi) hpi g n) x :
        divUniversalHighWindowSections (C := C) (pi := pi) hpi g (n + 1)) :
      C.left.functionField) = (x : C.left.functionField) :=
  coe_divisorWindowExponentEquiv (C := C) (pi := pi)
    (divUniversalHighWindowExponent_succ (C := C) (pi := pi) hpi g n) x

@[simp]
theorem coe_divUniversalHighWindowShiftMul (n : Nat)
    (a : ↥(divisorSections k
      (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤))
    (m : divUniversalHighWindowSections (C := C) (pi := pi) hpi g n) :
    ((divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n a m :
        divUniversalHighWindowSections (C := C) (pi := pi) hpi g (n + 1)) :
      C.left.functionField) =
      (a : C.left.functionField) * (m : C.left.functionField) := by
  rw [divUniversalHighWindowShiftMul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    divUniversalHighWindowSuccEquiv, LinearEquiv.coe_ofEq_apply,
    sectionMulBilin_apply_coe]

/-- The relation-tower multiplication map is generic theta-window multiplication followed
by the canonical successor-exponent reindexing. -/
theorem divUniversalHighWindowShiftMul_eq (n : Nat)
    (a : ↥(divisorSections k
      (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)) :
    divUniversalHighWindowShiftMul (C := C) (pi := pi) hpi g n a =
      (divUniversalHighWindowSuccExponentEquiv (C := C) (pi := pi) hpi g n).toLinearMap.comp
        (thetaWindowMul (C := C) (pi := pi)
          (windowS_choice pi hpi g)
          (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) a) := by
  ext m
  rw [coe_divUniversalHighWindowShiftMul, LinearMap.comp_apply]
  change (a : C.left.functionField) * (m : C.left.functionField) =
    ((divUniversalHighWindowSuccExponentEquiv (C := C) (pi := pi) hpi g n
      (thetaWindowMul (C := C) (pi := pi)
        (windowS_choice pi hpi g)
        (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) a m) :
      divUniversalHighWindowSections (C := C) (pi := pi) hpi g (n + 1)) :
        C.left.functionField)
  calc
    _ = ((thetaWindowMul (C := C) (pi := pi)
        (windowS_choice pi hpi g)
        (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) a m :
      ↥(divisorSections k
        ((windowS_choice pi hpi g +
          divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) •
            fiberWeilDivisor pi) ⊤)) :
        C.left.functionField) :=
      (thetaWindowMul_coe (C := C) (pi := pi)
        (windowS_choice pi hpi g)
        (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) a m).symm
    _ = _ := (coe_divUniversalHighWindowSuccExponentEquiv
      (C := C) (pi := pi) hpi g n
      (thetaWindowMul (C := C) (pi := pi)
        (windowS_choice pi hpi g)
        (divUniversalHighWindowExponent (C := C) (pi := pi) hpi g n) a m)).symm

end HighWindowMulCompatibility

end AlgebraicGeometry
