/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.BaseChangeInstances
import AlgebraicJacobian.Cohomology.RelativeTwoCover

/-!
# Canonical field-base-change instances for `relCurve`

The base-change package proves the curve properties using the product spelling
`(C ⊗ overSpec k K).left`. The reviewed Picard route uses the canonical spelling
`relCurve C K`. This module is the single bridge between them.

The bridge is scoped to avoid adding another competing global instance family. Consumers opt in
with `open scoped RelativeCurve`; inside that scope `relCurve.instOver` wins the otherwise tied
choice of scheme-over structures, and the property witnesses have low priority.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance 1001] relCurve.instOver

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  (K : Type u) [Field K] [Algebra k K]

omit [IsProper C.hom] in
/-- Integrality of the field-base-changed curve, in the canonical `relCurve` spelling. -/
theorem relCurve.isIntegral : IsIntegral (relCurve C K) :=
  instIsIntegralBaseChange C K

omit [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- Relative smoothness of the field-base-changed curve, in the canonical spelling. -/
theorem relCurve.smooth :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

omit [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] in
/-- Properness of the field-base-changed curve, in the canonical spelling. -/
theorem relCurve.proper : IsProper (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instIsProperBaseChange C K

omit [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] in
/-- Quasi-compactness of the field-base-changed curve, in the canonical spelling. -/
theorem relCurve.quasiCompact : QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] in
/-- Geometric irreducibility after field base change, in the canonical spelling. -/
theorem relCurve.geometricallyIrreducible :
    GeometricallyIrreducible (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instGeometricallyIrreducibleSndLeft C K

/-- Finiteness of structure-sheaf `H⁰` after field base change. -/
theorem relCurve.hModuleFiniteZero :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

/-- Finiteness of structure-sheaf `H¹` after field base change. -/
theorem relCurve.hModuleFiniteOne :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

scoped[RelativeCurve] attribute [instance 1001] AlgebraicGeometry.relCurve.instOver
scoped[RelativeCurve] attribute [instance 100] AlgebraicGeometry.relCurve.isIntegral
  AlgebraicGeometry.relCurve.smooth AlgebraicGeometry.relCurve.proper
  AlgebraicGeometry.relCurve.quasiCompact AlgebraicGeometry.relCurve.geometricallyIrreducible
  AlgebraicGeometry.relCurve.hModuleFiniteZero AlgebraicGeometry.relCurve.hModuleFiniteOne

end AlgebraicGeometry
