/-
Copyright (c) 2026 Frenzymath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frenzymath
-/
module

import AGLib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth reducedness smoke tests

These examples exercise the public smoothness-to-reducedness and geometric-integrality API
without importing either source route.
-/

universe u

open CategoryTheory
open AlgebraicGeometry

section SmoothOverField

variable {K : Type u} [Field K] {X : Scheme.{u}}

example (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X :=
  Smooth.isReduced_of_field f

end SmoothOverField

section GeometricIntegrality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

example [Smooth f] : GeometricallyReduced f := inferInstance

example [Smooth f] [GeometricallyIrreducible f] : GeometricallyIntegral f := inferInstance

example (n : ℕ) [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f] :
    GeometricallyIntegral f :=
  SmoothOfRelativeDimension.geometricallyIntegral n f

end GeometricIntegrality
