/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.GeometricallyReduced
import AlgebraicJacobian.Curve.MapToP1
import AlgebraicJacobian.Projective.FiniteMapToP1

/-!
# Projectivity of smooth proper curves

A finite morphism to the projective line gives a closed immersion into a
relative projective space. The existing finite-map construction therefore
makes every smooth proper geometrically integral curve projective over its
base field.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- A smooth proper geometrically integral relative curve is projective over
the base field. -/
theorem isProjective_of_smoothProperGeometricallyIntegral
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : C.hom.IsProjective := by
  obtain ⟨pi, hpi, hcomp⟩ := exists_isFinite_toP1 (C := C)
  letI : IsFinite pi := hpi
  exact isProjective_of_isFinite_toP1 C pi hcomp

/-- Projectivity under the smooth, proper, geometrically irreducible curve
hypotheses used by the algebraic Jacobian challenge. -/
theorem isProjective_of_smoothProperGeometricallyIrreducible
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] : C.hom.IsProjective := by
  letI : GeometricallyIntegral C.hom :=
    SmoothOfRelativeDimension.geometricallyIntegral 1 C.hom
  exact isProjective_of_smoothProperGeometricallyIntegral C

end AlgebraicGeometry
