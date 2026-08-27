/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FiniteMapProjectiveImmersion
import AlgebraicJacobian.Picard.ProjectiveMorphism
import AlgebraicJacobian.RiemannRoch.Adelic.P1ChartData
import AlgebraicJacobian.RiemannRoch.Adelic.NonconstantToP1
import AlgebraicJacobian.Curve.GeometricallyReduced

/-!
# Projectivity of smooth proper curves

A finite morphism to the projective line supplies finite Laurent two-chart
data, hence a closed immersion into a relative projective space.  The existing
nonconstant-map construction produces that finite morphism under exactly the
ambient hypotheses of the algebraic Jacobian challenge.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Adelic

variable {k : Type u} [Field k]

/-- A proper scheme admitting a finite morphism to the projective line is
projective over the base field. -/
theorem isProjective_of_hasFiniteMapToP1
    (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [HasFiniteMapToP1 C] : C.hom.IsProjective := by
  obtain ⟨pi, hpi⟩ := HasFiniteMapToP1.nonempty_finite_map (C := C)
  letI : IsFinite pi.left := hpi
  exact (p1LaurentChartData k).isProjective_of_finiteMap pi

/-- A smooth proper geometrically integral relative curve is projective over
the base field. -/
theorem isProjective_of_smoothProperGeometricallyIntegral
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : C.hom.IsProjective := by
  haveI : HasFiniteMapToP1 C := inferInstance
  exact isProjective_of_hasFiniteMapToP1 C

/-- At the scheme universe supported by `IsProjectiveWith`, a smooth proper
geometrically integral relative curve carries a relatively very ample line
bundle, with no hypothesis beyond the curve's own. -/
theorem exists_isProjectiveWith_of_smoothProperGeometricallyIntegral
    {k₀ : Type} [Field k₀] (C : Over (Spec (CommRingCat.of k₀)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    ∃ L : C.left.Modules, C.hom.IsProjectiveWith L :=
  (isProjective_of_smoothProperGeometricallyIntegral C).exists_isProjectiveWith

/-- Projectivity under exactly the smooth, proper, geometrically irreducible
curve hypotheses used by the algebraic Jacobian challenge. -/
theorem isProjective_of_smoothProperGeometricallyIrreducible
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] : C.hom.IsProjective := by
  letI : GeometricallyIntegral C.hom :=
    SmoothOfRelativeDimension.geometricallyIntegral 1 C.hom
  exact isProjective_of_smoothProperGeometricallyIntegral C

/-- At the scheme universe supported by `IsProjectiveWith`, the carried
relatively very ample line bundle under exactly the smooth, proper,
geometrically irreducible hypotheses used by the Jacobian challenge. -/
theorem exists_isProjectiveWith_of_smoothProperGeometricallyIrreducible
    {k₀ : Type} [Field k₀] (C : Over (Spec (CommRingCat.of k₀)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] :
    ∃ L : C.left.Modules, C.hom.IsProjectiveWith L :=
  (isProjective_of_smoothProperGeometricallyIrreducible C).exists_isProjectiveWith

end AlgebraicGeometry.Adelic
