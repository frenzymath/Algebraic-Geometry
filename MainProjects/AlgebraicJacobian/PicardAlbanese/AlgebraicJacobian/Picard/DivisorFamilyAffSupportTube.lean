/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFibreSupport
import AlgebraicJacobian.Picard.RelativeCurveFiniteInAffine
import AlgebraicJacobian.Picard.SupportTube

/-!
# Field-uniform affine support tubes

A finite support fibre of a divisor family lies in an arbitrary affine open of the
relative curve: graded prime avoidance gives `FiniteInAffine` for the curve.  Properness
then spreads the containment over a basic open of the test base.

This is the coordinate-free replacement for the old route through `GL₂` and two twisted
charts.  It introduces no field-size hypothesis and does not type the affine neighbourhood
into either pinned chart.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme ThetaGeneratorSeed

namespace Scheme.LocalEquations

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k))) [IsProper C.hom]
variable (R : Type u) [CommRing R] [Algebra k R]

/-- A finite support fibre is contained in an affine open, and after shrinking the base
to a basic open the whole family support remains in that same affine open. -/
theorem exists_affineOpen_basicOpen_supportLocus_subset
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (d : (relCurve C R).LocalEquations) (p : PrimeSpectrum R)
    (hfinite : (((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩
      d.supportLocus).Finite) :
    ∃ (W : (relCurve C R).affineOpens) (r : R), r ∉ p.asIdeal ∧
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹'
          (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ∩
        d.supportLocus ⊆ (W.1 : Set (relCurve C R)) := by
  let F : Set (relCurve C R) :=
    ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩ d.supportLocus
  obtain ⟨W, hFW⟩ :=
    Scheme.finiteInAffine_relCurve_of_isFinite_toP1 C R pi F hfinite
  obtain ⟨V, hpV, hV⟩ := d.exists_supportTube
    ((relCurve C R) ↘ Spec (.of R)) (Opens.isOpen W.1) hFW
  obtain ⟨U, hU, hpU, hUV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) hpV V.isOpen
  obtain ⟨r, rfl⟩ := hU
  exact ⟨W, r, (PrimeSpectrum.mem_basicOpen r p).mp hpU,
    fun x hx => hV ⟨hUV hx.1, hx.2⟩⟩

end Scheme.LocalEquations

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}

/-- A generator seed admits a base-local arbitrary affine neighbourhood of its whole
support, uniformly over every ground field. -/
theorem exists_affineOpen_basicOpen_supportLocus_subset
    (D : ThetaGeneratorSeed C R pi a K) (hD : D.IsGenerator)
    (p : PrimeSpectrum R) :
    ∃ (W : (relCurve C R).affineOpens) (r : R), r ∉ p.asIdeal ∧
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹'
          (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ∩
        (D.localEquations hD).supportLocus ⊆ (W.1 : Set (relCurve C R)) :=
  Scheme.LocalEquations.exists_affineOpen_basicOpen_supportLocus_subset
    C R (pi := pi) (D.localEquations hD) p
    (D.fibre_supportLocus_finite_aff hD p)

end ThetaGeneratorSeed

end AlgebraicGeometry
