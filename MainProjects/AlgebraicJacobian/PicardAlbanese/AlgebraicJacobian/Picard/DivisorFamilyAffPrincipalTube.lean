/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffSupportTube
import AlgebraicJacobian.Picard.FiniteSetPicTrivialization

/-!
# Picard-trivial affine support tubes

Starting from a finite residue-fibre support, first choose an affine neighbourhood,
then trivialize the divisor Picard class on a smaller affine neighbourhood of that
same finite set, and finally spread containment of the support by properness.  The
result is a single basic-open base shrink and an affine support piece carrying a
principal equation.
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

/-- A finite support fibre admits a Picard-trivial affine neighbourhood which contains
the whole family support after shrinking the base to one basic open. -/
theorem exists_affineOpen_basicOpen_supportLocus_subset_cechPicMap_ι_eq_one
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (d : (relCurve C R).LocalEquations) (p : PrimeSpectrum R)
    (hfinite : (((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩
      d.supportLocus).Finite) :
    ∃ (W : (relCurve C R).affineOpens) (r : R), r ∉ p.asIdeal ∧
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹'
          (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ∩
        d.supportLocus ⊆ (W.1 : Set (relCurve C R)) ∧
      Scheme.CechPic.map W.1.ι d.picClass = 1 := by
  let F : Set (relCurve C R) :=
    ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩ d.supportLocus
  obtain ⟨V, hFV⟩ :=
    Scheme.finiteInAffine_relCurve_of_isFinite_toP1 C R pi F hfinite
  obtain ⟨W, hWaff, hFW, _, hpic⟩ :=
    Scheme.exists_affineOpen_finset_subset_cechPicMap_ι_eq_one
      d.picClass hfinite V.2 hFV
  obtain ⟨O, hpO, hO⟩ := d.exists_supportTube
    ((relCurve C R) ↘ Spec (.of R)) (Opens.isOpen W) hFW
  obtain ⟨U, hU, hpU, hUO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) hpO O.isOpen
  obtain ⟨r, rfl⟩ := hU
  exact ⟨⟨W, hWaff⟩, r, (PrimeSpectrum.mem_basicOpen r p).mp hpU,
    fun x hx => hO ⟨hUO hx.1, hx.2⟩, hpic⟩

end Scheme.LocalEquations

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}

/-- A generator seed has a Picard-trivial affine support tube at every base prime,
without a field-size or coordinate-change hypothesis. -/
theorem exists_affineOpen_basicOpen_supportLocus_subset_cechPicMap_ι_eq_one
    (D : ThetaGeneratorSeed C R pi a K) (hD : D.IsGenerator)
    (p : PrimeSpectrum R) :
    ∃ (W : (relCurve C R).affineOpens) (r : R), r ∉ p.asIdeal ∧
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹'
          (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ∩
        (D.localEquations hD).supportLocus ⊆ (W.1 : Set (relCurve C R)) ∧
      Scheme.CechPic.map W.1.ι (D.localEquations hD).picClass = 1 :=
  Scheme.LocalEquations.exists_affineOpen_basicOpen_supportLocus_subset_cechPicMap_ι_eq_one
    C R (pi := pi) (D.localEquations hD) p
      (D.fibre_supportLocus_finite_aff hD p)

end ThetaGeneratorSeed
end AlgebraicGeometry
