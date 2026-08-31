/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffPrincipalAdaptation
import AlgebraicJacobian.Picard.DivisorFamilyAffPrincipalTube
import AlgebraicJacobian.Picard.DivisorFamilyAffSections
import AlgebraicJacobian.Picard.DivSchemeCertZarTransport

/-!
# Away-local principal adaptations

A Picard-trivial affine support tube pulls back to a Picard-trivial affine open over
the corresponding away localization.  Its pulled local-equation system therefore
admits a swallowed widened adaptation, with no subordination to the original cover.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme ThetaGeneratorSeed

namespace Scheme.LocalEquations

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k))) [IsProper C.hom]
variable (R : Type u) [CommRing R] [Algebra k R]

/-- A finite support fibre produces, after one away localization, a swallowed widened
adaptation of the pulled local-equation system. -/
theorem exists_away_affAdaptation_swallowedBy_of_finite_fibre
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (d : (relCurve C R).LocalEquations) (p : PrimeSpectrum R)
    (hfinite : (((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩
      d.supportLocus).Finite) :
    ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ (D : AffCoverData C (Localization.Away r))
        (_ : AffAdaptation D
          (d.pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) d))),
        D.SwallowedBy
          (d.pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) d)) := by
  obtain ⟨W, r, hr, htube, hpic⟩ :=
    d.exists_affineOpen_basicOpen_supportLocus_subset_cechPicMap_ι_eq_one
      C R pi p hfinite
  refine ⟨r, hr, ?_⟩
  letI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
    isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
  let f : relCurve C (Localization.Away r) ⟶ relCurve C R :=
    relCurveMap C R (Localization.Away r)
  let hreg :=
    Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion f d
  let dr := d.pullback f hreg
  let Wr : (relCurve C (Localization.Away r)).Opens := f ⁻¹ᵁ W.1
  have hWraff : IsAffineOpen Wr :=
    isAffineOpen_relCurveMap_preimage C (Localization.Away r) W.2
  have hsub : dr.supportLocus ⊆ (Wr : Set (relCurve C (Localization.Away r))) := by
    intro x hx
    have hx' : f.base x ∈ d.supportLocus := by
      have hx' : x ∈ f.base ⁻¹' d.supportLocus := by
        simpa only [dr, Scheme.LocalEquations.supportLocus_pullback] using hx
      exact hx'
    have hbase : relCurveBasePoint C R
        ((relCurveMap C R (Localization.Away r)).base x) =
        PrimeSpectrum.comap (algebraMap R (Localization.Away r))
          (relCurveBasePoint C (Localization.Away r) x) := by
      change (relCurveMap C R (Localization.Away r) ≫
        (snd C (overSpec k R)).left) x = _
      rw [relCurveMap_snd]
      rfl
    have hmem : relCurveBasePoint C R (f.base x) ∈ PrimeSpectrum.basicOpen r := by
      change relCurveBasePoint C R
        ((relCurveMap C R (Localization.Away r)).base x) ∈ PrimeSpectrum.basicOpen r
      rw [hbase]
      have hrange : PrimeSpectrum.comap (algebraMap R (Localization.Away r))
          (relCurveBasePoint C (Localization.Away r) x) ∈
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) :=
        ⟨_, rfl⟩
      rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at hrange
    change f.base x ∈ W.1
    exact htube ⟨hmem, hx'⟩
  have hrange : Set.range ((Wr.ι ≫ f).base) ⊆ Set.range W.1.ι.base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨f.base x.1, x.2⟩, rfl⟩
  let fw : (Wr : Scheme.{u}) ⟶ (W.1 : Scheme.{u}) :=
    IsOpenImmersion.lift W.1.ι (Wr.ι ≫ f) hrange
  have hfw : fw ≫ W.1.ι = Wr.ι ≫ f :=
    IsOpenImmersion.lift_fac W.1.ι (Wr.ι ≫ f) hrange
  have hpicr : Scheme.CechPic.map Wr.ι dr.picClass = 1 := by
    calc
      Scheme.CechPic.map Wr.ι dr.picClass
          = Scheme.CechPic.map Wr.ι (Scheme.CechPic.map f d.picClass) := by
              simp only [dr, Scheme.LocalEquations.picClass_pullback]
      _ = Scheme.CechPic.map (Wr.ι ≫ f) d.picClass := by
            rw [Scheme.CechPic.map_comp, MonoidHom.comp_apply]
      _ = Scheme.CechPic.map (fw ≫ W.1.ι) d.picClass := by rw [hfw]
      _ = Scheme.CechPic.map fw (Scheme.CechPic.map W.1.ι d.picClass) := by
            rw [Scheme.CechPic.map_comp, MonoidHom.comp_apply]
      _ = 1 := by rw [hpic, map_one]
  simpa only [f, hreg, dr, Wr] using
    AffAdaptation.exists_swallowedBy_of_cechPicMap_ι_eq_one dr hWraff hsub hpicr

end Scheme.LocalEquations

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}

/-- Every prime admits an away-local swallowed widened adaptation of a generator seed,
with no field-size, coordinate-change, or subordination hypothesis. -/
theorem exists_away_affAdaptation_swallowedBy
    (D : ThetaGeneratorSeed C R pi a K) (hD : D.IsGenerator)
    (p : PrimeSpectrum R) :
    ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ (Dr : AffCoverData C (Localization.Away r))
        (_ : AffAdaptation Dr
          ((D.localEquations hD).pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) (D.localEquations hD)))),
        Dr.SwallowedBy
          ((D.localEquations hD).pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) (D.localEquations hD))) :=
  Scheme.LocalEquations.exists_away_affAdaptation_swallowedBy_of_finite_fibre
    C R pi (D.localEquations hD) p (D.fibre_supportLocus_finite_aff hD p)

end ThetaGeneratorSeed
end AlgebraicGeometry
