/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUniv
import AlgebraicJacobian.Picard.DivSchemeSeedUnivPulledDegree
import AlgebraicJacobian.Picard.DivisorFamilyAffSeedEndpoint
import AlgebraicJacobian.Picard.DivisorFamilyAffStalkEval
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaSwallowed
import AlgebraicJacobian.Picard.DivSchemeCertZarTransport

/-!
# The universal widened rank datum

The widened seed endpoint asks for the rank of the colength on the one affine piece which
swallows the divisor support.  For the high-window universal seed that datum is already forced
by its certificate-free residue-fibre degree theorem.  This file transports that theorem through
the widened colength base-change equivalence and the swallowed-cover collapse.

The main theorem has exactly the cover/adaptation/support binders required by
`exists_isCertified_of_seed_of_swallowing_affineOpen`; it introduces no certificate or rank
hypothesis.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace ThetaGeneratorSeed

section AffPullback

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}

/-- A widened adaptation and the raw seed construction pull back the same local equations.
The regularity witnesses differ, but proof irrelevance makes the resulting systems equal. -/
theorem aff_pulledEquations_eq_residueFibreLocalEquations
    (D : ThetaGeneratorSeed C R pi a K) (hD : D.IsGenerator)
    {Dc : AffCoverData C R} (A : AffAdaptation Dc (D.localEquations hD))
    (hproj : ∀ l, Module.Projective R (A.colength l)) (p : PrimeSpectrum R) :
    A.pulledEquations p.asIdeal.ResidueField hproj =
      D.residueFibreLocalEquations hD p := by
  rfl

end AffPullback

end ThetaGeneratorSeed

namespace AffAdaptation

section SwallowedPulledDegree

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {Dc : AffCoverData C R} {d : (relCurve C R).LocalEquations}

noncomputable local instance instIsIntegralRelCurveSwallowedPulledDegree
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveSwallowedPulledDegree
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveSwallowedPulledDegree
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

set_option maxHeartbeats 2400000 in
-- The pulled CRT identity and both dependent base-change equivalences elaborate together.
set_option synthInstance.maxHeartbeats 300000 in
/-- On a swallowed widened cover, degree of the pulled presentation computes the stalk rank of
the swallowing colength.  This is independent of the seed which produced the equations. -/
theorem rankAtStalk_colength_eq_of_swallowedBy_of_pulled_degree
    (A : AffAdaptation Dc d) {n : Nat} (j0 : Dc.index)
    (hsub : d.supportLocus ⊆ (Dc.pieces j0 : Set (relCurve C R)))
    (hmiss : ∀ l : Dc.index, l ≠ j0 →
      Disjoint d.supportLocus (Dc.pieces l : Set (relCurve C R)))
    (hfin : ∀ l, Module.Finite R (A.colength l))
    (hproj : ∀ l, Module.Projective R (A.colength l)) (p : PrimeSpectrum R)
    (hdeg : CurveDivisor.deg p.asIdeal.ResidueField
      (Scheme.presentationDivisor p.asIdeal.ResidueField
        ((A.pulledEquations p.asIdeal.ResidueField hproj).presentation)) = (n : ℤ)) :
    Module.rankAtStalk (R := R) (A.colength j0) p = n := by
  classical
  let dκ := A.pulledEquations p.asIdeal.ResidueField hproj
  let Aκ := A.pullback p.asIdeal.ResidueField hproj
  have hsuppκ : dκ.supportLocus =
      (relCurveMap C R p.asIdeal.ResidueField).base ⁻¹' d.supportLocus := by
    exact Scheme.LocalEquations.supportLocus_pullback
      (relCurveMap C R p.asIdeal.ResidueField) d _
  have hsubκ : dκ.supportLocus ⊆
      ((Dc.baseChange p.asIdeal.ResidueField).pieces j0 :
        Set (relCurve C p.asIdeal.ResidueField)) := by
    rw [hsuppκ]
    exact Set.preimage_mono hsub
  have hmissκ : ∀ l : (Dc.baseChange p.asIdeal.ResidueField).index, l ≠ j0 →
      Disjoint dκ.supportLocus
        ((Dc.baseChange p.asIdeal.ResidueField).pieces l :
          Set (relCurve C p.asIdeal.ResidueField)) := by
    intro l hl
    rw [hsuppκ]
    exact (hmiss l hl).preimage (relCurveMap C R p.asIdeal.ResidueField).base
  have hswκ : (Dc.baseChange p.asIdeal.ResidueField).SwallowedBy dκ :=
    ⟨j0, hsubκ, hmissκ⟩
  have hdegFinrank : CurveDivisor.deg p.asIdeal.ResidueField
      (Scheme.presentationDivisor p.asIdeal.ResidueField dκ.presentation) =
        (Module.finrank p.asIdeal.ResidueField Aκ.Glued : ℤ) := by
    exact Aκ.deg_presentationDivisor
  have hfinrankGlued : Module.finrank p.asIdeal.ResidueField Aκ.Glued = n := by
    exact_mod_cast hdegFinrank.symm.trans hdeg
  let eGlued : Aκ.Glued ≃ₗ[p.asIdeal.ResidueField] Aκ.colength j0 :=
    (Aκ.gluedEquivChartProd_of_swallowedBy hswκ).trans
      (Aκ.chartProdEquivSwallowingPiece hmissκ)
  have hfinrankColengthκ :
      Module.finrank p.asIdeal.ResidueField (Aκ.colength j0) = n := by
    rw [← eGlued.finrank_eq]
    exact hfinrankGlued
  have hfinrankTensor : Module.finrank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] A.colength j0) = n := by
    rw [LinearEquiv.finrank_eq
      (A.colengthBaseChange p.asIdeal.ResidueField hproj j0).toLinearEquiv]
    exact hfinrankColengthκ
  haveI : Module.Free p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] A.colength j0) :=
    Module.Free.of_divisionRing p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] A.colength j0)
  have hrankκ : Module.rankAtStalk (R := p.asIdeal.ResidueField)
      (p.asIdeal.ResidueField ⊗[R] A.colength j0)
      (⊥ : PrimeSpectrum p.asIdeal.ResidueField) = n := by
    rw [congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := p.asIdeal.ResidueField)
      (M := p.asIdeal.ResidueField ⊗[R] A.colength j0))
        (⊥ : PrimeSpectrum p.asIdeal.ResidueField)]
    exact hfinrankTensor
  have hcomap : PrimeSpectrum.comap (algebraMap R p.asIdeal.ResidueField)
      (⊥ : PrimeSpectrum p.asIdeal.ResidueField) = p := by
    apply PrimeSpectrum.ext
    change RingHom.ker (algebraMap R p.asIdeal.ResidueField) = p.asIdeal
    exact Ideal.ker_algebraMap_residueField (R := R) (I := p.asIdeal)
  haveI : Module.Finite R (A.colength j0) := hfin j0
  rw [← hcomap, ← Module.rankAtStalk_baseChange]
  exact hrankκ

end SwallowedPulledDegree

end AffAdaptation

namespace PointwiseAchiever

section UniversalAffRank

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivAffRank :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k
    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k
    ((windowS_choice pi hpi g • fiberWeilDivisor pi) +
      (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

noncomputable local instance instIsIntegralRelCurveUnivAffRank
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveUnivAffRank
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveUnivAffRank
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j

set_option maxHeartbeats 2400000 in
-- Unfolding the high-window abbreviation exposes the full pointwise RD-N proof.
set_option synthInstance.maxHeartbeats 800000 in
/-- The certificate-free residue pullback of the abbreviated high-window universal seed has
degree `g`. -/
theorem deg_presentationDivisor_residueFibreLocalEquations_univSeed
    (hb : 0 < windowBound pi hpi) (p : PrimeSpectrum RZ) :
    CurveDivisor.deg p.asIdeal.ResidueField
      (Scheme.presentationDivisor p.asIdeal.ResidueField
        ((ThetaGeneratorSeed.residueFibreLocalEquations
          (univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)
          (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb) p).presentation)) =
      (g : ℤ) := by
  exact deg_presentationDivisor_residueFibreLocalEquations_pointwiseGeneratorSeed
    C hpi g r1 r2 b1 b2 i j hO hchi
      (pointwiseSeedRDN_of_highWindow
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb) p

set_option maxHeartbeats 2400000 in
-- The residue-fibre degree transport unfolds the dependent universal seed.
set_option synthInstance.maxHeartbeats 800000 in
/-- The residue pullback of the universal seed has degree `g` when the curve Euler
characteristic is normalized by an independent parameter `gamma ≤ g`. -/
theorem deg_presentationDivisor_residueFibreLocalEquations_univSeed_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (p : PrimeSpectrum RZ) :
    CurveDivisor.deg p.asIdeal.ResidueField
      (Scheme.presentationDivisor p.asIdeal.ResidueField
        ((ThetaGeneratorSeed.residueFibreLocalEquations
          (univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)
          (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)
          p).presentation)) = (g : ℤ) := by
  exact deg_presentationDivisor_residueFibreLocalEquations_pointwiseGeneratorSeed_at
    C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
      (pointwiseSeedRDN_of_highWindow_at
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma) p

set_option maxHeartbeats 8000000 in
-- The universal chart ring and fibre-regular projectivity proof carry large dependent types.
set_option synthInstance.maxHeartbeats 800000 in
/-- **The exact widened rank producer for the high-window universal seed.**  On every widened
cover and every adaptation of the universal seed equations, the colength of a piece swallowing
the support has stalk rank `g`.

Finiteness comes from the swallowed shape, projectivity from the seed's fibre regularity, and
the rank is computed after base change to `κ(p)`: the pulled swallowed cover collapses its glued
module to the distinguished colength, while the certificate-free universal residue divisor has
degree `g`. -/
theorem rankAtStalk_colength_univSeed_of_swallowedBy (hb : 0 < windowBound pi hpi)
    (Dc : AffCoverData C RZ)
    (A : AffAdaptation Dc
      ((univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
        (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)))
    (j0 : Dc.index)
    (hsub :
      ((univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
        (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)).supportLocus
          ⊆ (Dc.pieces j0 : Set (relCurve C RZ)))
    (hmiss : ∀ l : Dc.index, l ≠ j0 →
      Disjoint
        ((univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
          (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)).supportLocus
        (Dc.pieces l : Set (relCurve C RZ)))
    (p : PrimeSpectrum RZ) :
    Module.rankAtStalk (R := RZ) (A.colength j0) p = g := by
  classical
  let D := univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb
  let hD := isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb
  let d := D.localEquations hD
  have hsw : Dc.SwallowedBy d := ⟨j0, hsub, hmiss⟩
  have hfin : ∀ l, Module.Finite RZ (A.colength l) :=
    A.forall_finite_colength_of_swallowedBy hsw
  have hproj : ∀ l, Module.Projective RZ (A.colength l) := fun l => by
    haveI := hfin l
    exact A.projective_colength_of_forall_tmul_residueField l
      (fun q => D.affAdaptation_fibre_regular hD Dc A l q)
  have hpull := D.aff_pulledEquations_eq_residueFibreLocalEquations hD A hproj p
  have hdeg : CurveDivisor.deg p.asIdeal.ResidueField
      (Scheme.presentationDivisor p.asIdeal.ResidueField
        ((A.pulledEquations p.asIdeal.ResidueField hproj).presentation)) = (g : ℤ) := by
    rw [hpull]
    exact deg_presentationDivisor_residueFibreLocalEquations_univSeed
      C hpi g r1 r2 b1 b2 i j hO hchi hb p
  exact A.rankAtStalk_colength_eq_of_swallowedBy_of_pulled_degree
    j0 hsub hmiss hfin hproj p hdeg

set_option maxHeartbeats 8000000 in
-- The widened rank producer combines dependent pulled equations and stalk data.
set_option synthInstance.maxHeartbeats 800000 in
/-- The exact universal affine rank producer at independent curve parameter `gamma ≤ g`.
The colength rank remains the certified divisor degree `g`. -/
theorem rankAtStalk_colength_univSeed_of_swallowedBy_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (Dc : AffCoverData C RZ)
    (A : AffAdaptation Dc
      ((univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
        (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)))
    (j0 : Dc.index)
    (hsub :
      ((univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
        (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)).supportLocus
          ⊆ (Dc.pieces j0 : Set (relCurve C RZ)))
    (hmiss : ∀ l : Dc.index, l ≠ j0 →
      Disjoint
        ((univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
          (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)).supportLocus
        (Dc.pieces l : Set (relCurve C RZ)))
    (p : PrimeSpectrum RZ) :
    Module.rankAtStalk (R := RZ) (A.colength j0) p = g := by
  classical
  let D := univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
  let hD := isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
  let d := D.localEquations hD
  have hsw : Dc.SwallowedBy d := ⟨j0, hsub, hmiss⟩
  have hfin : ∀ l, Module.Finite RZ (A.colength l) :=
    A.forall_finite_colength_of_swallowedBy hsw
  have hproj : ∀ l, Module.Projective RZ (A.colength l) := fun l => by
    haveI := hfin l
    exact A.projective_colength_of_forall_tmul_residueField l
      (fun q => D.affAdaptation_fibre_regular hD Dc A l q)
  have hpull := D.aff_pulledEquations_eq_residueFibreLocalEquations hD A hproj p
  have hdeg : CurveDivisor.deg p.asIdeal.ResidueField
      (Scheme.presentationDivisor p.asIdeal.ResidueField
        ((A.pulledEquations p.asIdeal.ResidueField hproj).presentation)) = (g : ℤ) := by
    rw [hpull]
    exact deg_presentationDivisor_residueFibreLocalEquations_univSeed_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma p
  exact A.rankAtStalk_colength_eq_of_swallowedBy_of_pulled_degree
    j0 hsub hmiss hfin hproj p hdeg

end UniversalAffRank

end PointwiseAchiever

end AlgebraicGeometry
