/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffRank
import AlgebraicJacobian.Picard.DivisorFamilyAffFibreTower

/-!
# The universal widened rank after an away localization

The support-tube construction produces a swallowed widened adaptation only after an away
localization of the universal chart ring.  This file transports the already-computed universal
residue-fibre degree through that localization and feeds it to the swallowed-cover rank theorem.

The transport is seed-generic.  At a prime `q` of the away localization, its contraction `p`
has a canonical residue-field map `kappa(p) -> kappa(q)`.  Pullback functoriality identifies the
twice-pulled seed class with base change of the residue-fibre class at `p`, and base-field
invariance of `classDeg` preserves its degree.  No certificate, rank, coordinate, or cover
subordination hypothesis is introduced.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace ThetaGeneratorSeed

section AwayDegree

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}

local instance instIsOpenImmersionRelCurveMapAwayDegree (r : R) :
    IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
  isOpenImmersion_relCurveMap_away C R (Localization.Away r) r

noncomputable local instance instIsIntegralRelCurveAwayDegree
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveAwayDegree
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveAwayDegree
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveAwayDegree
    (L : Type u) [Field L] [Algebra k L] :
    LocallyOfFiniteType (relCurve C L ↘ Spec (.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveAwayDegree
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveAwayDegree
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 4000000 in
-- The two residue fields, three coefficient towers, and class-degree transition elaborate
-- together in the generic transport statement.
set_option synthInstance.maxHeartbeats 800000 in
/-- The presentation degree of an away-local adaptation at `q` is the presentation degree of
the original seed on the residue fibre at the contraction of `q`.

This is independent of the widened cover and of the adapted equations: those enter only through
the fact that `pulledEquations` is the pullback of the away-local seed system. -/
theorem deg_presentationDivisor_pulledEquations_away_eq_residueFibre
    (D : ThetaGeneratorSeed C R pi a K) (hD : D.IsGenerator) (r : R)
    (Dc : AffCoverData C (Localization.Away r))
    (A : AffAdaptation Dc
      ((D.localEquations hD).pullback
        (relCurveMap C R (Localization.Away r))
        (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
          (relCurveMap C R (Localization.Away r)) (D.localEquations hD))))
    (hproj : ∀ l, Module.Projective (Localization.Away r) (A.colength l))
    (q : PrimeSpectrum (Localization.Away r)) :
    CurveDivisor.deg q.asIdeal.ResidueField
        (Scheme.presentationDivisor q.asIdeal.ResidueField
          ((A.pulledEquations q.asIdeal.ResidueField hproj).presentation)) =
      let p := PrimeSpectrum.comap (algebraMap R (Localization.Away r)) q
      CurveDivisor.deg p.asIdeal.ResidueField
        (Scheme.presentationDivisor p.asIdeal.ResidueField
          ((D.residueFibreLocalEquations hD p).presentation)) := by
  classical
  let S := Localization.Away r
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let Kp := p.asIdeal.ResidueField
  let Kq := q.asIdeal.ResidueField
  let phi : Kp →ₐ[k] Kq :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal
      (IsScalarTower.toAlgHom k R S) rfl
  letI : Algebra Kp Kq := phi.toRingHom.toAlgebra
  haveI : IsScalarTower k Kp Kq :=
    IsScalarTower.of_algebraMap_eq fun x => (phi.commutes x).symm
  haveI : IsScalarTower R Kp Kq := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap R Kq x = phi (algebraMap R Kp x)
    rw [Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map_algebraMap]
    exact IsScalarTower.algebraMap_apply R S Kq x
  let d := D.localEquations hD
  let dS := d.pullback (relCurveMap C R S)
    (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
      (relCurveMap C R S) d)
  let dq := A.pulledEquations Kq hproj
  let dp := D.residueFibreLocalEquations hD p
  have hphi : (Algebra.ofId Kp Kq).restrictScalars k = phi :=
    AlgHom.ext fun _ => rfl
  have hcurve : relCurveMap C Kp Kq = (C ◁ Over.overSpecMap phi).left := by
    rw [relCurveMap_eq_cg, hphi]
  have hpic : dq.picClass = Scheme.CechPic.map (relCurveMap C Kp Kq) dp.picClass := by
    calc
      dq.picClass = Scheme.CechPic.map (relCurveMap C S Kq) dS.picClass := by
        exact A.picClass_pulledEquations Kq hproj
      _ = Scheme.CechPic.map (relCurveMap C S Kq)
          (Scheme.CechPic.map (relCurveMap C R S) d.picClass) := by
        simp only [dS, Scheme.LocalEquations.picClass_pullback]
      _ = Scheme.CechPic.map
          (relCurveMap C S Kq ≫ relCurveMap C R S) d.picClass := by
        rw [Scheme.CechPic.map_comp, MonoidHom.comp_apply]
      _ = Scheme.CechPic.map (relCurveMap C R Kq) d.picClass := by
        rw [relCurveMap_comp (R' := S) (R'' := Kq)]
      _ = Scheme.CechPic.map
          (relCurveMap C Kp Kq ≫ relCurveMap C R Kp) d.picClass := by
        rw [relCurveMap_comp (R' := Kp) (R'' := Kq)]
      _ = Scheme.CechPic.map (relCurveMap C Kp Kq)
          (Scheme.CechPic.map (relCurveMap C R Kp) d.picClass) := by
        rw [Scheme.CechPic.map_comp, MonoidHom.comp_apply]
      _ = Scheme.CechPic.map (relCurveMap C Kp Kq) dp.picClass := by
        simp only [dp, d, Kp, residueFibreLocalEquations,
          Scheme.LocalEquations.picClass_pullback]
  have degree_eq_class (L : Type u) [Field L] [Algebra k L]
      (e : (relCurve C L).LocalEquations) :
      CurveDivisor.deg L (Scheme.presentationDivisor L e.presentation) =
        classDeg L e.picClass := by
    rw [← classDeg_picClass, Scheme.CurveDivisor.picClass_presentationDivisor,
      Scheme.LocalEquations.presentation_picClass]
  change CurveDivisor.deg Kq (Scheme.presentationDivisor Kq dq.presentation) =
    CurveDivisor.deg Kp (Scheme.presentationDivisor Kp dp.presentation)
  calc
    CurveDivisor.deg Kq (Scheme.presentationDivisor Kq dq.presentation) =
        classDeg Kq dq.picClass := degree_eq_class Kq dq
    _ = classDeg Kq (Scheme.CechPic.map (relCurveMap C Kp Kq) dp.picClass) := by
      rw [hpic]
    _ = classDeg Kp dp.picClass := by
      rw [hcurve]
      exact classDeg_cechPicMap_baseFieldTransition C phi dp.picClass
    _ = CurveDivisor.deg Kp (Scheme.presentationDivisor Kp dp.presentation) :=
      (degree_eq_class Kp dp).symm

end AwayDegree

end ThetaGeneratorSeed

namespace PointwiseAchiever

section UniversalAwayRank

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivAffAwayRank :
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

noncomputable local instance instIsIntegralRelCurveUnivAwayRank
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveUnivAwayRank
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveUnivAwayRank
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j

local instance instIsOpenImmersionRelCurveMapUnivAwayRank (r : RZ) :
    IsOpenImmersion (relCurveMap C RZ (Localization.Away r)) :=
  isOpenImmersion_relCurveMap_away C RZ (Localization.Away r) r

set_option maxHeartbeats 8000000 in
-- The universal chart ring, swallowed adaptation, and contracted residue fibre all remain
-- visible in the endpoint's dependent type.
set_option synthInstance.maxHeartbeats 800000 in
/-- On every swallowed adaptation of the away-local universal seed equations, the colength of
the swallowing piece has rank `g` at every stalk of the away localization. -/
theorem rankAtStalk_colength_univSeed_pullback_away_of_swallowedBy
    (hb : 0 < windowBound pi hpi) (r : RZ)
    (Dc : AffCoverData C (Localization.Away r))
    (A : AffAdaptation Dc
      (((univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
        (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)).pullback
          (relCurveMap C RZ (Localization.Away r))
          (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
            (relCurveMap C RZ (Localization.Away r))
            ((univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
              (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)))))
    (j0 : Dc.index)
    (hsub :
      (((univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
        (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)).pullback
          (relCurveMap C RZ (Localization.Away r))
          (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
            (relCurveMap C RZ (Localization.Away r))
            ((univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
              (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)))).supportLocus
        ⊆ (Dc.pieces j0 : Set (relCurve C (Localization.Away r))))
    (hmiss : ∀ l : Dc.index, l ≠ j0 →
      Disjoint
        (((univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
          (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)).pullback
            (relCurveMap C RZ (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C RZ (Localization.Away r))
              ((univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
                (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)))).supportLocus
        (Dc.pieces l : Set (relCurve C (Localization.Away r))))
    (q : PrimeSpectrum (Localization.Away r)) :
    Module.rankAtStalk (R := Localization.Away r) (A.colength j0) q = g := by
  classical
  let D := univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb
  let hD := isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb
  let dR := (D.localEquations hD).pullback
    (relCurveMap C RZ (Localization.Away r))
    (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
      (relCurveMap C RZ (Localization.Away r)) (D.localEquations hD))
  have hsw : Dc.SwallowedBy dR := ⟨j0, hsub, hmiss⟩
  have hfin : ∀ l, Module.Finite (Localization.Away r) (A.colength l) :=
    A.forall_finite_colength_of_swallowedBy hsw
  have hproj : ∀ l, Module.Projective (Localization.Away r) (A.colength l) :=
    A.forall_projective_colength_seed_pullback_away hD r Dc hsw
  have hdegTransport := D.deg_presentationDivisor_pulledEquations_away_eq_residueFibre
    hD r Dc A hproj q
  have hdeg : CurveDivisor.deg q.asIdeal.ResidueField
      (Scheme.presentationDivisor q.asIdeal.ResidueField
        ((A.pulledEquations q.asIdeal.ResidueField hproj).presentation)) = (g : ℤ) := by
    rw [hdegTransport]
    exact deg_presentationDivisor_residueFibreLocalEquations_univSeed
      C hpi g r1 r2 b1 b2 i j hO hchi hb
        (PrimeSpectrum.comap (algebraMap RZ (Localization.Away r)) q)
  exact A.rankAtStalk_colength_eq_of_swallowedBy_of_pulled_degree
    j0 hsub hmiss hfin hproj q hdeg

set_option maxHeartbeats 8000000 in
-- The away-local rank producer transports the dependent seed through localization.
set_option synthInstance.maxHeartbeats 800000 in
/-- Away-local universal rank at independent curve parameter `gamma ≤ g`. -/
theorem rankAtStalk_colength_univSeed_pullback_away_of_swallowedBy_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (r : RZ)
    (Dc : AffCoverData C (Localization.Away r))
    (A : AffAdaptation Dc
      (((univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
        (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)).pullback
          (relCurveMap C RZ (Localization.Away r))
          (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
            (relCurveMap C RZ (Localization.Away r))
            ((univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
              (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)))))
    (j0 : Dc.index)
    (hsub :
      (((univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
        (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)).pullback
          (relCurveMap C RZ (Localization.Away r))
          (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
            (relCurveMap C RZ (Localization.Away r))
            ((univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
              (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)))).supportLocus
        ⊆ (Dc.pieces j0 : Set (relCurve C (Localization.Away r))))
    (hmiss : ∀ l : Dc.index, l ≠ j0 →
      Disjoint
        (((univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
          (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)).pullback
            (relCurveMap C RZ (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C RZ (Localization.Away r))
              ((univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
                (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j
                  hgamma hchiGamma)))).supportLocus
        (Dc.pieces l : Set (relCurve C (Localization.Away r))))
    (q : PrimeSpectrum (Localization.Away r)) :
    Module.rankAtStalk (R := Localization.Away r) (A.colength j0) q = g := by
  classical
  let D := univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
  let hD := isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
  let dR := (D.localEquations hD).pullback
    (relCurveMap C RZ (Localization.Away r))
    (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
      (relCurveMap C RZ (Localization.Away r)) (D.localEquations hD))
  have hsw : Dc.SwallowedBy dR := ⟨j0, hsub, hmiss⟩
  have hfin : ∀ l, Module.Finite (Localization.Away r) (A.colength l) :=
    A.forall_finite_colength_of_swallowedBy hsw
  have hproj : ∀ l, Module.Projective (Localization.Away r) (A.colength l) :=
    A.forall_projective_colength_seed_pullback_away hD r Dc hsw
  have hdegTransport := D.deg_presentationDivisor_pulledEquations_away_eq_residueFibre
    hD r Dc A hproj q
  have hdeg : CurveDivisor.deg q.asIdeal.ResidueField
      (Scheme.presentationDivisor q.asIdeal.ResidueField
        ((A.pulledEquations q.asIdeal.ResidueField hproj).presentation)) = (g : ℤ) := by
    rw [hdegTransport]
    exact deg_presentationDivisor_residueFibreLocalEquations_univSeed_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
        (PrimeSpectrum.comap (algebraMap RZ (Localization.Away r)) q)
  exact A.rankAtStalk_colength_eq_of_swallowedBy_of_pulled_degree
    j0 hsub hmiss hfin hproj q hdeg

end UniversalAwayRank

end PointwiseAchiever

end AlgebraicGeometry
