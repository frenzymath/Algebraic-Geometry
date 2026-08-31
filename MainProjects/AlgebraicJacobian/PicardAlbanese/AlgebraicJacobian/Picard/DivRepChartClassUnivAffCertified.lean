/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffAwayRank
import AlgebraicJacobian.Picard.DivisorFamilyAffPrincipalAway
import AlgebraicJacobian.Picard.DivisorFamilyAffRank
import AlgebraicJacobian.Picard.DivisorFamilyAffSeedGate

/-!
# The widened universal chart class

The Picard-trivial support tube supplies a swallowed adaptation after an away localization.
Seed regularity supplies projectivity, and the universal residue degree supplies rank `g`.
Thus every base prime has a certified away-local adaptation and the universal seed determines
a genuine `DivFamZarAff` class on its carve-chart ring, without additional hypotheses.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace PointwiseAchiever

section UniversalAffCertified

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivAffCertified :
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
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j

/-- The local-equation system underlying the high-window universal seed. -/
noncomputable abbrev univSystemAff (hb : 0 < windowBound pi hpi) :
    (relCurve C RZ).LocalEquations :=
  (univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
    (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)

/-- The universal local-equation system at independent curve parameter `gamma ≤ g`. -/
noncomputable abbrev univSystemAff_at {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    (relCurve C RZ).LocalEquations :=
  (univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
    (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)

set_option maxHeartbeats 8000000 in
-- The chart ring, away pullback, swallowed witness, and universal rank remain dependent.
set_option synthInstance.maxHeartbeats 800000 in
/-- Every chart-ring prime has a certified away-local widened adaptation of the universal
seed equations. -/
theorem exists_away_isCertified_univSeedAff (hb : 0 < windowBound pi hpi)
    (p : PrimeSpectrum RZ) :
    ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C RZ (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C RZ (Localization.Away r) r
      ∃ (Dc : AffCoverData C (Localization.Away r))
        (A : AffAdaptation Dc
          ((univSystemAff C hpi g r1 r2 b1 b2 i j hO hchi hb).pullback
            (relCurveMap C RZ (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C RZ (Localization.Away r))
              (univSystemAff C hpi g r1 r2 b1 b2 i j hO hchi hb)))),
        A.IsCertified g := by
  let D := univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb
  let hD := isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb
  obtain ⟨r, hr, Dc, A, hsw⟩ := D.exists_away_affAdaptation_swallowedBy hD p
  refine ⟨r, hr, Dc, A, ?_⟩
  obtain ⟨j0, hsub, hmiss⟩ := hsw
  have hfin : ∀ l, Module.Finite (Localization.Away r) (A.colength l) :=
    A.forall_finite_colength_of_swallowedBy ⟨j0, hsub, hmiss⟩
  have hproj : ∀ l, Module.Projective (Localization.Away r) (A.colength l) :=
    A.forall_projective_colength_seed_pullback_away hD r Dc ⟨j0, hsub, hmiss⟩
  exact A.isCertified_of_swallowedBy_of_c1_of_rank_piece hsub hmiss hfin hproj
    (rankAtStalk_colength_univSeed_pullback_away_of_swallowedBy
      C hpi g r1 r2 b1 b2 i j hO hchi hb r Dc A j0 hsub hmiss)

set_option maxHeartbeats 8000000 in
-- The per-prime certificate producer unfolds the high-window pointwise seed at every binder.
set_option synthInstance.maxHeartbeats 800000 in
/-- The high-window universal seed defines a widened locally certified class on its chart ring. -/
noncomputable def divFamZarAffUniv (hb : 0 < windowBound pi hpi) :
    DivFamZarAff C RZ g :=
  (univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)
    |>.divFamZarAff_of_forall_prime_certified_adaptation
      (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)
      (exists_away_isCertified_univSeedAff
        C hpi g r1 r2 b1 b2 i j hO hchi hb)

set_option maxHeartbeats 8000000 in
-- The local certificate assembles the widened rank and projectivity data.
set_option synthInstance.maxHeartbeats 800000 in
/-- Every chart-ring prime has an away-local certified adaptation of the off-diagonal
universal seed. The certificate degree is `g`; `gamma` only normalizes curve cohomology. -/
theorem exists_away_isCertified_univSeedAff_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (p : PrimeSpectrum RZ) :
    ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C RZ (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C RZ (Localization.Away r) r
      ∃ (Dc : AffCoverData C (Localization.Away r))
        (A : AffAdaptation Dc
          ((univSystemAff_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).pullback
            (relCurveMap C RZ (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C RZ (Localization.Away r))
              (univSystemAff_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)))),
        A.IsCertified g := by
  let D := univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
  let hD := isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
  obtain ⟨r, hr, Dc, A, hsw⟩ := D.exists_away_affAdaptation_swallowedBy hD p
  refine ⟨r, hr, Dc, A, ?_⟩
  obtain ⟨j0, hsub, hmiss⟩ := hsw
  have hfin : ∀ l, Module.Finite (Localization.Away r) (A.colength l) :=
    A.forall_finite_colength_of_swallowedBy ⟨j0, hsub, hmiss⟩
  have hproj : ∀ l, Module.Projective (Localization.Away r) (A.colength l) :=
    A.forall_projective_colength_seed_pullback_away hD r Dc ⟨j0, hsub, hmiss⟩
  exact A.isCertified_of_swallowedBy_of_c1_of_rank_piece hsub hmiss hfin hproj
    (rankAtStalk_colength_univSeed_pullback_away_of_swallowedBy_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma r Dc A j0 hsub hmiss)

set_option maxHeartbeats 8000000 in
-- The affine class packages the dependent family of away-local certificates.
set_option synthInstance.maxHeartbeats 800000 in
/-- The off-diagonal high-window universal seed defines a locally certified affine class. -/
noncomputable def divFamZarAffUniv_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    DivFamZarAff C RZ g :=
  (univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)
    |>.divFamZarAff_of_forall_prime_certified_adaptation
      (isGenerator_univSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)
      (exists_away_isCertified_univSeedAff_at
        C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)

end UniversalAffCertified

end PointwiseAchiever

end AlgebraicGeometry
