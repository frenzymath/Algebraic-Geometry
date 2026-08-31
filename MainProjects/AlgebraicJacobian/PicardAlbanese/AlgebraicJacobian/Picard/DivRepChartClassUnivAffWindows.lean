/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffCertified
import AlgebraicJacobian.Picard.DivRepChartClassUnivQuot
import AlgebraicJacobian.Picard.DivisorFamilyAffFraming
import AlgebraicJacobian.Picard.DivisorFamilyAffWindowMapRank

/-!
# Universal widened window comparison

The two pinned windows of a universal divisor-chart class agree after arbitrary base change with
the intrinsic windows of any certified representative of that class.  The declarations are kept
separate from the final classifier theorem so their dependent quotient proofs compile once.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Grassmannian Scheme ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace PointwiseAchiever

section UniversalAffWindows

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivAffWindows :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))

local notation "b2c" => b2.map (windowShiftEquiv hpi g).symm
local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2c i j

/-- The local-certification proof packaged by the universal widened chart class. -/
theorem isLocallyCertifiedAff_univSeed (i : (glueData k g r1).J)
    (j : (glueData k g r2).J) (hb : 0 < windowBound pi hpi) :
    IsLocallyCertifiedAff g
      (univSystemAff C hpi g r1 r2 b1 b2c i j hO hchi hb) :=
  ThetaGeneratorSeed.isLocallyCertifiedAff_of_forall_prime_certified_adaptation
    (isGenerator_univSeed C hpi g r1 r2 b1 b2c i j hO hchi hb)
    (exists_away_isCertified_univSeedAff
      C hpi g r1 r2 b1 b2c i j hO hchi hb)

@[simp]
theorem divFamZarAffUniv_eq_mk (i : (glueData k g r1).J)
    (j : (glueData k g r2).J) (hb : 0 < windowBound pi hpi) :
    divFamZarAffUniv C hpi g r1 r2 b1 b2c i j hO hchi hb =
      DivFamZarAff.mk
        (univSystemAff C hpi g r1 r2 b1 b2c i j hO hchi hb)
        (isLocallyCertifiedAff_univSeed
          C hpi g r1 r2 b1 b2 hO hchi i j hb) :=
  rfl

/-- The local-certification proof for the universal class at independent curve parameter
`gamma ≤ g`. -/
theorem isLocallyCertifiedAff_univSeed_at (i : (glueData k g r1).J)
    (j : (glueData k g r2).J) {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    IsLocallyCertifiedAff g
      (univSystemAff_at C hpi g r1 r2 b1 b2c i j hgamma hchiGamma) :=
  ThetaGeneratorSeed.isLocallyCertifiedAff_of_forall_prime_certified_adaptation
    (isGenerator_univSeed_at C hpi g r1 r2 b1 b2c i j hgamma hchiGamma)
    (exists_away_isCertified_univSeedAff_at
      C hpi g r1 r2 b1 b2c i j hgamma hchiGamma)

@[simp]
theorem divFamZarAffUniv_at_eq_mk (i : (glueData k g r1).J)
    (j : (glueData k g r2).J) {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    divFamZarAffUniv_at C hpi g r1 r2 b1 b2c i j hgamma hchiGamma =
      DivFamZarAff.mk
        (univSystemAff_at C hpi g r1 r2 b1 b2c i j hgamma hchiGamma)
        (isLocallyCertifiedAff_univSeed_at
          C hpi g r1 r2 b1 b2 i j hgamma hchiGamma) :=
  rfl

set_option maxHeartbeats 4000000 in
-- The dependent pullback predicate traverses the relative-curve section-ring tower.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
/-- The regularity predicate for the pulled universal equation system. -/
abbrev pullbackRegularity
    {R : Type u} [CommRing R] [Algebra k R]
    (d : (relCurve C R).LocalEquations)
    (T : Type u) [CommRing T] [Algebra k T] [Algebra R T]
    [IsScalarTower k R T] : Prop :=
  ∀ (y z : relCurve C T)
    (hz : z ∈ (d.cover.pullback (relCurveMap C R T)).opens y),
    ((relCurve C T).presheaf.germ
      ((d.cover.pullback (relCurveMap C R T)).opens y) z hz).hom
        (Scheme.LocalEquations.pullbackEqn (relCurveMap C R T) d y)
      ∈ nonZeroDivisors ((relCurve C T).presheaf.stalk z)

set_option maxHeartbeats 4000000 in
-- The helper matches two dependent window quotients across the induced scalar tower.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
include hO hchi in
/-- The certificate/rank half of a universal window comparison. -/
theorem divisorWindow_eq_map_of_divEq
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    (T : Type u) [CommRing T] [Algebra k T]
    (alpha : ChartRing i0 j0 →ₐ[k] T)
    (a : Nat)
    (ha1 : Subsingleton (relTwistPair C k pi
      (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a)
    (x : Grassmannian.grFunctorAff k
      (↥(divisorSections k (a • fiberWeilDivisor pi) ⊤)) g (ChartRing i0 j0))
    (d : (relCurve C (ChartRing i0 j0)).LocalEquations)
    (G : CertifiedDivisorFamilyAff C T g)
    (hx : x.toSubmodule ≤ divisorWindow d ha1) :
    letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
    letI : IsScalarTower k (ChartRing i0 j0) T :=
      .of_algebraMap_eq fun r => (alpha.commutes r).symm
    ∀ (hreg : pullbackRegularity C d T),
      G.eqns.DivEq (d.pullback (relCurveMap C (ChartRing i0 j0) T) hreg) →
      divisorWindow G.eqns ha1 =
        (Module.Grassmannian.map alpha x).toSubmodule := by
  letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
  letI : IsScalarTower k (ChartRing i0 j0) T :=
    .of_algebraMap_eq fun r => (alpha.commutes r).symm
  intro hreg hdiv
  have hpull : windowBaseChange T (divisorWindow d ha1) ≤
      divisorWindow G.eqns ha1 :=
    (windowBaseChange_divisorWindow_le C T pi a hreg ha1).trans_eq
      (divisorWindow_eq_of_divEq hdiv ha1).symm
  exact CertifiedDivisorFamilyAff.divisorWindow_eq_map_of_baseChange_le
    hpi g hO hchi alpha G a ha1 hMa x (divisorWindow d ha1) hx hpull

set_option maxHeartbeats 4000000 in
-- The helper matches off-diagonal dependent window quotients across the scalar tower.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
/-- The certificate/rank half of an off-diagonal universal window comparison. -/
theorem divisorWindow_eq_map_of_divEq_at
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (T : Type u) [CommRing T] [Algebra k T]
    (alpha : ChartRing i0 j0 →ₐ[k] T)
    (a : Nat)
    (ha1 : Subsingleton (relTwistPair C k pi
      (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a)
    (x : Grassmannian.grFunctorAff k
      (↥(divisorSections k (a • fiberWeilDivisor pi) ⊤)) g (ChartRing i0 j0))
    (d : (relCurve C (ChartRing i0 j0)).LocalEquations)
    (G : CertifiedDivisorFamilyAff C T g)
    (hx : x.toSubmodule ≤ divisorWindow d ha1) :
    letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
    letI : IsScalarTower k (ChartRing i0 j0) T :=
      .of_algebraMap_eq fun r => (alpha.commutes r).symm
    ∀ (hreg : pullbackRegularity C d T),
      G.eqns.DivEq (d.pullback (relCurveMap C (ChartRing i0 j0) T) hreg) →
      divisorWindow G.eqns ha1 =
        (Module.Grassmannian.map alpha x).toSubmodule := by
  letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
  letI : IsScalarTower k (ChartRing i0 j0) T :=
    .of_algebraMap_eq fun r => (alpha.commutes r).symm
  intro hreg hdiv
  have hpull : windowBaseChange T (divisorWindow d ha1) ≤
      divisorWindow G.eqns ha1 :=
    (windowBaseChange_divisorWindow_le C T pi a hreg ha1).trans_eq
      (divisorWindow_eq_of_divEq hdiv ha1).symm
  exact CertifiedDivisorFamilyAff.divisorWindow_eq_map_of_baseChange_le_at
    hpi g hgamma hchiGamma alpha G a ha1 hMa x (divisorWindow d ha1) hx hpull

set_option maxHeartbeats 4000000 in
-- The first pinned window instantiates the dependent quotient comparison.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
include hO hchi in
/-- First pinned window comparison, compiled independently from the second window. -/
theorem universalFstWindow_eq_map
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    (T : Type u) [CommRing T] [Algebra k T]
    (alpha : ChartRing i0 j0 →ₐ[k] T)
    (G : CertifiedDivisorFamilyAff C T g)
    (d : (relCurve C (ChartRing i0 j0)).LocalEquations)
    (hfst : (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0).toSubmodule ≤
      divisorWindow d (relThetaPairH1_windowM C pi hpi g)) :
    letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
    letI : IsScalarTower k (ChartRing i0 j0) T :=
      .of_algebraMap_eq fun r => (alpha.commutes r).symm
    ∀ (hreg : pullbackRegularity C d T),
      G.eqns.DivEq (d.pullback (relCurveMap C (ChartRing i0 j0) T) hreg) →
      (G.eps hpi g).1 =
        (Module.Grassmannian.map alpha
          (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule := by
  letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
  letI : IsScalarTower k (ChartRing i0 j0) T :=
    .of_algebraMap_eq fun r => (alpha.commutes r).symm
  intro hreg hdiv
  rw [CertifiedDivisorFamilyAff.eps_fst]
  exact (divisorWindow_eq_map_of_divEq
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) (hO := hO) (hchi := hchi)
    i0 j0 T alpha (windowM_choice pi hpi g)
    (relThetaPairH1_windowM C pi hpi g) le_rfl
    (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0)
    d G hfst) hreg hdiv

set_option maxHeartbeats 4000000 in
-- The first pinned window instantiates the off-diagonal quotient comparison.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
/-- First pinned window comparison at independent curve parameter `gamma ≤ g`. -/
theorem universalFstWindow_eq_map_at
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (T : Type u) [CommRing T] [Algebra k T]
    (alpha : ChartRing i0 j0 →ₐ[k] T)
    (G : CertifiedDivisorFamilyAff C T g)
    (d : (relCurve C (ChartRing i0 j0)).LocalEquations)
    (hfst : (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0).toSubmodule ≤
      divisorWindow d (relThetaPairH1_windowM C pi hpi g)) :
    letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
    letI : IsScalarTower k (ChartRing i0 j0) T :=
      .of_algebraMap_eq fun r => (alpha.commutes r).symm
    ∀ (hreg : pullbackRegularity C d T),
      G.eqns.DivEq (d.pullback (relCurveMap C (ChartRing i0 j0) T) hreg) →
      (G.eps hpi g).1 =
        (Module.Grassmannian.map alpha
          (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule := by
  letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
  letI : IsScalarTower k (ChartRing i0 j0) T :=
    .of_algebraMap_eq fun r => (alpha.commutes r).symm
  intro hreg hdiv
  rw [CertifiedDivisorFamilyAff.eps_fst]
  exact (divisorWindow_eq_map_of_divEq_at
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) i0 j0 hgamma hchiGamma T alpha
    (windowM_choice pi hpi g)
    (relThetaPairH1_windowM C pi hpi g) le_rfl
    (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0)
    d G hfst) hreg hdiv

set_option maxHeartbeats 4000000 in
-- The shifted pinned window instantiates the same dependent quotient comparison.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
include hO hchi in
/-- Second pinned window comparison, compiled independently from the first window. -/
theorem universalSndWindow_eq_map
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    (T : Type u) [CommRing T] [Algebra k T]
    (alpha : ChartRing i0 j0 →ₐ[k] T)
    (G : CertifiedDivisorFamilyAff C T g)
    (d : (relCurve C (ChartRing i0 j0)).LocalEquations)
    (hsnd : (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0).toSubmodule ≤
      divisorWindow d (relThetaPairH1_windowMS C pi hpi g)) :
    letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
    letI : IsScalarTower k (ChartRing i0 j0) T :=
      .of_algebraMap_eq fun r => (alpha.commutes r).symm
    ∀ (hreg : pullbackRegularity C d T),
      G.eqns.DivEq (d.pullback (relCurveMap C (ChartRing i0 j0) T) hreg) →
      (G.eps hpi g).2 =
        (Module.Grassmannian.map alpha
          (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule := by
  letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
  letI : IsScalarTower k (ChartRing i0 j0) T :=
    .of_algebraMap_eq fun r => (alpha.commutes r).symm
  intro hreg hdiv
  rw [CertifiedDivisorFamilyAff.eps_snd]
  exact (divisorWindow_eq_map_of_divEq
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) (hO := hO) (hchi := hchi)
    i0 j0 T alpha (windowM_choice pi hpi g + windowS_choice pi hpi g)
    (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _)
    (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)
    d G hsnd) hreg hdiv

set_option maxHeartbeats 4000000 in
-- The shifted pinned window instantiates the off-diagonal quotient comparison.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
/-- Second pinned window comparison at independent curve parameter `gamma ≤ g`. -/
theorem universalSndWindow_eq_map_at
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (T : Type u) [CommRing T] [Algebra k T]
    (alpha : ChartRing i0 j0 →ₐ[k] T)
    (G : CertifiedDivisorFamilyAff C T g)
    (d : (relCurve C (ChartRing i0 j0)).LocalEquations)
    (hsnd : (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0).toSubmodule ≤
      divisorWindow d (relThetaPairH1_windowMS C pi hpi g)) :
    letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
    letI : IsScalarTower k (ChartRing i0 j0) T :=
      .of_algebraMap_eq fun r => (alpha.commutes r).symm
    ∀ (hreg : pullbackRegularity C d T),
      G.eqns.DivEq (d.pullback (relCurveMap C (ChartRing i0 j0) T) hreg) →
      (G.eps hpi g).2 =
        (Module.Grassmannian.map alpha
          (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule := by
  letI : Algebra (ChartRing i0 j0) T := alpha.toAlgebra
  letI : IsScalarTower k (ChartRing i0 j0) T :=
    .of_algebraMap_eq fun r => (alpha.commutes r).symm
  intro hreg hdiv
  rw [CertifiedDivisorFamilyAff.eps_snd]
  exact (divisorWindow_eq_map_of_divEq_at
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) i0 j0 hgamma hchiGamma T alpha
    (windowM_choice pi hpi g + windowS_choice pi hpi g)
    (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _)
    (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)
    d G hsnd) hreg hdiv

end UniversalAffWindows

end PointwiseAchiever

end AlgebraicGeometry
