/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivQuot
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaEffective

/-!
# Recovering a mapped Grassmannian window from a widened certificate

A certified widened divisor family has projective intrinsic-window quotients of the prescribed
constant rank.  Consequently, any mapped Grassmannian window contained in the intrinsic window
is equal to it.  This module isolates the certificate-to-rank step from the geometric proof that
supplies the containment after base change.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxSynthPendingDepth 8

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {S T : Type u} [CommRing S] [Algebra k S] [CommRing T] [Algebra k T]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsDominant pi] [IsIntegral C.left]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

namespace CertifiedDivisorFamilyAff

set_option maxHeartbeats 4000000 in
-- The certificate witnesses live behind the dependent intrinsic-theta quotient equivalence.
set_option synthInstance.maxHeartbeats 800000 in
/-- A base-changed Grassmannian window that lies in a certified intrinsic window fills it. -/
theorem divisorWindow_eq_map_of_baseChange_le
    (hpi : pi ≫ P1.structureMap k = C.hom) (g : Nat)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    (alpha : S →ₐ[k] T) (G : CertifiedDivisorFamilyAff C T g)
    (a : Nat)
    (ha1 : Subsingleton (relTwistPair C k pi
      (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a)
    (x : Grassmannian.grFunctorAff k
      (↥(divisorSections k (a • fiberWeilDivisor pi) ⊤)) g S)
    (N : Submodule S (TensorProduct k S
      ↥(divisorSections k (a • fiberWeilDivisor pi) ⊤)))
    (hx : x.toSubmodule ≤ N) :
    letI : Algebra S T := alpha.toAlgebra
    letI : IsScalarTower k S T :=
      .of_algebraMap_eq fun r => (alpha.commutes r).symm
    windowBaseChange T N ≤ divisorWindow G.eqns ha1 →
      divisorWindow G.eqns ha1 =
        (Module.Grassmannian.map alpha x).toSubmodule := by
  letI : Algebra S T := alpha.toAlgebra
  letI : IsScalarTower k S T :=
    .of_algebraMap_eq fun r => (alpha.commutes r).symm
  intro hpull
  have hproj : Module.Projective T
      ((TensorProduct k T
        ↑(divisorSections k (a • fiberWeilDivisor pi) ⊤)) ⧸
          divisorWindow G.eqns ha1) :=
    G.certified.projective_intrinsicWindowQuotient
      (π := pi) G.adaptation a hpi hO hchi ha1 hMa
  have hrank : ∀ p : PrimeSpectrum T,
      Module.rankAtStalk
        ((TensorProduct k T
          ↑(divisorSections k (a • fiberWeilDivisor pi) ⊤)) ⧸
            divisorWindow G.eqns ha1) p = g :=
    fun p => G.certified.rankAtStalk_intrinsicWindowQuotient
      (π := pi) G.adaptation a hpi hO hchi ha1 hMa p
  exact Grassmannian.eq_map_toSubmodule_of_baseChange_le alpha x N
    (divisorWindow G.eqns ha1) hx hpull hproj hrank

set_option maxHeartbeats 4000000 in
-- The certificate witnesses live behind the off-diagonal intrinsic quotient equivalence.
set_option synthInstance.maxHeartbeats 800000 in
/-- A base-changed Grassmannian window fills a certified intrinsic window when the curve
parameter is independent of the certified divisor degree. -/
theorem divisorWindow_eq_map_of_baseChange_le_at
    (hpi : pi ≫ P1.structureMap k = C.hom) (g : Nat)
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (alpha : S →ₐ[k] T) (G : CertifiedDivisorFamilyAff C T g)
    (a : Nat)
    (ha1 : Subsingleton (relTwistPair C k pi
      (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a)
    (x : Grassmannian.grFunctorAff k
      (↥(divisorSections k (a • fiberWeilDivisor pi) ⊤)) g S)
    (N : Submodule S (TensorProduct k S
      ↥(divisorSections k (a • fiberWeilDivisor pi) ⊤)))
    (hx : x.toSubmodule ≤ N) :
    letI : Algebra S T := alpha.toAlgebra
    letI : IsScalarTower k S T :=
      .of_algebraMap_eq fun r => (alpha.commutes r).symm
    windowBaseChange T N ≤ divisorWindow G.eqns ha1 →
      divisorWindow G.eqns ha1 =
        (Module.Grassmannian.map alpha x).toSubmodule := by
  letI : Algebra S T := alpha.toAlgebra
  letI : IsScalarTower k S T :=
    .of_algebraMap_eq fun r => (alpha.commutes r).symm
  intro hpull
  have hproj : Module.Projective T
      ((TensorProduct k T
        ↑(divisorSections k (a • fiberWeilDivisor pi) ⊤)) ⧸
          divisorWindow G.eqns ha1) :=
    G.certified.projective_intrinsicWindowQuotient_at
      (π := pi) G.adaptation a hpi hgamma hchi ha1 hMa
  have hrank : ∀ p : PrimeSpectrum T,
      Module.rankAtStalk
        ((TensorProduct k T
          ↑(divisorSections k (a • fiberWeilDivisor pi) ⊤)) ⧸
            divisorWindow G.eqns ha1) p = g :=
    fun p => G.certified.rankAtStalk_intrinsicWindowQuotient_at
      (π := pi) G.adaptation a hpi hgamma hchi ha1 hMa p
  exact Grassmannian.eq_map_toSubmodule_of_baseChange_le alpha x N
    (divisorWindow G.eqns ha1) hx hpull hproj hrank

end CertifiedDivisorFamilyAff

end AlgebraicGeometry
