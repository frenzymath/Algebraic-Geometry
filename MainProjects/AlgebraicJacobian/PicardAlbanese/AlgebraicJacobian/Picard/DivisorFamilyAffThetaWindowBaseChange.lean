/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaEffective
import AlgebraicJacobian.Picard.DivisorFamilyEpsNaturality

/-!
# Base change of the widened intrinsic divisor window

Effective intrinsic theta descent supplies projective constant-rank window quotients for a
certified widened adaptation and for every pullback of it.  The formal inclusion of the
base-changed window into the pulled-equation window is therefore an equality by the standard
rank engine.  This is the arbitrary-affine-open analogue of the chart-typed window naturality
theorem, with no chart typing or additional certificate clause.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {R' : Type u} [CommRing R'] [Algebra k R'] [Algebra R R']
  [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsDominant π] [IsIntegral C.left]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

attribute [local instance] thetaPieceQuotientModule thetaOverlapQuotientModule
  thetaPieceQuotientBaseModule thetaOverlapQuotientBaseModule
  thetaPieceQuotientGluedModule thetaOverlapQuotientGluedModule

noncomputable section

set_option maxHeartbeats 1600000 in
-- Both the original and pulled dependent equalizers are transported to window quotients.
set_option synthInstance.maxHeartbeats 600000 in
/-- The divisor window of a pulled certified widened adaptation is exactly the canonical
base change of its original divisor window. -/
theorem IsCertified.divisorWindow_pulledEquations_eq
    {A : AffAdaptation D d} {g a : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    divisorWindow (A.pulledEquations R' hc.projective_colength) ha1 =
      windowBaseChange R' (divisorWindow d ha1) := by
  haveI hfinR : Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) :=
    hc.finite_intrinsicWindowQuotient hπ hO hχ ha1 hMa
  haveI hprojR : Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) :=
    hc.projective_intrinsicWindowQuotient (π := π) A a hπ hO hχ ha1 hMa
  have hrankR : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk ((R ⊗[k]
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d ha1) p = g :=
    fun p => hc.rankAtStalk_intrinsicWindowQuotient
      (π := π) A a hπ hO hχ ha1 hMa p
  let A' := A.pullback R' hc.projective_colength
  have hinf : ∀ i j : D.index, IsAffineOpen (D.pieces i ⊓ D.pieces j) :=
    fun i j => Over.isAffineOpen_inf (A := R) C
      (D.isAffineOpen i) (D.isAffineOpen j)
  have hc' : A'.IsCertified g := A.isCertified_pullback R' hinf hc
  haveI hprojR' : Module.Projective R' ((R' ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow (A.pulledEquations R' hc.projective_colength) ha1) :=
    hc'.projective_intrinsicWindowQuotient
      (π := π) A' a hπ hO hχ ha1 hMa
  have hrankR' : ∀ p : PrimeSpectrum R',
      Module.rankAtStalk ((R' ⊗[k]
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow (A.pulledEquations R' hc.projective_colength) ha1) p = g :=
    fun p => hc'.rankAtStalk_intrinsicWindowQuotient
      (π := π) A' a hπ hO hχ ha1 hMa p
  let x := windowBaseChangeGr R' (divisorWindow d ha1) g hrankR
  letI : Module.Projective R' ((R' ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        windowBaseChange R' (divisorWindow d ha1)) :=
    x.projective_quotient
  have hle : windowBaseChange R' (divisorWindow d ha1) ≤
      divisorWindow (A.pulledEquations R' hc.projective_colength) ha1 :=
    windowBaseChange_divisorWindow_le C R' π a
      (A.germ_pullbackEqn_mem_nonZeroDivisors R' hc.projective_colength) ha1
  refine (Submodule.eq_of_le_of_rankAtStalk_quotient_eq
    hle (fun p => ?_)).symm
  exact (x.rankAtStalk_eq p).trans (hrankR' p).symm

set_option maxHeartbeats 1600000 in
-- Both equalizers are transported using the off-diagonal intrinsic quotient package.
set_option synthInstance.maxHeartbeats 600000 in
/-- The pulled intrinsic divisor window commutes with base change when the curve parameter is
independent of the certified divisor degree. -/
theorem IsCertified.divisorWindow_pulledEquations_eq_at
    {A : AffAdaptation D d} {g gamma a : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    divisorWindow (A.pulledEquations R' hc.projective_colength) ha1 =
      windowBaseChange R' (divisorWindow d ha1) := by
  haveI hfinR : Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) :=
    hc.finite_intrinsicWindowQuotient_at hπ hgamma hχ ha1 hMa
  haveI hprojR : Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) :=
    hc.projective_intrinsicWindowQuotient_at
      (π := π) A a hπ hgamma hχ ha1 hMa
  have hrankR : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk ((R ⊗[k]
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d ha1) p = g :=
    fun p => hc.rankAtStalk_intrinsicWindowQuotient_at
      (π := π) A a hπ hgamma hχ ha1 hMa p
  let A' := A.pullback R' hc.projective_colength
  have hinf : ∀ i j : D.index, IsAffineOpen (D.pieces i ⊓ D.pieces j) :=
    fun i j => Over.isAffineOpen_inf (A := R) C
      (D.isAffineOpen i) (D.isAffineOpen j)
  have hc' : A'.IsCertified g := A.isCertified_pullback R' hinf hc
  haveI hprojR' : Module.Projective R' ((R' ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow (A.pulledEquations R' hc.projective_colength) ha1) :=
    hc'.projective_intrinsicWindowQuotient_at
      (π := π) A' a hπ hgamma hχ ha1 hMa
  have hrankR' : ∀ p : PrimeSpectrum R',
      Module.rankAtStalk ((R' ⊗[k]
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow (A.pulledEquations R' hc.projective_colength) ha1) p = g :=
    fun p => hc'.rankAtStalk_intrinsicWindowQuotient_at
      (π := π) A' a hπ hgamma hχ ha1 hMa p
  let x := windowBaseChangeGr R' (divisorWindow d ha1) g hrankR
  letI : Module.Projective R' ((R' ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        windowBaseChange R' (divisorWindow d ha1)) :=
    x.projective_quotient
  have hle : windowBaseChange R' (divisorWindow d ha1) ≤
      divisorWindow (A.pulledEquations R' hc.projective_colength) ha1 :=
    windowBaseChange_divisorWindow_le C R' π a
      (A.germ_pullbackEqn_mem_nonZeroDivisors R' hc.projective_colength) ha1
  refine (Submodule.eq_of_le_of_rankAtStalk_quotient_eq
    hle (fun p => ?_)).symm
  exact (x.rankAtStalk_eq p).trans (hrankR' p).symm

end

end AffAdaptation

end AlgebraicGeometry
