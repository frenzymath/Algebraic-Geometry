/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaSwallowed

/-!
# Swallowed intrinsic theta transport to the window quotient

The swallowed-cover descent identifies the intrinsic theta carrier with the distinguished
piece quotient. This file transports its finite, projective, and rank data through the
cover-independent intrinsic window quotient equivalence, producing the exact divisor-window
quotient inputs consumed by the frame-cover layer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable {A : AffAdaptation D d}
variable {g : Nat}

namespace AffAdaptation

attribute [local instance] thetaPieceQuotientModule thetaOverlapQuotientModule
  thetaPieceQuotientBaseModule thetaOverlapQuotientBaseModule
  thetaPieceQuotientGluedModule thetaOverlapQuotientGluedModule

set_option synthInstance.maxHeartbeats 300000 in
-- The rank calculation transports through the swallowed product and piece equivalences.
/-- The underlying intrinsic theta carrier has the certified constant stalk rank. -/
theorem IsCertified.rankAtStalk_intrinsicThetaGlued_of_swallowedBy
    (hc : A.IsCertified g) (a : Nat) (h : D.SwallowedBy d)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (A.IntrinsicThetaGlued (π := pi) a) p = g := by
  obtain ⟨j0, hsub, hmiss⟩ := h
  let e : A.IntrinsicThetaGlued (π := pi) a ≃ₗ[R]
      A.ThetaPieceQuotient (π := pi) a j0 :=
    (A.intrinsicThetaGluedEquivPieceProdOfSwallowedBy
      (pi := pi) a ⟨j0, hsub, hmiss⟩).trans
        (A.thetaPieceProdEquivSwallowingPiece (pi := pi) a hmiss)
  have hpiece : Module.rankAtStalk
      (A.ThetaPieceQuotient (π := pi) a j0) p =
      Module.rankAtStalk (A.colength j0) p := by
    letI : Module.Finite R (A.colength j0) := hc.finite_colength j0
    letI : Module.Projective R (A.colength j0) := hc.projective_colength j0
    letI : IsScalarTower R (A.colength j0)
        (A.ThetaPieceQuotient (π := pi) a j0) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : Module.Invertible (A.colength j0)
        (A.ThetaPieceQuotient (π := pi) a j0) :=
      A.invertible_thetaPieceQuotient (π := pi) a j0
    exact Module.Invertible.rankAtStalk_eq_of_module_finite p
  have hcolength : Module.rankAtStalk (A.colength j0) p = g := by
    let ecol : A.Glued ≃ₗ[R] A.colength j0 :=
      (A.gluedEquivChartProd_of_swallowedBy ⟨j0, hsub, hmiss⟩).trans
        (A.chartProdEquivSwallowingPiece hmiss)
    calc
      Module.rankAtStalk (A.colength j0) p = Module.rankAtStalk A.Glued p :=
        (congrFun (Module.rankAtStalk_eq_of_equiv ecol) p).symm
      _ = g := hc.rankAtStalk_glued p
  calc
    Module.rankAtStalk (A.IntrinsicThetaGlued (π := pi) a) p =
        Module.rankAtStalk (A.ThetaPieceQuotient (π := pi) a j0) p :=
      congrFun (Module.rankAtStalk_eq_of_equiv e) p
    _ = Module.rankAtStalk (A.colength j0) p := hpiece
    _ = g := hcolength

section WindowQuotientTransport

variable [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] [IsDominant pi] [IsIntegral C.left]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

/-- The swallowed descent supplies the projective window-quotient input used by the
frame-cover layer. The quotient is identified with the intrinsic theta carrier by the
cover-independent equivalence, so no chart typing is reintroduced here. -/
theorem IsCertified.projective_intrinsicWindowQuotient_of_swallowedBy
    (A : AffAdaptation D d) (hc : A.IsCertified g) (a : Nat)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (ha1 : Subsingleton (relTwistPair C k pi
      (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a) (h : D.SwallowedBy d) :
    Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor pi) ⊤)) ⧸
        divisorWindow d ha1) := by
  letI : Module.Projective R (A.IntrinsicThetaGlued (π := pi) a) :=
    IsCertified.projective_intrinsicThetaGlued_of_swallowedBy (pi := pi) hc a h
  exact Module.Projective.of_equiv
    (AlgebraicGeometry.AffAdaptation.IsCertified.intrinsicWindowQuotEquiv
      C R pi hc hpi hO hchi ha1 hMa).symm

/-- Finite companion for the same direct window-quotient route. -/
theorem IsCertified.finite_intrinsicWindowQuotient_of_swallowedBy
    (A : AffAdaptation D d) (hc : A.IsCertified g) (a : Nat)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (ha1 : Subsingleton (relTwistPair C k pi
      (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a) (h : D.SwallowedBy d) :
    Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor pi) ⊤)) ⧸
        divisorWindow d ha1) := by
  letI : Module.Finite R (A.IntrinsicThetaGlued (π := pi) a) :=
    IsCertified.finite_intrinsicThetaGlued_of_swallowedBy (pi := pi) hc a h
  exact Module.Finite.equiv
    (AlgebraicGeometry.AffAdaptation.IsCertified.intrinsicWindowQuotEquiv
      C R pi hc hpi hO hchi ha1 hMa).symm

/-- Constant-rank companion for the frame-cover input. -/
theorem IsCertified.rankAtStalk_intrinsicWindowQuotient_of_swallowedBy
    (A : AffAdaptation D d) (hc : A.IsCertified g) (a : Nat)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (ha1 : Subsingleton (relTwistPair C k pi
      (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a) (h : D.SwallowedBy d)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor pi) ⊤)) ⧸
        divisorWindow d ha1) p = g := by
  rw [congrFun (Module.rankAtStalk_eq_of_equiv
    (AlgebraicGeometry.AffAdaptation.IsCertified.intrinsicWindowQuotEquiv
      C R pi hc hpi hO hchi ha1 hMa)) p]
  exact hc.rankAtStalk_intrinsicThetaGlued_of_swallowedBy a h p

end WindowQuotientTransport

end AffAdaptation

end AlgebraicGeometry
