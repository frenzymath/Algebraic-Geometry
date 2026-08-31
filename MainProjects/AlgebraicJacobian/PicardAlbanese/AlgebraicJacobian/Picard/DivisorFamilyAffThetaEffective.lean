/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaDescentDatum
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaFinite

/-!
# Effective intrinsic theta descent over the test ring

The intrinsic theta equalizer is invertible over the widened equalizer algebra.  The
certificate already makes that algebra finite projective of constant rank over the test
ring.  This file combines those facts and transports them to the intrinsic window quotient,
giving the finite-projective constant-rank input used by the carrier-free frame layer.

No swallowing, chart typing, or additional certificate clause is used.
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
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

attribute [local instance] thetaPieceQuotientModule thetaOverlapQuotientModule
  thetaPieceQuotientBaseModule thetaOverlapQuotientBaseModule
  thetaPieceQuotientGluedModule thetaOverlapQuotientGluedModule

noncomputable section

variable (A : AffAdaptation D d) (a : ℕ)

/-- The equalizer-module presentation and its underlying `R`-linear presentation have the
same carrier. -/
noncomputable def intrinsicThetaGluedOverEquivIntrinsic :
    letI : Module R (A.IntrinsicThetaGluedOver (π := π) a) :=
      Module.compHom _ (algebraMap R (gluedSubalgebra A))
    A.IntrinsicThetaGluedOver (π := π) a ≃ₗ[R]
      A.IntrinsicThetaGlued (π := π) a := by
  let AD := gluedSubalgebra A
  let M := A.IntrinsicThetaGluedOver (π := π) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  exact
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

set_option maxHeartbeats 1000000 in
-- The transfer unfolds the dependent equalizer action over the base ring.
set_option synthInstance.maxHeartbeats 500000 in
-- The equalizer carrier has dependent product module structures over both base rings.
/-- The effective intrinsic theta equalizer is finite over the test ring. -/
theorem IsCertified.finite_intrinsicThetaGluedOver_base {g : ℕ}
    (hc : A.IsCertified g) :
    letI : Module R (A.IntrinsicThetaGluedOver (π := π) a) :=
      Module.compHom _ (algebraMap R (gluedSubalgebra A))
    Module.Finite R (A.IntrinsicThetaGluedOver (π := π) a) := by
  let AD := gluedSubalgebra A
  let M := A.IntrinsicThetaGluedOver (π := π) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  letI : IsScalarTower R AD M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module.Finite R AD := by
    letI := hc.finite_glued
    exact Module.Finite.equiv A.gluedSubalgebraEquiv.symm
  letI : Module.Invertible AD M :=
    hc.invertible_intrinsicThetaGluedOver (π := π) A a
  exact Module.Invertible.finite_trans (A := AD)

set_option maxHeartbeats 1000000 in
-- The transfer unfolds the dependent equalizer action over the base ring.
set_option synthInstance.maxHeartbeats 500000 in
-- The equalizer carrier has dependent product module structures over both base rings.
/-- The effective intrinsic theta equalizer is projective over the test ring. -/
theorem IsCertified.projective_intrinsicThetaGluedOver_base {g : ℕ}
    (hc : A.IsCertified g) :
    letI : Module R (A.IntrinsicThetaGluedOver (π := π) a) :=
      Module.compHom _ (algebraMap R (gluedSubalgebra A))
    Module.Projective R (A.IntrinsicThetaGluedOver (π := π) a) := by
  let AD := gluedSubalgebra A
  let M := A.IntrinsicThetaGluedOver (π := π) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  letI : IsScalarTower R AD M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module.Projective R AD := by
    letI := hc.projective_glued
    exact Module.Projective.of_equiv A.gluedSubalgebraEquiv.symm
  letI : Module.Invertible AD M :=
    hc.invertible_intrinsicThetaGluedOver (π := π) A a
  exact Module.Invertible.projective_trans (A := AD)

set_option maxHeartbeats 1000000 in
-- The rank comparison unfolds both equalizer module structures.
set_option synthInstance.maxHeartbeats 500000 in
-- Rank transport combines the two base-ring module structures on the equalizer carrier.
/-- The effective intrinsic theta equalizer has the certified constant stalk rank. -/
theorem IsCertified.rankAtStalk_intrinsicThetaGluedOver {g : ℕ}
    (hc : A.IsCertified g) (p : PrimeSpectrum R) :
    letI : Module R (A.IntrinsicThetaGluedOver (π := π) a) :=
      Module.compHom _ (algebraMap R (gluedSubalgebra A))
    Module.rankAtStalk (R := R) (A.IntrinsicThetaGluedOver (π := π) a) p = g := by
  let AD := gluedSubalgebra A
  let M := A.IntrinsicThetaGluedOver (π := π) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  letI : IsScalarTower R AD M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module.Finite R AD := by
    letI := hc.finite_glued
    exact Module.Finite.equiv A.gluedSubalgebraEquiv.symm
  letI : Module.Projective R AD := by
    letI := hc.projective_glued
    exact Module.Projective.of_equiv A.gluedSubalgebraEquiv.symm
  letI : Module.Invertible AD M :=
    hc.invertible_intrinsicThetaGluedOver (π := π) A a
  calc
    Module.rankAtStalk M p = Module.rankAtStalk AD p :=
      Module.Invertible.rankAtStalk_eq_of_module_finite p
    _ = Module.rankAtStalk A.Glued p :=
      congrFun (Module.rankAtStalk_eq_of_equiv A.gluedSubalgebraEquiv) p
    _ = g := hc.rankAtStalk_glued p

/-- The underlying intrinsic theta module is projective over the test ring. -/
theorem IsCertified.projective_intrinsicThetaGlued {g : ℕ}
    (hc : A.IsCertified g) :
    Module.Projective R (A.IntrinsicThetaGlued (π := π) a) := by
  let AD := gluedSubalgebra A
  let M := A.IntrinsicThetaGluedOver (π := π) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  letI : Module.Projective R M :=
    hc.projective_intrinsicThetaGluedOver_base (π := π) A a
  exact Module.Projective.of_equiv
    (A.intrinsicThetaGluedOverEquivIntrinsic (π := π) a)

/-- The underlying intrinsic theta module has the certified constant stalk rank. -/
theorem IsCertified.rankAtStalk_intrinsicThetaGlued {g : ℕ}
    (hc : A.IsCertified g) (p : PrimeSpectrum R) :
    Module.rankAtStalk (A.IntrinsicThetaGlued (π := π) a) p = g := by
  let AD := gluedSubalgebra A
  let M := A.IntrinsicThetaGluedOver (π := π) a
  letI : Module R M := Module.compHom M (algebraMap R AD)
  let e := A.intrinsicThetaGluedOverEquivIntrinsic (π := π) a
  calc
    Module.rankAtStalk (A.IntrinsicThetaGlued (π := π) a) p =
        Module.rankAtStalk M p :=
      (congrFun (Module.rankAtStalk_eq_of_equiv e) p).symm
    _ = g := hc.rankAtStalk_intrinsicThetaGluedOver (π := π) A a p

section WindowQuotient

variable [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] [IsDominant π] [IsIntegral C.left]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

/-- The intrinsic window quotient is projective with no cover-containment hypothesis. -/
theorem IsCertified.projective_intrinsicWindowQuotient {g : ℕ}
    (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) := by
  letI : Module.Projective R (A.IntrinsicThetaGlued (π := π) a) :=
    hc.projective_intrinsicThetaGlued (π := π) A a
  exact Module.Projective.of_equiv
    (hc.intrinsicWindowQuotEquiv C R π hπ hO hχ ha1 hMa).symm

/-- The intrinsic window quotient is projective when the curve parameter is
independent of the certified divisor degree. -/
theorem IsCertified.projective_intrinsicWindowQuotient_at {g gamma : ℕ}
    (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) := by
  letI : Module.Projective R (A.IntrinsicThetaGlued (π := π) a) :=
    hc.projective_intrinsicThetaGlued (π := π) A a
  exact Module.Projective.of_equiv
    (hc.intrinsicWindowQuotEquiv_at C R π hπ hgamma hχ ha1 hMa).symm

/-- The intrinsic window quotient has the certified constant stalk rank with no
cover-containment hypothesis. -/
theorem IsCertified.rankAtStalk_intrinsicWindowQuotient {g : ℕ}
    (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) p = g := by
  rw [congrFun (Module.rankAtStalk_eq_of_equiv
    (hc.intrinsicWindowQuotEquiv C R π hπ hO hχ ha1 hMa)) p]
  exact hc.rankAtStalk_intrinsicThetaGlued (π := π) A a p

/-- The intrinsic window quotient has constant stalk rank equal to the certified
divisor degree, independently of the curve parameter. -/
theorem IsCertified.rankAtStalk_intrinsicWindowQuotient_at {g gamma : ℕ}
    (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) p = g := by
  rw [congrFun (Module.rankAtStalk_eq_of_equiv
    (hc.intrinsicWindowQuotEquiv_at C R π hπ hgamma hχ ha1 hMa)) p]
  exact hc.rankAtStalk_intrinsicThetaGlued (π := π) A a p

end WindowQuotient

end

end AffAdaptation

end AlgebraicGeometry
