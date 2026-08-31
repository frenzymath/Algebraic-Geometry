/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaCokernelGlobal

/-!
# Finite transport for the widened intrinsic theta range

The global cokernel argument supplies surjectivity of the intrinsic high-window carve on an
arbitrary affine-open cover.  Since the high window is finite over the test ring, its image is
finite as well.  This file records that output in the exact quotient shape consumed by the
frame layer, and transports the certified glued-algebra module facts to the equalizer algebra
carrier used by the intrinsic Cech module.

No chart typing and no certificate clause are added here.  Projectivity and rank of the
intrinsic theta module still require the effective-descent invertibility seam; this file makes
the finite part and the equalizer-algebra transport available independently of that seam.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsDominant π] [IsIntegral C.left]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable {A : AffAdaptation D d}

attribute [local instance] thetaPieceQuotientBaseModule

section CertifiedWindow

variable {g a : ℕ} (hc : A.IsCertified g)

set_option maxHeartbeats 800000 in
-- The equalizer-module instance transport unfolds two dependent subtype module actions.
set_option synthInstance.maxHeartbeats 300000 in
/-- The intrinsic equalizer module is finite over the equalizer algebra itself.  The
surjective global evaluation first gives `R`-finiteness; the carrier identification between
the `R`- and equalizer-module presentations then applies restriction-of-scalars finiteness
in the useful direction. -/
theorem IsCertified.finite_intrinsicThetaGluedOver
    (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Module.Finite (↥(gluedSubalgebra A))
      (A.IntrinsicThetaGluedOver (π := π) a) := by
  let M := A.IntrinsicThetaGluedOver (π := π) a
  let AD := ↥(gluedSubalgebra A)
  letI : Module R M := Module.compHom M (algebraMap R AD)
  letI : IsScalarTower R AD M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite k
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤) :=
    inferInstance
  haveI : Module.Finite R
      (R ⊗[k] ↥(Scheme.divisorSections k
        (a • fiberWeilDivisor π) ⊤)) := inferInstance
  haveI : Module.Finite R (relThetaSections C R π a) :=
    Module.Finite.equiv (relThetaWindowEquiv C R π a ha1)
  have hfin : Module.Finite R
      (A.IntrinsicThetaGlued (π := π) a) :=
    Module.Finite.of_surjective
      (A.intrinsicThetaEvalRel (π := π) a)
      (AlgebraicGeometry.AffAdaptation.IsCertified.intrinsicThetaEvalRel_surjective
        C R π hc hπ hO hχ ha1 hMa)
  let e : M ≃ₗ[R] A.IntrinsicThetaGlued (π := π) a :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  letI : Module.Finite R M :=
    letI := hfin
    Module.Finite.equiv e.symm
  exact Module.Finite.of_restrictScalars_finite R AD M

include π in
/-- Each intrinsic theta quotient on a widened piece is finite over the test ring. -/
theorem IsCertified.finite_thetaPieceQuotient
    (hc : A.IsCertified g) (a : ℕ) (j : D.index) :
    Module.Finite R (A.ThetaPieceQuotient (π := π) a j) := by
  letI : Module R (A.ThetaPieceQuotient (π := π) a j) :=
    A.thetaPieceQuotientBaseModule (π := π) a j
  letI : IsScalarTower R (A.colength j)
      (A.ThetaPieceQuotient (π := π) a j) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module.Finite R (A.colength j) :=
    AlgebraicGeometry.AffAdaptation.IsCertified.finite_colength hc j
  letI : Module.Invertible (A.colength j)
      (A.ThetaPieceQuotient (π := π) a j) :=
    A.invertible_thetaPieceQuotient (π := π) a j
  exact Module.Invertible.finite_trans (A := A.colength j)

include π in
/-- Each intrinsic theta quotient on a widened piece is projective over the test ring. -/
theorem IsCertified.projective_thetaPieceQuotient
    (hc : A.IsCertified g) (a : ℕ) (j : D.index) :
    Module.Projective R (A.ThetaPieceQuotient (π := π) a j) := by
  letI : Module R (A.ThetaPieceQuotient (π := π) a j) :=
    A.thetaPieceQuotientBaseModule (π := π) a j
  letI : IsScalarTower R (A.colength j)
      (A.ThetaPieceQuotient (π := π) a j) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module.Projective R (A.colength j) :=
    AlgebraicGeometry.AffAdaptation.IsCertified.projective_colength hc j
  letI : Module.Invertible (A.colength j)
      (A.ThetaPieceQuotient (π := π) a j) :=
    A.invertible_thetaPieceQuotient (π := π) a j
  exact Module.Invertible.projective_trans (A := A.colength j)

include π in
/-- The product of the piece theta quotients is finite over `R`. -/
theorem IsCertified.finite_thetaPieceProd
    (hc : A.IsCertified g) (a : ℕ) :
    Module.Finite R (A.ThetaPieceProd (π := π) a) := by
  letI : ∀ j : D.index, Module R (A.ThetaPieceQuotient (π := π) a j) :=
    fun j => A.thetaPieceQuotientBaseModule (π := π) a j
  letI : ∀ j : D.index,
      Module.Finite R (A.ThetaPieceQuotient (π := π) a j) :=
    fun j => AlgebraicGeometry.AffAdaptation.IsCertified.finite_thetaPieceQuotient
      (A := A) hc a j
  exact Module.Finite.pi

include π in
/-- The product of the piece theta quotients is projective over `R`. -/
theorem IsCertified.projective_thetaPieceProd
    (hc : A.IsCertified g) (a : ℕ) :
    Module.Projective R (A.ThetaPieceProd (π := π) a) := by
  letI : ∀ j : D.index, Module R (A.ThetaPieceQuotient (π := π) a j) :=
    fun j => A.thetaPieceQuotientBaseModule (π := π) a j
  letI : ∀ j : D.index,
      Module.Projective R (A.ThetaPieceQuotient (π := π) a j) :=
    fun j => AlgebraicGeometry.AffAdaptation.IsCertified.projective_thetaPieceQuotient
      (A := A) hc a j
  exact Module.Projective.of_equiv
    (DirectSum.linearEquivFunOnFintype R D.index
      (fun j => A.ThetaPieceQuotient (π := π) a j))

/-- The certified intrinsic high-window carve has finite target.  The source is the finite
base-changed theta window, and the target is its surjective image. -/
theorem IsCertified.finite_intrinsicThetaGlued
    (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Module.Finite R (A.IntrinsicThetaGlued (π := π) a) := by
  exact Module.Finite.of_surjective
    (A.intrinsicWindowCarve (π := π) a ha1)
    (AlgebraicGeometry.AffAdaptation.IsCertified.intrinsicWindowCarve_surjective
      C R π hc hπ hO hχ ha1 hMa)

/-- The intrinsic high-window carve has finite target when the curve parameter
`gamma` is independent of the certified divisor degree `g`. -/
theorem IsCertified.finite_intrinsicThetaGlued_at
    {gamma : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Module.Finite R (A.IntrinsicThetaGlued (π := π) a) := by
  exact Module.Finite.of_surjective
    (A.intrinsicWindowCarve (π := π) a ha1)
    (AlgebraicGeometry.AffAdaptation.IsCertified.intrinsicWindowCarve_surjective_at
      C R π hc hπ hgamma hχ ha1 hMa)

/-- The high-window quotient by the intrinsic vanishing submodule is finite.  This is the
quotient presentation used by the Grassmannian/frame consumers. -/
theorem IsCertified.finite_intrinsicWindowQuotient
    (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Module.Finite R ((R ⊗[k] ↥(Scheme.divisorSections k
      (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) := by
  letI := AlgebraicGeometry.AffAdaptation.IsCertified.finite_intrinsicThetaGlued
    (C := C) (R := R) (π := π) hc hπ hO hχ ha1 hMa
  exact Module.Finite.equiv
    (AlgebraicGeometry.AffAdaptation.IsCertified.intrinsicWindowQuotEquiv
      C R π hc hπ hO hχ ha1 hMa).symm

/-- The intrinsic high-window quotient is finite with independent curve and divisor
parameters. -/
theorem IsCertified.finite_intrinsicWindowQuotient_at
    {gamma : ℕ} (hc : A.IsCertified g)
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Module.Finite R ((R ⊗[k] ↥(Scheme.divisorSections k
      (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1) := by
  letI := AlgebraicGeometry.AffAdaptation.IsCertified.finite_intrinsicThetaGlued_at
    (C := C) (R := R) (π := π) hc hπ hgamma hχ ha1 hMa
  exact Module.Finite.equiv
    (AlgebraicGeometry.AffAdaptation.IsCertified.intrinsicWindowQuotEquiv_at
      C R π hc hπ hgamma hχ ha1 hMa).symm

end CertifiedWindow

section EqualizerTransport

variable {g : ℕ} (hc : A.IsCertified g)

/-- The equalizer algebra and the certified glued module have the same finite `R`-module
carrier. -/
theorem IsCertified.finite_gluedSubalgebra (hc : A.IsCertified g) :
    Module.Finite R ↥(gluedSubalgebra A) := by
  letI := AlgebraicGeometry.AffAdaptation.IsCertified.finite_glued hc
  exact Module.Finite.equiv A.gluedSubalgebraEquiv.symm

/-- Projectivity of the certified glued module transports to the equalizer algebra. -/
theorem IsCertified.projective_gluedSubalgebra (hc : A.IsCertified g) :
    Module.Projective R ↥(gluedSubalgebra A) := by
  letI := AlgebraicGeometry.AffAdaptation.IsCertified.projective_glued hc
  exact Module.Projective.of_equiv A.gluedSubalgebraEquiv.symm

/-- The equalizer algebra has the same constant fibre rank as the certified glued module. -/
theorem IsCertified.rankAtStalk_gluedSubalgebra (hc : A.IsCertified g)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (↥(gluedSubalgebra A)) p = g := by
  rw [congrFun (Module.rankAtStalk_eq_of_equiv A.gluedSubalgebraEquiv) p]
  exact AlgebraicGeometry.AffAdaptation.IsCertified.rankAtStalk_glued hc p

end EqualizerTransport

end AffAdaptation

end AlgebraicGeometry
