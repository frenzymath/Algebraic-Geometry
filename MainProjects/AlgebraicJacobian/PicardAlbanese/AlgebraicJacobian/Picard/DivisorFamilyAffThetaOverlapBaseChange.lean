/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaBaseChange
import AlgebraicJacobian.Picard.DivisorSubschemeTensorOverlap
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaCech

/-!
# Theta modules on affine-cover overlaps are base changes

The intrinsic theta sheaf restricts from every widened affine piece to each pairwise
overlap by base change. Passing through the equation quotients therefore identifies the
piece theta quotient after extension to the overlap colength algebra with the overlap
theta quotient itself. No extra certificate or geometric hypothesis is introduced.
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

attribute [local instance] thetaPieceSectionsModule thetaOverlapSectionsModule
  thetaPieceQuotientModule thetaOverlapQuotientModule

@[reducible]
noncomputable def pieceSectionsToOverlapAlgebra (i j : D.index) :
    Algebra Γ(relCurve C R, D.pieces i)
      Γ(relCurve C R, D.pieces i ⊓ D.pieces j) :=
  (relResAlgHom C R
    (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i)).toRingHom.toAlgebra

attribute [local instance] pieceSectionsToOverlapAlgebra

@[reducible]
noncomputable def thetaOverlapSectionsLeftModule (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : Module Γ(relCurve C R, D.pieces i)
      (A.ThetaOverlapSections (π := π) a i j) :=
  letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
    A.thetaOverlapSectionsModule (π := π) a i j
  Module.compHom (A.ThetaOverlapSections (π := π) a i j)
    (relResAlgHom C R
      (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i)).toRingHom

attribute [local instance] thetaOverlapSectionsLeftModule

@[reducible]
noncomputable def thetaOverlapSectionsLeftTower (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : IsScalarTower Γ(relCurve C R, D.pieces i)
      Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] thetaOverlapSectionsLeftTower

noncomputable def thetaSectionsToOverlapLeftLinearRing (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : A.ThetaPieceSections (π := π) a i →ₗ[Γ(relCurve C R, D.pieces i)]
      A.ThetaOverlapSections (π := π) a i j :=
  { toFun := A.thetaSectionsToOverlapLeft (π := π) a i j
    map_add' := (A.thetaSectionsToOverlapLeft (π := π) a i j).map_add
    map_smul' := (A.thetaSectionsToOverlapLeft (π := π) a i j).map_smulₛₗ }

/-- Restriction of intrinsic theta sections from the left piece to an overlap is a
base change. -/
theorem isBaseChange_thetaSectionsToOverlapLeftLinearRing
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index) :
    IsBaseChange Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.thetaSectionsToOverlapLeftLinearRing (π := π) a i j) := by
  let MV := A.thetaPieceSectionsModel (π := π) a i
  let MW := A.thetaOverlapSectionsModel (π := π) a i j
  let F := thetaChartDatum C R π a
  letI := MV.qcoh
  letI : Module Γ(relCurve C R, D.pieces i)
      (F.sheaf.obj.obj (op (D.pieces i))) :=
    Scheme.QcohOn.moduleOfLE (F := F.sheaf) (le_refl (D.pieces i))
  letI := MW.qcoh
  letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (F.sheaf.obj.obj (op (D.pieces i ⊓ D.pieces j))) :=
    Scheme.QcohOn.moduleOfLE (F := F.sheaf)
      (le_refl (D.pieces i ⊓ D.pieces j))
  letI : Algebra Γ(relCurve C R, D.pieces i)
      Γ(relCurve C R, D.pieces i ⊓ D.pieces j) :=
    ((relCurve C R).resHom
      (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i)).toAlgebra
  letI : Module Γ(relCurve C R, D.pieces i)
      (A.ThetaOverlapSections (π := π) a i j) :=
    A.thetaOverlapSectionsLeftModule (π := π) a i j
  letI : IsScalarTower Γ(relCurve C R, D.pieces i)
      Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
    A.thetaOverlapSectionsLeftTower (π := π) a i j
  have hbij := F.affineSectionsBaseChange_bijective
    (D.isAffineOpen i) (D.hasAffineOverlaps_of_isProper i j)
    (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) MV MW
  apply IsBaseChange.of_equiv
    (LinearEquiv.ofBijective
      (F.affineSectionsBaseChange
        (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) MV MW) hbij)
  intro x
  change F.affineSectionsBaseChange
      (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) MV MW
        (1 ⊗ₜ x) = A.thetaSectionsToOverlapLeft (π := π) a i j x
  rw [F.affineSectionsBaseChange_tmul, one_smul]
  rfl

noncomputable def thetaPieceQuotientMkLinear (A : AffAdaptation D d) (a : ℕ)
    (i : D.index) : A.ThetaPieceSections (π := π) a i →ₗ[Γ(relCurve C R, D.pieces i)]
      A.ThetaPieceQuotient (π := π) a i :=
  (A.thetaPieceVanishing (π := π) a i).mkQ

noncomputable def thetaOverlapQuotientMkLinear (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : A.ThetaOverlapSections (π := π) a i j
      →ₗ[Γ(relCurve C R, D.pieces i ⊓ D.pieces j)]
        A.ThetaOverlapQuotient (π := π) a i j :=
  (A.thetaOverlapVanishing (π := π) a i j).mkQ

omit [IsProper C.hom] in
theorem isBaseChange_thetaPieceQuotientMkLinear (A : AffAdaptation D d) (a : ℕ)
    (i : D.index) : IsBaseChange (A.colength i)
      (A.thetaPieceQuotientMkLinear (π := π) a i) := by
  apply IsBaseChange.of_equiv
    (A.thetaPieceRestrictionEquivColength (π := π) a i)
  intro x
  change TensorProduct.quotTensorEquivQuotSMul
      (A.ThetaPieceSections (π := π) a i) (Ideal.span {A.eqn i})
      (1 ⊗ₜ x) = Submodule.Quotient.mk x
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ x

theorem isBaseChange_thetaOverlapQuotientMkLinear (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : IsBaseChange (A.ovlColength i j)
      (A.thetaOverlapQuotientMkLinear (π := π) a i j) := by
  apply IsBaseChange.of_equiv
    (A.thetaOverlapRestrictionEquivColength (π := π) a i j)
  intro x
  change TensorProduct.quotTensorEquivQuotSMul
      (A.ThetaOverlapSections (π := π) a i j) (A.ovlIdeal i j)
      (1 ⊗ₜ x) = Submodule.Quotient.mk x
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ x

@[reducible]
noncomputable def pieceToOverlapLeftAlgebra (A : AffAdaptation D d) (i j : D.index) :
    Algebra (A.colength i) (A.ovlColength i j) :=
  (A.toOvlLeft i j).toRingHom.toAlgebra

attribute [local instance] pieceToOverlapLeftAlgebra

@[reducible]
noncomputable def pieceSectionsColengthOverlapTower (A : AffAdaptation D d)
    (i j : D.index) : IsScalarTower Γ(relCurve C R, D.pieces i)
      (A.colength i) (A.ovlColength i j) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] pieceSectionsColengthOverlapTower

/-- The overlap quotient, restricted to the left piece colength algebra. -/
@[reducible]
noncomputable def thetaOverlapQuotientLeftModule (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    Module (A.colength i) (A.ThetaOverlapQuotient (π := π) a i j) :=
  letI : Module (A.ovlColength i j) (A.ThetaOverlapQuotient (π := π) a i j) :=
    A.thetaOverlapQuotientModule (π := π) a i j
  Module.compHom (A.ThetaOverlapQuotient (π := π) a i j)
    (A.toOvlLeft i j).toRingHom

attribute [local instance] thetaOverlapQuotientLeftModule

@[reducible]
noncomputable def thetaOverlapQuotientLeftTower (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : IsScalarTower (A.colength i) (A.ovlColength i j)
      (A.ThetaOverlapQuotient (π := π) a i j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] thetaOverlapQuotientLeftTower

@[reducible]
noncomputable def pieceSectionsColengthThetaOverlapTower
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index) :
    IsScalarTower Γ(relCurve C R, D.pieces i) (A.colength i)
      (A.ThetaOverlapQuotient (π := π) a i j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] pieceSectionsColengthThetaOverlapTower

@[reducible]
noncomputable def thetaPieceToOverlapCompatibleSMul (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : LinearMap.CompatibleSMul
      (A.ThetaPieceQuotient (π := π) a i)
      (A.ThetaOverlapQuotient (π := π) a i j)
      Γ(relCurve C R, D.pieces i) (A.colength i) where
  map_smul f r x := by
    change f (Ideal.Quotient.mk (Ideal.span {A.eqn i}) r • x) =
      A.toOvlLeft i j (Ideal.Quotient.mk (Ideal.span {A.eqn i}) r) • f x
    exact f.map_smul _ x

attribute [local instance] thetaPieceToOverlapCompatibleSMul

noncomputable def thetaToOverlapLeftLinearColength (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaPieceQuotient (π := π) a i →ₗ[A.colength i]
      A.ThetaOverlapQuotient (π := π) a i j :=
  { toFun := A.thetaToOverlapLeft (π := π) a i j
    map_add' := (A.thetaToOverlapLeft (π := π) a i j).map_add
    map_smul' := A.thetaToOverlapLeft_smul (π := π) a i j }

/-- Once arbitrary-affine restriction of the theta sheaf is known to be a base change,
the induced divisor-quotient restriction is a base change as well. -/
theorem isBaseChange_thetaToOverlapLeftLinearColength
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index) :
    IsBaseChange (A.ovlColength i j)
      (A.thetaToOverlapLeftLinearColength (π := π) a i j) := by
  have hcomp : IsBaseChange (A.ovlColength i j)
      (((A.thetaOverlapQuotientMkLinear (π := π) a i j).restrictScalars
          Γ(relCurve C R, D.pieces i)).comp
        (A.thetaSectionsToOverlapLeftLinearRing (π := π) a i j)) :=
    IsBaseChange.comp
      (A.isBaseChange_thetaSectionsToOverlapLeftLinearRing (π := π) a i j)
      (A.isBaseChange_thetaOverlapQuotientMkLinear (π := π) a i j)
  have heq :
      ((A.thetaToOverlapLeftLinearColength (π := π) a i j).restrictScalars
          Γ(relCurve C R, D.pieces i)).comp
        (A.thetaPieceQuotientMkLinear (π := π) a i) =
      ((A.thetaOverlapQuotientMkLinear (π := π) a i j).restrictScalars
          Γ(relCurve C R, D.pieces i)).comp
        (A.thetaSectionsToOverlapLeftLinearRing (π := π) a i j) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [← heq] at hcomp
  exact IsBaseChange.of_comp
    (A.isBaseChange_thetaPieceQuotientMkLinear (π := π) a i) hcomp

/-- The desired pairwise theta-module base-change equivalence. -/
noncomputable def thetaPieceBaseChangeToOverlapLeftEquiv
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index) :
    A.ovlColength i j ⊗[A.colength i] A.ThetaPieceQuotient (π := π) a i
      ≃ₗ[A.ovlColength i j] A.ThetaOverlapQuotient (π := π) a i j :=
  (A.isBaseChange_thetaToOverlapLeftLinearColength (π := π) a i j).equiv

@[simp]
theorem thetaPieceBaseChangeToOverlapLeftEquiv_tmul
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index)
    (c : A.ovlColength i j) (x : A.ThetaPieceQuotient (π := π) a i) :
    A.thetaPieceBaseChangeToOverlapLeftEquiv (π := π) a i j (c ⊗ₜ x) =
      c • A.thetaToOverlapLeft (π := π) a i j x :=
  IsBaseChange.equiv_tmul _ c x

/-- The canonical left map after base change to the pair overlap algebra. -/
noncomputable def thetaPieceBaseChangeToOverlapLeft (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ovlColength i j ⊗[A.colength i] A.ThetaPieceQuotient (π := π) a i →ₗ[A.ovlColength i j]
      A.ThetaOverlapQuotient (π := π) a i j :=
  LinearMap.liftBaseChange (A.ovlColength i j)
    (A.thetaToOverlapLeftLinearColength (π := π) a i j)

@[simp]
lemma thetaPieceBaseChangeToOverlapLeft_tmul (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) (c : A.ovlColength i j)
    (x : A.ThetaPieceQuotient (π := π) a i) :
    A.thetaPieceBaseChangeToOverlapLeft (π := π) a i j (c ⊗ₜ x) =
      c • A.thetaToOverlapLeft (π := π) a i j x := by
  exact LinearMap.liftBaseChange_tmul
    (A.ovlColength i j)
    (A.thetaToOverlapLeftLinearColength (π := π) a i j) c x

@[reducible]
noncomputable def pieceSectionsToOverlapRightAlgebra (i j : D.index) :
    Algebra Γ(relCurve C R, D.pieces j)
      Γ(relCurve C R, D.pieces i ⊓ D.pieces j) :=
  (relResAlgHom C R
    (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j)).toRingHom.toAlgebra

attribute [local instance] pieceSectionsToOverlapRightAlgebra

@[reducible]
noncomputable def thetaOverlapSectionsRightModule (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : Module Γ(relCurve C R, D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
  letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
    A.thetaOverlapSectionsModule (π := π) a i j
  Module.compHom (A.ThetaOverlapSections (π := π) a i j)
    (relResAlgHom C R
      (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j)).toRingHom

attribute [local instance] thetaOverlapSectionsRightModule

@[reducible]
noncomputable def thetaOverlapSectionsRightTower (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : IsScalarTower Γ(relCurve C R, D.pieces j)
      Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] thetaOverlapSectionsRightTower

noncomputable def thetaSectionsToOverlapRightLinearRing (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : A.ThetaPieceSections (π := π) a j →ₗ[Γ(relCurve C R, D.pieces j)]
      A.ThetaOverlapSections (π := π) a i j :=
  { toFun := A.thetaSectionsToOverlapRight (π := π) a i j
    map_add' := (A.thetaSectionsToOverlapRight (π := π) a i j).map_add
    map_smul' := (A.thetaSectionsToOverlapRight (π := π) a i j).map_smulₛₗ }

/-- Restriction of intrinsic theta sections from the right piece to an overlap is a
base change. -/
theorem isBaseChange_thetaSectionsToOverlapRightLinearRing
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index) :
    IsBaseChange Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.thetaSectionsToOverlapRightLinearRing (π := π) a i j) := by
  let MV := A.thetaPieceSectionsModel (π := π) a j
  let MW := A.thetaOverlapSectionsModel (π := π) a i j
  let F := thetaChartDatum C R π a
  letI := MV.qcoh
  letI : Module Γ(relCurve C R, D.pieces j)
      (F.sheaf.obj.obj (op (D.pieces j))) :=
    Scheme.QcohOn.moduleOfLE (F := F.sheaf) (le_refl (D.pieces j))
  letI := MW.qcoh
  letI : Module Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (F.sheaf.obj.obj (op (D.pieces i ⊓ D.pieces j))) :=
    Scheme.QcohOn.moduleOfLE (F := F.sheaf)
      (le_refl (D.pieces i ⊓ D.pieces j))
  letI : Algebra Γ(relCurve C R, D.pieces j)
      Γ(relCurve C R, D.pieces i ⊓ D.pieces j) :=
    ((relCurve C R).resHom
      (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j)).toAlgebra
  letI : Module Γ(relCurve C R, D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
    A.thetaOverlapSectionsRightModule (π := π) a i j
  letI : IsScalarTower Γ(relCurve C R, D.pieces j)
      Γ(relCurve C R, D.pieces i ⊓ D.pieces j)
      (A.ThetaOverlapSections (π := π) a i j) :=
    A.thetaOverlapSectionsRightTower (π := π) a i j
  have hbij := F.affineSectionsBaseChange_bijective
    (D.isAffineOpen j) (D.hasAffineOverlaps_of_isProper i j)
    (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) MV MW
  apply IsBaseChange.of_equiv
    (LinearEquiv.ofBijective
      (F.affineSectionsBaseChange
        (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) MV MW) hbij)
  intro x
  change F.affineSectionsBaseChange
      (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) MV MW
        (1 ⊗ₜ x) = A.thetaSectionsToOverlapRight (π := π) a i j x
  rw [F.affineSectionsBaseChange_tmul, one_smul]
  rfl

@[reducible]
noncomputable def pieceToOverlapRightAlgebra (A : AffAdaptation D d) (i j : D.index) :
    Algebra (A.colength j) (A.ovlColength i j) :=
  (A.toOvlRight i j).toRingHom.toAlgebra

attribute [local instance] pieceToOverlapRightAlgebra

@[reducible]
noncomputable def pieceSectionsColengthOverlapRightTower (A : AffAdaptation D d)
    (i j : D.index) : IsScalarTower Γ(relCurve C R, D.pieces j)
      (A.colength j) (A.ovlColength i j) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] pieceSectionsColengthOverlapRightTower

/-- The overlap quotient, restricted to the right piece colength algebra. -/
@[reducible]
noncomputable def thetaOverlapQuotientRightModule (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    Module (A.colength j) (A.ThetaOverlapQuotient (π := π) a i j) :=
  letI : Module (A.ovlColength i j) (A.ThetaOverlapQuotient (π := π) a i j) :=
    A.thetaOverlapQuotientModule (π := π) a i j
  Module.compHom (A.ThetaOverlapQuotient (π := π) a i j)
    (A.toOvlRight i j).toRingHom

attribute [local instance] thetaOverlapQuotientRightModule

@[reducible]
noncomputable def thetaOverlapQuotientRightTower (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) : IsScalarTower (A.colength j) (A.ovlColength i j)
      (A.ThetaOverlapQuotient (π := π) a i j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] thetaOverlapQuotientRightTower

@[reducible]
noncomputable def pieceSectionsColengthThetaOverlapRightTower
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index) :
    IsScalarTower Γ(relCurve C R, D.pieces j) (A.colength j)
      (A.ThetaOverlapQuotient (π := π) a i j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] pieceSectionsColengthThetaOverlapRightTower

@[reducible]
noncomputable def thetaPieceToOverlapRightCompatibleSMul
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index) :
    LinearMap.CompatibleSMul
      (A.ThetaPieceQuotient (π := π) a j)
      (A.ThetaOverlapQuotient (π := π) a i j)
      Γ(relCurve C R, D.pieces j) (A.colength j) where
  map_smul f r x := by
    change f (Ideal.Quotient.mk (Ideal.span {A.eqn j}) r • x) =
      A.toOvlRight i j (Ideal.Quotient.mk (Ideal.span {A.eqn j}) r) • f x
    exact f.map_smul _ x

attribute [local instance] thetaPieceToOverlapRightCompatibleSMul

noncomputable def thetaToOverlapRightLinearColength (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaPieceQuotient (π := π) a j →ₗ[A.colength j]
      A.ThetaOverlapQuotient (π := π) a i j :=
  { toFun := A.thetaToOverlapRight (π := π) a i j
    map_add' := (A.thetaToOverlapRight (π := π) a i j).map_add
    map_smul' := A.thetaToOverlapRight_smul (π := π) a i j }

/-- The induced right divisor-quotient restriction is a base change. -/
theorem isBaseChange_thetaToOverlapRightLinearColength
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index) :
    IsBaseChange (A.ovlColength i j)
      (A.thetaToOverlapRightLinearColength (π := π) a i j) := by
  have hcomp : IsBaseChange (A.ovlColength i j)
      (((A.thetaOverlapQuotientMkLinear (π := π) a i j).restrictScalars
          Γ(relCurve C R, D.pieces j)).comp
        (A.thetaSectionsToOverlapRightLinearRing (π := π) a i j)) :=
    IsBaseChange.comp
      (A.isBaseChange_thetaSectionsToOverlapRightLinearRing (π := π) a i j)
      (A.isBaseChange_thetaOverlapQuotientMkLinear (π := π) a i j)
  have heq :
      ((A.thetaToOverlapRightLinearColength (π := π) a i j).restrictScalars
          Γ(relCurve C R, D.pieces j)).comp
        (A.thetaPieceQuotientMkLinear (π := π) a j) =
      ((A.thetaOverlapQuotientMkLinear (π := π) a i j).restrictScalars
          Γ(relCurve C R, D.pieces j)).comp
        (A.thetaSectionsToOverlapRightLinearRing (π := π) a i j) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [← heq] at hcomp
  exact IsBaseChange.of_comp
    (A.isBaseChange_thetaPieceQuotientMkLinear (π := π) a j) hcomp

/-- Base change of the right piece theta quotient to the pair overlap. -/
noncomputable def thetaPieceBaseChangeToOverlapRightEquiv
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index) :
    A.ovlColength i j ⊗[A.colength j] A.ThetaPieceQuotient (π := π) a j
      ≃ₗ[A.ovlColength i j] A.ThetaOverlapQuotient (π := π) a i j :=
  (A.isBaseChange_thetaToOverlapRightLinearColength (π := π) a i j).equiv

@[simp]
theorem thetaPieceBaseChangeToOverlapRightEquiv_tmul
    (A : AffAdaptation D d) (a : ℕ) (i j : D.index)
    (c : A.ovlColength i j) (x : A.ThetaPieceQuotient (π := π) a j) :
    A.thetaPieceBaseChangeToOverlapRightEquiv (π := π) a i j (c ⊗ₜ x) =
      c • A.thetaToOverlapRight (π := π) a i j x :=
  IsBaseChange.equiv_tmul _ c x

/-- The canonical right map after base change to the pair overlap algebra. -/
noncomputable def thetaPieceBaseChangeToOverlapRight (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ovlColength i j ⊗[A.colength j] A.ThetaPieceQuotient (π := π) a j
      →ₗ[A.ovlColength i j] A.ThetaOverlapQuotient (π := π) a i j :=
  LinearMap.liftBaseChange (A.ovlColength i j)
    (A.thetaToOverlapRightLinearColength (π := π) a i j)

@[simp]
lemma thetaPieceBaseChangeToOverlapRight_tmul (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) (c : A.ovlColength i j)
    (x : A.ThetaPieceQuotient (π := π) a j) :
    A.thetaPieceBaseChangeToOverlapRight (π := π) a i j (c ⊗ₜ x) =
      c • A.thetaToOverlapRight (π := π) a i j x := by
  exact LinearMap.liftBaseChange_tmul
    (A.ovlColength i j)
    (A.thetaToOverlapRightLinearColength (π := π) a i j) c x

end AffAdaptation

end AlgebraicGeometry
