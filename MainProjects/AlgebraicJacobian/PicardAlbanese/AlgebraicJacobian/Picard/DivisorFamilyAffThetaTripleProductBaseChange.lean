/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaProductBaseChange
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaTripleBaseChange
import AlgebraicJacobian.Picard.DivisorSubschemeTensorTriple

/-!
# Product base change to intrinsic triple theta quotients

The first pairwise theta quotient restricts to a triple intersection by base change.
The affine divisor pushout square identifies the same triple coefficient ring with the
base change of the pairwise coefficient ring along the third piece.  Combining these
facts gives, for every triple,

`colength l ⊗[gluedSubalgebra A] ThetaOverlapQuotient i j ≃ ThetaTripleQuotient i j l`.

This is the component comparison used to test equality of the two base-changed Cech
faces.  It uses only the existing certification of the widened affine adaptation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

attribute [local instance] thetaOverlapQuotientModule thetaTripleQuotientModule
  thetaOverlapQuotientGluedModule overlap12ToTripleAlgebra
  gluedSubalgebraTripleAlgebra chartProdPieceAlgebra thetaOverlapProdADModule

noncomputable section

variable (A : AffAdaptation D d) (a : ℕ)

/-- The triple coefficient ring as an algebra over its third piece. -/
@[reducible]
noncomputable def pieceThirdToTripleAlgebra (i j l : D.index) :
    Algebra (A.colength l) (A.tripleColength i j l) :=
  (A.pieceToTripleThird i j l).toRingHom.toAlgebra

attribute [local instance] pieceThirdToTripleAlgebra

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent overlap and triple algebras require a larger synthesis budget.
/-- The global-to-overlap-to-triple scalar tower is the chosen global algebra structure
on the triple ring. -/
@[reducible]
noncomputable def gluedOverlapTripleTower (i j l : D.index) :
    IsScalarTower (gluedSubalgebra A) (A.ovlColength i j)
      (A.tripleColength i j l) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] gluedOverlapTripleTower

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent piece and triple algebras require a larger synthesis budget.
/-- Commutativity of the geometric pushout square supplies the other scalar tower. -/
@[reducible]
noncomputable def IsCertified.gluedPieceThirdTripleTower {n : ℕ}
    (hc : A.IsCertified n) (i j l : D.index) :
    IsScalarTower (gluedSubalgebra A) (A.colength l)
      (A.tripleColength i j l) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact congrArg (fun f => f.hom c)
    (hc.isPushout_gluedSubalgebraOverlapPieceMaps A i j l).w

/-- The triple quotient restricted to the third piece coefficient ring. -/
@[reducible]
noncomputable def thetaTripleQuotientPieceThirdModule (i j l : D.index) :
    Module (A.colength l) (A.ThetaTripleQuotient (π := π) a i j l) :=
  Module.compHom _ (A.pieceToTripleThird i j l).toRingHom

attribute [local instance] thetaTripleQuotientPieceThirdModule

/-- The third-piece/triple-ring scalar tower on the intrinsic triple quotient. -/
@[reducible]
noncomputable def pieceThirdTripleThetaTower (i j l : D.index) :
    IsScalarTower (A.colength l) (A.tripleColength i j l)
      (A.ThetaTripleQuotient (π := π) a i j l) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] pieceThirdTripleThetaTower

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent overlap algebra and quotient module require a larger synthesis budget.
/-- The global/overlap scalar tower on a pairwise theta quotient. -/
@[reducible]
noncomputable def gluedOverlapThetaTower (i j : D.index) :
    IsScalarTower (gluedSubalgebra A) (A.ovlColength i j)
      (A.ThetaOverlapQuotient (π := π) a i j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] gluedOverlapThetaTower

set_option synthInstance.maxHeartbeats 500000 in
-- Four dependent coefficient algebras meet in the pushout comparison.
/-- Base change of a pairwise theta quotient along a third divisor piece is the
intrinsic theta quotient on the corresponding triple intersection. -/
noncomputable def IsCertified.thetaOverlapBaseChangeToTripleCoord {n : ℕ}
    (hc : A.IsCertified n) (i j l : D.index) :
    A.colength l ⊗[gluedSubalgebra A]
        A.ThetaOverlapQuotient (π := π) a i j
      ≃ₗ[A.colength l]
        A.ThetaTripleQuotient (π := π) a i j l := by
  letI := hc.gluedPieceThirdTripleTower A i j l
  let hpush : Algebra.IsPushout (gluedSubalgebra A) (A.ovlColength i j)
      (A.colength l) (A.tripleColength i j l) :=
    CommRingCat.isPushout_iff_isPushout.mp
      (hc.isPushout_gluedSubalgebraOverlapPieceMaps A i j l)
  letI : Algebra.IsPushout (gluedSubalgebra A) (A.colength l)
      (A.ovlColength i j) (A.tripleColength i j l) :=
    Algebra.IsPushout.symm hpush
  let e := (Algebra.IsPushout.cancelBaseChange
    (gluedSubalgebra A) (A.colength l) (A.ovlColength i j)
      (A.tripleColength i j l)
      (A.ThetaOverlapQuotient (π := π) a i j)).symm
  exact e.trans ((A.thetaOverlap12BaseChangeToTripleEquiv
    (π := π) a i j l).restrictScalars (A.colength l))

set_option synthInstance.maxHeartbeats 500000 in
-- Elaborating the dependent pure tensor repeats the pushout instance search.
@[simp]
theorem IsCertified.thetaOverlapBaseChangeToTripleCoord_tmul {n : ℕ}
    (hc : A.IsCertified n) (i j l : D.index) (c : A.colength l)
    (x : A.ThetaOverlapQuotient (π := π) a i j) :
    hc.thetaOverlapBaseChangeToTripleCoord A a i j l
        (c ⊗ₜ[gluedSubalgebra A] x) =
      A.pieceToTripleThird i j l c •
        A.thetaOverlapToTriple (π := π) a i j i j l
          (A.thetaTripleOpen_le_pair12 i j l) x := by
  simp only [IsCertified.thetaOverlapBaseChangeToTripleCoord,
    LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul,
    thetaOverlap12BaseChangeToTripleEquiv_tmul]
  rfl

/-- The product of intrinsic theta quotients on ordered triple intersections, grouped
by the first pair and then the third index. -/
noncomputable abbrev ThetaTripleProd : Type u :=
  ∀ p : D.index × D.index, ∀ l : D.index,
    A.ThetaTripleQuotient (π := π) a p.1 p.2 l

/-- A triple theta quotient restricted to the chart-product algebra through its third
piece coordinate. -/
@[reducible]
noncomputable def thetaTripleQuotientCPModule (i j l : D.index) :
    Module A.chartProd (A.ThetaTripleQuotient (π := π) a i j l) :=
  Module.compHom _ (A.chartProdPieceAlgHom l).toRingHom

attribute [local instance] thetaTripleQuotientCPModule

/-- The chart-product/third-piece scalar tower on a triple theta quotient. -/
@[reducible]
noncomputable def chartProdPieceTripleThetaTower (i j l : D.index) :
    IsScalarTower A.chartProd (A.colength l)
      (A.ThetaTripleQuotient (π := π) a i j l) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] chartProdPieceTripleThetaTower

/-- The chart-product module on triple theta quotients for a fixed first pair. -/
@[reducible]
noncomputable def thetaTripleInnerCPModule (p : D.index × D.index) :
    Module A.chartProd (∀ l : D.index,
      A.ThetaTripleQuotient (π := π) a p.1 p.2 l) := by
  letI : ∀ l : D.index, Module A.chartProd
      (A.ThetaTripleQuotient (π := π) a p.1 p.2 l) :=
    fun l => A.thetaTripleQuotientCPModule (π := π) a p.1 p.2 l
  exact Pi.module D.index
    (fun l => A.ThetaTripleQuotient (π := π) a p.1 p.2 l) A.chartProd

attribute [local instance] thetaTripleInnerCPModule

/-- The pointwise chart-product module on all ordered triple intersections. -/
@[reducible]
noncomputable def thetaTripleProdCPModule :
    Module A.chartProd (A.ThetaTripleProd (π := π) a) := by
  letI : ∀ p : D.index × D.index, Module A.chartProd
      (∀ l : D.index, A.ThetaTripleQuotient (π := π) a p.1 p.2 l) :=
    fun p => A.thetaTripleInnerCPModule (π := π) a p
  exact Pi.module (D.index × D.index)
    (fun p => ∀ l : D.index,
      A.ThetaTripleQuotient (π := π) a p.1 p.2 l) A.chartProd

attribute [local instance] thetaTripleProdCPModule

/-- Tensoring the product of pairwise theta quotients distributes over its finite pair
index. -/
noncomputable def chartProdTensorOverlapPiEquiv :
    A.chartProd ⊗[gluedSubalgebra A] A.ThetaOverlapProd (π := π) a
      ≃ₗ[A.chartProd]
      (∀ p : D.index × D.index,
        A.chartProd ⊗[gluedSubalgebra A]
          A.ThetaOverlapQuotient (π := π) a p.1 p.2) :=
  TensorProduct.piRight (gluedSubalgebra A) A.chartProd A.chartProd
    (fun p : D.index × D.index =>
      A.ThetaOverlapQuotient (π := π) a p.1 p.2)

set_option synthInstance.maxHeartbeats 500000 in
-- The coefficient product and dependent overlap quotient require a larger synthesis budget.
/-- For a fixed pair, distribute the chart-product coefficient over the third index.
This is first recorded over the global glued algebra. -/
noncomputable def overlapCoordinateDistribBase (p : D.index × D.index) :
    A.chartProd ⊗[gluedSubalgebra A]
        A.ThetaOverlapQuotient (π := π) a p.1 p.2
      ≃ₗ[gluedSubalgebra A]
      (∀ l : D.index,
        A.colength l ⊗[gluedSubalgebra A]
          A.ThetaOverlapQuotient (π := π) a p.1 p.2) :=
  (TensorProduct.comm (gluedSubalgebra A) A.chartProd
      (A.ThetaOverlapQuotient (π := π) a p.1 p.2)).trans <|
    (TensorProduct.piRight (gluedSubalgebra A) (gluedSubalgebra A)
      (A.ThetaOverlapQuotient (π := π) a p.1 p.2)
      (fun l : D.index => A.colength l)).trans <|
        LinearEquiv.piCongrRight fun l : D.index =>
          TensorProduct.comm (gluedSubalgebra A)
            (A.ThetaOverlapQuotient (π := π) a p.1 p.2)
            (A.colength l)

set_option synthInstance.maxHeartbeats 500000 in
-- Expanding the dependent tensor distribution repeats its module synthesis.
@[simp]
theorem overlapCoordinateDistribBase_tmul_apply
    (p : D.index × D.index) (b : A.chartProd)
    (x : A.ThetaOverlapQuotient (π := π) a p.1 p.2) (l : D.index) :
    A.overlapCoordinateDistribBase (π := π) a p
        (b ⊗ₜ[gluedSubalgebra A] x) l =
      b l ⊗ₜ[gluedSubalgebra A] x := by
  simp [overlapCoordinateDistribBase, TensorProduct.piRight_apply]

set_option maxHeartbeats 1000000 in
-- Verifying chart-product linearity expands the full dependent tensor equivalence.
set_option synthInstance.maxHeartbeats 500000 in
-- Promoting the dependent distribution uses both global and coordinate scalar actions.
/-- The same coordinate distribution, with its natural chart-product linearity. -/
noncomputable def overlapCoordinateDistrib (p : D.index × D.index) :
    A.chartProd ⊗[gluedSubalgebra A]
        A.ThetaOverlapQuotient (π := π) a p.1 p.2
      ≃ₗ[A.chartProd]
      (∀ l : D.index,
        A.colength l ⊗[gluedSubalgebra A]
          A.ThetaOverlapQuotient (π := π) a p.1 p.2) := by
  let e := A.overlapCoordinateDistribBase (π := π) a p
  let f : A.chartProd ⊗[gluedSubalgebra A]
      A.ThetaOverlapQuotient (π := π) a p.1 p.2 →ₗ[A.chartProd]
      (∀ l : D.index,
        A.colength l ⊗[gluedSubalgebra A]
          A.ThetaOverlapQuotient (π := π) a p.1 p.2) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro c z
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero, smul_zero]
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul b x =>
            funext l
            change (c l * b l) ⊗ₜ[gluedSubalgebra A] x =
              c l • (b l ⊗ₜ[gluedSubalgebra A] x)
            rw [TensorProduct.smul_tmul', Algebra.smul_def,
              Algebra.algebraMap_self_apply] }
  exact LinearEquiv.ofBijective f e.bijective

set_option synthInstance.maxHeartbeats 500000 in
-- The chart-product-linear wrapper retains the dependent coordinate module structure.
@[simp]
theorem overlapCoordinateDistrib_tmul_apply
    (p : D.index × D.index) (b : A.chartProd)
    (x : A.ThetaOverlapQuotient (π := π) a p.1 p.2) (l : D.index) :
    A.overlapCoordinateDistrib (π := π) a p
        (b ⊗ₜ[gluedSubalgebra A] x) l =
      b l ⊗ₜ[gluedSubalgebra A] x := by
  change A.overlapCoordinateDistribBase (π := π) a p
      (b ⊗ₜ[gluedSubalgebra A] x) l = _
  exact A.overlapCoordinateDistribBase_tmul_apply (π := π) a p b x l

set_option synthInstance.maxHeartbeats 500000 in
-- The nested dependent products combine the chart, overlap, and triple module towers.
/-- Apply the component triple comparison over every pair and every third index. -/
noncomputable def IsCertified.thetaOverlapBaseChangeTripleNestedEquiv {n : ℕ}
    (hc : A.IsCertified n) :
    (∀ p : D.index × D.index,
      A.chartProd ⊗[gluedSubalgebra A]
        A.ThetaOverlapQuotient (π := π) a p.1 p.2)
      ≃ₗ[A.chartProd] A.ThetaTripleProd (π := π) a :=
  LinearEquiv.piCongrRight fun p =>
    (A.overlapCoordinateDistrib (π := π) a p).trans <|
      LinearEquiv.piCongrRight fun l =>
        (hc.thetaOverlapBaseChangeToTripleCoord A a p.1 p.2 l).restrictScalars
          A.chartProd

/-- The tensor base change of the pairwise theta product is the product of intrinsic
theta quotients on triple intersections. -/
noncomputable def IsCertified.thetaOverlapProdBaseChangeToTripleEquiv {n : ℕ}
    (hc : A.IsCertified n) :
    A.chartProd ⊗[gluedSubalgebra A] A.ThetaOverlapProd (π := π) a
      ≃ₗ[A.chartProd] A.ThetaTripleProd (π := π) a :=
  (A.chartProdTensorOverlapPiEquiv (π := π) a).trans
    (hc.thetaOverlapBaseChangeTripleNestedEquiv A a)

set_option synthInstance.maxHeartbeats 500000 in
-- Expanding a pure tensor traverses both finite-product distributions and the pushout.
@[simp]
theorem IsCertified.thetaOverlapProdBaseChangeToTripleEquiv_tmul_apply {n : ℕ}
    (hc : A.IsCertified n) (b : A.chartProd)
    (s : A.ThetaOverlapProd (π := π) a)
    (p : D.index × D.index) (l : D.index) :
    hc.thetaOverlapProdBaseChangeToTripleEquiv A a
        (b ⊗ₜ[gluedSubalgebra A] s) p l =
      A.pieceToTripleThird p.1 p.2 l (b l) •
        A.thetaOverlapToTriple (π := π) a p.1 p.2 p.1 p.2 l
          (A.thetaTripleOpen_le_pair12 p.1 p.2 l) (s p) := by
  simp only [IsCertified.thetaOverlapProdBaseChangeToTripleEquiv,
    LinearEquiv.trans_apply,
    IsCertified.thetaOverlapBaseChangeTripleNestedEquiv,
    LinearEquiv.piCongrRight_apply, chartProdTensorOverlapPiEquiv,
    TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    overlapCoordinateDistrib_tmul_apply,
    LinearEquiv.restrictScalars_apply,
    IsCertified.thetaOverlapBaseChangeToTripleCoord_tmul]

end

end AffAdaptation

end AlgebraicGeometry
