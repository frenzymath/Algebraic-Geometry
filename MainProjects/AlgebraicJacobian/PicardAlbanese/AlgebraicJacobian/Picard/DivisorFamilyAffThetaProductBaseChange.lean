/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaOverlapBaseChange
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaCech
import AlgebraicJacobian.Picard.DivisorSubschemeTensorOverlap
import AlgebraicJacobian.Algebra.LocalizationTrivialization

/-!
# Product base change for intrinsic theta modules

The pairwise theta restrictions are base changes along the two maps from a piece colength
algebra to an overlap colength algebra. Together with the tensor-square identification of
the finite affine divisor cover, this assembles into the comparison

`chartProd ⊗[gluedSubalgebra] ThetaPieceProd ≃ ThetaOverlapProd`.

The comparison is the Cech module interface consumed by faithful-flat descent. It is stated
for an arbitrary certified affine adaptation and introduces no containment, chart-typing, or
additional hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

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
  thetaOverlapQuotientLeftModule thetaOverlapQuotientLeftTower

noncomputable section

variable (A : AffAdaptation D d) (a : ℕ)

attribute [local instance] thetaPieceQuotientGluedModule
  thetaOverlapQuotientGluedModule

noncomputable def chartProdPieceAlgHom (j : D.index) :
    A.chartProd →ₐ[R] A.colength j :=
  Pi.evalAlgHom R (fun j : D.index => A.colength j) j

@[reducible]
noncomputable def chartProdPieceAlgebra (j : D.index) :
    Algebra A.chartProd (A.colength j) :=
  (A.chartProdPieceAlgHom j).toRingHom.toAlgebra

noncomputable def chartProdOverlapAlgHom (i j : D.index) :
    A.chartProd →ₐ[R] A.ovlColength i j :=
  (A.toOvlLeft i j).comp (A.chartProdPieceAlgHom i)

@[reducible]
noncomputable def chartProdOverlapAlgebra (i j : D.index) :
    Algebra A.chartProd (A.ovlColength i j) :=
  (A.chartProdOverlapAlgHom i j).toRingHom.toAlgebra

attribute [local instance] chartProdPieceAlgebra chartProdOverlapAlgebra

@[reducible]
noncomputable def thetaPieceProdADModule :
    Module (↥(gluedSubalgebra A)) (A.ThetaPieceProd (π := π) a) := by
  letI : ∀ j : D.index, Module (↥(gluedSubalgebra A))
      (A.ThetaPieceQuotient (π := π) a j) :=
    fun j => A.thetaPieceQuotientGluedModule (π := π) a j
  exact Pi.module D.index
    (fun j => A.ThetaPieceQuotient (π := π) a j)
    (↥(gluedSubalgebra A))

attribute [local instance] thetaPieceProdADModule

@[reducible]
noncomputable def thetaPieceProdCPModule :
    Module A.chartProd (A.ThetaPieceProd (π := π) a) := by
  letI : ∀ j : D.index, Module (A.colength j)
      (A.ThetaPieceQuotient (π := π) a j) :=
    fun j => A.thetaPieceQuotientModule (π := π) a j
  exact Pi.module' (f := fun j : D.index => A.colength j)
    (g := fun j => A.ThetaPieceQuotient (π := π) a j)

attribute [local instance] thetaPieceProdCPModule

@[reducible]
noncomputable def thetaPieceProdTower : IsScalarTower (↥(gluedSubalgebra A))
    A.chartProd (A.ThetaPieceProd (π := π) a) := by
  letI : ∀ j : D.index, Module (↥(gluedSubalgebra A))
      (A.ThetaPieceQuotient (π := π) a j) :=
    fun j => A.thetaPieceQuotientGluedModule (π := π) a j
  letI : ∀ j : D.index, Module (A.colength j)
      (A.ThetaPieceQuotient (π := π) a j) :=
    fun j => A.thetaPieceQuotientModule (π := π) a j
  constructor
  intro c b x
  funext j
  change (c.1 j * b j) • x j = c.1 j • (b j • x j)
  exact mul_smul _ _ _

attribute [local instance] thetaPieceProdTower

@[reducible]
noncomputable def thetaOverlapProdOvlModule : Module A.ovlProd
    (A.ThetaOverlapProd (π := π) a) := by
  letI : ∀ p : D.index × D.index, Module (A.ovlColength p.1 p.2)
      (A.ThetaOverlapQuotient (π := π) a p.1 p.2) :=
    fun p => A.thetaOverlapQuotientModule (π := π) a p.1 p.2
  exact Pi.module' (f := fun p : D.index × D.index => A.ovlColength p.1 p.2)
    (g := fun p => A.ThetaOverlapQuotient (π := π) a p.1 p.2)

attribute [local instance] thetaOverlapProdOvlModule

noncomputable def chartProdToOvlProdAlgHom : A.chartProd →ₐ[R] A.ovlProd :=
  Pi.algHom R (fun p : D.index × D.index => A.ovlColength p.1 p.2)
    (fun p => A.chartProdOverlapAlgHom p.1 p.2)

@[reducible]
noncomputable def thetaOverlapQuotientCPModule (i j : D.index) :
    Module A.chartProd (A.ThetaOverlapQuotient (π := π) a i j) :=
  Module.compHom _ (A.chartProdOverlapAlgHom i j).toRingHom

attribute [local instance] thetaOverlapQuotientCPModule

@[reducible]
noncomputable def thetaOverlapProdCPModule : Module A.chartProd
    (A.ThetaOverlapProd (π := π) a) := by
  letI : ∀ p : D.index × D.index, Module A.chartProd
      (A.ThetaOverlapQuotient (π := π) a p.1 p.2) :=
    fun p => A.thetaOverlapQuotientCPModule (π := π) a p.1 p.2
  exact Pi.module (D.index × D.index)
    (fun p => A.ThetaOverlapQuotient (π := π) a p.1 p.2) A.chartProd

attribute [local instance] thetaOverlapProdCPModule

noncomputable def chartProdTensorPiecePiEquiv :
    A.chartProd ⊗[↥(gluedSubalgebra A)]
        A.ThetaPieceProd (π := π) a ≃ₗ[A.chartProd]
      (∀ j : D.index,
        A.chartProd ⊗[↥(gluedSubalgebra A)]
          A.ThetaPieceQuotient (π := π) a j) := by
  exact TensorProduct.piRight (↥(gluedSubalgebra A)) A.chartProd A.chartProd
    (fun j : D.index => A.ThetaPieceQuotient (π := π) a j)

noncomputable def pieceCoordinateDistribBase (j : D.index) :
    A.chartProd ⊗[↥(gluedSubalgebra A)]
        A.ThetaPieceQuotient (π := π) a j ≃ₗ[↥(gluedSubalgebra A)]
      (∀ i : D.index,
        A.colength i ⊗[↥(gluedSubalgebra A)]
          A.ThetaPieceQuotient (π := π) a j) :=
  (TensorProduct.comm (↥(gluedSubalgebra A)) A.chartProd
      (A.ThetaPieceQuotient (π := π) a j)).trans <|
    (TensorProduct.piRight (↥(gluedSubalgebra A)) (↥(gluedSubalgebra A))
      (A.ThetaPieceQuotient (π := π) a j)
      (fun i : D.index => A.colength i)).trans <|
        LinearEquiv.piCongrRight fun i : D.index =>
          TensorProduct.comm (↥(gluedSubalgebra A))
            (A.ThetaPieceQuotient (π := π) a j) (A.colength i)

@[simp]
lemma pieceCoordinateDistribBase_tmul_apply (j : D.index)
    (b : A.chartProd) (m : A.ThetaPieceQuotient (π := π) a j) (i : D.index) :
    A.pieceCoordinateDistribBase (π := π) a j
        (b ⊗ₜ[↥(gluedSubalgebra A)] m) i =
      b i ⊗ₜ[↥(gluedSubalgebra A)] m := by
  simp [pieceCoordinateDistribBase, TensorProduct.piRight_apply]

noncomputable def pieceCoordinateDistrib (j : D.index) :
    A.chartProd ⊗[↥(gluedSubalgebra A)]
        A.ThetaPieceQuotient (π := π) a j ≃ₗ[A.chartProd]
      (∀ i : D.index,
        A.colength i ⊗[↥(gluedSubalgebra A)]
          A.ThetaPieceQuotient (π := π) a j) := by
  let e := A.pieceCoordinateDistribBase (π := π) a j
  let f : A.chartProd ⊗[↥(gluedSubalgebra A)]
      A.ThetaPieceQuotient (π := π) a j →ₗ[A.chartProd]
      (∀ i : D.index,
        A.colength i ⊗[↥(gluedSubalgebra A)]
          A.ThetaPieceQuotient (π := π) a j) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro c x
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero, smul_zero]
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul b m =>
            funext i
            change (c i * b i) ⊗ₜ[↥(gluedSubalgebra A)] m =
              c i • (b i ⊗ₜ[↥(gluedSubalgebra A)] m)
            rw [TensorProduct.smul_tmul', Algebra.smul_def,
              Algebra.algebraMap_self_apply] }
  exact LinearEquiv.ofBijective f e.bijective

@[simp]
theorem pieceCoordinateDistrib_tmul_apply (j : D.index)
    (b : A.chartProd) (m : A.ThetaPieceQuotient (π := π) a j) (i : D.index) :
    A.pieceCoordinateDistrib (π := π) a j
        (b ⊗ₜ[↥(gluedSubalgebra A)] m) i =
      b i ⊗ₜ[↥(gluedSubalgebra A)] m := by
  change A.pieceCoordinateDistribBase (π := π) a j
      (b ⊗ₜ[↥(gluedSubalgebra A)] m) i = _
  exact A.pieceCoordinateDistribBase_tmul_apply (π := π) a j b m i

@[reducible]
noncomputable def productOverlapRightAlgebra (i j : D.index) :
    Algebra (A.colength j) (A.ovlColength i j) :=
  (A.toOvlRight i j).toRingHom.toAlgebra

attribute [local instance] productOverlapRightAlgebra

@[reducible]
noncomputable def productOverlapLeftAlgebra (i j : D.index) :
    Algebra (A.colength i) (A.ovlColength i j) :=
  (A.toOvlLeft i j).toRingHom.toAlgebra

attribute [local instance] productOverlapLeftAlgebra

@[reducible]
noncomputable def productOverlapRightTower (i j : D.index) : IsScalarTower
    (↥(gluedSubalgebra A)) (A.colength j) (A.ovlColength i j) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change A.toOvlLeft i j (c.1 i) = A.toOvlRight i j (c.1 j)
  exact (A.mem_gluedSubmodule_iff (c : A.chartProd)).mp c.2 (i, j)

attribute [local instance] productOverlapRightTower

@[reducible]
noncomputable def productPieceTower (j : D.index) : IsScalarTower
    (↥(gluedSubalgebra A)) (A.colength j)
      (A.ThetaPieceQuotient (π := π) a j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] productPieceTower

@[reducible]
noncomputable def productOverlapLeftTower (i j : D.index) : IsScalarTower
    (↥(gluedSubalgebra A)) (A.colength i) (A.ovlColength i j) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] productOverlapLeftTower

@[reducible]
noncomputable def productOverlapThetaLeftTower (i j : D.index) : IsScalarTower
    (↥(gluedSubalgebra A)) (A.colength i)
      (A.ThetaOverlapQuotient (π := π) a i j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] productOverlapThetaLeftTower

@[reducible]
noncomputable def productOverlapThetaCPTower (i j : D.index) : IsScalarTower
    A.chartProd (A.colength i)
      (A.ThetaOverlapQuotient (π := π) a i j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] productOverlapThetaCPTower

noncomputable def thetaPieceBaseChangeToOverlapCoord {n : ℕ}
    (hc : A.IsCertified n) (i j : D.index) :
    A.colength i ⊗[↥(gluedSubalgebra A)]
        A.ThetaPieceQuotient (π := π) a j ≃ₗ[A.colength i]
      A.ThetaOverlapQuotient (π := π) a i j := by
  letI : Algebra.IsPushout (↥(gluedSubalgebra A)) (A.colength i)
      (A.colength j) (A.ovlColength i j) :=
    CommRingCat.isPushout_iff_isPushout.mp
      (hc.isPushout_gluedSubalgebraPieceMaps A i j)
  let e := (Algebra.IsPushout.cancelBaseChange
    (↥(gluedSubalgebra A)) (A.colength i) (A.colength j)
      (A.ovlColength i j)
      (A.ThetaPieceQuotient (π := π) a j)).symm
  exact e.trans ((A.thetaPieceBaseChangeToOverlapRightEquiv
    (π := π) a i j).restrictScalars (A.colength i))

@[simp]
theorem thetaPieceBaseChangeToOverlapCoord_tmul {n : ℕ}
    (hc : A.IsCertified n) (i j : D.index) (x : A.colength i)
    (m : A.ThetaPieceQuotient (π := π) a j) :
    A.thetaPieceBaseChangeToOverlapCoord (π := π) a hc i j
        (x ⊗ₜ[↥(gluedSubalgebra A)] m) =
      A.toOvlLeft i j x • A.thetaToOverlapRight (π := π) a i j m := by
  simp only [thetaPieceBaseChangeToOverlapCoord,
    LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul,
    thetaPieceBaseChangeToOverlapRightEquiv_tmul]
  rfl

@[reducible]
noncomputable def thetaOverlapProdADModule : Module (↥(gluedSubalgebra A))
    (A.ThetaOverlapProd (π := π) a) := by
  letI : ∀ p : D.index × D.index, Module (↥(gluedSubalgebra A))
      (A.ThetaOverlapQuotient (π := π) a p.1 p.2) :=
    fun p => A.thetaOverlapQuotientGluedModule (π := π) a p.1 p.2
  exact Pi.module (D.index × D.index)
    (fun p => A.ThetaOverlapQuotient (π := π) a p.1 p.2)
    (↥(gluedSubalgebra A))

attribute [local instance] thetaOverlapProdADModule

@[reducible]
noncomputable def thetaOverlapProdTower : IsScalarTower (↥(gluedSubalgebra A))
    A.chartProd (A.ThetaOverlapProd (π := π) a) := by
  constructor
  intro c b x
  funext p
  change A.toOvlLeft p.1 p.2 (c.1 p.1 * b p.1) • x p =
    A.toOvlLeft p.1 p.2 (c.1 p.1) •
      (A.toOvlLeft p.1 p.2 (b p.1) • x p)
  rw [map_mul, mul_smul]

attribute [local instance] thetaOverlapProdTower

@[reducible]
noncomputable def thetaOverlapNestedADModule : Module (↥(gluedSubalgebra A))
    (∀ j : D.index, ∀ i : D.index,
      A.ThetaOverlapQuotient (π := π) a i j) := by
  letI : ∀ j : D.index, ∀ i : D.index, Module (↥(gluedSubalgebra A))
      (A.ThetaOverlapQuotient (π := π) a i j) :=
    fun j i => A.thetaOverlapQuotientGluedModule (π := π) a i j
  letI : ∀ j : D.index, Module (↥(gluedSubalgebra A))
      (∀ i : D.index, A.ThetaOverlapQuotient (π := π) a i j) :=
    fun j => Pi.module D.index
      (fun i => A.ThetaOverlapQuotient (π := π) a i j)
      (↥(gluedSubalgebra A))
  exact Pi.module D.index
    (fun j => ∀ i : D.index,
      A.ThetaOverlapQuotient (π := π) a i j)
    (↥(gluedSubalgebra A))

attribute [local instance] thetaOverlapNestedADModule

@[reducible]
noncomputable def thetaOverlapInnerCPModule (j : D.index) :
    Module A.chartProd (∀ i : D.index,
      A.ThetaOverlapQuotient (π := π) a i j) := by
  letI : ∀ i : D.index, Module A.chartProd
      (A.ThetaOverlapQuotient (π := π) a i j) :=
    fun i => A.thetaOverlapQuotientCPModule (π := π) a i j
  exact Pi.module D.index
    (fun i => A.ThetaOverlapQuotient (π := π) a i j) A.chartProd

attribute [local instance] thetaOverlapInnerCPModule

@[reducible]
noncomputable def thetaOverlapNestedCPModule : Module A.chartProd
    (∀ j : D.index, ∀ i : D.index,
      A.ThetaOverlapQuotient (π := π) a i j) := by
  letI : ∀ j : D.index, Module A.chartProd
      (∀ i : D.index, A.ThetaOverlapQuotient (π := π) a i j) :=
    fun j => A.thetaOverlapInnerCPModule (π := π) a j
  exact Pi.module D.index
    (fun j => ∀ i : D.index,
      A.ThetaOverlapQuotient (π := π) a i j) A.chartProd

attribute [local instance] thetaOverlapNestedCPModule

noncomputable def thetaOverlapProdSwapEquiv :
    (∀ j : D.index, ∀ i : D.index,
      A.ThetaOverlapQuotient (π := π) a i j) ≃ₗ[A.chartProd]
      A.ThetaOverlapProd (π := π) a := by
  let e : D.index × D.index ≃ Σ _ : D.index, D.index :=
    (Equiv.prodComm D.index D.index).trans
      (Equiv.sigmaEquivProd D.index D.index).symm
  let φ : (Σ _ : D.index, D.index) → Type u := fun q =>
    A.ThetaOverlapQuotient (π := π) a q.2 q.1
  let ecurry := (LinearEquiv.piCurry A.chartProd (fun j i =>
    A.ThetaOverlapQuotient (π := π) a i j)).symm
  let ereindex := (LinearEquiv.piCongrLeft A.chartProd φ e).symm
  exact ecurry.trans ereindex

@[simp]
theorem thetaOverlapProdSwapEquiv_apply
    (x : ∀ j : D.index, ∀ i : D.index,
      A.ThetaOverlapQuotient (π := π) a i j)
    (p : D.index × D.index) :
    A.thetaOverlapProdSwapEquiv (π := π) a x p = x p.2 p.1 := by
  rfl

noncomputable def thetaPieceProdBaseChangeNestedEquiv {n : ℕ}
    (hc : A.IsCertified n) :
    (∀ j : D.index, A.chartProd ⊗[↥(gluedSubalgebra A)]
      A.ThetaPieceQuotient (π := π) a j) ≃ₗ[A.chartProd]
      (∀ j : D.index, ∀ i : D.index,
        A.ThetaOverlapQuotient (π := π) a i j) := by
  let e := LinearEquiv.piCongrRight (fun j =>
    (A.pieceCoordinateDistrib (π := π) a j).trans
        (LinearEquiv.piCongrRight (fun i =>
          (A.thetaPieceBaseChangeToOverlapCoord (π := π) a hc i j).restrictScalars
            A.chartProd)))
  exact e

/-- The Cech module comparison from the tensor square of the chart algebra. -/
noncomputable def thetaPieceProdBaseChangeToOverlapEquiv {n : ℕ}
    (hc : A.IsCertified n) :
    A.chartProd ⊗[↥(gluedSubalgebra A)]
      A.ThetaPieceProd (π := π) a ≃ₗ[A.chartProd]
      A.ThetaOverlapProd (π := π) a := by
  let e0 := A.chartProdTensorPiecePiEquiv (π := π) a
  let e2 := A.thetaPieceProdBaseChangeNestedEquiv (π := π) a hc
  let e3 := A.thetaOverlapProdSwapEquiv (π := π) a
  exact (e0.trans e2).trans e3

@[simp]
theorem thetaPieceProdBaseChangeToOverlapEquiv_tmul {n : ℕ}
    (hc : A.IsCertified n) (x : A.chartProd)
    (s : A.ThetaPieceProd (π := π) a) (p : D.index × D.index) :
    A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc (x ⊗ₜ s) p =
      A.toOvlLeft p.1 p.2 (x p.1) •
        A.thetaToOverlapRight (π := π) a p.1 p.2 (s p.2) := by
  simp only [thetaPieceProdBaseChangeToOverlapEquiv,
    LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    thetaOverlapProdSwapEquiv_apply,
    thetaPieceProdBaseChangeNestedEquiv, LinearEquiv.piCongrRight_apply,
    chartProdTensorPiecePiEquiv, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul, pieceCoordinateDistrib_tmul_apply,
    thetaPieceBaseChangeToOverlapCoord_tmul]

/- The right Cech arrow after tensoring is the comparison above. -/
noncomputable def thetaIntrinsicDeltaRightBaseChange {n : ℕ}
    (_hc : A.IsCertified n) :
    A.chartProd ⊗[↥(gluedSubalgebra A)]
      A.ThetaPieceProd (π := π) a →ₗ[A.chartProd]
      A.ThetaOverlapProd (π := π) a :=
  LinearMap.liftBaseChange A.chartProd
    (A.thetaIntrinsicDeltaRightGlued (π := π) a)

theorem thetaIntrinsicDeltaRightBaseChange_eq_comparison {n : ℕ}
    (hc : A.IsCertified n) :
    A.thetaIntrinsicDeltaRightBaseChange (π := π) a hc =
      (A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x s =>
      funext p
      rw [thetaIntrinsicDeltaRightBaseChange, LinearMap.liftBaseChange_tmul]
      change (x • A.thetaIntrinsicDeltaRightGlued (π := π) a s) p =
        A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc
          (x ⊗ₜ[↥(gluedSubalgebra A)] s) p
      rw [thetaPieceProdBaseChangeToOverlapEquiv_tmul]
      change A.toOvlLeft p.1 p.2 (x p.1) •
          A.thetaToOverlapRight (π := π) a p.1 p.2 (s p.2) = _
      rfl

theorem thetaIntrinsicDeltaRightBaseChange_bijective {n : ℕ}
    (hc : A.IsCertified n) :
    Function.Bijective (A.thetaIntrinsicDeltaRightBaseChange (π := π) a hc) := by
  rw [A.thetaIntrinsicDeltaRightBaseChange_eq_comparison (π := π) a hc]
  exact (A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc).bijective

end

end AffAdaptation

end AlgebraicGeometry
