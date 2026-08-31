/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaProductBaseChange
import AlgebraicJacobian.Picard.DivisorFamilyAffGlue
import AlgebraicJacobian.Descent.ModuleDescent

/-!
# The left theta face as a descent coaction

The product/base-change file identifies the tensor square of the chart algebra with the
intrinsic right theta Cech face.  This file records the complementary left face as a
chart-product-linear map and transports it back through that equivalence.  The result is the
candidate coaction consumed by `Module.DescentDatum`.

Only the existing certificate `A.IsCertified n` is used.  The counit and coassociativity laws
are intentionally left as separate obligations: recording the coaction and its pointwise
formula makes those laws directly testable without pretending that the left face itself is an
isomorphism under the right-factor scalar action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace Module

variable {A B M N : Type u}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- Transporting a candidate coaction through a right-face comparison reduces
coassociativity to equality of the base-changed left and right Cech faces. -/
theorem coassoc_iff_baseChange_faces
    (e : B ⊗[A] M ≃ₗ[B] N)
    (left : M →ₗ[B] N) (right : M →ₗ[A] N)
    (delta : M →ₗ[B] B ⊗[A] M)
    (hleft : (e.restrictScalars A).toLinearMap.comp (delta.restrictScalars A) =
      left.restrictScalars A)
    (hright : (e.restrictScalars A).toLinearMap.comp
      (TensorProduct.mk A B M 1) = right)
    (m : M) :
    (delta.restrictScalars A).baseChange B (delta m) =
        (TensorProduct.mk A B M 1).baseChange B (delta m) ↔
      (left.restrictScalars A).baseChange B (delta m) =
        right.baseChange B (delta m) := by
  let eA := e.restrictScalars A
  have hleft_transport :
      eA.toLinearMap.baseChange B
          ((delta.restrictScalars A).baseChange B (delta m)) =
        (left.restrictScalars A).baseChange B (delta m) := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hleft]
  have hright_transport :
      eA.toLinearMap.baseChange B
          ((TensorProduct.mk A B M 1).baseChange B (delta m)) =
        right.baseChange B (delta m) := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hright]
  constructor
  · intro h
    rw [← hleft_transport, ← hright_transport, h]
  · intro h
    let eAB := eA.baseChange A B _ _
    apply eAB.injective
    change
      eA.toLinearMap.baseChange B
          ((delta.restrictScalars A).baseChange B (delta m)) =
        eA.toLinearMap.baseChange B
          ((TensorProduct.mk A B M 1).baseChange B (delta m))
    rw [hleft_transport, hright_transport, h]

end Module

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
  thetaOverlapQuotientRightModule thetaOverlapQuotientRightTower
  productOverlapRightAlgebra productOverlapRightTower
  thetaPieceQuotientGluedModule thetaOverlapQuotientGluedModule
  chartProdPieceAlgebra chartProdOverlapAlgebra thetaPieceProdADModule
  thetaPieceProdCPModule thetaPieceProdTower thetaOverlapProdOvlModule
  thetaOverlapQuotientCPModule thetaOverlapProdCPModule thetaOverlapProdADModule
  thetaOverlapProdTower

noncomputable section

variable (A : AffAdaptation D d) (a : ℕ)

omit [IsProper C.hom] in
lemma ovlColengthDiagEquiv_toOvlLeft (i : D.index) (x : A.colength i) :
    A.ovlColengthDiagEquiv i (A.toOvlLeft i i x) = x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [A.toOvlLeft_mk]
  unfold ovlColengthDiagEquiv
  rw [Ideal.quotientEquivAlg_mk]
  change (Ideal.Quotient.mk (Ideal.span {A.eqn i}))
      ((sectionsInfSelfEquiv i) (relResAlgHom C R inf_le_left r)) = _
  rw [sectionsInfSelfEquiv_relResAlgHom]

omit [IsProper C.hom] in
lemma ovlColengthDiagEquiv_toOvlRight (i : D.index) (x : A.colength i) :
    A.ovlColengthDiagEquiv i (A.toOvlRight i i x) = x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [A.toOvlRight_mk]
  unfold ovlColengthDiagEquiv
  rw [Ideal.quotientEquivAlg_mk]
  change (Ideal.Quotient.mk (Ideal.span {A.eqn i}))
      ((sectionsInfSelfEquiv i) (relResAlgHom C R inf_le_right r)) = _
  rw [sectionsInfSelfEquiv_relResAlgHom]

theorem thetaToOverlap_diag_eq (i : D.index) :
    A.thetaToOverlapLeft (π := π) a i i =
      A.thetaToOverlapRight (π := π) a i i := by
  apply DFunLike.ext _ _
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [A.thetaToOverlapLeft_mk, A.thetaToOverlapRight_mk]

omit [IsProper C.hom] in
lemma toOvlRight_diag_eq_ovlColengthDiagEquiv_symm
    (i : D.index) (x : A.colength i) :
    A.toOvlRight i i x = (A.ovlColengthDiagEquiv i).symm x := by
  apply (A.ovlColengthDiagEquiv i).injective
  rw [A.ovlColengthDiagEquiv_toOvlRight]
  exact (A.ovlColengthDiagEquiv i).apply_symm_apply x |>.symm

noncomputable def diagColengthToOverlapLinear (i : D.index) :
    A.colength i ≃ₗ[A.colength i] A.ovlColength i i := by
  let e := (A.ovlColengthDiagEquiv i).symm
  exact
    { toFun := e
      invFun := A.ovlColengthDiagEquiv i
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro c x
        change e (c * x) = A.toOvlRight i i c * e x
        rw [A.toOvlRight_diag_eq_ovlColengthDiagEquiv_symm]
        exact e.map_mul c x }

noncomputable def diagTensorRid (i : D.index) :
    A.ovlColength i i ⊗[A.colength i]
        A.ThetaPieceQuotient (π := π) a i ≃ₗ[A.colength i]
      A.ThetaPieceQuotient (π := π) a i := by
  let e0 : A.ThetaPieceQuotient (π := π) a i ⊗[A.colength i]
      A.colength i ≃ₗ[A.colength i]
      A.ThetaPieceQuotient (π := π) a i := TensorProduct.rid _ _
  let e1 : A.ThetaPieceQuotient (π := π) a i ⊗[A.colength i]
      A.colength i ≃ₗ[A.colength i]
      A.ThetaPieceQuotient (π := π) a i ⊗[A.colength i]
        A.ovlColength i i :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
      (A.diagColengthToOverlapLinear i)
  exact (TensorProduct.comm _ _ _).trans (e1.symm.trans e0)

omit [IsProper C.hom] in
@[simp]
lemma diagTensorRid_tmul (i : D.index) (c : A.ovlColength i i)
    (m : A.ThetaPieceQuotient (π := π) a i) :
    A.diagTensorRid (π := π) a i (c ⊗ₜ m) =
      A.ovlColengthDiagEquiv i c • m := by
  simp [diagTensorRid, diagColengthToOverlapLinear]

omit [IsProper C.hom] in
@[simp]
lemma diagTensorRid_symm_apply (i : D.index)
    (m : A.ThetaPieceQuotient (π := π) a i) :
    (A.diagTensorRid (π := π) a i).symm m =
      1 ⊗ₜ[A.colength i] m := by
  simp [diagTensorRid, diagColengthToOverlapLinear]

noncomputable def thetaToOverlapRightDiagEquiv (i : D.index) :
    A.ThetaPieceQuotient (π := π) a i ≃ₗ[A.colength i]
      A.ThetaOverlapQuotient (π := π) a i i :=
  (A.diagTensorRid (π := π) a i).symm.trans
    ((A.thetaPieceBaseChangeToOverlapRightEquiv (π := π) a i i).restrictScalars
      (A.colength i))

@[simp]
lemma thetaToOverlapRightDiagEquiv_apply (i : D.index)
    (m : A.ThetaPieceQuotient (π := π) a i) :
    A.thetaToOverlapRightDiagEquiv (π := π) a i m =
      A.thetaToOverlapRight (π := π) a i i m := by
  simp [thetaToOverlapRightDiagEquiv]

theorem thetaToOverlapRight_diag_injective (i : D.index) :
    Function.Injective (A.thetaToOverlapRight (π := π) a i i) := by
  intro x y hxy
  apply (A.thetaToOverlapRightDiagEquiv (π := π) a i).injective
  simpa only [A.thetaToOverlapRightDiagEquiv_apply] using hxy

/-- The left Cech arrow is linear over the product piece algebra: both the source and the
overlap target use the first piece coordinate. -/
noncomputable def thetaIntrinsicDeltaLeftCP :
    A.ThetaPieceProd (π := π) a →ₗ[A.chartProd]
      A.ThetaOverlapProd (π := π) a where
  toFun := A.thetaIntrinsicDeltaLeftGlued (π := π) a
  map_add' := (A.thetaIntrinsicDeltaLeftGlued (π := π) a).map_add
  map_smul' := by
    intro b s
    funext p
    change A.thetaToOverlapLeft (π := π) a p.1 p.2 (b p.1 • s p.1) =
      A.toOvlLeft p.1 p.2 (b p.1) •
        A.thetaToOverlapLeft (π := π) a p.1 p.2 (s p.1)
    exact A.thetaToOverlapLeft_smul (π := π) a p.1 p.2 (b p.1) (s p.1)

@[simp]
theorem thetaIntrinsicDeltaLeftCP_apply
    (s : A.ThetaPieceProd (π := π) a) (p : D.index × D.index) :
    A.thetaIntrinsicDeltaLeftCP (π := π) a s p =
      A.thetaToOverlapLeft (π := π) a p.1 p.2 (s p.1) := by
  rfl

/- The left face transported through the right tensor comparison is the candidate descent
coaction on the product of local theta lines. -/
noncomputable def thetaDescentCoaction {n : ℕ} (hc : A.IsCertified n) :
    A.ThetaPieceProd (π := π) a →ₗ[A.chartProd]
      A.chartProd ⊗[↥(gluedSubalgebra A)] A.ThetaPieceProd (π := π) a :=
  (A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc).symm.toLinearMap.comp
    (A.thetaIntrinsicDeltaLeftCP (π := π) a)

@[simp]
theorem thetaPieceProdBaseChangeToOverlapEquiv_coaction {n : ℕ}
    (hc : A.IsCertified n) (s : A.ThetaPieceProd (π := π) a) :
    A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc
        (A.thetaDescentCoaction (π := π) a hc s) =
      A.thetaIntrinsicDeltaLeftCP (π := π) a s := by
  simp [thetaDescentCoaction]

@[simp]
theorem thetaPieceProdBaseChangeToOverlapEquiv_coaction_apply {n : ℕ}
    (hc : A.IsCertified n) (s : A.ThetaPieceProd (π := π) a)
    (p : D.index × D.index) :
    A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc
        (A.thetaDescentCoaction (π := π) a hc s) p =
      A.thetaToOverlapLeft (π := π) a p.1 p.2 (s p.1) := by
  rw [thetaPieceProdBaseChangeToOverlapEquiv_coaction]
  rfl

set_option synthInstance.maxHeartbeats 500000 in
theorem thetaPieceProdBaseChangeToOverlapEquiv_diag {n : ℕ}
    (hc : A.IsCertified n)
    (z : A.chartProd ⊗[↥(gluedSubalgebra A)]
      A.ThetaPieceProd (π := π) a) (i : D.index) :
    A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc z (i, i) =
      A.thetaToOverlapRight (π := π) a i i
        ((Module.actionMap (↥(gluedSubalgebra A)) A.chartProd
          (A.ThetaPieceProd (π := π) a) z) i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul b s =>
      rw [A.thetaPieceProdBaseChangeToOverlapEquiv_tmul,
        Module.actionMap_tmul]
      change A.toOvlLeft i i (b i) •
          A.thetaToOverlapRight (π := π) a i i (s i) =
        A.thetaToOverlapRight (π := π) a i i (b i • s i)
      rw [A.thetaToOverlapRight_smul]
      rw [A.toOvl_diag_eq i]

/-- The transported left face satisfies the normalization law required by
`Module.DescentDatum`. -/
theorem thetaDescentCoaction_counit {n : ℕ}
    (hc : A.IsCertified n) (s : A.ThetaPieceProd (π := π) a) :
    Module.actionMap (↥(gluedSubalgebra A)) A.chartProd
        (A.ThetaPieceProd (π := π) a)
        (A.thetaDescentCoaction (π := π) a hc s) = s := by
  funext i
  apply A.thetaToOverlapRight_diag_injective (π := π) a i
  rw [← A.thetaPieceProdBaseChangeToOverlapEquiv_diag (π := π) a hc
    (A.thetaDescentCoaction (π := π) a hc s) i]
  rw [A.thetaPieceProdBaseChangeToOverlapEquiv_coaction_apply]
  exact DFunLike.congr_fun (A.thetaToOverlap_diag_eq (π := π) a i) (s i)

/-- The product right-face comparison restricted to `1 ⊗ₜ m` is the intrinsic right
Cech arrow. -/
theorem thetaPieceProdBaseChangeToOverlapEquiv_one_tmul {n : ℕ}
    (hc : A.IsCertified n) (s : A.ThetaPieceProd (π := π) a) :
    A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc
        (1 ⊗ₜ[↥(gluedSubalgebra A)] s) =
      A.thetaIntrinsicDeltaRightGlued (π := π) a s := by
  funext p
  rw [A.thetaPieceProdBaseChangeToOverlapEquiv_tmul]
  change A.toOvlLeft p.1 p.2 (1 : A.colength p.1) •
      A.thetaToOverlapRight (π := π) a p.1 p.2 (s p.2) =
    A.thetaToOverlapRight (π := π) a p.1 p.2 (s p.2)
  simp

/-- The remaining `Module.DescentDatum.coassoc` law is exactly equality of the
base-changed intrinsic left and right Cech faces in the already typed module
`chartProd ⊗[gluedSubalgebra A] ThetaOverlapProd`. -/
theorem thetaDescentCoaction_coassoc_iff_baseChange_faces {n : ℕ}
    (hc : A.IsCertified n) (s : A.ThetaPieceProd (π := π) a) :
    ((A.thetaDescentCoaction (π := π) a hc).restrictScalars
        (↥(gluedSubalgebra A))).baseChange A.chartProd
        (A.thetaDescentCoaction (π := π) a hc s) =
      (TensorProduct.mk (↥(gluedSubalgebra A)) A.chartProd
        (A.ThetaPieceProd (π := π) a) 1).baseChange A.chartProd
        (A.thetaDescentCoaction (π := π) a hc s) ↔
    ((A.thetaIntrinsicDeltaLeftCP (π := π) a).restrictScalars
        (↥(gluedSubalgebra A))).baseChange A.chartProd
        (A.thetaDescentCoaction (π := π) a hc s) =
      (A.thetaIntrinsicDeltaRightGlued (π := π) a).baseChange A.chartProd
        (A.thetaDescentCoaction (π := π) a hc s) := by
  apply Module.coassoc_iff_baseChange_faces
    (e := A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc)
    (left := A.thetaIntrinsicDeltaLeftCP (π := π) a)
    (right := A.thetaIntrinsicDeltaRightGlued (π := π) a)
    (delta := A.thetaDescentCoaction (π := π) a hc)
  · apply LinearMap.ext
    intro x
    exact A.thetaPieceProdBaseChangeToOverlapEquiv_coaction (π := π) a hc x
  · apply LinearMap.ext
    intro x
    exact A.thetaPieceProdBaseChangeToOverlapEquiv_one_tmul (π := π) a hc x

end

end AffAdaptation

end AlgebraicGeometry
