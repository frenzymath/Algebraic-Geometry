/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffBaseChange
import AlgebraicJacobian.Picard.DivisorFamilyPullbackGlued

/-!
# Certified base change on the widened cover (R2, human decision I-0492)

The seven certificate clauses of `AffAdaptation.IsCertified` transport along an arbitrary test
change `R → R'`.  This is the last structural piece the widened value needed: without it
`DivFamZarAff` is a type with no functoriality, and nothing downstream can base-change a
widened class.

## Two definitional identities do most of the work

Both were probed and hold on the nose, which is why this file is short:

* the base-changed overlap **is** the preimage of the overlap
  (`(D.baseChange R').pieces i ⊓ (D.baseChange R').pieces j = relCurveMap ⁻¹ᵁ (pieces i ⊓
  pieces j)` by `rfl`, since `⁻¹ᵁ` commutes with `⊓` definitionally on `Opens`);
* the pulled colength **is** the quotient `relQuotBaseChangeAff` lands in.

So the widened colength and overlap transports are the SAME declaration
(`AffCoverData.pieceQuotBaseChange`) at two different opens, where the chart-typed layer
needed `pieceQuotBaseChange` and a separately-constructed `ovlQuotBaseChange` conjugated
through the overlap generator.

## What is reused verbatim

Clauses (c2)/(c3)/(c4) ride the abstract `FlatCokernel` keystones
(`LinearMap.ker_lTensor_eq_of_flat_coker`, `LinearMap.tensorKerEquivOfFlatCoker`,
`LinearMap.quotRangeBaseChangeEquiv`) and the two square-transport lemmas
(`LinearEquiv.map_ker_of_comp_eq`, `LinearEquiv.range_eq_map_range_of_comp_eq`).  All are
stated for bare modules and know nothing about covers, so the widening does not touch them.

## Main declarations

* `AffAdaptation.colengthBaseChange`, `ovlColengthBaseChange` — the (c1) and overlap
  transports, both `AffCoverData.pieceQuotBaseChange`.
* `AffAdaptation.chartProdBaseChange`, `ovlProdBaseChange` — the product transports.
* `AffAdaptation.delta_baseChange_comm` — `δ`-naturality, a `funext` over the pair index.
* `AffAdaptation.gluedBaseChange` and the (c2)/(c3)/(c4) transports.
* `AffAdaptation.isCertified_pullback` — **the certificate base-changes**, all seven clauses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d) (hproj : ∀ j, Module.Projective R (A.colength j))

/-! ## The colength transports (clause (c1)) -/

/-- **Base change of a piece colength**: `R' ⊗[R] colength j ≃ₐ[R'] (pullback).colength j`.
This is `AffCoverData.pieceQuotBaseChange` at the singleton `{eqn j}`; the target is
definitionally the pulled colength. -/
noncomputable def colengthBaseChange (j : D.index) :
    R' ⊗[R] A.colength j ≃ₐ[R'] (A.pullback R' hproj).colength j :=
  (D.pieceQuotBaseChange R' j {A.eqn j}).trans
    (Ideal.quotientEquivAlgOfEq R' (by rw [Set.image_singleton]; rfl))

/-- (c1) transport, finiteness. -/
theorem finite_colength_pullback (hfin : ∀ j, Module.Finite R (A.colength j)) (j : D.index) :
    Module.Finite R' ((A.pullback R' hproj).colength j) := by
  haveI := hfin j
  exact Module.Finite.equiv (A.colengthBaseChange R' hproj j).toLinearEquiv

/-- (c1) transport, projectivity. -/
theorem projective_colength_pullback (j : D.index) :
    Module.Projective R' ((A.pullback R' hproj).colength j) := by
  haveI := hproj j
  exact Module.Projective.of_equiv (A.colengthBaseChange R' hproj j).toLinearEquiv

/-- **Base change of an overlap colength**.  The SAME declaration as the piece transport, at
the open `pieces i ⊓ pieces j` — no overlap generator, no conjugation.  Requires the overlap
to be affine, which is a hypothesis rather than a field: `AffCoverData` demands affineness of
the pieces only, and overlaps are affine when the relative curve is separated. -/
noncomputable def ovlColengthBaseChange
    (hinf : ∀ i j : D.index, IsAffineOpen (D.pieces i ⊓ D.pieces j)) (i j : D.index) :
    R' ⊗[R] A.ovlColength i j ≃ₐ[R'] (A.pullback R' hproj).ovlColength i j :=
  (relQuotBaseChangeAff C R' (hinf i j)
      {relResAlgHom C R (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i),
       relResAlgHom C R (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) (A.eqn j)}).trans
    (Ideal.quotientEquivAlgOfEq R' (by
      rw [Set.image_insert_eq, Set.image_singleton]
      exact congrArg₂ (fun x y => Ideal.span {x, y})
        (relAffSectionsMap_res C R'
          (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i)).symm
        (relAffSectionsMap_res C R'
          (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) (A.eqn j)).symm))

/-! ## The computation rules of the two transports -/

lemma colengthBaseChange_one_tmul_mk (j : D.index) (t : Γ(relCurve C R, D.pieces j)) :
    A.colengthBaseChange R' hproj j
        ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span {A.eqn j}) t) =
      Ideal.Quotient.mk (Ideal.span {(A.pullback R' hproj).eqn j})
        (D.piecesMap R' j t) := by
  rw [colengthBaseChange, AlgEquiv.trans_apply,
    AffCoverData.pieceQuotBaseChange_one_tmul_mk, Ideal.quotientEquivAlgOfEq_mk]

lemma ovlColengthBaseChange_one_tmul_mk
    (hinf : ∀ i j : D.index, IsAffineOpen (D.pieces i ⊓ D.pieces j)) (i j : D.index)
    (t : Γ(relCurve C R, D.pieces i ⊓ D.pieces j)) :
    A.ovlColengthBaseChange R' hproj hinf i j
        ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (A.ovlIdeal i j) t) =
      Ideal.Quotient.mk ((A.pullback R' hproj).ovlIdeal i j)
        (relAffSectionsMap C R' (D.pieces i ⊓ D.pieces j) t) := by
  rw [ovlColengthBaseChange, AlgEquiv.trans_apply, relQuotBaseChangeAff_one_tmul_mk]
  exact Ideal.quotientEquivAlgOfEq_mk R' _ _

/-! ## The product transports -/

/-- Base change of the product of piece colengths. -/
noncomputable def chartProdBaseChange :
    R' ⊗[R] A.chartProd ≃ₗ[R'] (A.pullback R' hproj).chartProd :=
  (TensorProduct.piRight R R' R' (fun j : D.index => A.colength j)).trans
    (LinearEquiv.piCongrRight fun j => (A.colengthBaseChange R' hproj j).toLinearEquiv)

/-- Base change of the product of overlap colengths. -/
noncomputable def ovlProdBaseChange
    (hinf : ∀ i j : D.index, IsAffineOpen (D.pieces i ⊓ D.pieces j)) :
    R' ⊗[R] A.ovlProd ≃ₗ[R'] (A.pullback R' hproj).ovlProd :=
  (TensorProduct.piRight R R' R'
      (fun p : D.index × D.index => A.ovlColength p.1 p.2)).trans
    (LinearEquiv.piCongrRight fun p =>
      (A.ovlColengthBaseChange R' hproj hinf p.1 p.2).toLinearEquiv)

lemma chartProdBaseChange_tmul_apply (r' : R') (s : A.chartProd) (l : D.index) :
    A.chartProdBaseChange R' hproj (r' ⊗ₜ[R] s) l =
      A.colengthBaseChange R' hproj l (r' ⊗ₜ[R] s l) := by
  rw [chartProdBaseChange, LinearEquiv.trans_apply, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]
  rfl

lemma ovlProdBaseChange_tmul_apply
    (hinf : ∀ i j : D.index, IsAffineOpen (D.pieces i ⊓ D.pieces j))
    (r' : R') (s : A.ovlProd) (p : D.index × D.index) :
    A.ovlProdBaseChange R' hproj hinf (r' ⊗ₜ[R] s) p =
      A.ovlColengthBaseChange R' hproj hinf p.1 p.2 (r' ⊗ₜ[R] s p) := by
  rw [ovlProdBaseChange, LinearEquiv.trans_apply, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]
  rfl

/-! ## The overlap-restriction squares

The chart-typed proofs of these consumed `ovlMap_resHom_left`/`_right`, which conjugate through
the overlap generator.  Widened, the corresponding fact is `relAffSectionsMap_res` — plain
`appLE` naturality at `pieces i ⊓ pieces j`. -/

section Squares

/-- The left overlap-restriction map on a residue class (the widened mirror of the `private`
`toOvlLeft_mk` of `DivisorFamilyPullbackCert.lean`). -/
private lemma toOvlLeft_mk' (i j : D.index) (t : Γ(relCurve C R, D.pieces i)) :
    A.toOvlLeft i j (Ideal.Quotient.mk (Ideal.span {A.eqn i}) t) =
      Ideal.Quotient.mk (A.ovlIdeal i j) (relResAlgHom C R inf_le_left t) :=
  rfl

/-- The right overlap-restriction map on a residue class. -/
private lemma toOvlRight_mk' (i j : D.index) (t : Γ(relCurve C R, D.pieces j)) :
    A.toOvlRight i j (Ideal.Quotient.mk (Ideal.span {A.eqn j}) t) =
      Ideal.Quotient.mk (A.ovlIdeal i j) (relResAlgHom C R inf_le_right t) :=
  rfl

variable (hinf : ∀ i j : D.index, IsAffineOpen (D.pieces i ⊓ D.pieces j))

lemma pulledToOvlLeft_colengthBaseChange (i j : D.index) (x : R' ⊗[R] A.colength i) :
    (A.pullback R' hproj).toOvlLeft i j (A.colengthBaseChange R' hproj i x) =
      A.ovlColengthBaseChange R' hproj hinf i j
        ((AlgebraTensorModule.lTensor R' R' (A.toOvlLeft i j).toLinearMap) x) := by
  induction x with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r' y =>
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hsmul : (r' ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span {A.eqn i}) t) :
        R' ⊗[R] A.colength i) =
        r' • ((1 : R') ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span {A.eqn i}) t)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsmul]
    simp only [map_smul]
    congr 1
    have hlt : (AlgebraTensorModule.lTensor R' R' (A.toOvlLeft i j).toLinearMap)
        ((1 : R') ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span {A.eqn i}) t)) =
        (1 : R') ⊗ₜ[R] (A.toOvlLeft i j (Ideal.Quotient.mk (Ideal.span {A.eqn i}) t)) :=
      rfl
    rw [A.colengthBaseChange_one_tmul_mk R' hproj i t, hlt, A.toOvlLeft_mk' i j t,
      A.ovlColengthBaseChange_one_tmul_mk R' hproj hinf i j _,
      (A.pullback R' hproj).toOvlLeft_mk' i j _]
    exact congrArg (Ideal.Quotient.mk _)
      (relAffSectionsMap_res C R'
        (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) t)

lemma pulledToOvlRight_colengthBaseChange (i j : D.index) (x : R' ⊗[R] A.colength j) :
    (A.pullback R' hproj).toOvlRight i j (A.colengthBaseChange R' hproj j x) =
      A.ovlColengthBaseChange R' hproj hinf i j
        ((AlgebraTensorModule.lTensor R' R' (A.toOvlRight i j).toLinearMap) x) := by
  induction x with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r' y =>
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hsmul : (r' ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span {A.eqn j}) t) :
        R' ⊗[R] A.colength j) =
        r' • ((1 : R') ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span {A.eqn j}) t)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsmul]
    simp only [map_smul]
    congr 1
    have hlt : (AlgebraTensorModule.lTensor R' R' (A.toOvlRight i j).toLinearMap)
        ((1 : R') ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span {A.eqn j}) t)) =
        (1 : R') ⊗ₜ[R] (A.toOvlRight i j (Ideal.Quotient.mk (Ideal.span {A.eqn j}) t)) :=
      rfl
    rw [A.colengthBaseChange_one_tmul_mk R' hproj j t, hlt, A.toOvlRight_mk' i j t,
      A.ovlColengthBaseChange_one_tmul_mk R' hproj hinf i j _,
      (A.pullback R' hproj).toOvlRight_mk' i j _]
    exact congrArg (Ideal.Quotient.mk _)
      (relAffSectionsMap_res C R'
        (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) t)

set_option maxHeartbeats 1000000 in
-- The defeq checks through the mixed `relCurve`/product spellings are heavy here, exactly as in
-- the chart-typed `delta_baseChange_comm` (`DivisorFamilyPullbackCert.lean`), and the instance
-- searches on the large tensor/product types exceed the default.
set_option synthInstance.maxHeartbeats 400000 in
/-- **`δ`-naturality**: the pulled difference arrow matches `id ⊗ δ` through the product
transports.  A `funext` over the pair index feeding the two squares above — index-shape
agnostic, so the widening costs nothing here. -/
theorem delta_baseChange_comm :
    ((A.pullback R' hproj).deltaLeft - (A.pullback R' hproj).deltaRight) ∘ₗ
        (A.chartProdBaseChange R' hproj :
          R' ⊗[R] A.chartProd →ₗ[R'] (A.pullback R' hproj).chartProd) =
      (A.ovlProdBaseChange R' hproj hinf :
          R' ⊗[R] A.ovlProd →ₗ[R'] (A.pullback R' hproj).ovlProd) ∘ₗ
        AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  induction x with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r' s =>
    have hsmul : (r' ⊗ₜ[R] s : R' ⊗[R] A.chartProd) = r' • ((1 : R') ⊗ₜ[R] s) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsmul]
    simp only [map_smul]
    congr 1
    funext p
    have hlt : (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))
        ((1 : R') ⊗ₜ[R] s) = (1 : R') ⊗ₜ[R] ((A.deltaLeft - A.deltaRight) s) := rfl
    have hcomp : (A.deltaLeft - A.deltaRight) s =
        fun p : D.index × D.index =>
          A.toOvlLeft p.1 p.2 (s p.1) - A.toOvlRight p.1 p.2 (s p.2) := by
      funext q
      simp only [LinearMap.sub_apply, deltaLeft, deltaRight, LinearMap.pi_apply,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
        AlgHom.toLinearMap_apply, Pi.sub_apply]
    have hL : (((A.pullback R' hproj).deltaLeft - (A.pullback R' hproj).deltaRight)
        ((A.chartProdBaseChange R' hproj) ((1 : R') ⊗ₜ[R] s))) p =
        (A.pullback R' hproj).toOvlLeft p.1 p.2
            (A.colengthBaseChange R' hproj p.1 ((1 : R') ⊗ₜ[R] s p.1)) -
          (A.pullback R' hproj).toOvlRight p.1 p.2
            (A.colengthBaseChange R' hproj p.2 ((1 : R') ⊗ₜ[R] s p.2)) := by
      have h1 := A.chartProdBaseChange_tmul_apply R' hproj 1 s p.1
      have h2 := A.chartProdBaseChange_tmul_apply R' hproj 1 s p.2
      simp only [LinearMap.sub_apply, Pi.sub_apply, deltaLeft, deltaRight,
        LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.proj_apply, AlgHom.toLinearMap_apply, h1, h2]
    have hR : ((A.ovlProdBaseChange R' hproj hinf)
        ((AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))
          ((1 : R') ⊗ₜ[R] s))) p =
        A.ovlColengthBaseChange R' hproj hinf p.1 p.2
            ((1 : R') ⊗ₜ[R] (A.toOvlLeft p.1 p.2 (s p.1))) -
          A.ovlColengthBaseChange R' hproj hinf p.1 p.2
            ((1 : R') ⊗ₜ[R] (A.toOvlRight p.1 p.2 (s p.2))) := by
      rw [hlt, A.ovlProdBaseChange_tmul_apply R' hproj hinf 1 _ p, hcomp,
        TensorProduct.tmul_sub, map_sub]
    have hltL : (AlgebraTensorModule.lTensor R' R' (A.toOvlLeft p.1 p.2).toLinearMap)
        ((1 : R') ⊗ₜ[R] s p.1) = (1 : R') ⊗ₜ[R] (A.toOvlLeft p.1 p.2 (s p.1)) := rfl
    have hltR : (AlgebraTensorModule.lTensor R' R' (A.toOvlRight p.1 p.2).toLinearMap)
        ((1 : R') ⊗ₜ[R] s p.2) = (1 : R') ⊗ₜ[R] (A.toOvlRight p.1 p.2 (s p.2)) := rfl
    rw [hL, hR,
      A.pulledToOvlLeft_colengthBaseChange R' hproj hinf p.1 p.2 ((1 : R') ⊗ₜ[R] s p.1),
      A.pulledToOvlRight_colengthBaseChange R' hproj hinf p.1 p.2 ((1 : R') ⊗ₜ[R] s p.2),
      hltL, hltR]

/-- The `δ`-naturality square with the verticals inverted. -/
theorem delta_baseChange_comm' :
    (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)) ∘ₗ
        ((A.chartProdBaseChange R' hproj).symm :
          (A.pullback R' hproj).chartProd →ₗ[R'] R' ⊗[R] A.chartProd) =
      ((A.ovlProdBaseChange R' hproj hinf).symm :
          (A.pullback R' hproj).ovlProd →ₗ[R'] R' ⊗[R] A.ovlProd) ∘ₗ
        ((A.pullback R' hproj).deltaLeft - (A.pullback R' hproj).deltaRight) := by
  apply LinearMap.ext
  intro x
  have h := congr($(A.delta_baseChange_comm R' hproj hinf)
    ((A.chartProdBaseChange R' hproj).symm x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at h ⊢
  rw [h, LinearEquiv.symm_apply_apply]

/-! ## The glued transport (clause (c2)) and the flat-cokernel clauses (c3)/(c4)

Everything below rides the abstract keystones of `Picard/FlatCokernel.lean` and the
square-transport lemmas of `DivisorFamilyPullbackGlued.lean`, all stated for bare modules.
The widening is invisible to them. -/

include hinf in
lemma map_ker_lTensor_delta :
    (LinearMap.ker (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))).map
        (A.chartProdBaseChange R' hproj :
          R' ⊗[R] A.chartProd →ₗ[R'] (A.pullback R' hproj).chartProd) =
      (A.pullback R' hproj).gluedSubmodule :=
  LinearEquiv.map_ker_of_comp_eq (A.chartProdBaseChange R' hproj)
    (A.ovlProdBaseChange R' hproj hinf)
    (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))
    ((A.pullback R' hproj).deltaLeft - (A.pullback R' hproj).deltaRight)
    (A.delta_baseChange_comm R' hproj hinf)

include hinf in
lemma map_pulledGluedSubmodule_symm :
    ((A.pullback R' hproj).gluedSubmodule).map
        ((A.chartProdBaseChange R' hproj).symm :
          (A.pullback R' hproj).chartProd →ₗ[R'] R' ⊗[R] A.chartProd) =
      LinearMap.ker (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)) :=
  LinearEquiv.map_ker_of_comp_eq (A.chartProdBaseChange R' hproj).symm
    (A.ovlProdBaseChange R' hproj hinf).symm
    ((A.pullback R' hproj).deltaLeft - (A.pullback R' hproj).deltaRight)
    (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))
    (A.delta_baseChange_comm' R' hproj hinf)

include hinf in
lemma range_lTensor_delta :
    LinearMap.range (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)) =
      (LinearMap.range ((A.pullback R' hproj).deltaLeft -
        (A.pullback R' hproj).deltaRight)).map
        ((A.ovlProdBaseChange R' hproj hinf).symm :
          (A.pullback R' hproj).ovlProd →ₗ[R'] R' ⊗[R] A.ovlProd) :=
  LinearEquiv.range_eq_map_range_of_comp_eq (A.chartProdBaseChange R' hproj).symm
    (A.ovlProdBaseChange R' hproj hinf).symm
    ((A.pullback R' hproj).deltaLeft - (A.pullback R' hproj).deltaRight)
    (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))
    (A.delta_baseChange_comm' R' hproj hinf)

include hinf in
/-- **Base change of the glued colength module** (the (c2) keystone), widened. -/
noncomputable def gluedBaseChange
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))] :
    R' ⊗[R] A.Glued ≃ₗ[R'] (A.pullback R' hproj).Glued :=
  haveI : Module.Flat R (A.chartProd ⧸ LinearMap.ker (A.deltaLeft - A.deltaRight)) :=
    ‹Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)›
  (LinearMap.tensorKerEquivOfFlatCoker (A.deltaLeft - A.deltaRight) R').trans
    (((A.chartProdBaseChange R' hproj).submoduleMap
        (LinearMap.ker (AlgebraTensorModule.lTensor R' R'
          (A.deltaLeft - A.deltaRight)))).trans
      (LinearEquiv.ofEq _ _ (A.map_ker_lTensor_delta R' hproj hinf)))

include hinf in
/-- (c2) transport, finiteness. -/
theorem finite_glued_pullback
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))]
    (hfin : Module.Finite R A.Glued) :
    Module.Finite R' (A.pullback R' hproj).Glued := by
  haveI := hfin
  exact Module.Finite.equiv (A.gluedBaseChange R' hproj hinf)

include hinf in
/-- (c2) transport, projectivity. -/
theorem projective_glued_pullback
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))]
    (hproj' : Module.Projective R A.Glued) :
    Module.Projective R' (A.pullback R' hproj).Glued := by
  haveI := hproj'
  exact Module.Projective.of_equiv (A.gluedBaseChange R' hproj hinf)

include hinf in
/-- (c2) transport, constant fibre rank. -/
theorem rankAtStalk_glued_pullback {n : ℕ}
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))]
    (hfin : Module.Finite R A.Glued) (hproj' : Module.Projective R A.Glued)
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk A.Glued p = n)
    (p : PrimeSpectrum R') :
    Module.rankAtStalk ((A.pullback R' hproj).Glued) p = n := by
  haveI := hfin
  haveI := hproj'
  rw [← Module.rankAtStalk_eq_of_equiv (A.gluedBaseChange R' hproj hinf),
    Module.rankAtStalk_baseChange]
  exact hrank _

omit [Algebra k R'] [IsScalarTower k R R'] in
lemma range_baseChange_gluedSubtype
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))] :
    LinearMap.range ((A.gluedSubmodule).subtype.baseChange R') =
      LinearMap.ker (AlgebraTensorModule.lTensor R' R'
        (A.deltaLeft - A.deltaRight)) := by
  haveI : Module.Flat R (A.chartProd ⧸ LinearMap.ker (A.deltaLeft - A.deltaRight)) :=
    ‹Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)›
  have h := LinearMap.ker_lTensor_eq_of_flat_coker (A.deltaLeft - A.deltaRight) R'
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  have hx := SetLike.ext_iff.mp h x
  rw [LinearMap.mem_ker, LinearMap.mem_range] at hx
  exact ⟨fun ⟨y, hy⟩ => hx.mpr ⟨y, hy⟩, fun hker => hx.mp hker⟩

include hinf in
/-- (c3) transport: the cokernel of the pulled glued inclusion is flat. -/
theorem flat_coker_incl_pullback
    [Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)]
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))] :
    Module.Flat R' ((A.pullback R' hproj).chartProd ⧸
      (A.pullback R' hproj).gluedSubmodule) := by
  refine Module.Flat.of_linearEquiv
    (N := (A.pullback R' hproj).chartProd ⧸ (A.pullback R' hproj).gluedSubmodule)
    (M := R' ⊗[R] (A.chartProd ⧸ A.gluedSubmodule)) ?_
  refine (Submodule.Quotient.equiv ((A.pullback R' hproj).gluedSubmodule)
      (LinearMap.ker (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)))
      (A.chartProdBaseChange R' hproj).symm
      (A.map_pulledGluedSubmodule_symm R' hproj hinf)).trans
    ((Submodule.quotEquivOfEq _ _ (A.range_baseChange_gluedSubtype R').symm).trans
      (((LinearMap.quotRangeBaseChangeEquiv R' (A.gluedSubmodule).subtype).symm).trans
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R')
          (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype A.gluedSubmodule)))))

omit [Algebra k R'] [IsScalarTower k R R'] in
/-- The range of `id ⊗ δ` in the base-change spelling. -/
lemma range_lTensor_eq_range_baseChange :
    LinearMap.range (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)) =
      LinearMap.range ((A.deltaLeft - A.deltaRight).baseChange R') := by
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_range]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩

include hinf in
/-- (c4) transport: the cokernel of the pulled difference arrow is flat. -/
theorem flat_coker_diff_pullback
    [Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))] :
    Module.Flat R' ((A.pullback R' hproj).ovlProd ⧸
      LinearMap.range ((A.pullback R' hproj).deltaLeft -
        (A.pullback R' hproj).deltaRight)) := by
  refine Module.Flat.of_linearEquiv
    (N := (A.pullback R' hproj).ovlProd ⧸
      LinearMap.range ((A.pullback R' hproj).deltaLeft -
        (A.pullback R' hproj).deltaRight))
    (M := R' ⊗[R] (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))) ?_
  refine (Submodule.Quotient.equiv
      (LinearMap.range ((A.pullback R' hproj).deltaLeft -
        (A.pullback R' hproj).deltaRight))
      (LinearMap.range (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)))
      (A.ovlProdBaseChange R' hproj hinf).symm
      (A.range_lTensor_delta R' hproj hinf).symm).trans
    ((Submodule.quotEquivOfEq _ _ (A.range_lTensor_eq_range_baseChange R')).trans
      (LinearMap.quotRangeBaseChangeEquiv R' (A.deltaLeft - A.deltaRight)).symm)

/-! ## The certificate base-changes -/

include hinf in
/-- **Certified base change on the widened cover**: all seven clauses transport.  This is what
makes `DivFamZarAff` a functor value rather than a bare type. -/
theorem isCertified_pullback {n : ℕ} (hc : A.IsCertified n) :
    (A.pullback R' hc.projective_colength).IsCertified n := by
  haveI hc3 : Module.Flat R (A.chartProd ⧸ A.gluedSubmodule) := hc.flat_coker_incl
  haveI hc4 : Module.Flat R
      (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight)) := hc.flat_coker_diff
  exact
    { finite_colength := A.finite_colength_pullback R' hc.projective_colength
        hc.finite_colength
      projective_colength := A.projective_colength_pullback R' hc.projective_colength
      finite_glued := A.finite_glued_pullback R' hc.projective_colength hinf hc.finite_glued
      projective_glued := A.projective_glued_pullback R' hc.projective_colength hinf
        hc.projective_glued
      rankAtStalk_glued := A.rankAtStalk_glued_pullback R' hc.projective_colength hinf
        hc.finite_glued hc.projective_glued hc.rankAtStalk_glued
      flat_coker_incl := A.flat_coker_incl_pullback R' hc.projective_colength hinf
      flat_coker_diff := A.flat_coker_diff_pullback R' hc.projective_colength hinf }

end Squares

end AffAdaptation

end AlgebraicGeometry
