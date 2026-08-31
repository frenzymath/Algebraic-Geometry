/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyPullbackOverlap

/-!
# Certificate transport for base change of divisor adaptations (DD-1 stage (c))

For a divisor adaptation `A` over the test ring `R` and a test-ring change `R → R'`,
this file base-changes the whole colength apparatus — the pulled equations, chart-local
and overlap colengths, the two `δ`-arrows, and the glued equalizer module `W(d)` — and
transports the certificate clauses (`informal/spec-dd-1.md` §1c):

* `DivisorAdaptation.pulledEqn`/`pulledColength`/`pulledOvlIdeal`/`pulledOvlColength`/
  `pulledChartProd`/`pulledOvlProd`/`pulledDeltaLeft`/`pulledDeltaRight`/
  `pulledGluedSubmodule` — the raw `R'`-side colength apparatus on the base-changed
  pieces (definitionally the apparatus of the base-changed adaptation, once its
  refinement witness is supplied).
* `DivisorAdaptation.colengthBaseChange`/`ovlColengthBaseChange` — the chart-local and
  overlap colength transports `R' ⊗[R] colength ≃ₐ[R'] pulledColength`
  (instantiations of `pieceQuotBaseChange`/`ovlQuotBaseChange` at the equation ideals),
  with the (c1) clause transports `finite_pulledColength`/`projective_pulledColength`.
* `DivisorAdaptation.delta_baseChange_comm` — **`δ`-naturality**: the pulled difference
  arrow matches `id ⊗ δ` through the product transports
  `chartProdBaseChange`/`ovlProdBaseChange`.

The glued-module transport (clauses (c2)–(c4)) rides these in
`AlgebraicJacobian.Picard.DivisorFamilyPullbackGlued`.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d)

/-! ## The raw base-changed colength apparatus -/

/-- The pulled equation on the base-changed piece: the piece comparison of the
adaptation's equation. -/
noncomputable def pulledEqn (j : A.index) :
    Γ(relCurve C R', (A.toFinCoverData.baseChange R').pieces j) :=
  A.toFinCoverData.piecesMap R' j (A.eqn j)

/-- The pulled chart-local colength module `Γ(D(h'_j)) ⧸ (f'_j)`. -/
noncomputable abbrev pulledColength (j : A.index) : Type u :=
  Γ(relCurve C R', (A.toFinCoverData.baseChange R').pieces j) ⧸
    Ideal.span {A.pulledEqn R' j}

/-- The pulled symmetric overlap ideal. -/
noncomputable abbrev pulledOvlIdeal (i j : A.index) :
    Ideal Γ(relCurve C R',
      (A.toFinCoverData.baseChange R').pieces i ⊓
        (A.toFinCoverData.baseChange R').pieces j) :=
  Ideal.span
    {relResAlgHom C R' inf_le_left (A.pulledEqn R' i),
     relResAlgHom C R' inf_le_right (A.pulledEqn R' j)}

/-- The pulled overlap colength module. -/
noncomputable abbrev pulledOvlColength (i j : A.index) : Type u :=
  Γ(relCurve C R',
      (A.toFinCoverData.baseChange R').pieces i ⊓
        (A.toFinCoverData.baseChange R').pieces j) ⧸
    A.pulledOvlIdeal R' i j

/-! ## The chart-local colength transport (certificate clause (c1)) -/

/-- **Base change of a chart-local colength module**:
`R' ⊗[R] colength j ≃ₐ[R'] pulledColength j` (the index-level quotient transport at the
equation ideal). -/
noncomputable def colengthBaseChange (j : A.index) :
    R' ⊗[R] A.colength j ≃ₐ[R'] A.pulledColength R' j :=
  (A.toFinCoverData.pieceQuotBaseChange R' j {A.eqn j}).trans
    (Ideal.quotientEquivAlgOfEq R' (by rw [Set.image_singleton]; rfl))

/-- The colength transport on `1 ⊗ [t]`: the residue class of the compared section. -/
lemma colengthBaseChange_one_tmul_mk (j : A.index) (t : Γ(relCurve C R, A.pieces j)) :
    A.colengthBaseChange R' j
        ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span {A.eqn j}) t) =
      Ideal.Quotient.mk (Ideal.span {A.pulledEqn R' j})
        (A.toFinCoverData.piecesMap R' j t) := by
  rw [colengthBaseChange, AlgEquiv.trans_apply,
    FinCoverData.pieceQuotBaseChange_one_tmul_mk, Ideal.quotientEquivAlgOfEq_mk]

/-- (c1) transport, finiteness: the pulled colengths are finite over `R'`. -/
theorem finite_pulledColength (hfin : ∀ j, Module.Finite R (A.colength j)) (j : A.index) :
    Module.Finite R' (A.pulledColength R' j) := by
  haveI := hfin j
  exact Module.Finite.equiv (A.colengthBaseChange R' j).toLinearEquiv

/-- (c1) transport, projectivity: the pulled colengths are projective over `R'`. -/
theorem projective_pulledColength (hproj : ∀ j, Module.Projective R (A.colength j))
    (j : A.index) :
    Module.Projective R' (A.pulledColength R' j) := by
  haveI := hproj j
  exact Module.Projective.of_equiv (A.colengthBaseChange R' j).toLinearEquiv

/-! ## The overlap colength transport -/

/-- **Base change of an overlap colength module**:
`R' ⊗[R] ovlColength i j ≃ₐ[R'] pulledOvlColength i j` (the overlap linchpin at the
symmetric equation ideal; the generators are carried by
`ovlMap_resHom_left`/`ovlMap_resHom_right`). -/
noncomputable def ovlColengthBaseChange (i j : A.index) :
    R' ⊗[R] A.ovlColength i j ≃ₐ[R'] A.pulledOvlColength R' i j :=
  (A.toFinCoverData.ovlQuotBaseChange R' i j
    {relResAlgHom C R inf_le_left (A.eqn i),
     relResAlgHom C R inf_le_right (A.eqn j)}).trans
    (Ideal.quotientEquivAlgOfEq R' (by
      have hl : A.toFinCoverData.ovlMap R' i j (relResAlgHom C R inf_le_left (A.eqn i))
          = relResAlgHom C R' inf_le_left (A.pulledEqn R' i) :=
        A.toFinCoverData.ovlMap_resHom_left R' i j (A.eqn i)
      have hr : A.toFinCoverData.ovlMap R' i j (relResAlgHom C R inf_le_right (A.eqn j))
          = relResAlgHom C R' inf_le_right (A.pulledEqn R' j) :=
        A.toFinCoverData.ovlMap_resHom_right R' i j (A.eqn j)
      rw [Set.image_insert_eq, Set.image_singleton, hl, hr]))

/-- The overlap transport on `1 ⊗ [t]`: the residue class of the compared section. -/
lemma ovlColengthBaseChange_one_tmul_mk (i j : A.index)
    (t : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)) :
    A.ovlColengthBaseChange R' i j
        ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (A.ovlIdeal i j) t) =
      Ideal.Quotient.mk (A.pulledOvlIdeal R' i j)
        (A.toFinCoverData.ovlMap R' i j t) := by
  rw [ovlColengthBaseChange, AlgEquiv.trans_apply,
    FinCoverData.ovlQuotBaseChange_one_tmul_mk, Ideal.quotientEquivAlgOfEq_mk]

/-! ## The pulled `δ`-arrows and the glued module -/

/-- The pulled left overlap-restriction map (restrict, then quotient). -/
noncomputable def pulledToOvlLeft (i j : A.index) :
    A.pulledColength R' i →ₐ[R'] A.pulledOvlColength R' i j :=
  Ideal.Quotient.liftₐ (Ideal.span {A.pulledEqn R' i})
    ((Ideal.Quotient.mkₐ R' (A.pulledOvlIdeal R' i j)).comp
      (relResAlgHom C R' inf_le_left))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [AlgHom.comp_apply, map_mul]
      have hmem : relResAlgHom C R' inf_le_left (A.pulledEqn R' i)
          ∈ A.pulledOvlIdeal R' i j :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul])

/-- The pulled right overlap-restriction map. -/
noncomputable def pulledToOvlRight (i j : A.index) :
    A.pulledColength R' j →ₐ[R'] A.pulledOvlColength R' i j :=
  Ideal.Quotient.liftₐ (Ideal.span {A.pulledEqn R' j})
    ((Ideal.Quotient.mkₐ R' (A.pulledOvlIdeal R' i j)).comp
      (relResAlgHom C R' inf_le_right))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [AlgHom.comp_apply, map_mul]
      have hmem : relResAlgHom C R' inf_le_right (A.pulledEqn R' j)
          ∈ A.pulledOvlIdeal R' i j :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul])

/-- The left overlap-restriction maps on residue classes (`liftₐ` over `mk`).
`private`: the public copy lives in `DivisorFamilyTheta` (same-day concurrent coinage,
the I-0190 pattern — the join collision surfaced at the first full root build). -/
private lemma toOvlLeft_mk (i j : A.index) (t : Γ(relCurve C R, A.pieces i)) :
    A.toOvlLeft i j (Ideal.Quotient.mk (Ideal.span {A.eqn i}) t) =
      Ideal.Quotient.mk (A.ovlIdeal i j) (relResAlgHom C R inf_le_left t) :=
  rfl

/-- The right overlap-restriction maps on residue classes. `private`: see
`toOvlLeft_mk`. -/
private lemma toOvlRight_mk (i j : A.index) (t : Γ(relCurve C R, A.pieces j)) :
    A.toOvlRight i j (Ideal.Quotient.mk (Ideal.span {A.eqn j}) t) =
      Ideal.Quotient.mk (A.ovlIdeal i j) (relResAlgHom C R inf_le_right t) :=
  rfl

lemma pulledToOvlLeft_mk (i j : A.index)
    (x : Γ(relCurve C R', (A.toFinCoverData.baseChange R').pieces i)) :
    A.pulledToOvlLeft R' i j (Ideal.Quotient.mk (Ideal.span {A.pulledEqn R' i}) x) =
      Ideal.Quotient.mk (A.pulledOvlIdeal R' i j) (relResAlgHom C R' inf_le_left x) :=
  rfl

lemma pulledToOvlRight_mk (i j : A.index)
    (x : Γ(relCurve C R', (A.toFinCoverData.baseChange R').pieces j)) :
    A.pulledToOvlRight R' i j (Ideal.Quotient.mk (Ideal.span {A.pulledEqn R' j}) x) =
      Ideal.Quotient.mk (A.pulledOvlIdeal R' i j) (relResAlgHom C R' inf_le_right x) :=
  rfl

/-- The pulled product of chart-local colengths. -/
noncomputable abbrev pulledChartProd : Type u := ∀ j : A.index, A.pulledColength R' j

/-- The pulled product of overlap colengths. -/
noncomputable abbrev pulledOvlProd : Type u :=
  ∀ p : A.index × A.index, A.pulledOvlColength R' p.1 p.2

/-- The pulled left equalizer arrow. -/
noncomputable def pulledDeltaLeft : A.pulledChartProd R' →ₗ[R'] A.pulledOvlProd R' :=
  LinearMap.pi (fun p : A.index × A.index =>
    (A.pulledToOvlLeft R' p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.1)

/-- The pulled right equalizer arrow. -/
noncomputable def pulledDeltaRight : A.pulledChartProd R' →ₗ[R'] A.pulledOvlProd R' :=
  LinearMap.pi (fun p : A.index × A.index =>
    (A.pulledToOvlRight R' p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.2)

/-- The pulled glued colength module `W'`. -/
noncomputable def pulledGluedSubmodule : Submodule R' (A.pulledChartProd R') :=
  LinearMap.ker (A.pulledDeltaLeft R' - A.pulledDeltaRight R')

/-! ## The product transports and `δ`-naturality -/

/-- Base change of the chart product: componentwise colength transport after
`TensorProduct.piRight`. -/
noncomputable def chartProdBaseChange :
    R' ⊗[R] A.chartProd ≃ₗ[R'] A.pulledChartProd R' :=
  (TensorProduct.piRight R R' R' (fun j : A.index => A.colength j)).trans
    (LinearEquiv.piCongrRight fun j => (A.colengthBaseChange R' j).toLinearEquiv)

/-- Base change of the overlap product. -/
noncomputable def ovlProdBaseChange :
    R' ⊗[R] A.ovlProd ≃ₗ[R'] A.pulledOvlProd R' :=
  (TensorProduct.piRight R R' R'
      (fun p : A.index × A.index => A.ovlColength p.1 p.2)).trans
    (LinearEquiv.piCongrRight fun p => (A.ovlColengthBaseChange R' p.1 p.2).toLinearEquiv)

lemma chartProdBaseChange_tmul_apply (r' : R') (s : A.chartProd) (l : A.index) :
    A.chartProdBaseChange R' (r' ⊗ₜ[R] s) l =
      A.colengthBaseChange R' l (r' ⊗ₜ[R] s l) := by
  rw [chartProdBaseChange, LinearEquiv.trans_apply, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]
  rfl

lemma ovlProdBaseChange_tmul_apply (r' : R') (s : A.ovlProd) (p : A.index × A.index) :
    A.ovlProdBaseChange R' (r' ⊗ₜ[R] s) p =
      A.ovlColengthBaseChange R' p.1 p.2 (r' ⊗ₜ[R] s p) := by
  rw [ovlProdBaseChange, LinearEquiv.trans_apply, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]
  rfl

/-- The left overlap-restriction square: the colength transport intertwines the
overlap-restriction maps with their pulled versions. -/
lemma pulledToOvlLeft_colengthBaseChange (i j : A.index) (x : R' ⊗[R] A.colength i) :
    A.pulledToOvlLeft R' i j (A.colengthBaseChange R' i x) =
      A.ovlColengthBaseChange R' i j
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
    rw [colengthBaseChange_one_tmul_mk, hlt, toOvlLeft_mk,
      ovlColengthBaseChange_one_tmul_mk, pulledToOvlLeft_mk]
    have hl : A.toFinCoverData.ovlMap R' i j (relResAlgHom C R inf_le_left t)
        = relResAlgHom C R' inf_le_left (A.toFinCoverData.piecesMap R' i t) :=
      A.toFinCoverData.ovlMap_resHom_left R' i j t
    rw [hl]

/-- The right overlap-restriction square. -/
lemma pulledToOvlRight_colengthBaseChange (i j : A.index) (x : R' ⊗[R] A.colength j) :
    A.pulledToOvlRight R' i j (A.colengthBaseChange R' j x) =
      A.ovlColengthBaseChange R' i j
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
    rw [colengthBaseChange_one_tmul_mk, hlt, toOvlRight_mk,
      ovlColengthBaseChange_one_tmul_mk, pulledToOvlRight_mk]
    have hr : A.toFinCoverData.ovlMap R' i j (relResAlgHom C R inf_le_right t)
        = relResAlgHom C R' inf_le_right (A.toFinCoverData.piecesMap R' j t) :=
      A.toFinCoverData.ovlMap_resHom_right R' i j t
    rw [hr]

set_option maxHeartbeats 1000000 in
-- The mixed-spelling defeq checks through the `relCurve`/product spellings are heavy,
-- as in `relTermBaseChange_tmul` ...
set_option synthInstance.maxHeartbeats 400000 in
-- ... and the instance searches on the large tensor/product types exceed the default
-- limit.
/-- **`δ`-naturality** (`informal/spec-dd-1.md` §3 stage (c)): the pulled difference
arrow matches `id ⊗ δ` through the product transports. -/
theorem delta_baseChange_comm :
    (A.pulledDeltaLeft R' - A.pulledDeltaRight R') ∘ₗ
        (A.chartProdBaseChange R' : R' ⊗[R] A.chartProd →ₗ[R'] A.pulledChartProd R') =
      (A.ovlProdBaseChange R' : R' ⊗[R] A.ovlProd →ₗ[R'] A.pulledOvlProd R') ∘ₗ
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
        fun p : A.index × A.index =>
          A.toOvlLeft p.1 p.2 (s p.1) - A.toOvlRight p.1 p.2 (s p.2) := by
      funext q
      simp only [LinearMap.sub_apply, deltaLeft, deltaRight, LinearMap.pi_apply,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
        AlgHom.toLinearMap_apply, Pi.sub_apply]
    have hL : ((A.pulledDeltaLeft R' - A.pulledDeltaRight R')
        ((A.chartProdBaseChange R') ((1 : R') ⊗ₜ[R] s))) p =
        A.pulledToOvlLeft R' p.1 p.2
            (A.colengthBaseChange R' p.1 ((1 : R') ⊗ₜ[R] s p.1)) -
          A.pulledToOvlRight R' p.1 p.2
            (A.colengthBaseChange R' p.2 ((1 : R') ⊗ₜ[R] s p.2)) := by
      have h1 := A.chartProdBaseChange_tmul_apply R' 1 s p.1
      have h2 := A.chartProdBaseChange_tmul_apply R' 1 s p.2
      simp only [LinearMap.sub_apply, Pi.sub_apply, pulledDeltaLeft, pulledDeltaRight,
        LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.proj_apply, AlgHom.toLinearMap_apply, h1, h2]
    have hR : ((A.ovlProdBaseChange R')
        ((AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight))
          ((1 : R') ⊗ₜ[R] s))) p =
        A.ovlColengthBaseChange R' p.1 p.2
            ((1 : R') ⊗ₜ[R] (A.toOvlLeft p.1 p.2 (s p.1))) -
          A.ovlColengthBaseChange R' p.1 p.2
            ((1 : R') ⊗ₜ[R] (A.toOvlRight p.1 p.2 (s p.2))) := by
      rw [hlt, A.ovlProdBaseChange_tmul_apply R' 1 _ p, hcomp,
        TensorProduct.tmul_sub, map_sub]
    have hLcomm : A.pulledToOvlLeft R' p.1 p.2
        (A.colengthBaseChange R' p.1 ((1 : R') ⊗ₜ[R] s p.1)) =
        A.ovlColengthBaseChange R' p.1 p.2
          ((1 : R') ⊗ₜ[R] (A.toOvlLeft p.1 p.2 (s p.1))) :=
      A.pulledToOvlLeft_colengthBaseChange R' p.1 p.2 ((1 : R') ⊗ₜ[R] s p.1)
    have hRcomm : A.pulledToOvlRight R' p.1 p.2
        (A.colengthBaseChange R' p.2 ((1 : R') ⊗ₜ[R] s p.2)) =
        A.ovlColengthBaseChange R' p.1 p.2
          ((1 : R') ⊗ₜ[R] (A.toOvlRight p.1 p.2 (s p.2))) :=
      A.pulledToOvlRight_colengthBaseChange R' p.1 p.2 ((1 : R') ⊗ₜ[R] s p.2)
    rw [hL, hR, hLcomm, hRcomm]

/-- The `δ`-naturality square, inverted verticals. -/
theorem delta_baseChange_comm' :
    (AlgebraTensorModule.lTensor R' R' (A.deltaLeft - A.deltaRight)) ∘ₗ
        ((A.chartProdBaseChange R').symm :
          A.pulledChartProd R' →ₗ[R'] R' ⊗[R] A.chartProd) =
      ((A.ovlProdBaseChange R').symm :
          A.pulledOvlProd R' →ₗ[R'] R' ⊗[R] A.ovlProd) ∘ₗ
        (A.pulledDeltaLeft R' - A.pulledDeltaRight R') := by
  apply LinearMap.ext
  intro x
  have h := congr($(A.delta_baseChange_comm R') ((A.chartProdBaseChange R').symm x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at h ⊢
  rw [h, LinearEquiv.symm_apply_apply]


end DivisorAdaptation

end AlgebraicGeometry
