/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianTautological

/-!
# Matrix-presented Grassmannian points and their base change (DD-3, stage 3c)

The framed-point calculus of the DD-3 Grassmannian port (`informal/spec-dd-3.md` §2, the
(3c-i/ii) rows): a `d × r` matrix `X` over a `k`-algebra `S` whose row map is a split
surjection presents a Grassmannian point of `G(d, S ⊗[k] (Fin r → k); S)` — the kernel of
`X` acting through the coordinate identification, with free rank-`d` quotient.  This file
provides the point constructor and its two structural laws, the engine behind the
GL-cocycle compatibility of the tautological family, the `grPoint` forward map, and the
frame classification:

* `AlgebraicGeometry.Grassmannian.matrixProj`, `matrixPoint`: the presentation and the
  point (`chartTautologicalPoint` is the special case `X = universalMatrix`,
  `chartTautologicalPoint_eq_matrixPoint`).
* `AlgebraicGeometry.Grassmannian.map_matrixPoint`: **base change law** — mapping a
  matrix point along `f : S →ₐ[k] S'` gives the matrix point of the entrywise image
  `X.map f`.  In the small submodule spelling this is the entire GRQ `L1–L3` sheaf
  transport, collapsed to module algebra.
* `AlgebraicGeometry.Grassmannian.matrixPoint_unitMul`: **GL-invariance** — left
  multiplication by `GL_d(S)` does not move the point.
* the right-inverse kit (`matrixProj_surjective_of_mul_eq_one`,
  `exists_mul_eq_one_of_matrixProj_surjective`) transporting the split-surjectivity
  certificate along ring maps.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.Grassmannian

variable (k : Type u) [Field k] (d r : ℕ)
variable (S : Type u) [CommRing S] [Algebra k S]

/-- The **matrix presentation** over `S`: the composite of the coordinate identification
`S ⊗[k] (Fin r → k) ≃ (Fin r → S)` with multiplication by `X`.  For
`X = universalMatrix` this is the tautological presentation `chartTautologicalProj`. -/
noncomputable def matrixProj (X : Matrix (Fin d) (Fin r) S) :
    TensorProduct k S (Fin r → k) →ₗ[S] (Fin d → S) :=
  (Matrix.mulVecLin X).comp (TensorProduct.piScalarRight k S S (Fin r)).toLinearMap

@[simp]
lemma matrixProj_tmul (X : Matrix (Fin d) (Fin r) S) (s : S) (v : Fin r → k) :
    matrixProj k d r S X (s ⊗ₜ[k] v) = X.mulVec (fun q => v q • s) := by
  rw [matrixProj, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Matrix.mulVecLin_apply]

/-- The tautological presentation over a chart ring is the matrix presentation of the
universal matrix. -/
lemma chartTautologicalProj_eq_matrixProj (I : Finset (Fin r)) (hI : I.card = d) :
    chartTautologicalProj k d r I hI
      = matrixProj k d r (ChartRing k d r I) (universalMatrix k d r I hI) :=
  rfl

/-- A right-inverse matrix witnesses surjectivity of the matrix presentation. -/
lemma matrixProj_surjective_of_mul_eq_one (X : Matrix (Fin d) (Fin r) S)
    (Y : Matrix (Fin r) (Fin d) S) (hXY : X * Y = 1) :
    Function.Surjective (matrixProj k d r S X) := by
  intro y
  refine ⟨(TensorProduct.piScalarRight k S S (Fin r)).symm (Y.mulVec y), ?_⟩
  rw [matrixProj, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hXY,
    Matrix.one_mulVec]

/-- Surjectivity of the matrix presentation yields a right-inverse matrix (the split
certificate, in the form that transports along arbitrary ring maps). -/
lemma exists_mul_eq_one_of_matrixProj_surjective (X : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X)) :
    ∃ Y : Matrix (Fin r) (Fin d) S, X * Y = 1 := by
  choose w hw using fun p : Fin d => hX (Pi.single p 1)
  refine ⟨Matrix.of (fun q p => TensorProduct.piScalarRight k S S (Fin r) (w p) q), ?_⟩
  ext p p'
  have h1 : X.mulVec (TensorProduct.piScalarRight k S S (Fin r) (w p')) = Pi.single p' 1 := by
    have h := hw p'
    rwa [matrixProj, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Matrix.mulVecLin_apply] at h
  have h2 := congrFun h1 p
  rw [Matrix.mulVec, dotProduct] at h2
  rw [Matrix.mul_apply]
  simpa [Matrix.one_apply, Pi.single_apply] using h2

/-- The quotient by the kernel of a surjective matrix presentation is the free module
`Fin d → S`. -/
noncomputable def matrixQuotEquiv (X : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X)) :
    (TensorProduct k S (Fin r → k) ⧸ LinearMap.ker (matrixProj k d r S X)) ≃ₗ[S]
      (Fin d → S) :=
  LinearMap.quotKerEquivOfSurjective _ hX

/-- **The matrix-presented Grassmannian point**: the kernel of a surjective matrix
presentation, with its free rank-`d` quotient certificate. -/
noncomputable def matrixPoint (X : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X)) :
    grFunctorAff k (Fin r → k) d S where
  toSubmodule := LinearMap.ker (matrixProj k d r S X)
  finite_quotient := Module.Finite.equiv (matrixQuotEquiv k d r S X hX).symm
  projective_quotient := Module.Projective.of_equiv (matrixQuotEquiv k d r S X hX).symm
  rankAtStalk_eq p := by
    haveI : Nontrivial S := by
      rcases subsingleton_or_nontrivial S with hS | hS
      · exact absurd (p.asIdeal.eq_top_iff_one.mpr
          (by rw [Subsingleton.elim (1 : S) 0]; exact zero_mem _)) p.isPrime.ne_top
      · exact hS
    rw [show Module.rankAtStalk (R := S)
          (TensorProduct k S (Fin r → k) ⧸ LinearMap.ker (matrixProj k d r S X)) p
        = Module.rankAtStalk (R := S) (Fin d → S) p from
      congrFun (Module.rankAtStalk_eq_of_equiv (matrixQuotEquiv k d r S X hX)) p,
      show Module.rankAtStalk (R := S) (Fin d → S) p
        = Module.finrank S (Fin d → S) from
      congrFun Module.rankAtStalk_eq_finrank_of_free p,
      Module.finrank_fin_fun]

@[simp]
lemma matrixPoint_toSubmodule (X : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X)) :
    (matrixPoint k d r S X hX).toSubmodule = LinearMap.ker (matrixProj k d r S X) :=
  rfl

/-- The chart-wise tautological point is the matrix point of the universal matrix. -/
lemma chartTautologicalPoint_eq_matrixPoint (I : Finset (Fin r)) (hI : I.card = d) :
    chartTautologicalPoint k d r I hI
      = matrixPoint k d r (ChartRing k d r I) (universalMatrix k d r I hI)
          (chartTautologicalProj_surjective k d r I hI) :=
  Module.Grassmannian.ext rfl

/-- Two surjective presentations with equal kernels present the same point. -/
lemma matrixPoint_eq_of_ker_eq (X X' : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X))
    (hX' : Function.Surjective (matrixProj k d r S X'))
    (h : LinearMap.ker (matrixProj k d r S X) = LinearMap.ker (matrixProj k d r S X')) :
    matrixPoint k d r S X hX = matrixPoint k d r S X' hX' :=
  Module.Grassmannian.ext h

/-- Left multiplication by a matrix with unit determinant does not change the kernel of
the presentation. -/
lemma ker_matrixProj_unitMul (U : Matrix (Fin d) (Fin d) S) (hU : IsUnit U.det)
    (X : Matrix (Fin d) (Fin r) S) :
    LinearMap.ker (matrixProj k d r S (U * X)) = LinearMap.ker (matrixProj k d r S X) := by
  have hcomp : matrixProj k d r S (U * X)
      = (Matrix.mulVecLin U).comp (matrixProj k d r S X) := by
    rw [matrixProj, matrixProj, Matrix.mulVecLin_mul, LinearMap.comp_assoc]
  have hker : LinearMap.ker (Matrix.mulVecLin U) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    have h := congrArg (U⁻¹.mulVec) hab
    rwa [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul U hU, Matrix.one_mulVec,
      Matrix.one_mulVec] at h
  rw [hcomp, LinearMap.ker_comp, hker, Submodule.comap_bot]

/-- Surjectivity of a presentation is preserved by a unit-determinant left factor. -/
lemma matrixProj_surjective_unitMul (U : Matrix (Fin d) (Fin d) S) (hU : IsUnit U.det)
    (X : Matrix (Fin d) (Fin r) S) (hX : Function.Surjective (matrixProj k d r S X)) :
    Function.Surjective (matrixProj k d r S (U * X)) := by
  obtain ⟨Y, hY⟩ := exists_mul_eq_one_of_matrixProj_surjective k d r S X hX
  refine matrixProj_surjective_of_mul_eq_one k d r S _ (Y * U⁻¹) ?_
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc X Y, hY, Matrix.one_mul,
    Matrix.mul_nonsing_inv U hU]

/-- **GL-invariance of matrix points**: left multiplication by a matrix with unit
determinant presents the same Grassmannian point. -/
lemma matrixPoint_unitMul (U : Matrix (Fin d) (Fin d) S) (hU : IsUnit U.det)
    (X : Matrix (Fin d) (Fin r) S) (hX : Function.Surjective (matrixProj k d r S X))
    (hUX : Function.Surjective (matrixProj k d r S (U * X))) :
    matrixPoint k d r S (U * X) hUX = matrixPoint k d r S X hX :=
  Module.Grassmannian.ext (ker_matrixProj_unitMul k d r S U hU X)

section Map

variable {S} {S' : Type u} [CommRing S'] [Algebra k S']

/-- Surjectivity of a matrix presentation transports along any `k`-algebra map (through
the right-inverse certificate). -/
lemma matrixProj_surjective_map (f : S →ₐ[k] S') (X : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X)) :
    Function.Surjective (matrixProj k d r S' (X.map f)) := by
  obtain ⟨Y, hY⟩ := exists_mul_eq_one_of_matrixProj_surjective k d r S X hX
  refine matrixProj_surjective_of_mul_eq_one k d r S' _ (Y.map f) ?_
  have h := congrArg (Matrix.map · (f : S → S')) hY
  simpa [Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f)] using h

set_option maxHeartbeats 800000 in
-- The pure-tensor computation traverses the `f.toAlgebra` base-change tower on both
-- sides of the identification; elaboration cost, not a kernel raise.
/-- **The base-change law for matrix points**: mapping the matrix point of `X` along
`f : S →ₐ[k] S'` yields the matrix point of the entrywise image `X.map f`.  This is the
GRQ transport lane (`presentedMatrix_rqPullback`) collapsed to module algebra in the
small submodule spelling: the base-changed kernel of `X` is the kernel of `X.map f`. -/
theorem map_matrixPoint (f : S →ₐ[k] S') (X : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X))
    (hX' : Function.Surjective (matrixProj k d r S' (X.map f))) :
    Module.Grassmannian.map f (matrixPoint k d r S X hX)
      = matrixPoint k d r S' (X.map f) hX' := by
  letI : Algebra S S' := f.toAlgebra
  letI : IsScalarTower k S S' :=
    IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq k S S')
  -- the base-changed presentation, transported through the coordinate identifications
  set K := LinearMap.ker (matrixProj k d r S X) with hK
  set E := ((matrixQuotEquiv k d r S X hX).baseChange (R := S) (A := S')
        ≪≫ₗ TensorProduct.piScalarRight S S' S' (Fin d) :
      (S' ⊗[S] (TensorProduct k S (Fin r → k) ⧸ K)) ≃ₗ[S'] (Fin d → S')) with hE
  have key : ∀ x : TensorProduct k S' (Fin r → k),
      matrixProj k d r S' (X.map f) x
        = E (Module.Grassmannian.baseChangeMkQ S' K x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s' v =>
      rw [matrixProj_tmul, Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
        LinearMap.baseChange_tmul, Submodule.mkQ_apply, hE, LinearEquiv.trans_apply,
        LinearEquiv.baseChange_tmul,
        show (matrixQuotEquiv k d r S X hX) (Submodule.Quotient.mk ((1 : S) ⊗ₜ[k] v))
          = matrixProj k d r S X ((1 : S) ⊗ₜ[k] v) from
          LinearMap.quotKerEquivOfSurjective_apply_mk (matrixProj k d r S X) hX _,
        matrixProj_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      funext p
      simp only [Matrix.mulVec, dotProduct]
      rw [Algebra.smul_def, show algebraMap S S' = f.toRingHom from rfl, map_sum,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hterm : f.toRingHom (X p q * v q • (1 : S)) = f (X p q) * (v q • (1 : S')) := by
        rw [show f.toRingHom (X p q * v q • (1 : S)) = f (X p q * v q • (1 : S)) from rfl,
          map_mul, map_smul, map_one]
      rw [hterm, mul_assoc, smul_mul_assoc, one_mul, Matrix.map_apply]
  refine Module.Grassmannian.ext ?_
  have h0 : (Module.Grassmannian.map f (matrixPoint k d r S X hX)).toSubmodule
      = LinearMap.ker (Module.Grassmannian.baseChangeMkQ S' K) :=
    Module.Grassmannian.map_toSubmodule f _
  rw [h0, matrixPoint_toSubmodule]
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, key x, LinearEquiv.map_eq_zero_iff]

end Map

end AlgebraicGeometry.Grassmannian
