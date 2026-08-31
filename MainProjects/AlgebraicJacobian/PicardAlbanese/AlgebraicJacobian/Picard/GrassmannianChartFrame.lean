/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianMatrixPoint

/-!
# The `I`-minor-unit frame classification of matrix points (DD-3, stage 3c-ii)

The frame classification of the DD-3 Grassmannian port (`informal/spec-dd-3.md` §2, the
(3c-ii) row; worksheet `informal/dat-d-worksheet.md` §3.4): a matrix point over a
`k`-algebra `S` — the point presented by a split-surjective `d × r` matrix `X`, i.e. a
`grFunctorAff` point whose quotient is free with the chosen frame `X` — **factors through
the chart `U^I` iff the `I`-minor `det(X_I)` is a unit** of `S`.  When it is, the point is
the pullback of the tautological chart point `chartTautologicalPoint I` along the canonical
chart map `chartFrameMap` reading off the frame `X_I⁻¹ X` (whose `I`-minor is the
identity).  This is DD-R's chart-local inverse: from a matrix point sitting over chart `I`
it recovers the chart-`I` coordinates.

The forward direction (`… _of_isUnit`) is the piece DD-R consumes; the converse
(`isUnit_frameMinor_det_of_…`) completes the criterion via the fact that two
split-surjective presentations of the same point differ by a `GL_d(S)` left factor
(`exists_isUnit_mul_of_matrixPoint_eq`).  Everything here is module-algebra only (worksheet
§1.1 discipline): no scheme appears.

* `AlgebraicGeometry.Grassmannian.frameMinor`, `frameMatrix`, `chartFrameMap`: the
  `I`-minor `X_I`, the normalised frame `X_I⁻¹ X`, and the chart map it defines.
* `AlgebraicGeometry.Grassmannian.matrixPoint_eq_map_chartTautologicalPoint_of_isUnit`:
  **the forward frame factorisation** — a unit `I`-minor exhibits the point as the pullback
  of `chartTautologicalPoint I`.
* `AlgebraicGeometry.Grassmannian.exists_isUnit_mul_of_matrixPoint_eq`: two split
  presentations of the same point differ by a `GL_d(S)` left factor.
* `AlgebraicGeometry.Grassmannian.matrixPoint_factors_chart_iff`: **the full
  `I`-minor-unit criterion**.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.Grassmannian

variable (k : Type u) [Field k] (d r : ℕ)
variable (S : Type u) [CommRing S] [Algebra k S]

/-- The **`I`-minor** `X_I` of a `d × r` matrix `X` over `S`: the `d × d` submatrix on the
columns indexed by `I`, reindexed to `Fin d` by the order iso `Fin d ≃o ↥I`.  When `X`
presents a matrix point, `det(X_I)` is a unit exactly when the point factors through the
chart `U^I`. -/
noncomputable def frameMinor (k : Type u) [Field k] (d r : ℕ) (S : Type u) [CommRing S]
    [Algebra k S] (X : Matrix (Fin d) (Fin r) S) (I : Finset (Fin r))
    (hI : I.card = d) : Matrix (Fin d) (Fin d) S :=
  X.submatrix id (fun j => (I.orderIsoOfFin hI j : Fin r))

/-- The **normalised frame** `X_I⁻¹ X` of a matrix `X` with respect to the chart `I`: the
`GL_d(S)`-translate of `X` whose `I`-minor is the identity when `det(X_I)` is a unit
(`frameMinor_frameMatrix`).  Its free entries are the chart-`I` coordinates of the point. -/
noncomputable def frameMatrix (X : Matrix (Fin d) (Fin r) S) (I : Finset (Fin r))
    (hI : I.card = d) : Matrix (Fin d) (Fin r) S :=
  (frameMinor k d r S X I hI)⁻¹ * X

/-- The **canonical chart map** `R^I →ₐ[k] S` of a matrix `X` with unit `I`-minor: reads
each free indeterminate `x^I_{p,q}` off the corresponding entry of the normalised frame
`X_I⁻¹ X`.  It is the `k`-algebra map along which the point of `X` is the pullback of the
tautological chart point (`matrixPoint_eq_map_chartTautologicalPoint_of_isUnit`). -/
noncomputable def chartFrameMap (X : Matrix (Fin d) (Fin r) S) (I : Finset (Fin r))
    (hI : I.card = d) : ChartRing k d r I →ₐ[k] S :=
  MvPolynomial.aeval (fun e => frameMatrix k d r S X I hI e.1 e.2.1)

/-- The inverse of a unit `I`-minor again has unit determinant. -/
lemma isUnit_det_frameMinor_inv (X : Matrix (Fin d) (Fin r) S) (I : Finset (Fin r))
    (hI : I.card = d) (hu : IsUnit (frameMinor k d r S X I hI).det) :
    IsUnit ((frameMinor k d r S X I hI)⁻¹).det :=
  IsUnit.of_mul_eq_one _ (by
    rw [← Matrix.det_mul, Matrix.nonsing_inv_mul _ hu, Matrix.det_one] :
    ((frameMinor k d r S X I hI)⁻¹).det * (frameMinor k d r S X I hI).det = 1)

/-- The `I`-minor of the normalised frame `X_I⁻¹ X` is the identity (when `det(X_I)` is a
unit): `(X_I⁻¹ X)_I = X_I⁻¹ X_I = 1`. -/
theorem frameMinor_frameMatrix (X : Matrix (Fin d) (Fin r) S) (I : Finset (Fin r))
    (hI : I.card = d) (hu : IsUnit (frameMinor k d r S X I hI).det) :
    frameMinor k d r S (frameMatrix k d r S X I hI) I hI = 1 := by
  simp only [frameMinor, frameMatrix]
  rw [mul_submatrix_col]
  exact Matrix.nonsing_inv_mul _ hu

/-- The frame factors `X` on the left: `X_I · (X_I⁻¹ X) = X` (when `det(X_I)` is a unit). -/
theorem frameMinor_mul_frameMatrix (X : Matrix (Fin d) (Fin r) S) (I : Finset (Fin r))
    (hI : I.card = d) (hu : IsUnit (frameMinor k d r S X I hI).det) :
    frameMinor k d r S X I hI * frameMatrix k d r S X I hI = X := by
  rw [frameMatrix, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-- The universal matrix `X^I` maps to the normalised frame `X_I⁻¹ X` under the canonical
chart map: `θ(X^I) = X_I⁻¹ X`, mirroring `universalMatrix_map_transitionPreMap`.  On the
`I`-columns both sides are the identity block; off them the chart map reads the free
indeterminate onto its assigned frame entry. -/
theorem universalMatrix_map_chartFrameMap (X : Matrix (Fin d) (Fin r) S)
    (I : Finset (Fin r)) (hI : I.card = d) (hu : IsUnit (frameMinor k d r S X I hI).det) :
    (universalMatrix k d r I hI).map (chartFrameMap k d r S X I hI)
      = frameMatrix k d r S X I hI := by
  ext p q
  simp only [Matrix.map_apply, universalMatrix]
  by_cases hq : q ∈ I
  · rw [dif_pos hq]
    set c := (I.orderIsoOfFin hI).symm ⟨q, hq⟩ with hc
    have hqc : (I.orderIsoOfFin hI c : Fin r) = q := by simp [hc]
    have hframe : frameMatrix k d r S X I hI p q = (1 : Matrix (Fin d) (Fin d) S) p c := by
      have e := congrFun (congrFun (frameMinor_frameMatrix k d r S X I hI hu) p) c
      rw [frameMinor, Matrix.submatrix_apply, id_eq] at e
      rw [← hqc]; exact e
    rw [hframe, Matrix.one_apply, apply_ite (chartFrameMap k d r S X I hI), map_one, map_zero]
    have hcond : ((I.orderIsoOfFin hI p : Fin r) = q) ↔ (p = c) := by
      conv_lhs => rw [← hqc]
      rw [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq]
    by_cases hpc : p = c
    · rw [if_pos (hcond.mpr hpc), if_pos hpc]
    · rw [if_neg (hcond.not.mpr hpc), if_neg hpc]
  · rw [dif_neg hq, chartFrameMap, MvPolynomial.aeval_X]

/-- Surjectivity of the presentation transports to the normalised frame `X_I⁻¹ X`. -/
theorem matrixProj_surjective_frameMatrix (X : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X)) (I : Finset (Fin r)) (hI : I.card = d)
    (hu : IsUnit (frameMinor k d r S X I hI).det) :
    Function.Surjective (matrixProj k d r S (frameMatrix k d r S X I hI)) :=
  matrixProj_surjective_unitMul k d r S (frameMinor k d r S X I hI)⁻¹
    (isUnit_det_frameMinor_inv k d r S X I hI hu) X hX

/-- **The forward frame factorisation** (stage 3c-ii): when the `I`-minor `det(X_I)` is a
unit, the matrix point of `X` is the pullback of the tautological chart point
`chartTautologicalPoint I` along the canonical chart map `chartFrameMap`.  Content: `X` is
the `GL_d`-translate `X_I · (X_I⁻¹ X)` of the normalised frame `X_I⁻¹ X`, which is the image
of the universal matrix under `chartFrameMap`. -/
theorem matrixPoint_eq_map_chartTautologicalPoint_of_isUnit (X : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X)) (I : Finset (Fin r)) (hI : I.card = d)
    (hu : IsUnit (frameMinor k d r S X I hI).det) :
    matrixPoint k d r S X hX
      = Module.Grassmannian.map (chartFrameMap k d r S X I hI)
          (chartTautologicalPoint k d r I hI) := by
  have hF := matrixProj_surjective_frameMatrix k d r S X hX I hI hu
  have hker : LinearMap.ker (matrixProj k d r S X)
      = LinearMap.ker (matrixProj k d r S (frameMatrix k d r S X I hI)) :=
    (ker_matrixProj_unitMul k d r S (frameMinor k d r S X I hI)⁻¹
      (isUnit_det_frameMinor_inv k d r S X I hI hu) X).symm
  rw [matrixPoint_eq_of_ker_eq k d r S X (frameMatrix k d r S X I hI) hX hF hker,
    chartTautologicalPoint_eq_matrixPoint,
    map_matrixPoint k d r (chartFrameMap k d r S X I hI) (universalMatrix k d r I hI)
      (chartTautologicalProj_surjective k d r I hI)
      (matrixProj_surjective_map k d r (chartFrameMap k d r S X I hI) (universalMatrix k d r I hI)
        (chartTautologicalProj_surjective k d r I hI))]
  exact matrixPoint_eq_of_ker_eq k d r S _ _ hF _
    (by rw [universalMatrix_map_chartFrameMap k d r S X I hI hu])

/-- **Two split presentations of the same point differ by a `GL_d(S)` left factor**: if
`X` and `Y` present the same matrix point, there is a unit-determinant `U` with `X = U Y`.
Content: the two surjections `matrixProj X`, `matrixProj Y` share a kernel, hence induce
the same quotient of the ambient module, so the two identifications with the free quotient
`S^d` differ by a linear automorphism `u = mulVec U`; the reverse identification gives its
inverse, forcing `det U` to be a unit. -/
theorem exists_isUnit_mul_of_matrixPoint_eq (X Y : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X))
    (hY : Function.Surjective (matrixProj k d r S Y))
    (h : matrixPoint k d r S X hX = matrixPoint k d r S Y hY) :
    ∃ U : Matrix (Fin d) (Fin d) S, IsUnit U.det ∧ X = U * Y := by
  have hker : LinearMap.ker (matrixProj k d r S X)
      = LinearMap.ker (matrixProj k d r S Y) := by
    have h2 := congrArg Module.Grassmannian.toSubmodule h
    rwa [matrixPoint_toSubmodule, matrixPoint_toSubmodule] at h2
  set φX := matrixProj k d r S X with hφX
  set φY := matrixProj k d r S Y with hφY
  -- the two quotient identifications and the lifts of one map over the other's kernel
  set eY := LinearMap.quotKerEquivOfSurjective φY hY with heY
  set eX := LinearMap.quotKerEquivOfSurjective φX hX with heX
  set lX := (LinearMap.ker φY).liftQ φX hker.ge with hlX
  set lY := (LinearMap.ker φX).liftQ φY hker.le with hlY
  set u := lX ∘ₗ (eY.symm : (Fin d → S) →ₗ[S] _) with hu
  set v := lY ∘ₗ (eX.symm : (Fin d → S) →ₗ[S] _) with hv
  -- `u` intertwines the two surjections; `v` is its two-sided inverse
  have hmkY : (eY.symm : (Fin d → S) →ₗ[S] _) ∘ₗ φY = (LinearMap.ker φY).mkQ := by
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    apply eY.injective
    rw [LinearEquiv.apply_symm_apply, heY, Submodule.mkQ_apply,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  have hmkX : (eX.symm : (Fin d → S) →ₗ[S] _) ∘ₗ φX = (LinearMap.ker φX).mkQ := by
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    apply eX.injective
    rw [LinearEquiv.apply_symm_apply, heX, Submodule.mkQ_apply,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  have huφcomp : u ∘ₗ φY = φX := by
    rw [hu, LinearMap.comp_assoc, hmkY]
    exact (LinearMap.ker φY).liftQ_mkQ φX hker.ge
  have hvφcomp : v ∘ₗ φX = φY := by
    rw [hv, LinearMap.comp_assoc, hmkX]
    exact (LinearMap.ker φX).liftQ_mkQ φY hker.le
  have huφ : ∀ w, u (φY w) = φX w := fun w => LinearMap.congr_fun huφcomp w
  have hvφ : ∀ w, v (φX w) = φY w := fun w => LinearMap.congr_fun hvφcomp w
  have huv : u ∘ₗ v = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨w, rfl⟩ := hX y
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hvφ w, huφ w]
  -- transport `u` to a matrix and read off `X = U Y`
  set U := LinearMap.toMatrix' u with hUdef
  have hUu : U.mulVecLin = u := by
    rw [hUdef, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  refine ⟨U, ?_, ?_⟩
  · -- `det U` is a unit: `U · toMatrix' v = 1`
    have hcomp : U * LinearMap.toMatrix' v = 1 := by
      rw [hUdef, ← LinearMap.toMatrix'_comp, huv, LinearMap.toMatrix'_id]
    exact IsUnit.of_mul_eq_one _ (by
      rw [← Matrix.det_mul, hcomp, Matrix.det_one] :
      U.det * (LinearMap.toMatrix' v).det = 1)
  · -- `X = U · Y`: both send the coordinate frame the same way
    have hpt : ∀ w : Fin r → S, u (Y.mulVec w) = X.mulVec w := by
      intro w
      have hYw : φY ((TensorProduct.piScalarRight k S S (Fin r)).symm w) = Y.mulVec w := by
        rw [hφY, matrixProj, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply]
      have hXw : φX ((TensorProduct.piScalarRight k S S (Fin r)).symm w) = X.mulVec w := by
        rw [hφX, matrixProj, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply]
      rw [← hYw, ← hXw, huφ]
    have hML : (U * Y).mulVecLin = X.mulVecLin := by
      refine LinearMap.ext fun w => ?_
      rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVecLin_apply, hUu,
        hpt w, ← Matrix.mulVecLin_apply]
    have hUYX : U * Y = X := by
      have h2 := congrArg LinearMap.toMatrix' hML
      rwa [← Matrix.toLin'_apply', ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
        LinearMap.toMatrix'_toLin'] at h2
    exact hUYX.symm

/-- **The converse of the frame factorisation**: if the point of `X` is the pullback of the
tautological chart point `chartTautologicalPoint I` along some chart map `g`, then the
`I`-minor `det(X_I)` is a unit.  Content: any presentation of a chart-`I` pullback differs
from the universal frame `X^I.map g` (whose `I`-minor is the identity) by a `GL_d(S)`
factor, so its `I`-minor is that factor — a unit. -/
theorem isUnit_frameMinor_det_of_matrixPoint_eq_map (X : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X)) (I : Finset (Fin r)) (hI : I.card = d)
    (g : ChartRing k d r I →ₐ[k] S)
    (h : matrixPoint k d r S X hX
      = Module.Grassmannian.map g (chartTautologicalPoint k d r I hI)) :
    IsUnit (frameMinor k d r S X I hI).det := by
  set Y := (universalMatrix k d r I hI).map g with hY
  have hYs : Function.Surjective (matrixProj k d r S Y) :=
    matrixProj_surjective_map k d r g (universalMatrix k d r I hI)
      (chartTautologicalProj_surjective k d r I hI)
  have hXY : matrixPoint k d r S X hX = matrixPoint k d r S Y hYs := by
    rw [h, chartTautologicalPoint_eq_matrixPoint,
      map_matrixPoint k d r g (universalMatrix k d r I hI)
        (chartTautologicalProj_surjective k d r I hI) hYs]
  obtain ⟨U, hUdet, hXU⟩ := exists_isUnit_mul_of_matrixPoint_eq k d r S X Y hX hYs hXY
  have hminorY : frameMinor k d r S Y I hI = 1 := by
    rw [frameMinor, hY, Matrix.submatrix_map, universalMatrix_submatrix_self,
      Matrix.map_one _ (map_zero g) (map_one g)]
  have hminorX : frameMinor k d r S X I hI = U := by
    have hstep : frameMinor k d r S X I hI = U * frameMinor k d r S Y I hI := by
      simp only [frameMinor]
      rw [hXU, mul_submatrix_col]
    rw [hstep, hminorY, Matrix.mul_one]
  rw [hminorX]
  exact hUdet

/-- **The full `I`-minor-unit criterion** (stage 3c-ii): a matrix point over `S` factors
through the chart `U^I` — i.e. is the pullback of the tautological chart point along some
chart map `R^I →ₐ[k] S` — **iff** its `I`-minor `det(X_I)` is a unit of `S`.  The forward
map of the `←` direction is `chartFrameMap`, reading off the chart-`I` coordinates. -/
theorem matrixPoint_factors_chart_iff (X : Matrix (Fin d) (Fin r) S)
    (hX : Function.Surjective (matrixProj k d r S X)) (I : Finset (Fin r)) (hI : I.card = d) :
    (∃ g : ChartRing k d r I →ₐ[k] S, matrixPoint k d r S X hX
        = Module.Grassmannian.map g (chartTautologicalPoint k d r I hI))
      ↔ IsUnit (frameMinor k d r S X I hI).det := by
  constructor
  · rintro ⟨g, hg⟩
    exact isUnit_frameMinor_det_of_matrixPoint_eq_map k d r S X hX I hI g hg
  · intro hu
    exact ⟨chartFrameMap k d r S X I hI,
      matrixPoint_eq_map_chartTautologicalPoint_of_isUnit k d r S X hX I hI hu⟩

end AlgebraicGeometry.Grassmannian
