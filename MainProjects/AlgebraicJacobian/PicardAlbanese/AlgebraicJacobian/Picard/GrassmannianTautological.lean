/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianChart
import AlgebraicJacobian.Picard.GrassmannianFunctor

/-!
# The tautological Grassmannian point over a chart (DD-3, stage 3c-i seed)

The universal point of the Grassmannian functor over each chart ring
(`informal/spec-dd-3.md` §2, the (3c-i) row): over `R^I`, the universal matrix `X^I`
presents a surjection `R^I ⊗[k] (Fin r → k) → (Fin d → R^I)` (through the
`piScalarRight` coordinate identification), split by the `I`-columns since the
`I`-minor of `X^I` is the identity; its kernel is a Grassmannian point — the quotient
is free of rank `d`.

This is the chart-wise tautological family.  The GL-cocycle compatibility of the
family over the chart overlaps and the pullback map `grPoint` on general tests are the
trailing (3c-i)/(3c-ii) work — DD-R consumes the forward direction through these; the
carve statements themselves need only stages (3a)+(3b)+(3e), which are landed.

* `AlgebraicGeometry.Grassmannian.chartTautologicalProj`: the universal-matrix
  presentation over `R^I`, with `chartTautologicalProj_surjective`.
* `AlgebraicGeometry.Grassmannian.chartTautologicalPoint`: **the tautological point**
  in `grFunctorAff k (Fin r → k) d R^I`.
-/

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct

namespace AlgebraicGeometry.Grassmannian

variable (k : Type u) [Field k] (d r : ℕ) (I : Finset (Fin r)) (hI : I.card = d)

/-- The universal-matrix presentation over the chart ring: the composite of the
coordinate identification `R^I ⊗[k] (Fin r → k) ≃ (Fin r → R^I)` with multiplication
by the universal matrix `X^I`. -/
noncomputable def chartTautologicalProj :
    TensorProduct k (ChartRing k d r I) (Fin r → k) →ₗ[ChartRing k d r I]
      (Fin d → ChartRing k d r I) :=
  (Matrix.mulVecLin (universalMatrix k d r I hI)).comp
    (TensorProduct.piScalarRight k (ChartRing k d r I) (ChartRing k d r I)
      (Fin r)).toLinearMap

/-- The section of the universal-matrix presentation on coordinates: dilate a
`d`-vector into an `r`-vector supported on the `I`-columns. -/
noncomputable def chartSection (y : Fin d → ChartRing k d r I) :
    Fin r → ChartRing k d r I :=
  fun q => if h : q ∈ I then y ((I.orderIsoOfFin hI).symm ⟨q, h⟩) else 0

/-- Multiplication by `X^I` splits on the `I`-columns: the `I`-minor of the universal
matrix is the identity. -/
lemma mulVec_chartSection (y : Fin d → ChartRing k d r I) :
    (universalMatrix k d r I hI).mulVec (chartSection k d r I hI y) = y := by
  funext p
  rw [Matrix.mulVec, dotProduct]
  calc ∑ q, universalMatrix k d r I hI p q * chartSection k d r I hI y q
      = ∑ q ∈ I, universalMatrix k d r I hI p q * chartSection k d r I hI y q := by
        refine (Finset.sum_subset (Finset.subset_univ I) fun q _ hq => ?_).symm
        rw [chartSection, dif_neg hq, mul_zero]
    _ = ∑ x : {q : Fin r // q ∈ I}, universalMatrix k d r I hI p x.1 *
          chartSection k d r I hI y x.1 := (Finset.sum_coe_sort I _).symm
    _ = ∑ p' : Fin d, universalMatrix k d r I hI p (I.orderIsoOfFin hI p') *
          chartSection k d r I hI y (I.orderIsoOfFin hI p') :=
        (Fintype.sum_equiv (I.orderIsoOfFin hI).toEquiv _ _ (fun p' => rfl)).symm
    _ = ∑ p' : Fin d, (1 : Matrix (Fin d) (Fin d) (ChartRing k d r I)) p p' * y p' := by
        refine Finset.sum_congr rfl fun p' _ => ?_
        have h1 : universalMatrix k d r I hI p (I.orderIsoOfFin hI p')
            = (1 : Matrix (Fin d) (Fin d) (ChartRing k d r I)) p p' := by
          have := congrFun (congrFun (universalMatrix_submatrix_self k d r I hI) p) p'
          rw [Matrix.submatrix_apply, id_eq] at this
          exact this
        have h2 : chartSection k d r I hI y ((I.orderIsoOfFin hI p' : Fin r)) = y p' := by
          rw [chartSection, dif_pos (I.orderIsoOfFin hI p').2]
          congr 1
          rw [show (⟨(I.orderIsoOfFin hI p' : Fin r), (I.orderIsoOfFin hI p').2⟩ :
                {q : Fin r // q ∈ I}) = I.orderIsoOfFin hI p' from Subtype.ext rfl]
          exact (I.orderIsoOfFin hI).symm_apply_apply p'
        rw [h1, h2]
    _ = y p := by
        rw [Finset.sum_eq_single p (fun p' _ hp' => by
          rw [Matrix.one_apply_ne' hp', zero_mul])
          (fun hp => absurd (Finset.mem_univ p) hp), Matrix.one_apply_eq, one_mul]

/-- The universal-matrix presentation is surjective. -/
lemma chartTautologicalProj_surjective :
    Function.Surjective (chartTautologicalProj k d r I hI) := by
  intro y
  refine ⟨(TensorProduct.piScalarRight k (ChartRing k d r I) (ChartRing k d r I)
    (Fin r)).symm (chartSection k d r I hI y), ?_⟩
  rw [chartTautologicalProj, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply, mulVec_chartSection]

/-- The quotient of the ambient module by the kernel of the presentation is the free
module `Fin d → R^I`. -/
noncomputable def chartTautologicalQuotEquiv :
    (TensorProduct k (ChartRing k d r I) (Fin r → k) ⧸
        LinearMap.ker (chartTautologicalProj k d r I hI)) ≃ₗ[ChartRing k d r I]
      (Fin d → ChartRing k d r I) :=
  LinearMap.quotKerEquivOfSurjective _ (chartTautologicalProj_surjective k d r I hI)

/-- **The tautological Grassmannian point over the chart `U^I`**: the kernel of the
universal-matrix presentation, with its free rank-`d` quotient certificate.  The
chart-wise universal family of the ported Grassmannian. -/
noncomputable def chartTautologicalPoint :
    grFunctorAff k (Fin r → k) d (ChartRing k d r I) where
  toSubmodule := LinearMap.ker (chartTautologicalProj k d r I hI)
  finite_quotient := Module.Finite.equiv (chartTautologicalQuotEquiv k d r I hI).symm
  projective_quotient := Module.Projective.of_equiv
    (chartTautologicalQuotEquiv k d r I hI).symm
  rankAtStalk_eq p := by
    rw [show Module.rankAtStalk (R := ChartRing k d r I)
          (TensorProduct k (ChartRing k d r I) (Fin r → k) ⧸
            LinearMap.ker (chartTautologicalProj k d r I hI)) p
        = Module.rankAtStalk (R := ChartRing k d r I)
            (Fin d → ChartRing k d r I) p from
      congrFun (Module.rankAtStalk_eq_of_equiv (chartTautologicalQuotEquiv k d r I hI)) p,
      show Module.rankAtStalk (R := ChartRing k d r I) (Fin d → ChartRing k d r I) p
        = Module.finrank (ChartRing k d r I) (Fin d → ChartRing k d r I) from
      congrFun Module.rankAtStalk_eq_finrank_of_free p,
      Module.finrank_fin_fun]

end AlgebraicGeometry.Grassmannian
