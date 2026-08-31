/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianMatrixPoint

/-!
# GL-cocycle compatibility of the tautological family (DD-3, stage 3c-i)

The chart-wise tautological Grassmannian points (`GrassmannianTautological.lean`) agree
over the chart overlaps (`informal/spec-dd-3.md` §2, the (3c-i) row; route map: the GRQ
`bundleTransition` lane, collapsed to matrix algebra in the small submodule spelling —
no sheaf carrier, so the GRQ `L1–L3` transport disappears): over
`R^I_J = R^I[1/P^I_J]`, the pullback of the `J`-tautological point along the transition
pre-hom `θ̃_{I,J}` is the restriction of the `I`-tautological point.  The matrix heart is
the landed identity `θ̃_{I,J}(X^J) = (X^I_J)⁻¹ X^I` (`universalMatrix_map_transitionPreMap`)
plus GL-invariance of matrix points (`matrixPoint_unitMul`).

* `AlgebraicGeometry.Grassmannian.map_transitionPreMap_chartTautologicalPoint`:
  **the GL-cocycle compatibility** over the overlap ring.
* `AlgebraicGeometry.Grassmannian.map_comp_transitionPreMap_chartTautologicalPoint`: the
  composed form at an arbitrary test algebra under the overlap (the shape the basic-open
  gluing of `grPoint` consumes).
* `AlgebraicGeometry.Grassmannian.map_transitionMap_chartTautologicalPoint`: the
  glue-data spelling through the localised transition `θ_{I,J}`.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.Grassmannian

variable (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
variable (hI : I.card = d) (hJ : J.card = d)

/-- The Cramer inverse has unit determinant. -/
lemma isUnit_det_universalMinorInv :
    IsUnit (universalMinorInv k d r I J hI hJ).det :=
  IsUnit.of_mul_eq_one _ (by
    rw [← Matrix.det_mul, (universalMinorInv_mul_cancel k d r I J hI hJ).1, Matrix.det_one] :
    (universalMinorInv k d r I J hI hJ).det * (universalMinor k d r I J hI hJ).det = 1)

/-- **GL-cocycle compatibility of the tautological family** (stage 3c-i): over the chart
overlap ring `R^I_J`, pulling the `J`-tautological point back along the transition
pre-hom `θ̃_{I,J} : R^J →ₐ[k] R^I_J` gives the restriction of the `I`-tautological point
along the structure map `R^I →ₐ[k] R^I_J`.  Matrix content: `θ̃_{I,J}(X^J)` is the image
matrix `(X^I_J)⁻¹ X^I`, a `GL_d`-translate of `X^I` base-changed. -/
theorem map_transitionPreMap_chartTautologicalPoint :
    Module.Grassmannian.map (transitionPreMap k d r I J hI hJ)
        (chartTautologicalPoint k d r J hJ)
      = Module.Grassmannian.map
          (Algebra.algHom k (ChartRing k d r I)
            (Localization.Away (minorDet k d r I J hI hJ)))
          (chartTautologicalPoint k d r I hI) := by
  set L := Localization.Away (minorDet k d r I J hI hJ)
  have hJs := chartTautologicalProj_surjective k d r J hJ
  have hIs := chartTautologicalProj_surjective k d r I hI
  calc Module.Grassmannian.map (transitionPreMap k d r I J hI hJ)
        (chartTautologicalPoint k d r J hJ)
      = matrixPoint k d r L
          ((universalMatrix k d r J hJ).map (transitionPreMap k d r I J hI hJ))
          (matrixProj_surjective_map k d r _ _ hJs) := by
        rw [chartTautologicalPoint_eq_matrixPoint]
        exact map_matrixPoint k d r _ _ _ _
    _ = matrixPoint k d r L
          ((universalMatrix k d r I hI).map
            ⇑(Algebra.algHom k (ChartRing k d r I) L))
          (matrixProj_surjective_map k d r _ _ hIs) := by
        refine matrixPoint_eq_of_ker_eq k d r L _ _ _ _ ?_
        rw [show (universalMatrix k d r J hJ).map ⇑(transitionPreMap k d r I J hI hJ)
            = imageMatrix k d r I J hI hJ from
          universalMatrix_map_transitionPreMap k d r I J hI hJ,
          show imageMatrix k d r I J hI hJ
            = universalMinorInv k d r I J hI hJ *
              (universalMatrix k d r I hI).map
                ⇑(Algebra.algHom k (ChartRing k d r I) L) from rfl]
        exact ker_matrixProj_unitMul k d r L _
          (isUnit_det_universalMinorInv k d r I J hI hJ) _
    _ = Module.Grassmannian.map
          (Algebra.algHom k (ChartRing k d r I) L)
          (chartTautologicalPoint k d r I hI) := by
        rw [chartTautologicalPoint_eq_matrixPoint]
        exact (map_matrixPoint k d r _ _ _ _).symm

/-- The GL-cocycle compatibility composed into an arbitrary test algebra under the
overlap: for any `k`-algebra map `w : R^I_J →ₐ[k] D`, pulling the `J`-tautological point
along `w ∘ θ̃_{I,J}` equals pulling the `I`-tautological point along `w ∘ (R^I → R^I_J)`.
This is the shape consumed by the overlap bookkeeping of the basic-open gluing of
`grPoint`. -/
theorem map_comp_transitionPreMap_chartTautologicalPoint {D : Type u} [CommRing D]
    [Algebra k D]
    (w : Localization.Away (minorDet k d r I J hI hJ) →ₐ[k] D) :
    Module.Grassmannian.map (w.comp (transitionPreMap k d r I J hI hJ))
        (chartTautologicalPoint k d r J hJ)
      = Module.Grassmannian.map
          (w.comp (Algebra.algHom k (ChartRing k d r I)
            (Localization.Away (minorDet k d r I J hI hJ))))
          (chartTautologicalPoint k d r I hI) := by
  rw [Module.Grassmannian.map_comp, Module.Grassmannian.map_comp,
    map_transitionPreMap_chartTautologicalPoint]

/-- The GL-cocycle compatibility in the glue-data spelling: transporting the restriction
of the `J`-tautological point to `U^J_I` along the localised transition
`θ_{I,J} : R^J[1/P^J_I] →ₐ[k] R^I[1/P^I_J]` gives the restriction of the
`I`-tautological point to `U^I_J`. -/
theorem map_transitionMap_chartTautologicalPoint :
    Module.Grassmannian.map (transitionMap k d r I J hI hJ)
        (Module.Grassmannian.map
          (Algebra.algHom k (ChartRing k d r J)
            (Localization.Away (minorDet k d r J I hJ hI)))
          (chartTautologicalPoint k d r J hJ))
      = Module.Grassmannian.map
          (Algebra.algHom k (ChartRing k d r I)
            (Localization.Away (minorDet k d r I J hI hJ)))
          (chartTautologicalPoint k d r I hI) := by
  rw [← Module.Grassmannian.map_comp, transitionMap_comp_algHom]
  exact map_transitionPreMap_chartTautologicalPoint k d r I J hI hJ

end AlgebraicGeometry.Grassmannian
