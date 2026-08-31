/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianCocycle

/-!
# The rotated triple-overlap cocycle `Φ = id` over a field (DD-3, stage 3a)

The `cocycle` field of the Grassmannian glue data reduces (after stripping the
conjugating pullback isomorphisms) to a single ring identity `Φ = id` over the
triple-overlap ring `S_I = R^I[1/(P^I_J P^I_K)]`, where
`Φ = Θ_{I,J,K} ∘ swap_J ∘ Θ_{J,K,I} ∘ swap_K ∘ Θ_{K,I,J} ∘ swap_I` (rotated index
triples).  We prove it by telescoping with `cocycleCondition` down to a single inverse
pair `θ_{I,K} ∘ θ_{K,I} = id`, closed by the matrix collapse
`transitionInvImageMatrix` (`informal/spec-dd-3.md` §2/§3; route map: the
GR-Quot-Closure tree's `GrassmannianCells.lean` Φ-section, in the `→ₐ[k]`
architecture — generators-only extensionality).

* `AlgebraicGeometry.Grassmannian.awayMulCommAlgEquiv`: the order-swap
  `R[1/(xy)] ≃ₐ[k] R[1/(yx)]`.
* `AlgebraicGeometry.Grassmannian.rotMid`: conjugating the rotated `Θ_{J,K,I}` by the
  two order-swaps recovers `Θ_{J,K}` in the `I,J,K` frame.
* `AlgebraicGeometry.Grassmannian.transitionInvPair`: the inverse-pair identity
  `Θ_{I,K} ∘ Θ_{K,I} ∘ swap_I = id`.
* `AlgebraicGeometry.Grassmannian.cocyclePhiId`: **the rotated cocycle** `Φ = id`.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Grassmannian

/-- The product-commutativity equivalence `R[1/(xy)] ≃ₐ[k] R[1/(yx)]`: the two
away-localisations agree because `Submonoid.powers (x*y) = Submonoid.powers (y*x)`.
Resolves the product-order mismatch between `cocycleΘIJ` (domain `R[1/(P^J_I P^J_K)]`)
and the away-pullback identification (codomain `R[1/(P^J_K P^J_I)]`) in the
triple-overlap `t'`-field of the glue data. -/
noncomputable def awayMulCommAlgEquiv (k : Type u) [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (x y : A) :
    Localization.Away (x * y) ≃ₐ[k] Localization.Away (y * x) := by
  haveI : IsLocalization.Away (y * x) (Localization.Away (x * y)) := by
    rw [mul_comm y x]; infer_instance
  exact (IsLocalization.algEquiv (Submonoid.powers (y * x))
    (Localization.Away (x * y)) (Localization.Away (y * x))).restrictScalars k

/-- The order-swap lies over the base ring, pointwise form. -/
lemma awayMulCommAlgEquiv_algebraMap_apply (k : Type u) [Field k] {A : Type u}
    [CommRing A] [Algebra k A] (x y : A) (a : A) :
    awayMulCommAlgEquiv k x y (algebraMap A (Localization.Away (x * y)) a)
      = algebraMap A (Localization.Away (y * x)) a := by
  haveI : IsLocalization.Away (y * x) (Localization.Away (x * y)) := by
    rw [mul_comm y x]; infer_instance
  exact (IsLocalization.algEquiv (Submonoid.powers (y * x))
    (Localization.Away (x * y)) (Localization.Away (y * x))).commutes a

/-- The order-swap lies over the base ring: it intertwines the structure maps
(`AlgHom` composition form). -/
lemma awayMulCommAlgEquiv_comp_algHom (k : Type u) [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (x y : A) :
    (awayMulCommAlgEquiv k x y).toAlgHom.comp
        (Algebra.algHom k A (Localization.Away (x * y)))
      = Algebra.algHom k A (Localization.Away (y * x)) :=
  AlgHom.ext fun a => awayMulCommAlgEquiv_algebraMap_apply k x y a

/-- The order-swap lies over the base ring: ring-hom composition form, for the matrix
computations. -/
lemma awayMulCommAlgEquiv_comp_algebraMap (k : Type u) [Field k] {A : Type u}
    [CommRing A] [Algebra k A] (x y : A) :
    (awayMulCommAlgEquiv k x y).toAlgHom.toRingHom.comp
        (algebraMap A (Localization.Away (x * y)))
      = algebraMap A (Localization.Away (y * x)) :=
  RingHom.ext fun a => awayMulCommAlgEquiv_algebraMap_apply k x y a

/-- The order-swap absorbs a left away-inclusion into a right one:
`swap_{x,y} ∘ ι^L_{x,y} = ι^R_{y,x}` as maps `R[1/x] →ₐ[k] R[1/(yx)]`. -/
lemma awayMulCommAlgEquiv_comp_awayInclLeft (k : Type u) [Field k] {A : Type u}
    [CommRing A] [Algebra k A] (x y : A) :
    (awayMulCommAlgEquiv k x y).toAlgHom.comp (awayInclLeft k x y)
      = awayInclRight k y x := by
  apply IsLocalization.algHom_ext (Submonoid.powers x)
  refine AlgHom.ext fun a => ?_
  change awayMulCommAlgEquiv k x y
      (awayInclLeft k x y (algebraMap A (Localization.Away x) a))
    = awayInclRight k y x (algebraMap A (Localization.Away x) a)
  rw [awayInclLeft_algebraMap_apply, awayMulCommAlgEquiv_algebraMap_apply,
    awayInclRight_algebraMap_apply]

/-- **Rotation lemma** for the triple-overlap transitions: conjugating the rotated
`Θ_{J,K,I}` by the two order-swaps recovers the `J,K`-transition `Θ_{J,K}` in the
`I,J,K` frame.  Both sides are lifts of `θ̃_{J,K}`; checked on the chart ring `R^K`. -/
lemma rotMid (k : Type u) [Field k] (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    ((awayMulCommAlgEquiv k (minorDet k d r J K hJ hK)
        (minorDet k d r J I hJ hI)).toAlgHom.comp
        (cocycleΘIJ k d r J K I hJ hK hI)).comp
        (awayMulCommAlgEquiv k (minorDet k d r K I hK hI)
          (minorDet k d r K J hK hJ)).toAlgHom
      = cocycleΘJK k d r I J K hI hJ hK := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (minorDet k d r K I hK hI * minorDet k d r K J hK hJ))
  rw [AlgHom.comp_assoc, awayMulCommAlgEquiv_comp_algHom, AlgHom.comp_assoc,
    cocycleΘIJ_comp_algHom, ← AlgHom.comp_assoc, awayMulCommAlgEquiv_comp_awayInclLeft,
    cocycleΘJK_comp_algHom]

/-- The matrix collapse behind the inverse pair `θ_{I,K} ∘ θ_{K,I} = id`: pushing the
image matrix `(X^K_I)⁻¹ X^K` of `θ_{K,I}` forward along `θ_{I,K}` (realised as
`Θ_{I,K} ∘ ι^L`) recovers the universal matrix `X^I` over the triple-overlap ring
`S_I`.  Both reduce to `W = X^I` over `S_I` via the `(W_K)⁻¹ W` computation, using
`W_I = 1`. -/
lemma transitionInvImageMatrix (k : Type u) [Field k] (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (imageMatrix k d r K I hK hI).map
        ((cocycleΘIK k d r I J K hI hJ hK).toRingHom.comp
          (awayInclLeft k (minorDet k d r K I hK hI)
            (minorDet k d r K J hK hJ)).toRingHom)
      = (universalMatrix k d r I hI).map
          (algebraMap (ChartRing k d r I)
            (Localization.Away (minorDet k d r I J hI hJ * minorDet k d r I K hI hK))) := by
  set incl := (cocycleΘIK k d r I J K hI hJ hK).toRingHom.comp
    (awayInclLeft k (minorDet k d r K I hK hI) (minorDet k d r K J hK hJ)).toRingHom
    with hincldef
  have hcomp : incl.comp (algebraMap (ChartRing k d r K)
        (Localization.Away (minorDet k d r K I hK hI)))
      = (awayInclRight k (minorDet k d r I J hI hJ)
            (minorDet k d r I K hI hK)).toRingHom.comp
          (transitionPreMap k d r I K hI hK).toRingHom := by
    rw [hincldef, RingHom.comp_assoc, awayInclLeft_comp_algebraMap]
    exact cocycleΘIK_comp_algebraMap k d r I J K hI hJ hK
  set W := (universalMatrix k d r I hI).map
      (algebraMap (ChartRing k d r I)
        (Localization.Away (minorDet k d r I J hI hJ * minorDet k d r I K hI hK)))
    with hW
  have hWK : IsUnit (W.submatrix id (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r))).det := by
    have e : (W.submatrix id (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r))).det
        = algebraMap (ChartRing k d r I)
            (Localization.Away (minorDet k d r I J hI hJ * minorDet k d r I K hI hK))
            (minorDet k d r I K hI hK) := by
      rw [hW, Matrix.submatrix_map]
      exact (RingHom.map_det _ _).symm
    rw [e]; exact isUnit_algebraMap_away_right _ _
  have hMK : (universalMatrix k d r K hK).map
        ((awayInclRight k (minorDet k d r I J hI hJ)
            (minorDet k d r I K hI hK)).toRingHom.comp
          (transitionPreMap k d r I K hI hK).toRingHom)
      = (W.submatrix id (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r)))⁻¹ * W := by
    have e1 : (universalMatrix k d r K hK).map
          ((awayInclRight k (minorDet k d r I J hI hJ)
              (minorDet k d r I K hI hK)).toRingHom.comp
            (transitionPreMap k d r I K hI hK).toRingHom)
        = (imageMatrix k d r I K hI hK).map
            (awayInclRight k (minorDet k d r I J hI hJ)
              (minorDet k d r I K hI hK)).toRingHom := by
      rw [← map_map_eq_of_comp (universalMatrix k d r K hK)
          (transitionPreMap k d r I K hI hK).toRingHom
          (awayInclRight k (minorDet k d r I J hI hJ)
            (minorDet k d r I K hI hK)).toRingHom _ rfl]
      congr 1
      exact universalMatrix_map_transitionPreMap k d r I K hI hK
    rw [e1, imageMatrix_map_eq k d r I K hI hK
      (awayInclRight k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).toRingHom
      (awayInclRight_comp_algebraMap k _ _), hW]
  have hWI : W.submatrix id (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) = 1 := by
    rw [hW, Matrix.submatrix_map, universalMatrix_submatrix_self]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hmm : (imageMatrix k d r K I hK hI).map incl
      = (universalMinorInv k d r K I hK hI).map incl
        * ((universalMatrix k d r K hK).map
            (algebraMap (ChartRing k d r K)
              (Localization.Away (minorDet k d r K I hK hI)))).map incl := by
    rw [imageMatrix]; exact Matrix.map_mul
  rw [hmm, map_map_eq_of_comp _ _ _ _ hcomp, hMK, universalMinorInv,
    ← map_nonsing_inv incl (universalMinor k d r K I hK hI)
      (isUnit_det_universalMinor k d r K I hK hI),
    universalMinor, map_map_eq_of_comp _ _ _ _ hcomp, ← Matrix.submatrix_map, hMK,
    mul_submatrix_col (W.submatrix id (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r)))⁻¹ W
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)),
    hWI, mul_one, Matrix.nonsing_inv_nonsing_inv _ hWK, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hWK, Matrix.one_mul]

/-- The inverse-pair identity `θ_{I,K} ∘ θ_{K,I} = id` over the triple-overlap ring
`S_I = R^I[1/(P^I_J P^I_K)]`, phrased through the localised transitions and the
order-swap: `Θ_{I,K} ∘ Θ_{K,I,J} ∘ swap_I = id`.  Closed on chart-ring generators by
the matrix collapse `transitionInvImageMatrix`. -/
lemma transitionInvPair (k : Type u) [Field k] (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (cocycleΘIK k d r I J K hI hJ hK).comp
        ((cocycleΘIJ k d r K I J hK hI hJ).comp
          (awayMulCommAlgEquiv k (minorDet k d r I J hI hJ)
            (minorDet k d r I K hI hK)).toAlgHom)
      = AlgHom.id k (Localization.Away
          (minorDet k d r I J hI hJ * minorDet k d r I K hI hK)) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (minorDet k d r I J hI hJ * minorDet k d r I K hI hK))
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc, awayMulCommAlgEquiv_comp_algHom,
    cocycleΘIJ_comp_algHom, ← AlgHom.comp_assoc, AlgHom.id_comp]
  apply MvPolynomial.algHom_ext
  intro e
  change ((cocycleΘIK k d r I J K hI hJ hK).comp
      (awayInclLeft k (minorDet k d r K I hK hI) (minorDet k d r K J hK hJ)))
      (transitionPreMap k d r K I hK hI (MvPolynomial.X e))
    = algebraMap (ChartRing k d r I)
        (Localization.Away (minorDet k d r I J hI hJ * minorDet k d r I K hI hK))
        (MvPolynomial.X e)
  have h := congrFun (congrFun (transitionInvImageMatrix k d r I J K hI hJ hK) e.1) e.2.1
  rw [Matrix.map_apply, Matrix.map_apply] at h
  rw [show universalMatrix k d r I hI e.1 e.2.1 = MvPolynomial.X e from by
    rw [universalMatrix, dif_neg e.2.2]] at h
  rw [transitionPreMap, MvPolynomial.aeval_X]
  exact h

/-- **The rotated triple-overlap cocycle** `Φ = id`: over the triple-overlap ring
`S_I = R^I[1/(P^I_J P^I_K)]`, the composite
`Θ_{I,J,K} ∘ swap_J ∘ Θ_{J,K,I} ∘ swap_K ∘ Θ_{K,I,J} ∘ swap_I` is the identity.  This
is the ring identity underlying the `cocycle` field of the Grassmannian glue data.
Proved by telescoping: the middle `swap_J ∘ Θ_{J,K,I} ∘ swap_K` collapses to `Θ_{J,K}`
(`rotMid`), then `Θ_{I,J} ∘ Θ_{J,K} = Θ_{I,K}` (`cocycleCondition`), leaving the
inverse pair `Θ_{I,K} ∘ Θ_{K,I} ∘ swap_I = id` (`transitionInvPair`). -/
theorem cocyclePhiId (k : Type u) [Field k] (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (cocycleΘIJ k d r I J K hI hJ hK).comp
        ((awayMulCommAlgEquiv k (minorDet k d r J K hJ hK)
            (minorDet k d r J I hJ hI)).toAlgHom.comp
          ((cocycleΘIJ k d r J K I hJ hK hI).comp
            ((awayMulCommAlgEquiv k (minorDet k d r K I hK hI)
                (minorDet k d r K J hK hJ)).toAlgHom.comp
              ((cocycleΘIJ k d r K I J hK hI hJ).comp
                (awayMulCommAlgEquiv k (minorDet k d r I J hI hJ)
                  (minorDet k d r I K hI hK)).toAlgHom))))
      = AlgHom.id k (Localization.Away
          (minorDet k d r I J hI hJ * minorDet k d r I K hI hK)) := by
  have hΦ : (cocycleΘIJ k d r I J K hI hJ hK).comp
        ((awayMulCommAlgEquiv k (minorDet k d r J K hJ hK)
            (minorDet k d r J I hJ hI)).toAlgHom.comp
          ((cocycleΘIJ k d r J K I hJ hK hI).comp
            ((awayMulCommAlgEquiv k (minorDet k d r K I hK hI)
                (minorDet k d r K J hK hJ)).toAlgHom.comp
              ((cocycleΘIJ k d r K I J hK hI hJ).comp
                (awayMulCommAlgEquiv k (minorDet k d r I J hI hJ)
                  (minorDet k d r I K hI hK)).toAlgHom))))
      = (cocycleΘIK k d r I J K hI hJ hK).comp
          ((cocycleΘIJ k d r K I J hK hI hJ).comp
            (awayMulCommAlgEquiv k (minorDet k d r I J hI hJ)
              (minorDet k d r I K hI hK)).toAlgHom) := by
    rw [show (awayMulCommAlgEquiv k (minorDet k d r J K hJ hK)
          (minorDet k d r J I hJ hI)).toAlgHom.comp
          ((cocycleΘIJ k d r J K I hJ hK hI).comp
            ((awayMulCommAlgEquiv k (minorDet k d r K I hK hI)
                (minorDet k d r K J hK hJ)).toAlgHom.comp
              ((cocycleΘIJ k d r K I J hK hI hJ).comp
                (awayMulCommAlgEquiv k (minorDet k d r I J hI hJ)
                  (minorDet k d r I K hI hK)).toAlgHom)))
        = (cocycleΘJK k d r I J K hI hJ hK).comp
            ((cocycleΘIJ k d r K I J hK hI hJ).comp
              (awayMulCommAlgEquiv k (minorDet k d r I J hI hJ)
                (minorDet k d r I K hI hK)).toAlgHom) from by
        rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, rotMid],
      ← AlgHom.comp_assoc, ← cocycleCondition]
  rw [hΦ]
  exact transitionInvPair k d r I J K hI hJ hK

end AlgebraicGeometry.Grassmannian
