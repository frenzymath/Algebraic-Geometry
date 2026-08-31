/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianChart

/-!
# The Grassmannian transition cocycle over a field (DD-3, stage 3a)

The triple-overlap rings and the cocycle condition for the Grassmannian charts over the
base field `k` (`informal/spec-dd-3.md` §2/§3; route map: the GR-Quot-Closure tree's
`GrassmannianCells.lean` cocycle section, re-derived in the `→ₐ[k]` architecture).

The cocycle `θ_{I,K} = θ_{I,J} ∘ θ_{J,K}` cannot be stated on the plain transition maps
(codomain/domain mismatch); it lives over the **triple-overlap** rings obtained by
inverting both relevant minors: `S_I := R^I[1/(P^I_J P^I_K)]`, etc.

* `AlgebraicGeometry.Grassmannian.awayInclLeft`, `awayInclRight`: the inclusions
  `R[1/x] →ₐ[k] R[1/xy]`, `R[1/y] →ₐ[k] R[1/xy]`.
* `AlgebraicGeometry.Grassmannian.cocycleΘIJ/JK/IK`: the triple-overlap transitions,
  e.g. `Θ_{I,J} : S_J →ₐ[k] S_I`.
* `AlgebraicGeometry.Grassmannian.cocycle_imageMatrix_eq`: the central matrix identity —
  both transported image matrices collapse to `(Y_K)⁻¹ Y` with `Y = X^I` over `S_I`.
* `AlgebraicGeometry.Grassmannian.cocycleCondition`: **the cocycle**
  `Θ_{I,K} = Θ_{I,J} ∘ Θ_{J,K}` as `k`-algebra maps `S_K →ₐ[k] S_I` — extensionality
  runs on polynomial generators only (no integer-constants case, unlike the ℤ-model).
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Grassmannian

/-- Reduce the units hypothesis of `IsLocalization.liftAlgHom` at an away-localisation
to the single generator: if `f x` is a unit then `f` sends all powers of `x` to units. -/
lemma isUnit_algHom_powers {k R S : Type u} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) {x : R} (hx : IsUnit (f x)) :
    ∀ y : Submonoid.powers x, IsUnit (f y) := fun y => by
  obtain ⟨n, hn⟩ := y.2
  simpa [← hn, map_pow] using hx.pow n

/-- Inclusion of the away-localisation at `x` into the away-localisation at `x * y`
(inverting the extra factor `y`), as a `k`-algebra map: the structure map of the triple
overlap relative to a double localisation. -/
noncomputable def awayInclLeft (k : Type u) [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (x y : A) : Localization.Away x →ₐ[k] Localization.Away (x * y) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers x)
    (f := Algebra.algHom k A (Localization.Away (x * y)))
    (isUnit_algHom_powers _ (by
      have h : IsUnit (algebraMap A (Localization.Away (x * y)) (x * y)) :=
        IsLocalization.Away.algebraMap_isUnit _
      rw [map_mul] at h
      exact isUnit_of_mul_isUnit_left h))

/-- Inclusion of the away-localisation at `y` into the away-localisation at `x * y`
(inverting the extra factor `x`), as a `k`-algebra map. -/
noncomputable def awayInclRight (k : Type u) [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (x y : A) : Localization.Away y →ₐ[k] Localization.Away (x * y) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers y)
    (f := Algebra.algHom k A (Localization.Away (x * y)))
    (isUnit_algHom_powers _ (by
      have h : IsUnit (algebraMap A (Localization.Away (x * y)) (x * y)) :=
        IsLocalization.Away.algebraMap_isUnit _
      rw [map_mul] at h
      exact isUnit_of_mul_isUnit_right h))

/-- `awayInclLeft` is the canonical map over `A`, pointwise form. -/
lemma awayInclLeft_algebraMap_apply (k : Type u) [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (x y : A) (a : A) :
    awayInclLeft k x y (algebraMap A (Localization.Away x) a)
      = algebraMap A (Localization.Away (x * y)) a :=
  IsLocalization.lift_eq _ a

/-- `awayInclLeft` is the canonical map over `A`: it intertwines the structure maps. -/
lemma awayInclLeft_comp_algebraMap (k : Type u) [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (x y : A) :
    (awayInclLeft k x y).toRingHom.comp (algebraMap A (Localization.Away x)) =
      algebraMap A (Localization.Away (x * y)) :=
  RingHom.ext fun a => awayInclLeft_algebraMap_apply k x y a

/-- `awayInclRight` is the canonical map over `A`, pointwise form. -/
lemma awayInclRight_algebraMap_apply (k : Type u) [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (x y : A) (a : A) :
    awayInclRight k x y (algebraMap A (Localization.Away y) a)
      = algebraMap A (Localization.Away (x * y)) a :=
  IsLocalization.lift_eq _ a

/-- `awayInclRight` is the canonical map over `A`: it intertwines the structure maps. -/
lemma awayInclRight_comp_algebraMap (k : Type u) [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (x y : A) :
    (awayInclRight k x y).toRingHom.comp (algebraMap A (Localization.Away y)) =
      algebraMap A (Localization.Away (x * y)) :=
  RingHom.ext fun a => awayInclRight_algebraMap_apply k x y a

/-- The left factor of a product is a unit in the away-localisation at the product. -/
lemma isUnit_algebraMap_away_left {A : Type*} [CommRing A] (x y : A) :
    IsUnit (algebraMap A (Localization.Away (x * y)) x) := by
  have h : IsUnit (algebraMap A (Localization.Away (x * y)) (x * y)) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

/-- The right factor of a product is a unit in the away-localisation at the product. -/
lemma isUnit_algebraMap_away_right {A : Type*} [CommRing A] (x y : A) :
    IsUnit (algebraMap A (Localization.Away (x * y)) y) := by
  have h : IsUnit (algebraMap A (Localization.Away (x * y)) (x * y)) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

/-- The "cross" minor `P^B_C` is sent by `θ̃_{A,B}`, then pushed into a double
localisation `D` (in which `P^A_C` is a unit), to a unit:
`θ̃_{A,B}(P^B_C) = det((X^A_B)⁻¹) · P^A_C`, a product of two units once `P^A_C` is
inverted.  The cross-factor input to each triple-overlap transition lift. -/
lemma isUnit_incl_transitionPreMap_cross (k : Type u) [Field k] (d r : ℕ)
    (A B C : Finset (Fin r)) (hA : A.card = d) (hB : B.card = d) (hC : C.card = d)
    {D : Type*} [CommRing D] [Algebra (ChartRing k d r A) D]
    (incl : Localization.Away (minorDet k d r A B hA hB) →+* D)
    (hincl : incl.comp (algebraMap (ChartRing k d r A)
        (Localization.Away (minorDet k d r A B hA hB)))
        = algebraMap (ChartRing k d r A) D)
    (hunit : IsUnit (algebraMap (ChartRing k d r A) D (minorDet k d r A C hA hC))) :
    IsUnit (incl (transitionPreMap k d r A B hA hB (minorDet k d r B C hB hC))) := by
  have hsub : (imageMatrix k d r A B hA hB).submatrix id
        (fun j : Fin d => (C.orderIsoOfFin hC j : Fin r))
      = universalMinorInv k d r A B hA hB *
        (((universalMatrix k d r A hA).map (algebraMap _ _)).submatrix id
          (fun j : Fin d => (C.orderIsoOfFin hC j : Fin r))) := mul_submatrix_col _ _ _
  rw [transitionPreMap_minorDet, hsub, Matrix.det_mul, map_mul]
  refine IsUnit.mul ?_ ?_
  · refine IsUnit.map incl ?_
    refine IsUnit.of_mul_eq_one (universalMinor k d r A B hA hB).det ?_
    rw [← Matrix.det_mul, (universalMinorInv_mul_cancel k d r A B hA hB).1, Matrix.det_one]
  · have hdet : (((universalMatrix k d r A hA).map
            (algebraMap _ (Localization.Away (minorDet k d r A B hA hB)))).submatrix id
            (fun j : Fin d => (C.orderIsoOfFin hC j : Fin r))).det
          = algebraMap _ (Localization.Away (minorDet k d r A B hA hB))
              (minorDet k d r A C hA hC) := by
      rw [Matrix.submatrix_map]
      exact (RingHom.map_det _ _).symm
    rw [hdet]
    have hcomp : incl (algebraMap (ChartRing k d r A)
        (Localization.Away (minorDet k d r A B hA hB)) (minorDet k d r A C hA hC))
        = algebraMap (ChartRing k d r A) D (minorDet k d r A C hA hC) :=
      RingHom.congr_fun hincl _
    rw [hcomp]
    exact hunit

/-- The triple-overlap transition map `Θ_{I,J} : S_J →ₐ[k] S_I`, where
`S_J = R^J[1/(P^J_I P^J_K)]` and `S_I = R^I[1/(P^I_J P^I_K)]`: the away-localisation
lift of `θ̃_{I,J}` (post-composed into `S_I`) along the doubly-inverted minor. -/
noncomputable def cocycleΘIJ (k : Type u) [Field k] (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    Localization.Away (minorDet k d r J I hJ hI * minorDet k d r J K hJ hK) →ₐ[k]
      Localization.Away (minorDet k d r I J hI hJ * minorDet k d r I K hI hK) :=
  IsLocalization.liftAlgHom
    (M := Submonoid.powers (minorDet k d r J I hJ hI * minorDet k d r J K hJ hK))
    (f := (awayInclLeft k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).comp
            (transitionPreMap k d r I J hI hJ))
    (isUnit_algHom_powers _ (by
      rw [map_mul]
      refine IsUnit.mul ?_ ?_
      · exact (isUnit_transitionPreMap_minorDet k d r I J hI hJ).map
          (awayInclLeft k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK))
      · exact isUnit_incl_transitionPreMap_cross k d r I J K hI hJ hK
          (awayInclLeft k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).toRingHom
          (awayInclLeft_comp_algebraMap k _ _)
          (isUnit_algebraMap_away_right _ _)))

/-- The triple-overlap transition map `Θ_{J,K} : S_K →ₐ[k] S_J`. -/
noncomputable def cocycleΘJK (k : Type u) [Field k] (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    Localization.Away (minorDet k d r K I hK hI * minorDet k d r K J hK hJ) →ₐ[k]
      Localization.Away (minorDet k d r J I hJ hI * minorDet k d r J K hJ hK) :=
  IsLocalization.liftAlgHom
    (M := Submonoid.powers (minorDet k d r K I hK hI * minorDet k d r K J hK hJ))
    (f := (awayInclRight k (minorDet k d r J I hJ hI) (minorDet k d r J K hJ hK)).comp
            (transitionPreMap k d r J K hJ hK))
    (isUnit_algHom_powers _ (by
      rw [map_mul]
      refine IsUnit.mul ?_ ?_
      · exact isUnit_incl_transitionPreMap_cross k d r J K I hJ hK hI
          (awayInclRight k (minorDet k d r J I hJ hI) (minorDet k d r J K hJ hK)).toRingHom
          (awayInclRight_comp_algebraMap k _ _)
          (isUnit_algebraMap_away_left _ _)
      · exact (isUnit_transitionPreMap_minorDet k d r J K hJ hK).map
          (awayInclRight k (minorDet k d r J I hJ hI) (minorDet k d r J K hJ hK))))

/-- The triple-overlap transition map `Θ_{I,K} : S_K →ₐ[k] S_I`. -/
noncomputable def cocycleΘIK (k : Type u) [Field k] (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    Localization.Away (minorDet k d r K I hK hI * minorDet k d r K J hK hJ) →ₐ[k]
      Localization.Away (minorDet k d r I J hI hJ * minorDet k d r I K hI hK) :=
  IsLocalization.liftAlgHom
    (M := Submonoid.powers (minorDet k d r K I hK hI * minorDet k d r K J hK hJ))
    (f := (awayInclRight k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).comp
            (transitionPreMap k d r I K hI hK))
    (isUnit_algHom_powers _ (by
      rw [map_mul]
      refine IsUnit.mul ?_ ?_
      · exact (isUnit_transitionPreMap_minorDet k d r I K hI hK).map
          (awayInclRight k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK))
      · exact isUnit_incl_transitionPreMap_cross k d r I K J hI hK hJ
          (awayInclRight k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).toRingHom
          (awayInclRight_comp_algebraMap k _ _)
          (isUnit_algebraMap_away_left _ _)))

/-- `Θ_{I,J}` restricted along the structure map of `S_J` is
`ι^L ∘ θ̃_{I,J}` (ring-hom composition form, for the matrix computations). -/
theorem cocycleΘIJ_comp_algebraMap (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (cocycleΘIJ k d r I J K hI hJ hK).toRingHom.comp
        (algebraMap (ChartRing k d r J)
          (Localization.Away (minorDet k d r J I hJ hI * minorDet k d r J K hJ hK)))
      = ((awayInclLeft k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).comp
          (transitionPreMap k d r I J hI hJ)).toRingHom :=
  IsLocalization.lift_comp _

/-- `Θ_{J,K}` restricted along the structure map of `S_K` is `ι^R ∘ θ̃_{J,K}`. -/
theorem cocycleΘJK_comp_algebraMap (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (cocycleΘJK k d r I J K hI hJ hK).toRingHom.comp
        (algebraMap (ChartRing k d r K)
          (Localization.Away (minorDet k d r K I hK hI * minorDet k d r K J hK hJ)))
      = ((awayInclRight k (minorDet k d r J I hJ hI) (minorDet k d r J K hJ hK)).comp
          (transitionPreMap k d r J K hJ hK)).toRingHom :=
  IsLocalization.lift_comp _

/-- `Θ_{I,K}` restricted along the structure map of `S_K` is `ι^R ∘ θ̃_{I,K}`. -/
theorem cocycleΘIK_comp_algebraMap (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (cocycleΘIK k d r I J K hI hJ hK).toRingHom.comp
        (algebraMap (ChartRing k d r K)
          (Localization.Away (minorDet k d r K I hK hI * minorDet k d r K J hK hJ)))
      = ((awayInclRight k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).comp
          (transitionPreMap k d r I K hI hK)).toRingHom :=
  IsLocalization.lift_comp _

/-- `AlgHom`-level composition form of `cocycleΘIJ_comp_algebraMap`. -/
theorem cocycleΘIJ_comp_algHom (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (cocycleΘIJ k d r I J K hI hJ hK).comp
        (Algebra.algHom k (ChartRing k d r J)
          (Localization.Away (minorDet k d r J I hJ hI * minorDet k d r J K hJ hK)))
      = (awayInclLeft k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).comp
          (transitionPreMap k d r I J hI hJ) :=
  AlgHom.coe_ringHom_injective (cocycleΘIJ_comp_algebraMap k d r I J K hI hJ hK)

/-- `AlgHom`-level composition form of `cocycleΘJK_comp_algebraMap`. -/
theorem cocycleΘJK_comp_algHom (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (cocycleΘJK k d r I J K hI hJ hK).comp
        (Algebra.algHom k (ChartRing k d r K)
          (Localization.Away (minorDet k d r K I hK hI * minorDet k d r K J hK hJ)))
      = (awayInclRight k (minorDet k d r J I hJ hI) (minorDet k d r J K hJ hK)).comp
          (transitionPreMap k d r J K hJ hK) :=
  AlgHom.coe_ringHom_injective (cocycleΘJK_comp_algebraMap k d r I J K hI hJ hK)

/-- `AlgHom`-level composition form of `cocycleΘIK_comp_algebraMap`. -/
theorem cocycleΘIK_comp_algHom (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (cocycleΘIK k d r I J K hI hJ hK).comp
        (Algebra.algHom k (ChartRing k d r K)
          (Localization.Away (minorDet k d r K I hK hI * minorDet k d r K J hK hJ)))
      = (awayInclRight k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).comp
          (transitionPreMap k d r I K hI hK) :=
  AlgHom.coe_ringHom_injective (cocycleΘIK_comp_algebraMap k d r I J K hI hJ hK)

/-- Mapping the image matrix `M = (X^I_X)⁻¹ X^I` through any ring hom `incl` lying over
the structure map `R^I → D` yields `(Y_X)⁻¹ Y`, where `Y := X^I` base-changed to `D`.
The key reusable step in the cocycle computation. -/
lemma imageMatrix_map_eq (k : Type u) [Field k] (d r : ℕ) (I X : Finset (Fin r))
    (hI : I.card = d) (hX : X.card = d) {D : Type*} [CommRing D]
    [Algebra (ChartRing k d r I) D]
    (incl : Localization.Away (minorDet k d r I X hI hX) →+* D)
    (hincl : incl.comp (algebraMap (ChartRing k d r I)
        (Localization.Away (minorDet k d r I X hI hX)))
        = algebraMap (ChartRing k d r I) D) :
    (imageMatrix k d r I X hI hX).map incl
      = (((universalMatrix k d r I hI).map
            (algebraMap (ChartRing k d r I) D)).submatrix id
          (fun j : Fin d => (X.orderIsoOfFin hX j : Fin r)))⁻¹ *
        (universalMatrix k d r I hI).map (algebraMap (ChartRing k d r I) D) := by
  have hmm : (imageMatrix k d r I X hI hX).map incl
      = (universalMinorInv k d r I X hI hX).map incl
        * ((universalMatrix k d r I hI).map
            (algebraMap (ChartRing k d r I)
              (Localization.Away (minorDet k d r I X hI hX)))).map incl := by
    rw [imageMatrix]; exact Matrix.map_mul
  rw [hmm, map_map_eq_of_comp _ _ _ _ hincl, universalMinorInv,
    ← map_nonsing_inv incl (universalMinor k d r I X hI hX)
        (isUnit_det_universalMinor k d r I X hI hX)]
  congr 1
  rw [universalMinor, map_map_eq_of_comp _ _ _ _ hincl, ← Matrix.submatrix_map]

/-- The central matrix identity behind the cocycle condition: over the triple-overlap
ring `S_I`, the image matrix `(X^I_K)⁻¹ X^I` of `θ_{I,K}` equals `Θ_{I,J}` applied
entrywise to the image matrix `(X^J_K)⁻¹ X^J` of `θ_{J,K}`.  Both reduce to `(Y_K)⁻¹ Y`
with `Y = X^I` over `S_I`. -/
lemma cocycle_imageMatrix_eq (k : Type u) [Field k] (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (imageMatrix k d r I K hI hK).map
        (awayInclRight k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).toRingHom
      = (imageMatrix k d r J K hJ hK).map
          ((cocycleΘIJ k d r I J K hI hJ hK).toRingHom.comp
            (awayInclRight k (minorDet k d r J I hJ hI)
              (minorDet k d r J K hJ hK)).toRingHom) := by
  -- LHS = (Y_K)⁻¹ * Y, where `Y := X^I` over `S_I`.
  have hLHS := imageMatrix_map_eq k d r I K hI hK
    (awayInclRight k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).toRingHom
    (awayInclRight_comp_algebraMap k _ _)
  -- `(imageMatrix I J).map (awayInclLeft …) = (Y_J)⁻¹ Y`.
  have hMJimg := imageMatrix_map_eq k d r I J hI hJ
    (awayInclLeft k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).toRingHom
    (awayInclLeft_comp_algebraMap k _ _)
  set Y := (universalMatrix k d r I hI).map
      (algebraMap (ChartRing k d r I)
        (Localization.Away (minorDet k d r I J hI hJ * minorDet k d r I K hI hK)))
    with hY
  -- Unit fact for the `J`-minor of `Y`.
  have hYJ : IsUnit (Y.submatrix id (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r))).det := by
    have e : (Y.submatrix id (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r))).det
        = algebraMap (ChartRing k d r I)
            (Localization.Away (minorDet k d r I J hI hJ * minorDet k d r I K hI hK))
            (minorDet k d r I J hI hJ) := by
      rw [hY, Matrix.submatrix_map]
      exact (RingHom.map_det _ _).symm
    rw [e]; exact isUnit_algebraMap_away_left _ _
  -- `M^J := θ_{I,J}(X^J) = (Y_J)⁻¹ Y` over `S_I`.
  have hχ : ((cocycleΘIJ k d r I J K hI hJ hK).toRingHom.comp
        (awayInclRight k (minorDet k d r J I hJ hI)
          (minorDet k d r J K hJ hK)).toRingHom).comp
          (algebraMap (ChartRing k d r J)
            (Localization.Away (minorDet k d r J K hJ hK)))
      = (awayInclLeft k (minorDet k d r I J hI hJ)
            (minorDet k d r I K hI hK)).toRingHom.comp
          (transitionPreMap k d r I J hI hJ).toRingHom := by
    rw [RingHom.comp_assoc, awayInclRight_comp_algebraMap]
    exact cocycleΘIJ_comp_algebraMap k d r I J K hI hJ hK
  have hMJ : (universalMatrix k d r J hJ).map
        ((awayInclLeft k (minorDet k d r I J hI hJ)
            (minorDet k d r I K hI hK)).toRingHom.comp
          (transitionPreMap k d r I J hI hJ).toRingHom)
      = (Y.submatrix id (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r)))⁻¹ * Y := by
    have e1 : (universalMatrix k d r J hJ).map
          ((awayInclLeft k (minorDet k d r I J hI hJ)
              (minorDet k d r I K hI hK)).toRingHom.comp
            (transitionPreMap k d r I J hI hJ).toRingHom)
        = (imageMatrix k d r I J hI hJ).map
            (awayInclLeft k (minorDet k d r I J hI hJ)
              (minorDet k d r I K hI hK)).toRingHom := by
      rw [← map_map_eq_of_comp (universalMatrix k d r J hJ)
          (transitionPreMap k d r I J hI hJ).toRingHom
          (awayInclLeft k (minorDet k d r I J hI hJ)
            (minorDet k d r I K hI hK)).toRingHom _ rfl]
      congr 1
      exact universalMatrix_map_transitionPreMap k d r I J hI hJ
    rw [e1, hMJimg]
  -- RHS = (M^J_K)⁻¹ M^J = (Y_K)⁻¹ Y.
  have hRHS : (imageMatrix k d r J K hJ hK).map
        ((cocycleΘIJ k d r I J K hI hJ hK).toRingHom.comp
          (awayInclRight k (minorDet k d r J I hJ hI)
            (minorDet k d r J K hJ hK)).toRingHom)
      = (Y.submatrix id (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r)))⁻¹ * Y := by
    have hmm : (imageMatrix k d r J K hJ hK).map
          ((cocycleΘIJ k d r I J K hI hJ hK).toRingHom.comp
            (awayInclRight k (minorDet k d r J I hJ hI)
              (minorDet k d r J K hJ hK)).toRingHom)
        = (universalMinorInv k d r J K hJ hK).map
            ((cocycleΘIJ k d r I J K hI hJ hK).toRingHom.comp
              (awayInclRight k (minorDet k d r J I hJ hI)
                (minorDet k d r J K hJ hK)).toRingHom)
          * ((universalMatrix k d r J hJ).map
              (algebraMap (ChartRing k d r J)
                (Localization.Away (minorDet k d r J K hJ hK)))).map
                  ((cocycleΘIJ k d r I J K hI hJ hK).toRingHom.comp
                    (awayInclRight k (minorDet k d r J I hJ hI)
                      (minorDet k d r J K hJ hK)).toRingHom) := by
      rw [imageMatrix]; exact Matrix.map_mul
    rw [hmm, map_map_eq_of_comp _ _ _ _ hχ, hMJ, universalMinorInv,
      ← map_nonsing_inv _ _ (isUnit_det_universalMinor k d r J K hJ hK), universalMinor,
      map_map_eq_of_comp _ _ _ _ hχ, ← Matrix.submatrix_map, hMJ,
      mul_submatrix_col (Y.submatrix id (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r)))⁻¹ Y
        (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r)),
      Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hYJ,
      inv_mul_inv_mul_cancel _ _ _ hYJ]
  rw [hLHS, hRHS]

/-- **Cocycle condition**: over the triple overlap, the transition maps satisfy
`Θ_{I,K} = Θ_{I,J} ∘ Θ_{J,K}` as `k`-algebra maps `S_K →ₐ[k] S_I`.  Together with
`θ_{I,I} = id` (`transitionMap_self`) this is the gluing datum for the Grassmannian
charts.  In the `→ₐ[k]` architecture the extensionality runs on polynomial generators
only; the ℤ-model's integer-constants case disappears. -/
theorem cocycleCondition (k : Type u) [Field k] (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    cocycleΘIK k d r I J K hI hJ hK
      = (cocycleΘIJ k d r I J K hI hJ hK).comp (cocycleΘJK k d r I J K hI hJ hK) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (minorDet k d r K I hK hI * minorDet k d r K J hK hJ))
  apply MvPolynomial.algHom_ext
  intro e
  change cocycleΘIK k d r I J K hI hJ hK
      (algebraMap (ChartRing k d r K)
        (Localization.Away (minorDet k d r K I hK hI * minorDet k d r K J hK hJ))
        (MvPolynomial.X e))
    = cocycleΘIJ k d r I J K hI hJ hK (cocycleΘJK k d r I J K hI hJ hK
        (algebraMap (ChartRing k d r K)
          (Localization.Away (minorDet k d r K I hK hI * minorDet k d r K J hK hJ))
          (MvPolynomial.X e)))
  have hIKe : cocycleΘIK k d r I J K hI hJ hK
      (algebraMap (ChartRing k d r K)
        (Localization.Away (minorDet k d r K I hK hI * minorDet k d r K J hK hJ))
        (MvPolynomial.X e))
      = awayInclRight k (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)
          (transitionPreMap k d r I K hI hK (MvPolynomial.X e)) :=
    RingHom.congr_fun (cocycleΘIK_comp_algebraMap k d r I J K hI hJ hK) (MvPolynomial.X e)
  have hJKe : cocycleΘJK k d r I J K hI hJ hK
      (algebraMap (ChartRing k d r K)
        (Localization.Away (minorDet k d r K I hK hI * minorDet k d r K J hK hJ))
        (MvPolynomial.X e))
      = awayInclRight k (minorDet k d r J I hJ hI) (minorDet k d r J K hJ hK)
          (transitionPreMap k d r J K hJ hK (MvPolynomial.X e)) :=
    RingHom.congr_fun (cocycleΘJK_comp_algebraMap k d r I J K hI hJ hK) (MvPolynomial.X e)
  rw [hIKe, hJKe]
  have h := congrFun (congrFun (cocycle_imageMatrix_eq k d r I J K hI hJ hK) e.1) e.2.1
  simpa [Matrix.map_apply, transitionPreMap, MvPolynomial.aeval_X,
    RingHom.comp_apply] using h

end AlgebraicGeometry.Grassmannian
