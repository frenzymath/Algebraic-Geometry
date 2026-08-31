/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Grassmannian affine charts over a field (DD-3, stage 3a)

The affine charts of the Grassmannian `Gr(d, r)` over an arbitrary base field `k`, with
the universal matrix, minor determinants, Cramer transitions, and the pre-localisation
transition homs — the chart-ring layer of the DD-3 Grassmannian port
(`informal/spec-dd-3.md` §2/§3; route map: the GR-Quot-Closure tree's
`GrassmannianCells.lean`, re-derived over `k` in the `→ₐ[k]` architecture so that every
extensionality argument runs on generators only, with no integer-constants case).

For `I ⊆ Fin r` with `#I = d`, the chart `U^I` is `Spec k[x^I_{p,q}]_{q ∉ I}`, the
spectrum of the polynomial ring on the `d(r-d)` free entries of the universal `d × r`
matrix `X^I` whose `I`-minor is the identity.  The transition `θ_{I,J}` is the Cramer
computation `X^J ↦ (X^I_J)⁻¹ X^I` over the localised chart ring `R^I_J = R^I[1/P^I_J]`.

* `AlgebraicGeometry.Grassmannian.ChartRing`, `affineChart`: the chart ring `R^I` and
  its spectrum `U^I`.
* `AlgebraicGeometry.Grassmannian.universalMatrix`, `minorDet`, `universalMinor`,
  `universalMinorInv`, `imageMatrix`: the universal matrix `X^I`, the minors `P^I_J`,
  the Cramer inverse, and the image matrix `M = (X^I_J)⁻¹ X^I`.
* `AlgebraicGeometry.Grassmannian.transitionPreMap`: `θ̃_{I,J} : R^J →ₐ[k] R^I_J`.
* `AlgebraicGeometry.Grassmannian.transitionMap`: the localised transition
  `θ_{I,J} : R^J[1/P^J_I] →ₐ[k] R^I[1/P^I_J]`, with `transitionMap_self : θ_{I,I} = id`.
* Minor bookkeeping for the cocycle/diagonal/frame lanes: `transitionPreMap_minorDet`,
  `transitionPreMap_minorDet_swap_mul`, `transitionPreMap_minorDet_mul`, `minorDet_self`.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Grassmannian

/-- The **chart ring** `R^I = k[x^I_{p,q}]` of the Grassmannian chart `U^I` over the
base field `k`: the polynomial ring on the `d(r-d)` free entries of the universal
matrix, indexed by `Fin d × {q : Fin r // q ∉ I}`. -/
abbrev ChartRing (k : Type u) [Field k] (d r : ℕ) (I : Finset (Fin r)) : Type u :=
  MvPolynomial (Fin d × {q : Fin r // q ∉ I}) k

/-- The **affine chart** `U^I = Spec R^I` of the Grassmannian `Gr(d, r)` over `k`,
indexed by a `d`-element subset `I : Finset (Fin r)`; non-canonically `≅ 𝔸^{d(r-d)}_k`.
The Grassmannian scheme is glued from the `Nat.choose r d` charts `U^I` along the
Cramer transition isomorphisms. -/
noncomputable def affineChart (k : Type u) [Field k] (d r : ℕ) (I : Finset (Fin r)) :
    Scheme :=
  Spec (CommRingCat.of (ChartRing k d r I))

/-- The **universal matrix** `X^I`: the `d × r` matrix over the chart ring `R^I` whose
`I`-minor is the `d × d` identity (read through the order iso `Fin d ≃o ↥I`) and whose
remaining `d(r-d)` entries are the free indeterminates `x^I_{p,q}` (`q ∉ I`). -/
noncomputable def universalMatrix (k : Type u) [Field k] (d r : ℕ) (I : Finset (Fin r))
    (hI : I.card = d) : Matrix (Fin d) (Fin r) (ChartRing k d r I) :=
  fun p q =>
    if h : q ∈ I then (if (I.orderIsoOfFin hI p : Fin r) = q then 1 else 0)
    else MvPolynomial.X (p, ⟨q, h⟩)

/-- The **minor determinant** `P^I_J = det(X^I_J)`: the determinant of the `d × d`
submatrix of `universalMatrix` on the columns indexed by `J`, reindexed to `Fin d` via
the order iso.  Defines the principal open `U^I_J = Spec R^I[1/P^I_J]`. -/
noncomputable def minorDet (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) : ChartRing k d r I :=
  ((universalMatrix k d r I hI).submatrix id
    (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r))).det

/-- The **localised `J`-minor** `X^I_J` over `R^I_J`: the `J`-minor of `universalMatrix`
with entries pushed along `R^I → R^I_J = Localization.Away P^I_J`. -/
noncomputable def universalMinor (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) :
    Matrix (Fin d) (Fin d) (Localization.Away (minorDet k d r I J hI hJ)) :=
  ((universalMatrix k d r I hI).submatrix id
    (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r))).map (algebraMap _ _)

/-- The localised minor determinant is a unit: `det(X^I_J)` is the image of `P^I_J`
under the away-localisation structure map, hence a unit. -/
theorem isUnit_det_universalMinor (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) : IsUnit (universalMinor k d r I J hI hJ).det := by
  have h : (universalMinor k d r I J hI hJ).det
      = (algebraMap _ (Localization.Away (minorDet k d r I J hI hJ)))
          (minorDet k d r I J hI hJ) :=
    (RingHom.map_det _ _).symm
  rw [h]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The **Cramer inverse** `(X^I_J)⁻¹`: the nonsingular inverse of the localised
`J`-minor; its entries lie in `R^I_J` by Cramer's rule. -/
noncomputable def universalMinorInv (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    Matrix (Fin d) (Fin d) (Localization.Away (minorDet k d r I J hI hJ)) :=
  (universalMinor k d r I J hI hJ)⁻¹

/-- The Cramer inverse is a two-sided inverse: since `det(X^I_J)` is a unit,
`(X^I_J)⁻¹` is a genuine left and right inverse. -/
theorem universalMinorInv_mul_cancel (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    universalMinorInv k d r I J hI hJ * universalMinor k d r I J hI hJ = 1 ∧
    universalMinor k d r I J hI hJ * universalMinorInv k d r I J hI hJ = 1 :=
  ⟨Matrix.nonsing_inv_mul _ (isUnit_det_universalMinor k d r I J hI hJ),
   Matrix.mul_nonsing_inv _ (isUnit_det_universalMinor k d r I J hI hJ)⟩

/-- The **image matrix** `M = (X^I_J)⁻¹ X^I`: the product of the Cramer inverse with the
universal matrix base-changed to `R^I_J`.  Its entries are the images of the
indeterminates `x^J_{p,q}` under the transition `θ_{I,J}`. -/
noncomputable def imageMatrix (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) :
    Matrix (Fin d) (Fin r) (Localization.Away (minorDet k d r I J hI hJ)) :=
  universalMinorInv k d r I J hI hJ * (universalMatrix k d r I hI).map (algebraMap _ _)

/-- The **pre-localisation transition hom** `θ̃_{I,J} : R^J →ₐ[k] R^I_J`: the `k`-algebra
map out of the chart ring of `J` sending each free indeterminate `x^J_{p,q}` to the
`(p,q)`-entry of the image matrix `M = (X^I_J)⁻¹ X^I`. -/
noncomputable def transitionPreMap (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) :
    ChartRing k d r J →ₐ[k] Localization.Away (minorDet k d r I J hI hJ) :=
  MvPolynomial.aeval (fun e => imageMatrix k d r I J hI hJ e.1 e.2.1)

/-- The `I`-minor of the universal matrix `X^I` is the `d × d` identity (`P^I_I = 1`
underlies `transitionMap_self`): the `I`-columns of `X^I` read through the order iso
form the identity block. -/
theorem universalMatrix_submatrix_self (k : Type u) [Field k] (d r : ℕ)
    (I : Finset (Fin r)) (hI : I.card = d) :
    (universalMatrix k d r I hI).submatrix id
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) = 1 := by
  ext p p'
  simp only [Matrix.submatrix_apply, id_eq, universalMatrix]
  rw [dif_pos (I.orderIsoOfFin hI p').2, Matrix.one_apply]
  have hiff : ((I.orderIsoOfFin hI p : Fin r) = (I.orderIsoOfFin hI p')) ↔ (p = p') := by
    rw [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : p = p'
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (hiff.not.mpr h), if_neg h]

/-- Submatrix on the columns of a right matrix factor commutes with the product (rows
reindexed by `id`).  Shared helper: avoids a matrix-multiplication instance-keying issue
that blocks the generic `rw` of Mathlib's submatrix-mul lemmas. -/
lemma mul_submatrix_col {d r : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin d) (Fin d) R) (B : Matrix (Fin d) (Fin r) R) (g : Fin d → Fin r) :
    (A * B).submatrix id g = A * B.submatrix id g := by
  ext i j; simp [Matrix.mul_apply, Matrix.submatrix_apply]

/-- A ring homomorphism carries the nonsingular (Cramer) inverse to the nonsingular
inverse, provided the determinant is a unit.  Shared helper. -/
lemma map_nonsing_inv {n : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (h : IsUnit A.det) :
    (A.map f)⁻¹ = A⁻¹.map f := by
  have hmul : (A.map f) * (A⁻¹.map f) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A h, Matrix.map_one f (map_zero f) (map_one f)]
  exact Matrix.inv_eq_right_inv hmul

/-- Mapping a base-changed matrix through a further ring hom collapses to a single base
change when the homs compose correctly.  Shared helper. -/
lemma map_map_eq_of_comp {m n : ℕ} {R A D : Type*} [CommRing R] [CommRing A] [CommRing D]
    (M : Matrix (Fin m) (Fin n) R) (f : R →+* A) (g : A →+* D) (h : R →+* D)
    (hcomp : g.comp f = h) : (M.map f).map g = M.map h := by
  rw [Matrix.map_map, ← RingHom.coe_comp, hcomp]

/-- Matrix cancellation `(B⁻¹ A)(A⁻¹ M) = B⁻¹ M` when `A` is invertible.  Shared helper
for the final step of the cocycle. -/
lemma inv_mul_inv_mul_cancel {d e : ℕ} {R : Type*} [CommRing R]
    (A B : Matrix (Fin d) (Fin d) R) (M : Matrix (Fin d) (Fin e) R) (hA : IsUnit A.det) :
    (B⁻¹ * A) * (A⁻¹ * M) = B⁻¹ * M := by
  rw [Matrix.mul_assoc B⁻¹ A (A⁻¹ * M), ← Matrix.mul_assoc A A⁻¹ M,
    Matrix.mul_nonsing_inv A hA, Matrix.one_mul]

/-- The `J`-minor of the image matrix `M = (X^I_J)⁻¹ X^I` is the identity:
`M_J = (X^I_J)⁻¹ X^I_J = 1`. -/
theorem imageMatrix_submatrix_self (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) :
    (imageMatrix k d r I J hI hJ).submatrix id
      (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r)) = 1 := by
  have h1 : (imageMatrix k d r I J hI hJ).submatrix id
        (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r))
      = universalMinorInv k d r I J hI hJ *
        (((universalMatrix k d r I hI).map (algebraMap _ _)).submatrix id
          (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r))) := mul_submatrix_col _ _ _
  rw [h1, Matrix.submatrix_map]
  exact (universalMinorInv_mul_cancel k d r I J hI hJ).1

/-- The `I`-minor of the image matrix `M = (X^I_J)⁻¹ X^I` is the Cramer inverse:
`M_I = (X^I_J)⁻¹ X^I_I = (X^I_J)⁻¹`. -/
theorem imageMatrix_submatrix_I (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) :
    (imageMatrix k d r I J hI hJ).submatrix id
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))
      = universalMinorInv k d r I J hI hJ := by
  have h1 : (imageMatrix k d r I J hI hJ).submatrix id
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))
      = universalMinorInv k d r I J hI hJ *
        (((universalMatrix k d r I hI).map (algebraMap _ _)).submatrix id
          (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) := mul_submatrix_col _ _ _
  rw [h1, Matrix.submatrix_map, universalMatrix_submatrix_self,
    Matrix.map_one _ (map_zero _) (map_one _), mul_one]

/-- The pre-localisation hom realises the matrix formula `θ̃_{I,J}(X^J) = (X^I_J)⁻¹ X^I`:
applying `θ̃_{I,J}` entrywise to the universal matrix `X^J` yields the image matrix. -/
theorem universalMatrix_map_transitionPreMap (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    (universalMatrix k d r J hJ).map (transitionPreMap k d r I J hI hJ)
      = imageMatrix k d r I J hI hJ := by
  ext p q
  simp only [Matrix.map_apply, universalMatrix]
  by_cases hq : q ∈ J
  · rw [dif_pos hq]
    set c := (J.orderIsoOfFin hJ).symm ⟨q, hq⟩ with hc
    have hqc : (J.orderIsoOfFin hJ c : Fin r) = q := by simp [hc]
    have himg : imageMatrix k d r I J hI hJ p q = (1 : Matrix (Fin d) (Fin d) _) p c := by
      have e := congrFun (congrFun (imageMatrix_submatrix_self k d r I J hI hJ) p) c
      rw [Matrix.submatrix_apply, id_eq] at e
      rw [← hqc]; exact e
    rw [himg, Matrix.one_apply, apply_ite (transitionPreMap k d r I J hI hJ), map_one,
      map_zero]
    have hcond : ((J.orderIsoOfFin hJ p : Fin r) = q) ↔ (p = c) := by
      conv_lhs => rw [← hqc]
      rw [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq]
    by_cases hpc : p = c
    · rw [if_pos (hcond.mpr hpc), if_pos hpc]
    · rw [if_neg (hcond.not.mpr hpc), if_neg hpc]
  · rw [dif_neg hq, transitionPreMap, MvPolynomial.aeval_X]

/-- The pre-hom sends `P^J_I` to a unit: `θ̃_{I,J}(P^J_I) = det((X^I_J)⁻¹) = 1/P^I_J`, a
unit of `R^I_J`.  This lets `θ̃_{I,J}` extend along the away-localisation at `P^J_I`. -/
theorem isUnit_transitionPreMap_minorDet (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    IsUnit (transitionPreMap k d r I J hI hJ (minorDet k d r J I hJ hI)) := by
  have e1 : transitionPreMap k d r I J hI hJ (minorDet k d r J I hJ hI)
      = (((universalMatrix k d r J hJ).submatrix id
          (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))).map
            (transitionPreMap k d r I J hI hJ)).det :=
    RingHom.map_det (transitionPreMap k d r I J hI hJ).toRingHom _
  rw [e1, ← Matrix.submatrix_map, universalMatrix_map_transitionPreMap,
    imageMatrix_submatrix_I]
  have hmul : (universalMinorInv k d r I J hI hJ).det
      * (universalMinor k d r I J hI hJ).det = 1 := by
    rw [← Matrix.det_mul, (universalMinorInv_mul_cancel k d r I J hI hJ).1, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ hmul

/-- The **transition map** `θ_{I,J} : R^J[1/P^J_I] →ₐ[k] R^I[1/P^I_J]`: the
away-localisation lift of the pre-hom `θ̃_{I,J}` along `P^J_I`, available because
`θ̃_{I,J}(P^J_I)` is a unit.  It is the comorphism of the chart-overlap isomorphism
`U^I_J → U^J_I`, carried as a `k`-algebra map so every extensionality argument below
runs on polynomial generators only. -/
noncomputable def transitionMap (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) :
    Localization.Away (minorDet k d r J I hJ hI) →ₐ[k]
      Localization.Away (minorDet k d r I J hI hJ) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (minorDet k d r J I hJ hI))
    (f := transitionPreMap k d r I J hI hJ)
    (fun y => by
      obtain ⟨n, hn⟩ := y.2
      simpa [← hn, map_pow] using (isUnit_transitionPreMap_minorDet k d r I J hI hJ).pow n)

/-- The transition map restricted along the away-localisation structure map is the
pre-localisation hom: `θ_{I,J}(a/1) = θ̃_{I,J}(a)`. -/
theorem transitionMap_algebraMap_apply (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (a : ChartRing k d r J) :
    transitionMap k d r I J hI hJ
        (algebraMap (ChartRing k d r J) (Localization.Away (minorDet k d r J I hJ hI)) a)
      = transitionPreMap k d r I J hI hJ a :=
  IsLocalization.lift_eq _ a

/-- Composition form of `transitionMap_algebraMap_apply`, at the ring-hom level:
`θ_{I,J} ∘ (R^J → R^J[1/P^J_I]) = θ̃_{I,J}`. -/
theorem transitionMap_comp_algebraMap (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    (transitionMap k d r I J hI hJ).toRingHom.comp
        (algebraMap (ChartRing k d r J) (Localization.Away (minorDet k d r J I hJ hI)))
      = (transitionPreMap k d r I J hI hJ).toRingHom :=
  RingHom.ext fun a => transitionMap_algebraMap_apply k d r I J hI hJ a

/-- `AlgHom`-level composition form: `θ_{I,J} ∘ (R^J →ₐ[k] R^J[1/P^J_I]) = θ̃_{I,J}`. -/
theorem transitionMap_comp_algHom (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    (transitionMap k d r I J hI hJ).comp
        (Algebra.algHom k (ChartRing k d r J)
          (Localization.Away (minorDet k d r J I hJ hI)))
      = transitionPreMap k d r I J hI hJ :=
  AlgHom.coe_ringHom_injective (transitionMap_comp_algebraMap k d r I J hI hJ)

/-- `θ_{I,I}` is the identity: since `P^I_I = 1` the minor `X^I_I = 1` is its own Cramer
inverse, so the pre-hom is the structure map and its away-localisation lift is the
identity.  The `k`-algebra architecture reduces this to the polynomial generators. -/
theorem transitionMap_self (k : Type u) [Field k] (d r : ℕ) (I : Finset (Fin r))
    (hI : I.card = d) :
    transitionMap k d r I I hI hI
      = AlgHom.id k (Localization.Away (minorDet k d r I I hI hI)) := by
  have hmin1 : universalMinor k d r I I hI hI = 1 := by
    simp only [universalMinor, universalMatrix_submatrix_self]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hinv1 : universalMinorInv k d r I I hI hI = 1 := by
    simp only [universalMinorInv, hmin1]
    exact inv_one
  have himg : imageMatrix k d r I I hI hI
      = (universalMatrix k d r I hI).map (algebraMap _ _) := by
    rw [imageMatrix, hinv1]
    exact Matrix.one_mul _
  apply IsLocalization.algHom_ext (Submonoid.powers (minorDet k d r I I hI hI))
  apply MvPolynomial.algHom_ext
  intro e
  change transitionMap k d r I I hI hI
      (algebraMap (ChartRing k d r I)
        (Localization.Away (minorDet k d r I I hI hI)) (MvPolynomial.X e))
    = algebraMap (ChartRing k d r I)
        (Localization.Away (minorDet k d r I I hI hI)) (MvPolynomial.X e)
  rw [transitionMap_algebraMap_apply, transitionPreMap, MvPolynomial.aeval_X, himg,
    Matrix.map_apply,
    show universalMatrix k d r I hI e.1 e.2.1 = MvPolynomial.X e from by
      rw [universalMatrix, dif_neg e.2.2]]

/-- `P^I_I = 1`: the `I`-minor determinant of the universal matrix is the unit `1`. -/
theorem minorDet_self (k : Type u) [Field k] (d r : ℕ) (I : Finset (Fin r))
    (hI : I.card = d) : minorDet k d r I I hI hI = 1 := by
  rw [minorDet, universalMatrix_submatrix_self, Matrix.det_one]

/-- The image of a general minor determinant `P^B_C` under the pre-localisation hom
`θ̃_{A,B}` is the determinant of the `C`-minor of the image matrix `M = (X^A_B)⁻¹ X^A`. -/
theorem transitionPreMap_minorDet (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    transitionPreMap k d r I J hI hJ (minorDet k d r J K hJ hK)
      = ((imageMatrix k d r I J hI hJ).submatrix id
          (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r))).det := by
  have e1 : transitionPreMap k d r I J hI hJ (minorDet k d r J K hJ hK)
      = (((universalMatrix k d r J hJ).submatrix id
          (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r))).map
            (transitionPreMap k d r I J hI hJ)).det :=
    RingHom.map_det (transitionPreMap k d r I J hI hJ).toRingHom _
  rw [e1, ← Matrix.submatrix_map, universalMatrix_map_transitionPreMap]

/-- The pre-hom sends `P^J_I` to the multiplicative inverse of (the image of) `P^I_J`:
`θ̃_{I,J}(P^J_I) · P^I_J = 1` in `R^I_J`.  Refines `isUnit_transitionPreMap_minorDet` to
the explicit two-sided inverse; realises `1/P^I_J` in the image of the diagonal ring map
of the separatedness argument. -/
theorem transitionPreMap_minorDet_swap_mul (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    transitionPreMap k d r I J hI hJ (minorDet k d r J I hJ hI) *
        algebraMap (ChartRing k d r I)
          (Localization.Away (minorDet k d r I J hI hJ)) (minorDet k d r I J hI hJ) = 1 := by
  have e1 : transitionPreMap k d r I J hI hJ (minorDet k d r J I hJ hI)
      = (((universalMatrix k d r J hJ).submatrix id
          (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))).map
            (transitionPreMap k d r I J hI hJ)).det :=
    RingHom.map_det (transitionPreMap k d r I J hI hJ).toRingHom _
  rw [e1, ← Matrix.submatrix_map, universalMatrix_map_transitionPreMap,
    imageMatrix_submatrix_I]
  have hu : (universalMinor k d r I J hI hJ).det
      = algebraMap (ChartRing k d r I)
          (Localization.Away (minorDet k d r I J hI hJ)) (minorDet k d r I J hI hJ) :=
    (RingHom.map_det _ _).symm
  rw [← hu, ← Matrix.det_mul, (universalMinorInv_mul_cancel k d r I J hI hJ).1,
    Matrix.det_one]

/-- **The minor-ratio identity** `θ̃_{I,J}(P^J_K) · P^I_J = P^I_K` over `R^I_J`
(generalises `transitionPreMap_minorDet_swap_mul`, the `K = I` case where `P^I_I = 1`):
the pre-localisation hom sends the `K`-minor of `X^J` to `P^I_K / P^I_J`.  This is the
algebraic core of the frame-locus classification (stage 3c-ii). -/
theorem transitionPreMap_minorDet_mul (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    transitionPreMap k d r I J hI hJ (minorDet k d r J K hJ hK) *
        algebraMap (ChartRing k d r I)
          (Localization.Away (minorDet k d r I J hI hJ)) (minorDet k d r I J hI hJ)
      = algebraMap (ChartRing k d r I)
          (Localization.Away (minorDet k d r I J hI hJ)) (minorDet k d r I K hI hK) := by
  rw [transitionPreMap_minorDet]
  have hsub : (imageMatrix k d r I J hI hJ).submatrix id
        (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r))
      = universalMinorInv k d r I J hI hJ *
        (((universalMatrix k d r I hI).map (algebraMap _ _)).submatrix id
          (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r))) := mul_submatrix_col _ _ _
  rw [hsub, Matrix.det_mul]
  have hdet : (((universalMatrix k d r I hI).map
          (algebraMap _ (Localization.Away (minorDet k d r I J hI hJ)))).submatrix id
          (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r))).det
        = algebraMap _ (Localization.Away (minorDet k d r I J hI hJ))
            (minorDet k d r I K hI hK) := by
    rw [Matrix.submatrix_map]; exact (RingHom.map_det _ _).symm
  rw [hdet]
  have hu : (universalMinor k d r I J hI hJ).det
      = algebraMap _ (Localization.Away (minorDet k d r I J hI hJ))
          (minorDet k d r I J hI hJ) :=
    (RingHom.map_det _ _).symm
  have hone : (universalMinorInv k d r I J hI hJ).det *
      algebraMap _ (Localization.Away (minorDet k d r I J hI hJ))
        (minorDet k d r I J hI hJ) = 1 := by
    rw [← hu, ← Matrix.det_mul, (universalMinorInv_mul_cancel k d r I J hI hJ).1,
      Matrix.det_one]
  rw [mul_assoc, mul_comm _ (algebraMap _ _ (minorDet k d r I J hI hJ)), ← mul_assoc,
    hone, one_mul]

end AlgebraicGeometry.Grassmannian
