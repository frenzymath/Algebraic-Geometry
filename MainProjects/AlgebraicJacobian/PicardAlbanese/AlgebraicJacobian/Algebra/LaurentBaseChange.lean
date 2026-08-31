/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Base change for polynomial and Laurent polynomial rings

For a commutative ring `k` and a `k`-algebra `A` we record the canonical algebra
equivalences

* `polyBaseChange`   : `k[X] ⊗[k] A ≃ₐ[k] A[X]`,
* `laurentBaseChange`: `k[T;T⁻¹] ⊗[k] A ≃ₐ[k] A[T;T⁻¹]`,

and compute their effect on the tensors `x ⊗ₜ 1`.  On such elements each equivalence
is the coefficient-change ring homomorphism induced by `algebraMap k A`: for
polynomials this is `Polynomial.map (algebraMap k A)`, and for Laurent polynomials it
is `AddMonoidAlgebra.mapRingHom (algebraMap k A)` (there is no dedicated
`LaurentPolynomial.map` in mathlib).

The final two lemmas are the payload consumed by the scheme-level `ℙ¹` bridge: the two
`ℙ¹` chart maps `Polynomial.toLaurent` (`X ↦ T 1`) and
`Polynomial.eval₂RingHom C (T (-1))` (`X ↦ T (-1)`) intertwine base change with the
polynomial coefficient map.  These are pure commutative algebra.
-/

set_option autoImplicit false

universe u

open Polynomial LaurentPolynomial TensorProduct

namespace AlgebraicGeometry

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]

/-- Base change for the polynomial ring: `k[X] ⊗[k] A ≃ₐ[k] A[X]`. -/
noncomputable def polyBaseChange (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] :
    (Polynomial k) ⊗[k] A ≃ₐ[k] Polynomial A :=
  (Algebra.TensorProduct.comm k (Polynomial k) A).trans (polyEquivTensor k A).symm

/-- Base change for the Laurent polynomial ring: `k[T;T⁻¹] ⊗[k] A ≃ₐ[k] A[T;T⁻¹]`. -/
noncomputable def laurentBaseChange (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] :
    (LaurentPolynomial k) ⊗[k] A ≃ₐ[k] LaurentPolynomial A :=
  (Algebra.TensorProduct.comm k (LaurentPolynomial k) A).trans
    (((AddMonoidAlgebra.tensorEquiv (M := ℤ) k A k).restrictScalars k).trans
      (AddMonoidAlgebra.mapAlgEquiv k ℤ (Algebra.TensorProduct.rid k k A)))

/-- The final coefficient-change equivalence sends a `single` to a `single`. -/
private lemma mapAlgEquiv_single (n : ℤ) (x : A ⊗[k] k) :
    (AddMonoidAlgebra.mapAlgEquiv k ℤ (Algebra.TensorProduct.rid k k A))
        (AddMonoidAlgebra.single n x)
      = AddMonoidAlgebra.single n (Algebra.TensorProduct.rid k k A x) := by
  rw [AddMonoidAlgebra.mapAlgEquiv_apply]; exact AddMonoidAlgebra.mapAlgHom_single _ _ _

/-- `laurentBaseChange` on a monomial tensor `single n c ⊗ₜ 1`. -/
private lemma lbc_single (n : ℤ) (c : k) :
    laurentBaseChange k A (AddMonoidAlgebra.single n c ⊗ₜ 1)
      = AddMonoidAlgebra.single n (algebraMap k A c) := by
  simp only [laurentBaseChange, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    AlgEquiv.restrictScalars_apply, AddMonoidAlgebra.tensorEquiv_tmul,
    map_one, one_mul, AddMonoidAlgebra.mapAlgHom_single, mapAlgEquiv_single,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.rid_tmul,
    Algebra.smul_def, mul_one]

/-- On `x ⊗ₜ 1`, Laurent base change is the coefficient-change ring homomorphism induced
by `algebraMap k A`. -/
theorem laurentBaseChange_tmul_one (x : LaurentPolynomial k) :
    laurentBaseChange k A (x ⊗ₜ[k] 1)
      = AddMonoidAlgebra.mapRingHom (M := ℤ) (algebraMap k A) x := by
  have h : ((laurentBaseChange k A).toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom))
      = (AddMonoidAlgebra.mapRingHom (M := ℤ) (algebraMap k A)) := by
    apply AddMonoidAlgebra.ringHom_ext ?_ ?_
    · intro r
      rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
      change laurentBaseChange k A (AddMonoidAlgebra.single 0 r ⊗ₜ 1) = _
      rw [lbc_single, AddMonoidAlgebra.mapRingHom_single]
    · intro m
      rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
      change laurentBaseChange k A (AddMonoidAlgebra.single m 1 ⊗ₜ 1) = _
      rw [lbc_single, AddMonoidAlgebra.mapRingHom_single, map_one]
  exact DFunLike.congr_fun h x

/-- Laurent base change fixes the constant `C c ⊗ₜ 1 ↦ C (algebraMap k A c)`. -/
theorem laurentBaseChange_C (c : k) :
    laurentBaseChange k A (LaurentPolynomial.C c ⊗ₜ 1)
      = LaurentPolynomial.C (algebraMap k A c) := by
  rw [← LaurentPolynomial.single_eq_C, lbc_single, LaurentPolynomial.single_eq_C]

/-- Laurent base change fixes the generator `T n ⊗ₜ 1 ↦ T n`. -/
theorem laurentBaseChange_T (n : ℤ) :
    laurentBaseChange k A (LaurentPolynomial.T n ⊗ₜ 1) = LaurentPolynomial.T n := by
  rw [LaurentPolynomial.T, lbc_single, map_one, LaurentPolynomial.T]

/-- `polyBaseChange` fixes the constant `C c ⊗ₜ 1 ↦ C (algebraMap k A c)`. -/
theorem polyBaseChange_C (c : k) :
    polyBaseChange k A (Polynomial.C c ⊗ₜ 1) = Polynomial.C (algebraMap k A c) := by
  simp only [polyBaseChange, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    polyEquivTensor_symm_apply_tmul, Polynomial.sum_C_index, one_mul, map_zero,
    Polynomial.monomial_zero_left]

/-- `polyBaseChange` fixes the generator `X ⊗ₜ 1 ↦ X`. -/
theorem polyBaseChange_X : polyBaseChange k A (Polynomial.X ⊗ₜ 1) = Polynomial.X := by
  simp only [polyBaseChange, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    polyEquivTensor_symm_apply_tmul]
  simp [Polynomial.X, Polynomial.sum_monomial_index]

/-- On `p ⊗ₜ 1`, polynomial base change is `Polynomial.map (algebraMap k A)`. -/
theorem polyBaseChange_tmul_one (p : Polynomial k) :
    polyBaseChange k A (p ⊗ₜ[k] 1) = Polynomial.map (algebraMap k A) p := by
  have h : ((polyBaseChange k A).toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom))
      = (Polynomial.mapRingHom (algebraMap k A)) := by
    apply Polynomial.ringHom_ext ?_ ?_
    · intro c
      rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
      change polyBaseChange k A (Polynomial.C c ⊗ₜ 1) = _
      rw [polyBaseChange_C, Polynomial.coe_mapRingHom, Polynomial.map_C]
    · rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
      change polyBaseChange k A (Polynomial.X ⊗ₜ 1) = _
      rw [polyBaseChange_X, Polynomial.coe_mapRingHom, Polynomial.map_X]
  exact DFunLike.congr_fun h p

/-- Naturality of the left chart map `Polynomial.toLaurent` under coefficient change. -/
theorem mapRingHom_toLaurent (p : Polynomial k) :
    AddMonoidAlgebra.mapRingHom (M := ℤ) (algebraMap k A) (Polynomial.toLaurent p)
      = Polynomial.toLaurent (Polynomial.map (algebraMap k A) p) := by
  have h : (AddMonoidAlgebra.mapRingHom (M := ℤ) (algebraMap k A)).comp
      (Polynomial.toLaurent (R := k))
      = (Polynomial.toLaurent (R := A)).comp (Polynomial.mapRingHom (algebraMap k A)) := by
    apply Polynomial.ringHom_ext ?_ ?_
    · intro c
      simp only [RingHom.comp_apply, Polynomial.toLaurent_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C, ← LaurentPolynomial.single_eq_C,
        AddMonoidAlgebra.mapRingHom_single]
    · simp only [RingHom.comp_apply, Polynomial.toLaurent_X, Polynomial.coe_mapRingHom,
        Polynomial.map_X, LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]
  exact DFunLike.congr_fun h p

/-- Naturality of the right chart map `eval₂RingHom C (T (-1))` under coefficient change. -/
theorem mapRingHom_rightChart (p : Polynomial k) :
    AddMonoidAlgebra.mapRingHom (M := ℤ) (algebraMap k A)
        (Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) p)
      = Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))
          (Polynomial.map (algebraMap k A) p) := by
  have h : (AddMonoidAlgebra.mapRingHom (M := ℤ) (algebraMap k A)).comp
      (Polynomial.eval₂RingHom (LaurentPolynomial.C (R := k)) (LaurentPolynomial.T (-1)))
      = (Polynomial.eval₂RingHom (LaurentPolynomial.C (R := A)) (LaurentPolynomial.T (-1))).comp
          (Polynomial.mapRingHom (algebraMap k A)) := by
    apply Polynomial.ringHom_ext ?_ ?_
    · intro c
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, ← LaurentPolynomial.single_eq_C,
        AddMonoidAlgebra.mapRingHom_single]
    · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_mapRingHom, Polynomial.map_X, LaurentPolynomial.T,
        AddMonoidAlgebra.mapRingHom_single, map_one]
  exact DFunLike.congr_fun h p

/-- Left chart intertwining: base change commutes with `Polynomial.toLaurent`. -/
theorem laurentBaseChange_toLaurent (p : Polynomial k) :
    laurentBaseChange k A (Polynomial.toLaurent p ⊗ₜ[k] 1)
      = Polynomial.toLaurent (Polynomial.map (algebraMap k A) p) := by
  rw [laurentBaseChange_tmul_one, mapRingHom_toLaurent]

/-- Right chart intertwining: base change commutes with `eval₂RingHom C (T (-1))`. -/
theorem laurentBaseChange_rightChart (p : Polynomial k) :
    laurentBaseChange k A
        (Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) p ⊗ₜ[k] 1)
      = Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))
          (Polynomial.map (algebraMap k A) p) := by
  rw [laurentBaseChange_tmul_one, mapRingHom_rightChart]

end AlgebraicGeometry
