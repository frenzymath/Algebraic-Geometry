/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.Algebra.Polynomial.Monic

/-!
# The diagonal-equation regularity engine (brick B1)

The regularity half of deg-D4b (sub-brick B1): the single engine lemma discharging the
`regular` field of the diagonal `LocalEquations` (deg-D4b) *and* deg-D4c's pullback
regularity hypothesis `hreg`, uniformly in an arbitrary second tensor factor.

Let `k` be a commutative ring and `B` a `Polynomial k`-algebra which is **flat** over
`Polynomial k` (the étale coordinate ring of a standard-smooth chart, `u := algebraMap X`).
For *any* `k`-algebra `A` and *any* `b : A`, the element `u ⊗ 1 - 1 ⊗ b` is a
nonzerodivisor of `B ⊗[k] A`.

The proof is `monic + flat base change`, with **no** integrality, fibre, or
transcendence hypothesis (so it survives at every point of a non-integral product
`C ⊗ T`, which is why deg-D4c can discharge its regularity hypothesis on non-integral
products):

* `X - C b` is monic hence a nonzerodivisor of `A[X]` (`Polynomial.Monic.mem_nonZeroDivisors`);
* the composite `A[X] ≃ A ⊗[k] k[X] → A ⊗[k] B ≃ B ⊗[k] A` sending `X - C b ↦ u ⊗ 1 - 1 ⊗ b`
  is a **flat** ring homomorphism — the base change `Algebra.TensorProduct.map (id) (k[X]→B)`
  of the flat coordinate map is flat (`RingHom.Flat.tensorProductMap`), pre/post-composed
  with the algebra isomorphisms `polyEquivTensor` and `Algebra.TensorProduct.comm`;
* a flat ring homomorphism carries nonzerodivisors to nonzerodivisors
  (`RingHom.Flat.mem_nonZeroDivisors`, from `Module.Flat.isSMulRegular_of_nonZeroDivisors`).

## Main results

* `RingHom.Flat.mem_nonZeroDivisors`: a flat ring hom preserves nonzerodivisors.
* `AlgebraicJacobian.Diagonal.tmul_one_sub_one_tmul_mem_nonZeroDivisors`: the engine.
* `AlgebraicJacobian.Diagonal.diagGen_mem_nonZeroDivisors`: the `A = B`, `b = u`
  specialisation, i.e. the section-level `regular` of deg-D4b's diagonal equation.

This file is pure commutative algebra (no scheme imports); the germ-level regularity helper
(`germ regular of section regular on an affine open`, D2/D6) needs scheme imports and is
therefore deferred to the mixed brick B4, exactly as flagged in
`informal/deg-d4b-worksheet.md` (B1 spec).
-/

set_option autoImplicit false

open scoped TensorProduct nonZeroDivisors
open Polynomial

namespace RingHom.Flat

/-- **The `IsSMulRegular` bridge.** A flat ring homomorphism carries nonzerodivisors to
nonzerodivisors: if `r ∈ R⁰` and `f : R →+* S` is flat, then `f r ∈ S⁰`. Scalar
multiplication by `r` is injective on the flat `R`-module `S`
(`Module.Flat.isSMulRegular_of_nonZeroDivisors`), and `r • · = f r * ·`. 


 * Provenance: CUSTOM.
-/
lemma mem_nonZeroDivisors {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.Flat) {r : R} (hr : r ∈ R⁰) : f r ∈ S⁰ := by
  letI : Algebra R S := f.toAlgebra
  have hflat : Module.Flat R S := hf
  have hreg : IsSMulRegular S r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have key : ∀ y : S, f r * y = 0 → y = 0 := by
    intro y hy
    refine hreg ?_
    change r • y = r • 0
    rw [smul_zero, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact hy
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun y hy => key y (by rw [mul_comm]; exact hy)⟩

end RingHom.Flat

namespace AlgebraicJacobian.Diagonal

variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
  [Algebra (Polynomial k) B] [IsScalarTower k (Polynomial k) B] [Module.Flat (Polynomial k) B]

/-- **The regularity engine (deg-D4b §D2).** For a flat coordinate `Polynomial k → B`, an
*arbitrary* `k`-algebra `A`, and *any* `b : A`, the element `u ⊗ 1 - 1 ⊗ b` is a
nonzerodivisor of `B ⊗[k] A`, where `u := algebraMap (Polynomial k) B X`.

Instantiations: deg-D4b's `regular` field is `A = B`, `b = u`
(`diagGen_mem_nonZeroDivisors`); deg-D4c's `hreg` is `A =` a chart of the test object,
`b = t^♯ u`. No integrality of `B ⊗[k] A` is used, so the engine runs at every point of a
non-integral product. 


 * Provenance: CUSTOM.
-/
theorem tmul_one_sub_one_tmul_mem_nonZeroDivisors
    {A : Type*} [CommRing A] [Algebra k A] (b : A) :
    algebraMap (Polynomial k) B X ⊗ₜ[k] (1 : A) - (1 : B) ⊗ₜ[k] b ∈ (B ⊗[k] A)⁰ := by
  set φ : Polynomial k →ₐ[k] B := IsScalarTower.toAlgHom k (Polynomial k) B with hφdef
  have hφ : φ.Flat := by
    rw [show φ.toRingHom = algebraMap (Polynomial k) B from rfl, RingHom.flat_algebraMap_iff]
    infer_instance
  -- the flat map `A[X] ≃ A ⊗ k[X] → A ⊗ B ≃ B ⊗ A` sending `X - C b ↦ u ⊗ 1 - 1 ⊗ b`
  let Θ : Polynomial A →ₐ[k] (B ⊗[k] A) :=
    (Algebra.TensorProduct.comm k A B).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id k A) φ).comp (polyEquivTensor k A).toAlgHom)
  have hΘ : Θ.toRingHom.Flat :=
    RingHom.Flat.comp
      (RingHom.Flat.comp
        (RingHom.Flat.of_bijective (polyEquivTensor k A).bijective)
        (RingHom.Flat.tensorProductMap (RingHom.Flat.id A) hφ))
      (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm k A B).bijective)
  have himg : Θ (X - C b)
      = algebraMap (Polynomial k) B X ⊗ₜ[k] (1 : A) - (1 : B) ⊗ₜ[k] b := by
    simp only [Θ, map_sub, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    rw [show polyEquivTensor k A X = (1 : A) ⊗ₜ[k] X by simp [polyEquivTensor_apply],
        show polyEquivTensor k A (C b) = b ⊗ₜ[k] (1 : Polynomial k) by simp [polyEquivTensor_apply]]
    simp [Algebra.TensorProduct.map_tmul, hφdef]
  have hnzd := RingHom.Flat.mem_nonZeroDivisors hΘ
    (Polynomial.Monic.mem_nonZeroDivisors (monic_X_sub_C b))
  rwa [show Θ.toRingHom (X - C b) = Θ (X - C b) from rfl, himg] at hnzd

/-- The section-level `regular` datum of deg-D4b: the diagonal equation `u ⊗ 1 - 1 ⊗ u` is a
nonzerodivisor of `B ⊗[k] B` (the `A = B`, `b = u` instance of the engine). This is the
input to the affine germ-regularity helper (built in brick B4). 


 * Provenance: CUSTOM.
-/
theorem diagGen_mem_nonZeroDivisors :
    algebraMap (Polynomial k) B X ⊗ₜ[k] (1 : B)
        - (1 : B) ⊗ₜ[k] algebraMap (Polynomial k) B X ∈ (B ⊗[k] B)⁰ :=
  tmul_one_sub_one_tmul_mem_nonZeroDivisors _

end AlgebraicJacobian.Diagonal
