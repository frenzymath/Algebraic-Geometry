/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRelDivisor

/-!
# DD-4 redesign: scalar change for a flat ideal quotient

Let `R → B → A` be a tower of commutative rings and let `J` be an ideal of `B`.
If `B/J` is flat over `R` and every element of `J` vanishes in `B ⊗[R] A`, then
`J ⊗[B] A` vanishes.  The first step is purity over `R`, which gives
`J ⊗[R] A = 0`; base change in stages then descends this vanishing to tensoring over `B`.

The hypothesis here is deliberately the ambient tensor equality
`x ⊗ 1 = 0` in `B ⊗[R] A`.  For a total-point residue field this is a
whole-base-fibre vanishing statement.  It is stronger than the assertion that `x` maps to
zero in `A`, and it does not follow merely from local generation at one point.  The sharp
single-point route instead uses `RankOneFibre` on `A ⊗[B] J` directly.
-/

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

namespace FlatIdealFibre

/-- If `B/J` is `R`-flat and `J` vanishes in the ambient `R`-base change to the
`B`-algebra `A`, then the ideal's `B`-fibre over `A` is zero.

No flatness over `B` is assumed.  The `hzero` premise is an equality in `B ⊗[R] A`,
not merely pointwise vanishing under the multiplication map `B ⊗[R] A → A`. -/
theorem subsingleton_tensor_over_algebra_of_flat_quotient_of_fibre_vanishing
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
    (J : Ideal B) [Module.Flat R (B ⧸ J)]
    (hzero : ∀ x : J, (x : B) ⊗ₜ[R] (1 : A) = (0 : B ⊗[R] A)) :
    Subsingleton (J ⊗[B] A) := by
  let P : Submodule R B := J.restrictScalars R
  letI : Module.Flat R (B ⧸ P) :=
    Module.Flat.of_linearEquiv
      (Submodule.Quotient.restrictScalarsEquiv R (J : Submodule B B))
  have hP : Subsingleton (P ⊗[R] A) :=
    subsingleton_tmul_of_flat_quotient P (fun x a => by
      rw [show (x : B) ⊗ₜ[R] a =
          (TensorProduct.comm R A B) (a ⊗ₜ[R] (x : B)) from
        (TensorProduct.comm_tmul R A B a (x : B)).symm]
      have h1 : (1 : A) ⊗ₜ[R] (x : B) = 0 := by
        have hx := hzero ⟨x, x.property⟩
        have hc := congrArg (TensorProduct.comm R B A) hx
        rwa [TensorProduct.comm_tmul, map_zero] at hc
      rw [show a ⊗ₜ[R] (x : B) = a • ((1 : A) ⊗ₜ[R] (x : B)) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], h1, smul_zero, map_zero])
  let g : B ⊗[R] J →ₗ[B] J :=
    ((LinearMap.id (R := B) (M := J)).restrictScalars R).liftBaseChange B
  have hg : Function.Surjective g := by
    intro x
    refine ⟨(1 : B) ⊗ₜ[R] x, ?_⟩
    simp [g]
  have hgt : Function.Surjective (g.rTensor A) :=
    LinearMap.rTensor_surjective A hg
  have hsource : Subsingleton ((B ⊗[R] J) ⊗[B] A) := by
    have e := TensorProduct.AlgebraTensorModule.cancelBaseChange R B A A J
    have he : Subsingleton (A ⊗[R] J) :=
      (TensorProduct.comm R J A).toEquiv.subsingleton_congr.mp hP
    have he' : Subsingleton (A ⊗[B] (B ⊗[R] J)) :=
      e.toEquiv.subsingleton_congr.mpr he
    exact (TensorProduct.comm B (B ⊗[R] J) A).toEquiv.subsingleton_congr.mpr he'
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := hgt x
  obtain ⟨y', rfl⟩ := hgt y
  rw [hsource.elim x' y']

/-- The surjective-image form of
`subsingleton_tensor_over_algebra_of_flat_quotient_of_fibre_vanishing`.
It applies, for example, to the image of `J` under a quotient map. -/
theorem subsingleton_surjective_image_tensor_over_algebra_of_flat_quotient_of_fibre_vanishing
    {R B A N : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
    [AddCommGroup N] [Module B N]
    (J : Ideal B) [Module.Flat R (B ⧸ J)]
    (f : J →ₗ[B] N) (hf : Function.Surjective f)
    (hzero : ∀ x : J, (x : B) ⊗ₜ[R] (1 : A) = (0 : B ⊗[R] A)) :
    Subsingleton (N ⊗[B] A) := by
  have hJ :=
    subsingleton_tensor_over_algebra_of_flat_quotient_of_fibre_vanishing J hzero
  have hft : Function.Surjective (f.rTensor A) :=
    LinearMap.rTensor_surjective A hf
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := hft x
  obtain ⟨y', rfl⟩ := hft y
  rw [hJ.elim x' y']

end FlatIdealFibre

end AlgebraicGeometry
