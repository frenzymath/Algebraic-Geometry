/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.PiLocalization

/-!
# The tensor product of two `Away` localizations as an `Away` localization of the tensor product

Let `A → B₁` and `A → B₂` be maps of commutative rings, `r : B₁` and `s : B₂`.  Fix models
`Si`, `Sj` for the localizations `B₁[1/r]`, `B₂[1/s]` (as `B₁`- resp. `B₂`-algebras, via
`IsScalarTower A B₁ Si`, `IsScalarTower A B₂ Sj`).  This file exhibits their `A`-tensor
product `Si ⊗[A] Sj` as a localization of the tensor product `B₁ ⊗[A] B₂` away from the
element `(r ⊗ₜ 1) * (1 ⊗ₜ s) = r ⊗ₜ s`.

This is the two-base analogue of `IsLocalization.Away.tensor'`
(`AlgebraicJacobian.Algebra.PiLocalization`): there the two factors are `Away`
localizations over the *same* base `A`, giving `Away (f * g)` over `A`; here the two
factors are `Away` localizations over `B₁` resp. `B₂`, tensored over the smaller ring `A`,
giving an `Away` localization over `B₁ ⊗[A] B₂`.  The instantiations in the ζ2·ii
pi-assembly are `B₁ = B₂ = B` (double tensors, components `Sᵢ ⊗[A] Sⱼ` over `B ⊗[A] B`)
and `B₁ = B`, `B₂ = B ⊗[A] B` (triple tensors, components `Sᵢ ⊗[A] (Sⱼ ⊗[A] Sₖ)` over
`B ⊗[A] (B ⊗[A] B)`).

## Main declarations

* `IsLocalization.Away.tensorAwayAlgebra` — the canonical `B₁ ⊗[A] B₂`-algebra structure on
  `Si ⊗[A] Sj`, coming from `Algebra.TensorProduct.map` applied to the two structure maps
  `B₁ →ₐ[A] Si`, `B₂ →ₐ[A] Sj`.  It is a `def` (not a global instance) so as not to clash
  with `Algebra.id` in the degenerate case `Si = B₁`, `Sj = B₂`; consumers introduce it with
  `letI`.
* `IsLocalization.Away.tensorAwayScalarTower` — the accompanying scalar tower
  `A → B₁ ⊗[A] B₂ → Si ⊗[A] Sj`.
* `IsLocalization.Away.isLocalization_away_tensor` — the localization statement
  `IsLocalization.Away ((r ⊗ₜ 1) * (1 ⊗ₜ s)) (Si ⊗[A] Sj)`.
* `IsLocalization.Away.tensorAwayEquiv` — the canonical `B₁ ⊗[A] B₂`-algebra equivalence to
  any other model of this localization, with `tensorAwayEquiv_tmul` computing it on pure
  tensors.

## Implementation notes

The localization is factored through the intermediate ring `Si ⊗[A] B₂`: first the left
factor `B₁ → Si` is localized at `r`, then the right factor `B₂ → Sj` at `s`, combined with
`IsLocalization.Away.mul'`.  Each individual localization is provided by mathlib's
`IsLocalization.tensorProduct_tensorProduct` (left factor) and
`IsLocalization.tensorProduct_tensorProduct_right` (right factor), both of which take the
tensor-`map` algebra structure as an explicit hypothesis, thereby avoiding any
`Algebra.TensorProduct.rightAlgebra` instance diamonds.
-/

universe u

set_option autoImplicit false

open TensorProduct

namespace IsLocalization.Away

variable (A B₁ B₂ : Type u) [CommRing A] [CommRing B₁] [CommRing B₂]
variable [Algebra A B₁] [Algebra A B₂]
variable (r : B₁) (s : B₂)
variable (Si Sj : Type u) [CommRing Si] [CommRing Sj]
variable [Algebra B₁ Si] [Algebra B₂ Sj] [Algebra A Si] [Algebra A Sj]
variable [IsScalarTower A B₁ Si] [IsScalarTower A B₂ Sj]

/-! ## The canonical algebra maps and structure -/

/-- The `A`-algebra map `B₁ ⊗[A] B₂ →ₐ[A] Si ⊗[A] B₂` localizing only the left factor. -/
noncomputable def leftMap : B₁ ⊗[A] B₂ →ₐ[A] Si ⊗[A] B₂ :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B₁ Si) (AlgHom.id A B₂)

/-- The `A`-algebra map `Si ⊗[A] B₂ →ₐ[A] Si ⊗[A] Sj` localizing the right factor. -/
noncomputable def rightMap : Si ⊗[A] B₂ →ₐ[A] Si ⊗[A] Sj :=
  Algebra.TensorProduct.map (AlgHom.id A Si) (IsScalarTower.toAlgHom A B₂ Sj)

/-- The `A`-algebra map `B₁ ⊗[A] B₂ →ₐ[A] Si ⊗[A] Sj` localizing both factors. 


 * Provenance: CUSTOM.
-/
noncomputable def tensorMap : B₁ ⊗[A] B₂ →ₐ[A] Si ⊗[A] Sj :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B₁ Si) (IsScalarTower.toAlgHom A B₂ Sj)

@[simp]
lemma tensorMap_tmul (x : B₁) (y : B₂) :
    tensorMap A B₁ B₂ Si Sj (x ⊗ₜ[A] y) = algebraMap B₁ Si x ⊗ₜ[A] algebraMap B₂ Sj y :=
  rfl

/-- The two-step factorisation of `tensorMap` through the intermediate `Si ⊗[A] B₂`. -/
lemma rightMap_comp_leftMap :
    (rightMap A B₂ Si Sj).comp (leftMap A B₁ B₂ Si) = tensorMap A B₁ B₂ Si Sj := by
  rw [rightMap, leftMap, tensorMap, ← Algebra.TensorProduct.map_comp]; rfl

/-- The canonical `B₁ ⊗[A] B₂`-algebra structure on `Si ⊗[A] Sj`, given by `tensorMap`.

Provided as a `def` (introduce it with `letI`), *not* a global instance: as a global
instance it would compete with `Algebra.id` in the degenerate case `Si = B₁`, `Sj = B₂`. 
 * Provenance: CUSTOM.
-/
@[reducible] noncomputable def tensorAwayAlgebra : Algebra (B₁ ⊗[A] B₂) (Si ⊗[A] Sj) :=
  (tensorMap A B₁ B₂ Si Sj).toRingHom.toAlgebra

/-- The scalar tower `A → B₁ ⊗[A] B₂ → Si ⊗[A] Sj` accompanying `tensorAwayAlgebra`. -/
lemma tensorAwayScalarTower :
    letI := tensorAwayAlgebra A B₁ B₂ Si Sj
    IsScalarTower A (B₁ ⊗[A] B₂) (Si ⊗[A] Sj) :=
  letI := tensorAwayAlgebra A B₁ B₂ Si Sj
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap (tensorMap A B₁ B₂ Si Sj)).symm

/-! ## The localization statement -/

/-- **The tensor product of an `Away` localization over `B₁` and an `Away` localization
over `B₂` is an `Away` localization of the tensor product `B₁ ⊗[A] B₂`.**  Namely,
`Si ⊗[A] Sj` (with the canonical `tensorAwayAlgebra` structure) is the localization of
`B₁ ⊗[A] B₂` away from `(r ⊗ₜ 1) * (1 ⊗ₜ s)`, which equals `r ⊗ₜ s`. 


 * Provenance: CUSTOM.
-/
theorem isLocalization_away_tensor
    [IsLocalization.Away r Si] [IsLocalization.Away s Sj] :
    letI := tensorAwayAlgebra A B₁ B₂ Si Sj
    IsLocalization.Away ((r ⊗ₜ[A] 1) * (1 ⊗ₜ[A] s) : B₁ ⊗[A] B₂) (Si ⊗[A] Sj) := by
  letI algL : Algebra (B₁ ⊗[A] B₂) (Si ⊗[A] B₂) := (leftMap A B₁ B₂ Si).toRingHom.toAlgebra
  letI algR : Algebra (Si ⊗[A] B₂) (Si ⊗[A] Sj) := (rightMap A B₂ Si Sj).toRingHom.toAlgebra
  letI := tensorAwayAlgebra A B₁ B₂ Si Sj
  -- the tower `B₁ ⊗[A] B₂ → Si ⊗[A] B₂ → Si ⊗[A] Sj`
  haveI stRST : IsScalarTower (B₁ ⊗[A] B₂) (Si ⊗[A] B₂) (Si ⊗[A] Sj) :=
    IsScalarTower.of_algebraMap_eq' <| by
      change (tensorMap A B₁ B₂ Si Sj).toRingHom
        = (rightMap A B₂ Si Sj).toRingHom.comp (leftMap A B₁ B₂ Si).toRingHom
      rw [← rightMap_comp_leftMap A B₁ B₂ Si Sj]; rfl
  -- left factor: `Si ⊗[A] B₂` is `Away (r ⊗ₜ 1)` over `B₁ ⊗[A] B₂`
  haveI stL : IsScalarTower B₁ (B₁ ⊗[A] B₂) (Si ⊗[A] B₂) :=
    IsScalarTower.of_algebraMap_eq (fun _ => by
      simp [RingHom.algebraMap_toAlgebra, leftMap, Algebra.TensorProduct.map_tmul,
        IsScalarTower.coe_toAlgHom'])
  have H1 : (algebraMap (B₁ ⊗[A] B₂) (Si ⊗[A] B₂)).comp
      Algebra.TensorProduct.includeRight.toRingHom
        = Algebra.TensorProduct.includeRight.toRingHom := by
    have key : (leftMap A B₁ B₂ Si).comp Algebra.TensorProduct.includeRight
        = Algebra.TensorProduct.includeRight := by
      rw [leftMap, Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_id]
    ext b
    simpa [RingHom.algebraMap_toAlgebra] using congrArg (fun f => f b) key
  haveI hL : IsLocalization.Away (r ⊗ₜ[A] (1 : B₂) : B₁ ⊗[A] B₂) (Si ⊗[A] B₂) := by
    have he : Algebra.algebraMapSubmonoid (B₁ ⊗[A] B₂) (Submonoid.powers r)
        = Submonoid.powers (r ⊗ₜ[A] (1 : B₂)) := by
      rw [Algebra.algebraMapSubmonoid_powers]; rfl
    rw [IsLocalization.Away, ← he]
    exact IsLocalization.tensorProduct_tensorProduct (R := A) (S := B₂)
      (Submonoid.powers r) Si H1
  -- right factor: `Si ⊗[A] Sj` is `Away (1 ⊗ₜ s)` over `Si ⊗[A] B₂`
  haveI stR : IsScalarTower Si (Si ⊗[A] B₂) (Si ⊗[A] Sj) :=
    IsScalarTower.of_algebraMap_eq (fun _ => by
      simp [RingHom.algebraMap_toAlgebra, rightMap, Algebra.TensorProduct.map_tmul,
        IsScalarTower.coe_toAlgHom'])
  have H2 : (algebraMap (Si ⊗[A] B₂) (Si ⊗[A] Sj)).comp
      Algebra.TensorProduct.includeRight.toRingHom
        = Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap B₂ Sj) := by
    have key : (rightMap A B₂ Si Sj).comp Algebra.TensorProduct.includeRight
        = Algebra.TensorProduct.includeRight.comp (IsScalarTower.toAlgHom A B₂ Sj) := by
      rw [rightMap, Algebra.TensorProduct.map_comp_includeRight]
    ext b
    simpa [RingHom.algebraMap_toAlgebra] using congrArg (fun f => f b) key
  haveI hR : IsLocalization.Away
      (algebraMap (B₁ ⊗[A] B₂) (Si ⊗[A] B₂) ((1 : B₁) ⊗ₜ[A] s)) (Si ⊗[A] Sj) := by
    have hmap : algebraMap (B₁ ⊗[A] B₂) (Si ⊗[A] B₂) ((1 : B₁) ⊗ₜ[A] s)
        = ((1 : Si) ⊗ₜ[A] s) := by
      simp [RingHom.algebraMap_toAlgebra, leftMap, Algebra.TensorProduct.map_tmul]
    rw [hmap]
    have he : (Submonoid.powers s).map
        (Algebra.TensorProduct.includeRight (R := A) (A := Si) (B := B₂))
          = Submonoid.powers ((1 : Si) ⊗ₜ[A] s) := by
      rw [Submonoid.map_powers]; rfl
    rw [IsLocalization.Away, ← he]
    exact IsLocalization.tensorProduct_tensorProduct_right A Si (Submonoid.powers s) Sj H2
  exact IsLocalization.Away.mul' (S := Si ⊗[A] B₂) (Si ⊗[A] Sj)
    (r ⊗ₜ[A] (1 : B₂)) ((1 : B₁) ⊗ₜ[A] s)

/-- The localization element in `simp`-normal form: `(r ⊗ₜ 1) * (1 ⊗ₜ s) = r ⊗ₜ s`. -/
@[simp] lemma tmul_one_mul_one_tmul (r : B₁) (s : B₂) :
    ((r ⊗ₜ[A] 1) * (1 ⊗ₜ[A] s) : B₁ ⊗[A] B₂) = r ⊗ₜ[A] s := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-! ## Comparison with an arbitrary model -/

variable (Tij : Type u) [CommRing Tij] [Algebra (B₁ ⊗[A] B₂) Tij]

/-- The canonical `B₁ ⊗[A] B₂`-algebra equivalence from `Si ⊗[A] Sj` (with the
`tensorAwayAlgebra` structure) to any other model `Tij` of the localization of
`B₁ ⊗[A] B₂` away from `(r ⊗ₜ 1) * (1 ⊗ₜ s)`. 


 * Provenance: CUSTOM.
-/
noncomputable def tensorAwayEquiv
    [IsLocalization.Away r Si] [IsLocalization.Away s Sj]
    [IsLocalization.Away ((r ⊗ₜ[A] 1) * (1 ⊗ₜ[A] s) : B₁ ⊗[A] B₂) Tij] :
    letI := tensorAwayAlgebra A B₁ B₂ Si Sj
    Si ⊗[A] Sj ≃ₐ[B₁ ⊗[A] B₂] Tij :=
  letI := tensorAwayAlgebra A B₁ B₂ Si Sj
  haveI := isLocalization_away_tensor A B₁ B₂ r s Si Sj
  IsLocalization.algEquiv (Submonoid.powers ((r ⊗ₜ[A] 1) * (1 ⊗ₜ[A] s))) (Si ⊗[A] Sj) Tij

/-- `tensorAwayEquiv` sends `tensorMap w` (equivalently, the image of `w : B₁ ⊗[A] B₂`
under the canonical structure map) to `algebraMap w`; in particular it is a
`B₁ ⊗[A] B₂`-algebra map. 


 * Provenance: CUSTOM.
-/
lemma tensorAwayEquiv_tensorMap
    [IsLocalization.Away r Si] [IsLocalization.Away s Sj]
    [IsLocalization.Away ((r ⊗ₜ[A] 1) * (1 ⊗ₜ[A] s) : B₁ ⊗[A] B₂) Tij] (w : B₁ ⊗[A] B₂) :
    letI := tensorAwayAlgebra A B₁ B₂ Si Sj
    tensorAwayEquiv A B₁ B₂ r s Si Sj Tij (tensorMap A B₁ B₂ Si Sj w)
      = algebraMap (B₁ ⊗[A] B₂) Tij w :=
  letI := tensorAwayAlgebra A B₁ B₂ Si Sj
  (tensorAwayEquiv A B₁ B₂ r s Si Sj Tij).commutes w

/-- `tensorAwayEquiv` on a pure tensor of structure-map images: it sends
`algebraMap B₁ Si x ⊗ₜ algebraMap B₂ Sj y` to `algebraMap (B₁ ⊗[A] B₂) Tij (x ⊗ₜ y)`. 


 * Provenance: CUSTOM.
-/
lemma tensorAwayEquiv_tmul
    [IsLocalization.Away r Si] [IsLocalization.Away s Sj]
    [IsLocalization.Away ((r ⊗ₜ[A] 1) * (1 ⊗ₜ[A] s) : B₁ ⊗[A] B₂) Tij] (x : B₁) (y : B₂) :
    letI := tensorAwayAlgebra A B₁ B₂ Si Sj
    tensorAwayEquiv A B₁ B₂ r s Si Sj Tij (algebraMap B₁ Si x ⊗ₜ[A] algebraMap B₂ Sj y)
      = algebraMap (B₁ ⊗[A] B₂) Tij (x ⊗ₜ[A] y) := by
  letI := tensorAwayAlgebra A B₁ B₂ Si Sj
  rw [← tensorAwayEquiv_tensorMap A B₁ B₂ r s Si Sj Tij]
  rfl

end IsLocalization.Away
