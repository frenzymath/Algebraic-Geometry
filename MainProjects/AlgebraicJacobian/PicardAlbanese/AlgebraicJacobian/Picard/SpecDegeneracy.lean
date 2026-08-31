/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CoherentWitness

/-!
# The simplicial degeneracies at `Spec` level (ζ2·ii prerequisites)

Complementing the coface maps `tensorInl`, `tensorInr`, `tensorFace₁₂/₁₃/₂₃` and their
`Spec`-level coincidences (`AlgebraicJacobian.Picard.EtaleSeparatedness`,
`AlgebraicJacobian.Picard.AmitsurCochain`, `AlgebraicJacobian.Picard.CoherentWitness`),
this file provides the two *degeneracies* the ζ2·ii pi-assembly pulls back along:

* `AlgebraicGeometry.tensorMul : B ⊗[A] B →ₐ[k] B` — the multiplication, whose `Spec` is
  the diagonal `Δ : Spec B ⟶ Spec (B ⊗[A] B)`;
* `AlgebraicGeometry.tensorMul₁₂ : B ⊗[A] (B ⊗[A] B) →ₐ[k] B ⊗[A] B` — multiplication of
  the first two tensor positions, `x ⊗ (y ⊗ z) ↦ xy ⊗ z`, whose `Spec` is the degeneracy
  `σ : Spec (B ⊗[A] B) ⟶ Spec (B ⊗[A] (B ⊗[A] B))`;

together with the simplicial identities they satisfy against the cofaces, at ring level
(`tensorMul_comp_tensorInl`, …, `tensorMul₁₂_comp_tensorFace₁₃`) and at `Spec` level in
the `.left`-composite form consumed by the unit-section calculus
(`Over.overSpecMap_left_mul_inl`, …, `Over.overSpecMap_left_mul₁₂_face₁₃`).

Pulling the Amitsur coherence of a `CoherentCechWitness` back along `σ` and then along
`Δ` is what forces the witness cochain to be `1` on the diagonal
(`AlgebraicJacobian.Picard.WitnessComponents`), which in turn makes the corrected
components of the pi-assembly collapse onto the Zariski cover cocycle (G6).
-/

set_option autoImplicit false

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

/-! ## The degeneracies at ring level -/

/-- The multiplication `B ⊗[A] B →ₐ[k] B` — the `k`-restriction of
`Algebra.TensorProduct.lmul'`; its `Spec` is the diagonal `Spec B ⟶ Spec (B ⊗[A] B)`. -/
noncomputable abbrev tensorMul : B ⊗[A] B →ₐ[k] B :=
  (Algebra.TensorProduct.lmul' A (S := B)).restrictScalars k

/-- The `A`-linear degeneracy multiplying the first two tensor positions,
`x ⊗ (y ⊗ z) ↦ xy ⊗ z`. -/
noncomputable def descentMul₁₂ : B ⊗[A] (B ⊗[A] B) →ₐ[A] B ⊗[A] B :=
  Algebra.TensorProduct.lift (Module.descentIncl₁ A B) (AlgHom.id A (B ⊗[A] B))
    fun _ _ => Commute.all _ _

@[simp]
lemma descentMul₁₂_tmul (x : B) (w : B ⊗[A] B) :
    descentMul₁₂ (x ⊗ₜ[A] w) = (x ⊗ₜ[A] 1) * w := by
  simp [descentMul₁₂]

/-- The degeneracy multiplying the first two tensor positions,
`x ⊗ (y ⊗ z) ↦ xy ⊗ z`, as a `k`-algebra map; its `Spec` is the degeneracy
`Spec (B ⊗[A] B) ⟶ Spec (B ⊗[A] (B ⊗[A] B))`. -/
noncomputable abbrev tensorMul₁₂ : B ⊗[A] (B ⊗[A] B) →ₐ[k] B ⊗[A] B :=
  (descentMul₁₂ (A := A) (B := B)).restrictScalars k

/-! ## The simplicial identities at ring level -/

/-- **Degeneracy identity, position `1`.** `tensorMul ∘ tensorInl = id`. -/
lemma tensorMul_comp_tensorInl :
    (tensorMul (k := k) (A := A) (B := B)).comp tensorInl = AlgHom.id k B := by
  ext b
  simp [tensorInl, Algebra.TensorProduct.lmul'_apply_tmul]

/-- **Degeneracy identity, position `2`.** `tensorMul ∘ tensorInr = id`. -/
lemma tensorMul_comp_tensorInr :
    (tensorMul (k := k) (A := A) (B := B)).comp tensorInr = AlgHom.id k B := by
  ext b
  simp [tensorInr, Algebra.TensorProduct.lmul'_apply_tmul]

private lemma descentMul₁₂_comp_descentFace₂₃ :
    (descentMul₁₂ (A := A) (B := B)).comp (Module.descentFace₂₃ A B)
      = AlgHom.id A (B ⊗[A] B) :=
  Algebra.TensorProduct.ext' fun x y => by simp

private lemma descentMul₁₂_comp_descentFace₁₂ :
    (descentMul₁₂ (A := A) (B := B)).comp (Module.descentFace₁₂ A B)
      = (Module.descentIncl₁ A B).comp (Algebra.TensorProduct.lmul' A) :=
  Algebra.TensorProduct.ext' fun x y => by
    simp [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.tmul_mul_tmul]

private lemma descentMul₁₂_comp_descentFace₁₃ :
    (descentMul₁₂ (A := A) (B := B)).comp (Module.descentFace₁₃ A B)
      = AlgHom.id A (B ⊗[A] B) :=
  Algebra.TensorProduct.ext' fun x y => by
    simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- **Degeneracy identity against the `2,3`-coface.** `tensorMul₁₂ ∘ tensorFace₂₃ = id`. -/
lemma tensorMul₁₂_comp_tensorFace₂₃ :
    (tensorMul₁₂ (k := k) (A := A) (B := B)).comp tensorFace₂₃
      = AlgHom.id k (B ⊗[A] B) :=
  AlgHom.ext fun w => DFunLike.congr_fun descentMul₁₂_comp_descentFace₂₃ w

/-- **Degeneracy identity against the `1,2`-coface.**
`tensorMul₁₂ ∘ tensorFace₁₂ = tensorInl ∘ tensorMul`. -/
lemma tensorMul₁₂_comp_tensorFace₁₂ :
    (tensorMul₁₂ (k := k) (A := A) (B := B)).comp tensorFace₁₂
      = (tensorInl (A := A) (B := B)).comp tensorMul :=
  AlgHom.ext fun w => DFunLike.congr_fun descentMul₁₂_comp_descentFace₁₂ w

/-- **Degeneracy identity against the `1,3`-coface.** `tensorMul₁₂ ∘ tensorFace₁₃ = id`. -/
lemma tensorMul₁₂_comp_tensorFace₁₃ :
    (tensorMul₁₂ (k := k) (A := A) (B := B)).comp tensorFace₁₃
      = AlgHom.id k (B ⊗[A] B) :=
  AlgHom.ext fun w => DFunLike.congr_fun descentMul₁₂_comp_descentFace₁₃ w

/-! ## The degeneracy coincidences at `Spec` level -/

namespace Over

/-- **`Spec`-level degeneracy coincidence, diagonal against `inl`**:
`Δ ≫ q₁ = 𝟙 (Spec B)`. -/
lemma overSpecMap_left_mul_inl :
    (Over.overSpecMap (tensorMul (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorInl (A := A) (B := B))).left
      = 𝟙 (overSpec k B).left := by
  rw [← Over.comp_left, ← Over.overSpecMap_comp, tensorMul_comp_tensorInl,
    Over.overSpecMap_id]
  rfl

/-- **`Spec`-level degeneracy coincidence, diagonal against `inr`**:
`Δ ≫ q₂ = 𝟙 (Spec B)`. -/
lemma overSpecMap_left_mul_inr :
    (Over.overSpecMap (tensorMul (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorInr (A := A) (B := B))).left
      = 𝟙 (overSpec k B).left := by
  rw [← Over.comp_left, ← Over.overSpecMap_comp, tensorMul_comp_tensorInr,
    Over.overSpecMap_id]
  rfl

/-- **`Spec`-level degeneracy coincidence against the `2,3`-coface**:
`σ ≫ f₂₃ = 𝟙 (Spec (B ⊗[A] B))`. -/
lemma overSpecMap_left_mul₁₂_face₂₃ :
    (Over.overSpecMap (tensorMul₁₂ (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))).left
      = 𝟙 (overSpec k (B ⊗[A] B)).left := by
  rw [← Over.comp_left, ← Over.overSpecMap_comp, tensorMul₁₂_comp_tensorFace₂₃,
    Over.overSpecMap_id]
  rfl

/-- **`Spec`-level degeneracy coincidence against the `1,2`-coface**:
`σ ≫ f₁₂ = q₁ ≫ Δ`. -/
lemma overSpecMap_left_mul₁₂_face₁₂ :
    (Over.overSpecMap (tensorMul₁₂ (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))).left
      = (Over.overSpecMap (tensorInl (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorMul (k := k) (A := A) (B := B))).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Over.overSpecMap_comp, ← Over.overSpecMap_comp,
    tensorMul₁₂_comp_tensorFace₁₂]

/-- **`Spec`-level degeneracy coincidence against the `1,3`-coface**:
`σ ≫ f₁₃ = 𝟙 (Spec (B ⊗[A] B))`. -/
lemma overSpecMap_left_mul₁₂_face₁₃ :
    (Over.overSpecMap (tensorMul₁₂ (k := k) (A := A) (B := B))).left
        ≫ (Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))).left
      = 𝟙 (overSpec k (B ⊗[A] B)).left := by
  rw [← Over.comp_left, ← Over.overSpecMap_comp, tensorMul₁₂_comp_tensorFace₁₃,
    Over.overSpecMap_id]
  rfl

end Over

end AlgebraicGeometry
