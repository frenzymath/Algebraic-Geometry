/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TruncExpUnits

/-!
# Dual numbers under base change: `A ⊗[k] k[ε] ≃ₐ[A] A[ε]` (W5-T2, §7 port)

The algebra core of the chart-sections identification (substrate piece (i) of the
geometric cocycle leg, consumed by W5-T3): for an affine chart `V = Spec A` of the
curve, the base-changed chart `V ×_{Spec k} Spec k[ε]` is `Spec (A ⊗[k] k[ε])`
(Mathlib's `pullbackSpecIso`), and this file supplies the missing ring identification
`A ⊗[k] k[ε] ≃ₐ[A] A[ε]` — so the thickened chart sections are the dual numbers of the
chart ring, which is what feeds the two-chart unit-cocycle engine of
`AlgebraicJacobian.Tangent.TruncExpCech` (`Γ((U₀ ⊓ U₁)_ε) = Γ(U₀ ⊓ U₁)[ε]`, transition
units in `(B[ε])ˣ`). The trivial-square-zero base is finite free, so no flatness input
is needed: the inverse is written down explicitly (`x ↦ x.fst ⊗ 1 + x.snd ⊗ ε`).

In the Rebuild, compose with the landed `Over.sectionsBaseChange`
(`AlgebraicJacobian.Cohomology.SectionsBaseChange`) at `A = k[ε]` to identify the
sections of a base-changed affine chart `V × Spec k[ε]` with `Γ(V, 𝒪)[ε]`.

Ported (Wave-5 brick T2, stage 1) from the old draft's
`Algebraic-Jacobian-Challenge/AlgebraicJacobian/Picard/Pic0DualNumberCocycle.lean` §7,
re-proved against the Rebuild's pin, in the collision-safe project namespace
`TruncExpCech` (see `AlgebraicJacobian.Tangent.TruncExpUnits`).

## Main declarations

* `TruncExpCech.mapAlgHom : k[ε] →ₐ[k] A[ε]` — the functorial dual-number map over
  `algebraMap k A`.
* `TruncExpCech.baseChangeAlgEquiv : A ⊗[k] k[ε] ≃ₐ[A] A[ε]` — dual numbers under base
  change, `a ⊗ y ↦ a · ȳ`, with explicit inverse `x ↦ x.fst ⊗ 1 + x.snd ⊗ ε`
  (`baseChangeAlgEquiv_symm_apply`).

## References

Kleiman, "The Picard scheme", §5, proof of Thm 5.11 (arXiv:math/0504020).
-/

set_option autoImplicit false

universe u v

namespace TruncExpCech

open TrivSqZeroExt DualNumber TensorProduct

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]

/-- The functorial dual-number map `k[ε] → A[ε]` over the algebra map `k → A`, as a
`k`-algebra homomorphism (`mapRingHom` with its `algebraMap`-compatibility, which holds
componentwise). -/
def mapAlgHom : DualNumber k →ₐ[k] DualNumber A :=
  { mapRingHom (algebraMap k A) with
    commutes' := fun c => by
      refine TrivSqZeroExt.ext ?_ ?_ <;>
        simp [TrivSqZeroExt.algebraMap_eq_inl' k A, TrivSqZeroExt.algebraMap_eq_inl] }

@[simp]
theorem mapAlgHom_apply (x : DualNumber k) :
    mapAlgHom k A x = mapRingHom (algebraMap k A) x := rfl

/-- The base-change comparison `A ⊗[k] k[ε] →ₐ[A] A[ε]`, `a ⊗ y ↦ a · ȳ` (the
`A`-algebra map extending `mapAlgHom` along scalar extension, `AlgHom.liftEquiv`). An
isomorphism by `baseChangeAlgHom_bijective`. -/
noncomputable def baseChangeAlgHom : A ⊗[k] DualNumber k →ₐ[A] DualNumber A :=
  AlgHom.liftEquiv k A (DualNumber k) (DualNumber A) (mapAlgHom k A)

@[simp]
theorem baseChangeAlgHom_tmul (a : A) (y : DualNumber k) :
    baseChangeAlgHom k A (a ⊗ₜ[k] y) = a • mapRingHom (algebraMap k A) y := by
  simp [baseChangeAlgHom, AlgHom.liftEquiv]

/-- The base-change comparison is bijective: the two-sided inverse is the explicit
`x ↦ x.fst ⊗ 1 + x.snd ⊗ ε` (the dual numbers are finite free over the base, so no
flatness is needed). -/
theorem baseChangeAlgHom_bijective : Function.Bijective (baseChangeAlgHom k A) := by
  have hGF : Function.LeftInverse
      (fun x : DualNumber A =>
        x.fst ⊗ₜ[k] (1 : DualNumber k) + x.snd ⊗ₜ[k] (ε : DualNumber k))
      (baseChangeAlgHom k A) := by
    intro z
    dsimp only
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
        rw [baseChangeAlgHom_tmul]
        have hfst : (a • mapRingHom (algebraMap k A) y).fst = y.fst • a := by
          rw [TrivSqZeroExt.fst_smul, smul_eq_mul, fst_mapRingHom, Algebra.smul_def,
            mul_comm]
        have hsnd : (a • mapRingHom (algebraMap k A) y).snd = y.snd • a := by
          rw [TrivSqZeroExt.snd_smul, smul_eq_mul, snd_mapRingHom, Algebra.smul_def,
            mul_comm]
        rw [hfst, hsnd, smul_tmul, smul_tmul, ← TensorProduct.tmul_add]
        congr 1
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp
    | add z₁ z₂ ih₁ ih₂ =>
        rw [map_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
          TensorProduct.add_tmul, TensorProduct.add_tmul, add_add_add_comm, ih₁, ih₂]
  have hFG : Function.RightInverse
      (fun x : DualNumber A =>
        x.fst ⊗ₜ[k] (1 : DualNumber k) + x.snd ⊗ₜ[k] (ε : DualNumber k))
      (baseChangeAlgHom k A) := by
    intro x
    dsimp only
    rw [map_add, baseChangeAlgHom_tmul, baseChangeAlgHom_tmul]
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [smul_eq_mul]
  exact ⟨hGF.injective, hFG.surjective⟩

/-- **Dual numbers under base change** (substrate piece (i), algebra core): for a
`k`-algebra `A`, extension of scalars of the dual numbers is the dual numbers of `A` —
`A ⊗[k] k[ε] ≃ₐ[A] A[ε]`, `a ⊗ y ↦ a · ȳ`. Composed with Mathlib's `pullbackSpecIso`
(equivalently, the Rebuild's `Over.sectionsBaseChange` at `A = k[ε]`), this identifies
the sections of a base-changed affine chart `V × Spec k[ε]` with `Γ(V, 𝒪)[ε]` — the
section rings the two-chart unit-cocycle engine consumes. -/
noncomputable def baseChangeAlgEquiv : A ⊗[k] DualNumber k ≃ₐ[A] DualNumber A :=
  AlgEquiv.ofBijective (baseChangeAlgHom k A) (baseChangeAlgHom_bijective k A)

@[simp]
theorem baseChangeAlgEquiv_tmul (a : A) (y : DualNumber k) :
    baseChangeAlgEquiv k A (a ⊗ₜ[k] y) = a • mapRingHom (algebraMap k A) y :=
  baseChangeAlgHom_tmul k A a y

/-- The inverse of the base-change comparison, explicitly:
`x ↦ x.fst ⊗ 1 + x.snd ⊗ ε`. -/
theorem baseChangeAlgEquiv_symm_apply (x : DualNumber A) :
    (baseChangeAlgEquiv k A).symm x
      = x.fst ⊗ₜ[k] (1 : DualNumber k) + x.snd ⊗ₜ[k] (ε : DualNumber k) := by
  apply (baseChangeAlgEquiv k A).injective
  rw [AlgEquiv.apply_symm_apply, map_add, baseChangeAlgEquiv_tmul,
    baseChangeAlgEquiv_tmul]
  refine (TrivSqZeroExt.ext ?_ ?_).symm <;> simp [smul_eq_mul]

end TruncExpCech
