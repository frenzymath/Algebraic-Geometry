/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeClassify

/-!
# DDR-6 §3a — the multiplier bridge (split from `DivSchemeClassify.lean`)

The campaign-spelling bridge between DDR-2's `windowShiftMul` and DDR-1's
`divCarveMul`: `windowShiftEquiv`/`windowShiftMul_eq` (the window-shift reindexing),
`divCarveMul_basis_map` (the multiplier bridge at the boundary bases) and
`carvePairArrow_divCarveMul_eq_zero_iff` (the coordinate transfer of the ε-carve).
Split into its own compilation unit for memory (the two bridge proofs dominate the
elaboration footprint of the original file; see `informal/spec-w4-gates.md` memory
discipline).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

open Grassmannian

/-! ## The abstract multiplier bridge

Proved on opaque module variables so the campaign instantiation below is a single
term-mode application — no rewriting under the window-typed composites (the original
`rw`+`simp` proof at the campaign types exceeded the machine's memory; see
`informal/spec-w4-gates.md` memory discipline and inbox I-0227). -/

section CoordBridge

variable {k : Type u} [Field k]
variable {V₁ V₂ V₂' : Type u}
variable [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
variable [AddCommGroup V₂'] [Module k V₂']

/-- The coordinate conjugate of a composite through a transported basis: conjugating
`μ` by `b₁`/`b₂.map e.symm` coordinates equals conjugating `e ∘ₗ μ` by `b₁`/`b₂`
coordinates. -/
theorem equivFun_map_symm_comp_comp {n₁ n₂ : ℕ} (b₁ : Module.Basis (Fin n₁) k V₁)
    (b₂ : Module.Basis (Fin n₂) k V₂') (e : V₂ ≃ₗ[k] V₂') (μ : V₁ →ₗ[k] V₂) :
    (b₂.map e.symm).equivFun.toLinearMap ∘ₗ μ ∘ₗ b₁.equivFun.symm.toLinearMap
      = b₂.equivFun.toLinearMap ∘ₗ (e.toLinearMap ∘ₗ μ)
          ∘ₗ b₁.equivFun.symm.toLinearMap := by
  rw [Module.Basis.map_equivFun, LinearEquiv.symm_symm]
  simp only [LinearEquiv.coe_trans, LinearMap.comp_assoc]

end CoordBridge

/-! ## §3 The campaign spelling: `divClassifyAff` -/

section Curve

open Scheme

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftClassify :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant π]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

/-- **The window-shift reindexing** `H⁰(𝒪(s·F + M·F)) = H⁰(𝒪((M+s)·F))`: the section
spaces of the two spellings of the shifted window divisor.  `windowShiftMul` is the
section multiplication followed by this reindexing (`windowShiftMul_eq`); the second
DD-4 boundary basis of `DivScheme` is transported along its inverse. -/
noncomputable def windowShiftEquiv (g : ℕ) :
    ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π
        + windowM_choice π hπ g • fiberWeilDivisor π) ⊤) ≃ₗ[k]
      ↥(divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤) :=
  LinearEquiv.ofEq _ _ (congrArg (fun D => divisorSections k D ⊤)
    (by rw [add_nsmul]; exact add_comm _ _))

/-- DDR-2's window-shift multiplier is the section multiplication followed by the
window-shift reindexing — definitional. -/
theorem windowShiftMul_eq (g : ℕ)
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    windowShiftMul hπ g a
      = (windowShiftEquiv hπ g).toLinearMap
          ∘ₗ sectionMulBilin k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) a :=
  rfl

variable (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(divisorSections k
    ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤))

/-- **The multiplier bridge** (DDR-1 meets DDR-2): the coordinate multiplier
`divCarveMul` of the carve ideal, at the boundary bases `b₁` and
`b₂.map (windowShiftEquiv …).symm`, is the conjugate of DDR-2's `windowShiftMul` by
the basis coordinate equivalences.  Term-mode instance of the abstract bridge:
`divCarveMul` delta-unfolds to the abstract LHS and `windowShiftMul` is
definitionally `(windowShiftEquiv …).toLinearMap ∘ₗ sectionMulBilin …`
(`windowShiftMul_eq` is `rfl`), so no rewriting happens at the campaign types. -/
theorem divCarveMul_basis_map
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    divCarveMul k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm) a
      = b₂.equivFun.toLinearMap ∘ₗ windowShiftMul hπ g a
          ∘ₗ b₁.equivFun.symm.toLinearMap :=
  equivFun_map_symm_comp_comp b₁ b₂ (windowShiftEquiv hπ g)
    (sectionMulBilin k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) a)


end Curve

end AlgebraicGeometry
