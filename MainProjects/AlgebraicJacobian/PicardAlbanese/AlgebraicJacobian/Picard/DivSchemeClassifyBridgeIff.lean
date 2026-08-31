/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeClassifyBridge

/-!
# DDR-6 §3a′ — the coordinate transfer of the ε-carve (split for memory)

`carvePairArrow_divCarveMul_eq_zero_iff`: the carve `(♦)` in DDR-2's `windowShiftMul`
spelling holds iff it holds for the coordinate images under the boundary bases at the
carve-ideal multiplier `divCarveMul`.  Own compilation unit (see
`informal/spec-w4-gates.md` memory discipline).
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

section Curve

open Scheme

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftClassifyIff :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant π]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

variable (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(divisorSections k
    ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤))

variable {S : Type u} [CommRing S] [Algebra k S]

/-- **The coordinate transfer of the ε-carve**: the carve `(♦)` for a submodule pair in
the abstract window ambients (DDR-2's `windowShiftMul` spelling) holds iff it holds for
the coordinate images under the boundary bases at the carve-ideal multiplier
`divCarveMul`. -/
theorem carvePairArrow_divCarveMul_eq_zero_iff
    (K₁ : Submodule S (TensorProduct k S
      ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)))
    (K₂ : Submodule S (TensorProduct k S
      ↥(divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)))
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    carvePairArrow (divCarveMul k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm) a)
        (K₁.map (LinearMap.baseChange S b₁.equivFun.toLinearMap))
        (K₂.map (LinearMap.baseChange S b₂.equivFun.toLinearMap)) = 0
      ↔ carvePairArrow (windowShiftMul hπ g a) K₁ K₂ = 0 := by
  rw [divCarveMul_basis_map]
  exact Grassmannian.carvePairArrow_map_baseChange_eq_zero_iff
    b₁.equivFun b₂.equivFun (windowShiftMul hπ g a) K₁ K₂



end Curve

end AlgebraicGeometry
