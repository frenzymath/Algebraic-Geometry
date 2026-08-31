/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignHinjChart
import AlgebraicJacobian.Picard.DivSchemeSeedUnivAssembleKappa
import AlgebraicJacobian.Picard.DivSchemeSeedUnivRes
import AlgebraicJacobian.Picard.SlicingFlatKernel

/-!
# DD-4 — the carve pin `hinj_chart` (BUILD, probe stage)

Probe of the residue-field `k`-tower synthesis at `κ(p)` over `R_Z = DivCarveChartRing`
before assembling the three-step carve pin.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace ThetaGeneratorSeed

section CarvePin

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftCarvePin : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(Scheme.divisorSections k ((windowS_choice π hπ g • fiberWeilDivisor π)
    + (windowM_choice π hπ g • fiberWeilDivisor π)) ⊤))
variable (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)

/-- The `Z(♦)`-chart ring in the seed context (`R_Z`). -/
abbrev seedChartRing : Type u :=
  DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j

/-! ## Step 1 — the window transport at `κ(p)`

The residue-field `k`-tower `k → R_Z → κ(p)` at a prime `p` of the (quotient) carve
chart ring `R_Z` is a **native** tower (`κ(p)` is `R_Z`'s residue field, `R_Z` is a
`k`-algebra by the quotient instance), *not* a `RingHom.toAlgebra` composite: the
`Algebra k κ(p)`/`IsScalarTower k R_Z κ(p)` instances synthesize without a composite
`letI`.  They exceed the default whnf/synth budgets (the I-0255 class) but terminate;
the escalation below is a budget bump, not a workaround. -/

set_option maxHeartbeats 2000000 in
-- native (non-composite) `k → R_Z → κ(p)` residue-field tower over the quotient carve
-- chart ring; the tower terminates but exceeds default whnf/synth budgets (I-0255 class)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
/-- **Step 1 — window transport at `κ(p)`**: the base-change transport (through the
chart-ring iso `relPinnedTermBaseChangeAlg`) of the reading `relThetaResSide` of a
relative window section `Θ x = relThetaWindowEquiv x` is the reading of the **fibre**
window section `Θ_{κ(p)}(windowCompare x)` of the compared vector.  This composes
`relPinnedTermBaseChangeAlg_one_tmul` (`1 ⊗ s ↦ relPinnedSectionsMap s`) with the chart
crux triangle `relPinnedSectionsMap_relThetaResSide_windowEquiv` at `κ(p)` over `R_Z`,
so `f_V ⊗ κ(p)` moves to compared-window fibre readings. -/
theorem relPinnedTermBaseChangeAlg_reading_windowEquiv
    (p : PrimeSpectrum (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)) (b : Bool)
    (x : (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) ⊗[k]
      ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    relPinnedTermBaseChangeAlg C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)
        p.asIdeal.ResidueField π b
        ((1 : p.asIdeal.ResidueField) ⊗ₜ[seedChartRing C hπ g r₁ r₂ b₁ b₂ i j]
          relThetaResSide (windowM_choice π hπ g) b le_rfl
            (relThetaWindowEquiv C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π
              (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x))
      = relThetaResSide (windowM_choice π hπ g) b le_rfl
          (relThetaWindowEquiv C p.asIdeal.ResidueField π (windowM_choice π hπ g)
            (relThetaPairH1_windowM C π hπ g)
            (windowCompare (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)
              p.asIdeal.ResidueField x)) :=
  (relPinnedTermBaseChangeAlg_one_tmul C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)
      p.asIdeal.ResidueField π b _).trans
    (relPinnedSectionsMap_relThetaResSide_windowEquiv C
      (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) p.asIdeal.ResidueField π
      (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) b x)

end CarvePin

end ThetaGeneratorSeed

end AlgebraicGeometry
