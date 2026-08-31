/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignFreeFlatChart
import AlgebraicJacobian.Picard.DivSchemeRedesignCascade

/-!
# DD-4 redesign — RD-N step 1: the unconditional chart-level `J`-flat at the seed

The chart-level free-codomain flat `forall_flat_colength_quotient_of_hsub_free`
(`Picard/DivSchemeRedesignFreeFlatChart.lean`, I-0301) consumes the carve pin `hsub_chart`
(`Picard/DivSchemeRedesignHsubChartPin.lean`, I-0299), which is itself threaded on two
hypotheses: `hχ` (the genus condition `χ = 1 − g`, campaign-fixed) and `hη` (the generic
point of every residue-fibre curve lies in the pinned chart).  The latter is **landed
unconditionally** as `genericPoint_mem_relPinnedChart` (`Picard/DivSchemeRedesignCascade.lean`,
I-0300).

This file discharges `hη` at the seed base ring `R_Z = DivCarveChartRing …` and threads it
into the chart flat, producing the **unconditional (bar `hχ`) chart-level `J`-flatness**

`Module.Flat R_Z (Γ(V) ⧸ range (chartReadMap divUniversalSeedK b))`,

the exact `hflat` shape the relative-local-BPF stalk Nakayama `RD-N` and the non-circular
certificate consume (`Picard/DivSchemeRedesignJFlat.lean` doc, I-0289 §1.4).  `hχ` is the
only remaining hypothesis — the campaign genus/χ fact threaded identically through the
achiever (`exists_relThetaWindowEquiv_mem_divUniversalSeedK_achieves_seedPrime`, I-0291) and
`hsub_chart`.

This is I-0289 build step 1 ("`hχ` discharge so `hsub_chart` becomes unconditional and the
chart flat fires") — the foundational RD-N input, landed as a standalone keystone with the
anti-circular ordering `hsub_chart → hη → flat` preserved (no `IsGenerator`/`IsCertified`/
`seedUniv'`/`h z` consumed).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

namespace ThetaGeneratorSeed

section ChartFlat

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftRDN : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
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

set_option maxHeartbeats 2000000 in
-- applying the landed `hsub_chart` (itself elaborated at 2M) at the native residue-field
-- tower `k → R_Z → κ(p)` over the composite carve chart ring, then the free-codomain flat,
-- re-synthesizes the heavy relCurve/base-change instances past the defaults (I-0295 class)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- **RD-N step 1 — the unconditional chart-level `J`-flat at the seed** (I-0289 build step 1):
at the seed base ring `R_Z = seedChartRing`, the chart base-ideal colength
`Γ(V) ⧸ range (chartReadMap divUniversalSeedK b)` is `R_Z`-flat, gated only on the campaign
genus condition `hχ`.

Threads the landed `hη` discharge (`genericPoint_mem_relPinnedChart`, I-0300) into the carve
pin `hsub_chart` (I-0299), making it unconditional bar `hχ`, then feeds it to the chart-level
free-codomain flat `forall_flat_colength_quotient_of_hsub_free` (I-0301).  `divUniversalSeedK`
is a finite `R_Z`-module (`finite_divUniversalSeedK`).  This is the exact chart-level `hflat`
shape RD-N and the non-circular certificate consume — the `k[ε]` trap (I-0231) ruled out by
this flatness. -/
theorem flat_chart_colength_divUniversalSeedK (b : Bool)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    Module.Flat (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)
      (Γ(relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j),
          relPinnedChart C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π b)
        ⧸ LinearMap.range (chartReadMap (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b)) := by
  haveI : Module.Finite (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)
      ↥(divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) :=
    finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  exact forall_flat_colength_quotient_of_hsub_free
    (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b
    (hsub_chart C hπ g r₁ r₂ b₁ b₂ i j b hχ
      (fun p => genericPoint_mem_relPinnedChart C π b p.asIdeal.ResidueField))

end ChartFlat

end ThetaGeneratorSeed

end AlgebraicGeometry
