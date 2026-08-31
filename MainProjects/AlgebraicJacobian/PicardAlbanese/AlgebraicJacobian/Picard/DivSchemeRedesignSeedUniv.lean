/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUnivFacts
import AlgebraicJacobian.Picard.DivSchemeRedesignRDNChart
import AlgebraicJacobian.Picard.DivSchemeRedesignSeed
import AlgebraicJacobian.Picard.DivSchemeRedesignCarvePin

/-!
# DD-4 redesign — the concrete universal seed `seedUniv'` and its generator clause

The redesigned universal theta generator seed (`informal/spec-dd4-redesign.md` §1.5, landing
note I-0289/I-0292): the value `seedUniv'` at the `Z(♦)`-chart ring `R_Z = seedChartRing` and
the embedding window `K_univ = divUniversalSeedK`, whose

* `side`/`sec`/`sec_mem` are the **landed** universal seed's (`seedUniv`, I-0278) — the section
  `sec z` is the relative achiever window image (fibrewise nonzero, in `K_univ`);
* `h z` is the **ann-based fibre-cutter** (redesign brick 3, `DivSchemeRedesignRDNChart.lean`):
  a genuine relative fibre-cutter in `ann(N z)` (with `N z = chartColengthModule`), replacing
  the old base-pullback `h z = algebraMap f` that made `D(h z)` the whole fibre chart (I-0288).

The cutter `h z` is produced by the ann-cutter engine from **RD-N proper** — the support
avoidance `primeIdealOf z ∉ Module.support Γ(V) (N z)` — threaded here as the hypothesis
`hrdn` (the honest remaining geometric wall, I-0302 §residual 2b/2c; identically to how the
flat and achiever are gated on `hχ`).

* `seedUniv'` — the concrete redesigned seed (`hrdn`-gated).
* `isGenerator_seedUniv'` — `seedUniv'.IsGenerator`, via the redesigned finale
  `isGenerator_of_ann_cutter`: the DIRECT `hdvd` (`hann`) is **discharged** from the ann-cutter
  (the `hann` containment `h z · read ψ ∈ ⟨read sec z⟩` is the ann-cutter's defining property,
  through the ann→hdvd bridge `forall_mul_read_mem_span_of_forall_smul_eq_zero`); the fibre
  nonvanishing `hfib` (the achiever's fibrewise nonzero reading on the cutter neighbourhood,
  the analogue of the landed `seedUniv_hfib` with the ann-cutter in the premise) is threaded.

Anti-circular: certificate-free, `IsCertified`/`certifiedFamily`-free.  Order preserved
`flat(landed) → RD-N(gated `hrdn`) → seedUniv'(here) → isGenerator(here) → certificate → U1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace ThetaGeneratorSeed

section SeedUnivRedesign

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftSeedUnivRD : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

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
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

set_option maxHeartbeats 2400000 in
-- the seed structure projection over the heavy `DivCarveChartRing`/`relCurve` chart types
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Every point lies in its `seedUniv` covering chart (`piece_le` composed with `mem_piece`).
The `hz` input the ann-cutter and the RD-N support-prime consume. -/
theorem seedUniv_mem_chart
    (z : relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)) :
    z ∈ relPinnedChart C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π
      ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) :=
  (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).piece_le z
    ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).mem_piece z)

set_option maxHeartbeats 2400000 in
-- the colength type spells out the heavy `DivCarveChartRing`/window/`relThetaSections` types
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- **The concrete colength `N z` of the universal seed** (I-0302 §residual 2a at `R_Z`): the
chart-level colength `chartColengthModule` at the covering chart `seedUniv.side z` and the
achiever section `seedUniv.sec z`.  Its support-avoidance is the seed's RD-N. -/
noncomputable def seedUnivColength
    (z : relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)) :
    Submodule Γ(relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j),
        relPinnedChart C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π
          ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z))
      (Γ(relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j),
          relPinnedChart C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)) ⧸
        Ideal.span {relThetaResSide (windowM_choice π hπ g)
          ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) (le_rfl)
          ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z)}) :=
  chartColengthModule (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)
    ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)
    ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z)

set_option maxHeartbeats 2400000 in
-- the RD-N support type spells out the heavy chart section-ring / `Module.support` over `R_Z`
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- **RD-N proper for the universal seed** (the `hrdn` hypothesis): at every point `z`, the
seed colength `seedUnivColength z` avoids the module-stalk prime of `z` — i.e.
`read sec z` generates the base ideal `J z` at the stalk `𝒪_z` (the achiever cuts exactly
`d_p`, so `z` is not an extra zero).  The honest remaining geometric wall (I-0302 §residual
2b/2c: the achiever fibre-generation + landed chart flat via the `κ(p)→𝒪_z` transport). -/
abbrev SeedUnivRDN : Prop :=
  ∀ z : relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j),
    (isAffineOpen_relPinnedChart C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π
        ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)).primeIdealOf
        ⟨z, seedUniv_mem_chart C hπ g r₁ r₂ b₁ b₂ i j hO hχ z⟩ ∉
      Module.support Γ(relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j),
          relPinnedChart C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z))
        ↥(seedUnivColength C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)

set_option maxHeartbeats 2400000 in
-- the seed base ring `R_Z = DivCarveChartRing …`, the `κ(p)` tower, and the finite window
-- module re-elaborate the heavy chart section-ring / support instances past the defaults
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- **The ann-based cutter existence at the universal seed** (from RD-N): at every `z`, a
section `h ∈ Γ(V)` with `z ∈ D(h)` and the ann containment `h · read ψ ∈ ⟨read sec z⟩` for
every `ψ ∈ K_univ`.  Packages `exists_h_mem_basicOpen_forall_mul_read_mem_span` with the
window finiteness `finite_divUniversalSeedK`. -/
theorem exists_seedUniv'_h (hrdn : SeedUnivRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ)
    (z : relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)) :
    ∃ h : Γ(relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j),
        relPinnedChart C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π
          ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)),
      z ∈ (relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)).basicOpen h ∧
      ∀ ⦃ψ : relThetaSections C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π
          (windowM_choice π hπ g)⦄, ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j →
        h * relThetaResSide (windowM_choice π hπ g)
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) (le_rfl) ψ
          ∈ Ideal.span {relThetaResSide (windowM_choice π hπ g)
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) (le_rfl)
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z)} := by
  haveI := finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  exact exists_h_mem_basicOpen_forall_mul_read_mem_span
    (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)
    ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)
    ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z)
    (seedUniv_mem_chart C hπ g r₁ r₂ b₁ b₂ i j hO hχ z) (hrdn z)

set_option maxHeartbeats 2400000 in
-- the seed structure fields carry the huge `DivCarveChartRing`/window/`relThetaSections`
-- types; the field-dependency substitution re-elaborates them (recorded hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- **`seedUniv'`** (I-0292 residual 1, the concrete redesigned seed): the universal theta
generator seed over `R_Z` at `K_univ` whose `side`/`sec`/`sec_mem` are the landed `seedUniv`'s
(the relative achiever) and whose `h z` is the **ann-based fibre-cutter** produced from RD-N
(`exists_seedUniv'_h`).  The genuine relative cutter dissolving I-0288's razor. -/
noncomputable def seedUniv' (hrdn : SeedUnivRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ) :
    ThetaGeneratorSeed C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π (windowM_choice π hπ g)
      (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) where
  side := fun z => (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z
  h := fun z => (exists_seedUniv'_h C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose
  mem_basicOpen := fun z =>
    (exists_seedUniv'_h C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose_spec.1
  sec := fun z => (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z
  sec_mem := fun z => (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec_mem z

set_option maxHeartbeats 2400000 in
-- the `isGenerator_of_ann_cutter` finale over the seed structure literal re-elaborates the
-- heavy `DivCarveChartRing`/window types past the defaults (recorded hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- **`isGenerator_seedUniv'`** (I-0292 residual 1, the redesigned finale): the concrete
redesigned seed is a `ThetaGeneratorSeed.IsGenerator`, via `isGenerator_of_ann_cutter`.

The DIRECT `hdvd` (`hann`) is **discharged**: `seedUniv'.h z` is the ann-cutter, whose defining
property (from `exists_seedUniv'_h`) is exactly the ann containment `h z · read ψ ∈ ⟨read sec z⟩`
that `isGenerator_of_ann_cutter` consumes — no per-fibre `hfield`, no fibrewise-ker-span
capstone.  The fibre nonvanishing `hfib` (the achiever's fibrewise-nonzero reading on the
cutter neighbourhood, the analogue of the landed `seedUniv_hfib` with the ann-cutter in the
premise) is threaded — the second honest input alongside RD-N (`hrdn`). -/
theorem isGenerator_seedUniv' (hrdn : SeedUnivRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ)
    (hfib : ∀ (z : relCurve C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j))
      (p : PrimeSpectrum (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)),
      ((relCurve C p.asIdeal.ResidueField).basicOpen
          (relPinnedSectionsMap C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)
            p.asIdeal.ResidueField π
            ((seedUniv' C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).side z)
            ((seedUniv' C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).h z)) :
        (relCurve C p.asIdeal.ResidueField).Opens) ≠ ⊥ →
      relPinnedSectionsMap C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) p.asIdeal.ResidueField π
        ((seedUniv' C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).side z)
        (relThetaResSide (windowM_choice π hπ g)
          ((seedUniv' C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).side z) (le_rfl)
          ((seedUniv' C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).sec z)) ≠ 0) :
    (seedUniv' C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).IsGenerator :=
  isGenerator_of_ann_cutter (seedUniv' C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn)
    (fun z _ψ hψ => (exists_seedUniv'_h C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose_spec.2 hψ)
    hfib

end SeedUnivRedesign

end ThetaGeneratorSeed

end AlgebraicGeometry
