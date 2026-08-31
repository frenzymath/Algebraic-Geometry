/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUnivBridge
import AlgebraicJacobian.Picard.DivSchemeSeedUnivAssembleKappa
import AlgebraicJacobian.Picard.DivSchemeFamily
import AlgebraicJacobian.Picard.DivSchemeRelDivisor

/-!
# G-4 — the universal theta generator seed `seedUniv` (I-0278 decomposition)

The pointwise assembly of the universal `ThetaGeneratorSeed` over the `Z(♦)`-chart ring
`R_Z = DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j` at the embedding window `K_univ`.  Per
I-0278, `ThetaGeneratorSeed` has five *pointwise* fields (`side`/`h`/`mem_basicOpen`/`sec`/
`sec_mem`) with no global-consistency constraint, so the seed is a **pointwise
classical-choice construction** over the three geometric sub-lemmas landed here:

* `exists_mem_relPinnedChart` — **(a) the two-chart cover**: every point of the relative
  curve lies in one of the two pinned charts (`relCover_sup`);
* `divUniversalFibreKM_ne_bot_seedPrime` — the fibre window at every seed-base prime is
  nonzero (`finrank_divUniversalFibreKM_add` + `deg N ≥ 2g` Riemann–Roch), the `≠ ⊥`
  input the seed-prime bridge consumes;
* `exists_sec_windowCompare_ne_zero_seedPrime` — **(b) the seed section**: at every prime
  a window vector with nonzero fibre comparison whose window image lies in `K_univ`
  (the landed seed-prime bridge of `Picard/DivSchemeSeedUnivBridge.lean`);
* `exists_h_mem_basicOpen_windowCompare` — **(c) the base→curve shrink**: a chart section
  `h` with `z ∈ D(h)` cut out as the base-open pullback of a `windowCompare`-surviving
  base element (`exists_forall_windowCompare_ne_zero` + `notMem_basePrime_iff`);
* `seedUniv` — the assembled seed via `Classical.choose` per point.
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
attribute [local instance 10000] relCurve.instOver

/-! ## (a) The two-chart cover of the relative curve -/

section Cover

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

/-- **(a) The two-chart cover** (I-0278 sub-lemma (a)): every point of the relative curve
`C_R` lies in one of the two pinned charts `relPinnedChart C R π b` (`b : Bool`).  Immediate
from `relCover_sup` (`V₀ ⊔ V₁ = ⊤`): the pinned charts are exactly `V₀`/`V₁`, and their
join is the whole curve. -/
theorem exists_mem_relPinnedChart (z : relCurve C R) :
    ∃ b : Bool, z ∈ relPinnedChart C R π b := by
  have hz : z ∈ (relPinnedChart C R π false ⊔ relPinnedChart C R π true) := by
    rw [relPinnedChart_false, relPinnedChart_true, relCover_sup]
    exact TopologicalSpace.Opens.mem_top z
  rcases (TopologicalSpace.Opens.mem_sup).mp hz with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

end Cover

/-! ## The base→curve basic-open shrink -/

section Shrink

/-- **The base→curve basic-open shrink** (the geometric core of I-0278 sub-lemma (c)): for
a scheme `X` over `Spec R` and a point `z ∈ U`, the pullback `algebraMap R Γ(X,U) f` of a
base element `f` outside the base point of `z` (the contraction of the maximal ideal of the
stalk, `basePrime` of the germ) cuts a basic open still containing `z`.  Directly:
`z ∈ D(algebraMap f)` iff the germ of `algebraMap f` is a unit (`mem_basicOpen`), which is
exactly `f ∉ basePrime(germ_z)` (`notMem_basePrime_iff`). -/
theorem mem_basicOpen_algebraMap_of_notMem_basePrime {R : Type u} [CommRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] {U : X.Opens} {z : X} (hz : z ∈ U) (f : R)
    (hf : f ∉ (basePrime (R := R) (X.presheaf.germ U z hz).hom).asIdeal) :
    z ∈ X.basicOpen (algebraMap R Γ(X, U) f) := by
  rw [X.mem_basicOpen (algebraMap R Γ(X, U) f) z hz]
  exact (notMem_basePrime_iff _).mp hf

end Shrink

/-! ## The seed-prime context: fibre-window nonvanishing, `sec`, and the shrink -/

section SeedGen

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftSeedGen : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

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

-- The fibre-curve package at every field extension (the `DivSchemeMonoBridgeRel` pack).
noncomputable local instance instIsIntegralRelCurveSeedGen (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveSeedGen (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveSeedGen (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveSeedGen (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveSeedGen (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveSeedGen (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

set_option maxHeartbeats 2400000 in
-- the seed-base residue-field tower `k → R_{I,J} → R_Z → κ(p)` drives the finrank/`windowN`
-- instance chains past the defaults (the recorded `divUniversal_carve_residueField` hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
include hO hχ in
/-- **The fibre window is nonzero at every seed-base prime** (the `≠ ⊥` input of the
seed-prime bridge): at any prime `p` of `R_Z`, the first fibre window
`divUniversalFibreKM … κ(p)` contains a nonzero section.  Its `κ(p)`-dimension is
`h⁰(𝒪(N)) − g` (`finrank_divUniversalFibreKM_add`), and Riemann–Roch on the fibre curve
gives `h⁰(𝒪(N)) = deg N + 1 − g ≥ 2g + 1 − g = g + 1 > g` (`deg N ≥ 2g` by
`two_mul_genus_le_deg_windowN`), so the dimension is `≥ 1`. -/
theorem exists_mem_ne_zero_divUniversalFibreKM_seedPrime
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    ∃ f ∈ divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField, f ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
  have hfr := finrank_divUniversalFibreKM_add C hπ g r₁ r₂ b₁ i j
    p.asIdeal.ResidueField hχ
  rw [hbot, finrank_bot] at hfr
  -- `h⁰(𝒪(N)) : ℤ = deg N + χ`, `χ = 1 − g`, `2g ≤ deg N`
  have he := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := p.asIdeal.ResidueField)
    (windowN C p.asIdeal.ResidueField hπ g)
    (subsingleton_h1_windowN C p.asIdeal.ResidueField hπ g)
  have hchi := chi_relCurve_baseField C p.asIdeal.ResidueField g hχ
  have hdeg := two_mul_genus_le_deg_windowN C p.asIdeal.ResidueField hπ g hO hχ
  rw [hchi] at he
  omega

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
/-- The first universal fibre window is nonzero at every seed prime when its
Grassmannian corank is the divisor degree `g` and `chi(O) = 1 - gamma` with
`gamma ≤ g`. -/
theorem exists_mem_ne_zero_divUniversalFibreKM_seedPrime_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    ∃ f ∈ divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField, f ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
  have hfr := finrank_divUniversalFibreKM_add_at C hπ g r₁ r₂ b₁ i j
    p.asIdeal.ResidueField hχ
  rw [hbot, finrank_bot] at hfr
  have he := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := p.asIdeal.ResidueField)
    (windowN C p.asIdeal.ResidueField hπ g)
    (subsingleton_h1_windowN C p.asIdeal.ResidueField hπ g)
  have hchi := chi_relCurve_baseField C p.asIdeal.ResidueField gamma hχ
  have hdeg := two_mul_degree_le_deg_windowN C p.asIdeal.ResidueField hπ g
  rw [hchi] at he
  omega

set_option maxHeartbeats 2400000 in
-- the seed-base residue-field tower drives the `windowCompare`/`relThetaWindowEquiv` defeq
-- past the defaults (the recorded `divUniversal_carve_residueField` hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- **(b) The universal seed section at every seed-base prime** (I-0278 sub-lemma (b)):
combining the fibre-window nonvanishing (`exists_mem_ne_zero_divUniversalFibreKM_seedPrime`)
with the landed seed-prime bridge, at every prime `p` of `R_Z` there is a universal window
vector `x ∈ divUniversalFstWindow` with nonzero fibre comparison `windowCompare … ≠ 0`
whose window image `relThetaWindowEquiv … x` lies in `K_univ = divUniversalSeedK`. -/
theorem exists_sec_windowCompare_ne_zero_seedPrime
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    ∃ x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule,
      windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          p.asIdeal.ResidueField x ≠ 0 ∧
      relThetaWindowEquiv C
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x
        ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j := by
  obtain ⟨f, hf_mem, hf_ne⟩ :=
    exists_mem_ne_zero_divUniversalFibreKM_seedPrime C hπ g r₁ r₂ b₁ b₂ i j hO hχ p
  exact exists_relThetaWindowEquiv_mem_divUniversalSeedK_windowCompare_ne_zero_seedPrime
    C hπ g r₁ r₂ b₁ b₂ i j p hf_mem hf_ne

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- A universal first-window vector with nonzero residue comparison at curve parameter
`gamma ≤ g`. -/
theorem exists_sec_windowCompare_ne_zero_seedPrime_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    ∃ x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule,
      windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          p.asIdeal.ResidueField x ≠ 0 ∧
      relThetaWindowEquiv C
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x
        ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j := by
  obtain ⟨f, hf_mem, hf_ne⟩ :=
    exists_mem_ne_zero_divUniversalFibreKM_seedPrime_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p
  exact exists_relThetaWindowEquiv_mem_divUniversalSeedK_windowCompare_ne_zero_seedPrime
    C hπ g r₁ r₂ b₁ b₂ i j p hf_mem hf_ne

set_option maxHeartbeats 2400000 in
-- the seed-base residue-field tower drives the `windowCompare`/`relThetaWindowEquiv` and
-- `basePrime` germ defeq past the defaults (the `divUniversal_carve_residueField` hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- **(c) The pointwise seed data** (I-0278 sub-lemma (c), the base→curve shrink threaded
onto the seed section): at every point `z` of the relative curve `C_R_Z`, a pinned chart
side `b`, a universal window vector `x`, and a base element `f` such that

* `x ∈ divUniversalFstWindow` and its window image lies in `K_univ` (`sec_mem`);
* the base-open pullback `algebraMap f` cuts a basic open still containing `z`
  (`mem_basicOpen`, from the shrink `mem_basicOpen_algebraMap_of_notMem_basePrime` at the
  base point `p = basePrime(germ_z)`);
* `windowCompare … x` survives at every prime of `D(f)` (`hsurvive`, the base-locus
  keeper `exists_forall_windowCompare_ne_zero`).

The side/section/base-open of `seedUniv`; `hsurvive` (with `sec = relThetaWindowEquiv … x`
and `h = algebraMap f`) is the fibre-regularity coherence the `hfib` clause consumes. -/
theorem exists_seedPoint
    (z : relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    ∃ (b : Bool)
      (x : TensorProduct k
        (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
        ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
      (f : DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
      x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule ∧
      z ∈ (relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).basicOpen
        (algebraMap (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          Γ(relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
            relPinnedChart C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) π b) f) ∧
      relThetaWindowEquiv C
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x
        ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j ∧
      ∀ q : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
        f ∉ q.asIdeal →
        windowCompare
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            q.asIdeal.ResidueField x ≠ 0 := by
  obtain ⟨b, hzb⟩ := exists_mem_relPinnedChart (C := C) (π := π) z
  set p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) :=
    basePrime (R := DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
      ((relCurve C _).presheaf.germ (relPinnedChart C _ π b) z hzb).hom with hp
  obtain ⟨x, hx_mem, hx_ne, hsec_mem⟩ :=
    exists_sec_windowCompare_ne_zero_seedPrime C hπ g r₁ r₂ b₁ b₂ i j hO hχ p
  obtain ⟨f, hf_notMem, hf_survive⟩ :=
    exists_forall_windowCompare_ne_zero C hπ g r₁ r₂ b₁ b₂ i j x p hx_ne
  exact ⟨b, x, f, hx_mem,
    mem_basicOpen_algebraMap_of_notMem_basePrime hzb f hf_notMem, hsec_mem, hf_survive⟩

set_option maxHeartbeats 2400000 in
-- the seed structure fields carry the huge `DivCarveChartRing`/`relThetaSections`/window
-- types; the field-dependency substitution re-elaborates them (recorded hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- **`seedUniv`** (I-0278): the universal theta generator seed over the `Z(♦)`-chart ring
`R_Z` at the embedding window `K_univ = divUniversalSeedK`.  Assembled pointwise by
`Classical.choose` on `exists_seedPoint`: the side is the covering chart, the base-open is
the base→curve pullback `algebraMap f` of the `windowCompare`-surviving base element, and
the section is the window image `relThetaWindowEquiv … x` (in `K_univ` by the seed-prime
bridge).  This is the seed the DDR-3 assembly (`isGenerator_of_fibre_ne_zero` → the local
divisor) consumes. -/
noncomputable def seedUniv :
    ThetaGeneratorSeed C
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
      π (windowM_choice π hπ g) (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) where
  side := fun z => (exists_seedPoint C hπ g r₁ r₂ b₁ b₂ i j hO hχ z).choose
  h := fun z => algebraMap
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
      Γ(relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
        relPinnedChart C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) π
          (exists_seedPoint C hπ g r₁ r₂ b₁ b₂ i j hO hχ z).choose)
      (exists_seedPoint C hπ g r₁ r₂ b₁ b₂ i j hO hχ z).choose_spec.choose_spec.choose
  mem_basicOpen := fun z =>
    (exists_seedPoint C hπ g r₁ r₂ b₁ b₂ i j hO hχ z).choose_spec.choose_spec.choose_spec.2.1
  sec := fun z => relThetaWindowEquiv C
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
      π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
      (exists_seedPoint C hπ g r₁ r₂ b₁ b₂ i j hO hχ z).choose_spec.choose
  sec_mem := fun z =>
    (exists_seedPoint C hπ g r₁ r₂ b₁ b₂ i j hO hχ z).choose_spec.choose_spec.choose_spec.2.2.1

set_option maxHeartbeats 2400000 in
-- the `rfl` for `seedUniv.sec`/`seedUniv.h` unfolds the seed structure literal over the
-- huge `DivCarveChartRing`/window types past the defaults (recorded hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- **The `seedUniv` fibre-regularity coherence** (the `hfib` bridge for the DDR-3
assembly): at every point `z`, `seedUniv.sec z = relThetaWindowEquiv … x` and
`seedUniv.h z = algebraMap … f` for a window vector `x ∈ divUniversalFstWindow` and a base
element `f` whose fibre comparison `windowCompare … x` is nonzero at every prime of `D(f)`.
Composed with `relPinnedSectionsMap_relThetaResSide_windowEquiv_ne_zero` (and the no-leak
that a nonempty fibre of `D(algebraMap f)` forces `f ∉ q`), this discharges the
fibre-regularity `hfib` clause of `isGenerator_of_fibre_ne_zero`. -/
theorem seedUniv_sec_h_windowCompare
    (z : relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    ∃ (x : TensorProduct k
        (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
        ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
      (f : DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
      x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule ∧
      (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z
        = relThetaWindowEquiv C
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x ∧
      (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).h z
        = algebraMap (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            Γ(relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
              relPinnedChart C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) π
                ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)) f ∧
      ∀ q : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
        f ∉ q.asIdeal →
        windowCompare
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            q.asIdeal.ResidueField x ≠ 0 :=
  ⟨(exists_seedPoint C hπ g r₁ r₂ b₁ b₂ i j hO hχ z).choose_spec.choose,
    (exists_seedPoint C hπ g r₁ r₂ b₁ b₂ i j hO hχ z).choose_spec.choose_spec.choose,
    (exists_seedPoint C hπ g r₁ r₂ b₁ b₂ i j hO hχ z).choose_spec.choose_spec.choose_spec.1,
    rfl, rfl,
    (exists_seedPoint C hπ g r₁ r₂ b₁ b₂ i j hO hχ z).choose_spec.choose_spec.choose_spec.2.2.2⟩

end SeedGen

end AlgebraicGeometry
