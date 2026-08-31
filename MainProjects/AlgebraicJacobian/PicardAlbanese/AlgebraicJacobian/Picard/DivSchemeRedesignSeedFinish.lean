/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignRDNChart
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.LocalRing.Module

/-!
# DD-4 redesign — RD-N step 2c: the stalk support bridge (`κ(p)`-fibre ⟹ `z ∉ supp N z`)

RD-N proper for the concrete chart colength `N z = chartColengthModule K b s` is the
support-avoidance `primeIdealOf z ∉ Module.support Γ(V) (N z)` — the premise the ann-cutter
engine (`DivSchemeRedesignFibreCut.lean`, I-0292) consumes.  This file lands the **2c stalk
bridge** (I-0302/I-0303 §residual 2c) that reduces that support-avoidance to a single
`κ(p)`-fibre-vanishing input over the base `R`, using **only** mathlib's finite-module
support machinery — no germ/stalk plumbing.

The route (`Module.support_eq_zeroLocus` for a finite module, avoiding the
`isLocalization_stalk` detour):

* the **base colength** `chartColengthModuleBase K b s` — the `R`-linear range of the chart
  reading map into `Γ(V) ⧸ ⟨read s⟩` — is a **finite `R`-module** (`Module.Finite.range`,
  `K` finite over `R`);
* if its residue-field fibre `N_R ⊗ κ(p)` vanishes at the base prime
  `p = (primeIdealOf z).comap (algebraMap R Γ(V))`, then `p ∉ Module.support R N_R`, so — by
  `Module.support_eq_zeroLocus` — the annihilator `Ann_R(N_R)` is **not** contained in `p`;
* a witness `r₀ ∈ Ann_R(N_R)`, `r₀ ∉ p` gives `algebraMap R Γ(V) r₀ ∉ primeIdealOf z`
  (by definition of `comap`) that annihilates every chart reading `[read ψ]` — hence the whole
  `Γ(V)`-span `N z` — so `primeIdealOf z ∉ Module.support Γ(V) (N z)` via
  `Module.notMem_support_iff'`.

* `ThetaGeneratorSeed.chartColengthModuleBase` — the finite `R`-form of the chart colength.
* `ThetaGeneratorSeed.notMem_support_chartColengthModule_of_subsingleton_tmul_residueField`
  — **the 2c bridge**: `Subsingleton (N_R ⊗ κ(p)) ⟹ RD-N proper` at a single point.

The remaining honest content is the `κ(p)`-fibre-vanishing hypothesis
`Subsingleton (N_R ⊗ κ(p))` — the `d_p` achiever's fibre divisibility of the window readings
by `read s` (I-0302 §residual 2b, the achiever + landed chart flat via the `κ(p)→𝒪_z`
transport).  This file is certificate-free, `IsGenerator`-free, and consumes only the landed
`chartReadMap`/`chartColengthModule` + mathlib support theory.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}

namespace ThetaGeneratorSeed

/-- **The finite `R`-form of the chart colength `N z`** (I-0302 §residual 2a→2b): the
`R`-linear range of the chart reading map `[read ·] : K → Γ(V) ⧸ ⟨read s⟩`.  Unlike the
`Γ(V)`-span `chartColengthModule` (which is finite over `Γ(V)`), this `R`-submodule is finite
over the **base** `R` (`Module.Finite.range`, `K` finite over `R`), so mathlib's finite-module
support theory applies to it.  Its `Γ(V)`-span is `chartColengthModule K b s`, and the
`κ(p)`-fibre-vanishing `Subsingleton (chartColengthModuleBase ⊗ κ(p))` is the honest input the
2c bridge below consumes. -/
noncomputable def chartColengthModuleBase (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) :
    Submodule R (Γ(relCurve C R, relPinnedChart C R π b) ⧸
        Ideal.span {relThetaResSide a b (le_rfl) s}) :=
  LinearMap.range
    ((Ideal.Quotient.mkₐ R (Ideal.span {relThetaResSide a b (le_rfl) s})).toLinearMap.comp
      (chartReadMap K b))

/-- Every chart reading of a `K`-element lies in the base colength `N_R`. -/
theorem mk_relThetaResSide_mem_chartColengthModuleBase
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) {ψ : relThetaSections C R π a} (hψ : ψ ∈ K) :
    Ideal.Quotient.mk (Ideal.span {relThetaResSide a b (le_rfl) s})
        (relThetaResSide a b (le_rfl) ψ) ∈ chartColengthModuleBase K b s :=
  ⟨⟨ψ, hψ⟩, rfl⟩

set_option maxHeartbeats 800000 in
-- the `Module.Finite.range` instance over the heavy `relCurve` chart section-ring colength
-- re-checks the range-finiteness `whnf` past the default budget
/-- **`N_R` is a finite `R`-module** (the base finiteness feeding the support theory): the
range of an `R`-linear map out of the finite `R`-module `K`. -/
instance chartColengthModuleBase_finite (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) [Module.Finite R ↥K] :
    Module.Finite R ↥(chartColengthModuleBase K b s) :=
  Module.Finite.range _

set_option maxHeartbeats 2400000 in
-- the base residue-field tower `R → κ(p)` and the support/annihilator theory over the heavy
-- `relCurve` chart section-ring colength re-elaborate the finite-module instances past defaults
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- **RD-N step 2c — the stalk support bridge** (I-0302/I-0303 §residual 2c): at a point `z`
in the chart `V = relPinnedChart C R π b`, if the residue-field fibre
`chartColengthModuleBase K b s ⊗ κ(p)` of the **base** colength vanishes at the base prime
`p = (primeIdealOf z).comap (algebraMap R Γ(V))`, then **RD-N proper** holds:
`primeIdealOf z ∉ Module.support Γ(V) (chartColengthModule K b s)`.

The fibre vanishing places `p` outside `Module.support R N_R = Z(Ann_R N_R)` (finite module),
so a base annihilator element `r₀ ∈ Ann_R(N_R) \ p` maps to
`algebraMap R Γ(V) r₀ ∉ primeIdealOf z` (definition of `comap`) and annihilates every chart
reading `[read ψ]`, hence the whole `Γ(V)`-span `N z`.  This is exactly the ann-cutter engine's
support-avoidance premise, reduced to the single honest `κ(p)`-fibre-vanishing (the `d_p`
achiever's fibre divisibility, I-0302 §residual 2b). -/
theorem notMem_support_chartColengthModule_of_subsingleton_tmul_residueField
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) [Module.Finite R ↥K]
    {z : relCurve C R} (hz : z ∈ relPinnedChart C R π b)
    (hfib : Subsingleton (↥(chartColengthModuleBase K b s) ⊗[R]
      (PrimeSpectrum.comap (algebraMap R Γ(relCurve C R, relPinnedChart C R π b))
          ((isAffineOpen_relPinnedChart C R π b).primeIdealOf ⟨z, hz⟩)).asIdeal.ResidueField)) :
    (isAffineOpen_relPinnedChart C R π b).primeIdealOf ⟨z, hz⟩ ∉
      Module.support Γ(relCurve C R, relPinnedChart C R π b) ↥(chartColengthModule K b s) := by
  set pz := (isAffineOpen_relPinnedChart C R π b).primeIdealOf ⟨z, hz⟩ with hpz
  set pR := PrimeSpectrum.comap
    (algebraMap R Γ(relCurve C R, relPinnedChart C R π b)) pz with hpR
  -- (i) the base fibre vanishing places `pR` outside the (finite-module) base support
  have hns : pR ∉ Module.support R ↥(chartColengthModuleBase K b s) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
    haveI := hfib
    exact (TensorProduct.comm R (↥(chartColengthModuleBase K b s)) _).symm.toEquiv.subsingleton
  -- (ii) so the base annihilator is not contained in `pR`
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus] at hns
  obtain ⟨r₀, hr₀_ann, hr₀_notp⟩ := Set.not_subset.mp hns
  rw [SetLike.mem_coe] at hr₀_ann
  -- (iii) the transported killer `algebraMap r₀` avoids `pz` and annihilates every reading
  set rk := algebraMap R Γ(relCurve C R, relPinnedChart C R π b) r₀ with hrk
  have hrk_notp : rk ∉ pz.asIdeal := fun hmem => hr₀_notp (Ideal.mem_comap.mpr hmem)
  have hkill : ∀ x ∈ chartColengthModule K b s, rk • x = 0 := by
    intro x hx
    refine Submodule.span_induction (p := fun y _ => rk • y = 0) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨w, rfl⟩
      rw [hrk, algebraMap_smul]
      have hm := Module.mem_annihilator.mp hr₀_ann ⟨_, LinearMap.mem_range_self _ w⟩
      simpa using congrArg (Subtype.val) hm
    · rw [smul_zero]
    · intro y₁ y₂ _ _ h₁ h₂; rw [smul_add, h₁, h₂, add_zero]
    · intro c y _ h; rw [smul_comm, h, smul_zero]
  -- (iv) conclude via the finite-support characterization over `Γ(V)`
  rw [Module.notMem_support_iff']
  intro m
  refine ⟨rk, hrk_notp, ?_⟩
  apply Subtype.ext
  simpa using hkill (m : Γ(relCurve C R, relPinnedChart C R π b) ⧸
    Ideal.span {relThetaResSide a b (le_rfl) s}) m.2

end ThetaGeneratorSeed

end AlgebraicGeometry
