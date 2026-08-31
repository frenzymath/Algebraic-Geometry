/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.H1BaseFieldInvariance
import AlgebraicJacobian.Picard.DivSchemeSeedUnivAssemble
import AlgebraicJacobian.Picard.DivSchemeSeedUniv

/-!
# G-4 — the κ(q) assembly: the universal fibre divisor (worksheet §1.5, I-0241 gap 1)

At every field point `K` of a `Z(♦)`-chart — a `k`-algebra field under the pair chart
ring killing the carve ideal, in particular every residue field `κ(q)` at a prime
`q ⊇ I_♦` — the universal tautological kernel pair is presented as function-field
subspaces (`divUniversalFibreKM`/`divUniversalFibreK'`: `b₁`/`b₂`-congr, the G-3
dictionary `Φ`, the `K'`-side translated by the coherence unit onto `N + S`), with
corank-`g` laws (`finrank_divUniversalFibre…_add`) and the elementwise hcarve
(`divUniversalFibre_carve`, from the universal carve law through the `Φ` product law
`divFamPhi_one_tmul_mul`); the fibre keystone fires
(`existsUnique_effective_divisor_divUniversalFibre`, `…_residueField` the κ(q)
spelling on the pair chart ring): a **unique effective divisor of degree `g`** —
`divUniversalFibreDivisor` — cuts both windows.  `h0_relCurve_baseField`/
`chi_relCurve_baseField` are `hOK`/`hχK` at every field extension, public.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
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

/-! ## `hOK`/`hχK` at every field extension (the fibre normalizations, public) -/

section Normalization

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable (K : Type u) [Field K] [Algebra k K]

/-- **`hOK` at every field extension**: `h⁰(𝒪) = 1` on the fibre curve —
`h0_moduleKSheaf` at the base-changed bundle (the `GluedSheafDatumFibre` firing
pattern, public form of the `DivSchemeMonoBridgeRel` private lemma). -/
theorem h0_relCurve_baseField : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1 := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  exact h0_moduleKSheaf (baseChangeBundle C K)

/-- **`hχK` at every field extension**: `χ(𝒪) = 1 − g` on the fibre curve, from the
base normalization — `chi_moduleKSheaf` at the base-changed bundle +
`genus_baseField`. -/
theorem chi_relCurve_baseField (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ) := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  have h1 : Sheaf.chi ((relCurve C K).moduleKSheaf K)
      = 1 - (genus (baseChangeBundle C K) : ℤ) :=
    chi_moduleKSheaf (baseChangeBundle C K)
  have h2 : genus (baseChangeBundle C K) = genus C := genus_baseField C K
  have h3 : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (genus C : ℤ) := chi_moduleKSheaf C
  have h4 : (genus C : ℤ) = (g : ℤ) := by rw [h3] at hχ; linarith
  rw [h1, h2, h4]

end Normalization

/-! ## The κ-assembly: fibre windows, coranks, carve, and the keystone -/

section Kappa

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftKappa : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

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
variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r₁ g r₂ i j) K]
  [IsScalarTower k (PairChartRing k g r₁ g r₂ i j) K]

-- The fibre-curve package at every field extension (the `DivSchemeMonoBridgeRel` pack).
noncomputable local instance instIsIntegralRelCurveKappa (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveKappa (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveKappa (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveKappa (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveKappa (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveKappa (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option linter.unusedSectionVars false in
/-- (Implementation) The window-shift multiplier through the first boundary basis is
the coordinate carve multiplier through the second boundary basis and the window
regluing — the recorded DD-4 boundary seam, closed on the `k`-level maps. -/
private lemma windowShiftMul_comp_divCarveMul
    (a : ↥(Scheme.divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    windowShiftMul hπ g a ∘ₗ b₁.equivFun.symm.toLinearMap
      = (b₂.equivFun.symm.trans (seedWindowShiftEquiv C π hπ g)).toLinearMap
          ∘ₗ divCarveMul k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) r₁ r₂ b₁ b₂ a := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    windowShiftMul, divCarveMul]
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- **The first fibre window `K_M`-fibre at `K`**: the kernel of the base-changed first
tautological quotient, pushed through the `b₁`-boundary congruence and the dictionary
`Φ_M` — a subspace of the fibre function field under the transported window `N`. -/
noncomputable def divUniversalFibreKM : Submodule K (relCurve C K).functionField :=
  Submodule.map
    (divFamPhi C K π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g))
    (Submodule.map
      (LinearEquiv.baseChange k K _ _ b₁.equivFun.symm).toLinearMap
      (LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
        (pairTautFst k g r₁ r₂ i j).toSubmodule)))

/-- **The second fibre window `K'`-fibre at `K`**: the kernel of the base-changed
second tautological quotient, pushed through the `b₂`-boundary congruence (composed
with the window regluing), the dictionary `Φ_{M+s}`, and translated by the coherence
unit onto the keystone's `N + S` side. -/
noncomputable def divUniversalFibreK' : Submodule K (relCurve C K).functionField :=
  Submodule.map
    (Scheme.mulLinear K ((msCoherenceUnit C K hπ g :
      (relCurve C K).functionFieldˣ) : (relCurve C K).functionField))
    (Submodule.map
      (divFamPhi C K π (windowM_choice π hπ g + windowS_choice π hπ g)
        (relThetaPairH1_windowMS C π hπ g))
      (Submodule.map
        (LinearEquiv.baseChange k K _ _
          (b₂.equivFun.symm.trans (seedWindowShiftEquiv C π hπ g))).toLinearMap
        (LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
          (pairTautSnd k g r₁ r₂ i j).toSubmodule))))

/-- The first fibre window obeys the transported pole bound `N`. -/
theorem divUniversalFibreKM_le :
    divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K
      ≤ Scheme.divisorSections K (windowN C K hπ g) ⊤ := by
  rintro _ ⟨y, -, rfl⟩
  exact divFamPhi_apply_mem C K π (windowM_choice π hπ g)
    (relThetaPairH1_windowM C π hπ g) y

/-- The second fibre window obeys the pole bound `N + S`. -/
theorem divUniversalFibreK'_le :
    divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K
      ≤ Scheme.divisorSections K (windowN C K hπ g + windowS C K hπ g) ⊤ := by
  rintro _ ⟨y, ⟨z, -, rfl⟩, rfl⟩
  rw [← map_mulLinear_msCoherenceUnit_top C K hπ g]
  exact Submodule.mem_map_of_mem
    (divFamPhi_apply_mem C K π (windowM_choice π hπ g + windowS_choice π hπ g)
      (relThetaPairH1_windowMS C π hπ g) z)

set_option maxHeartbeats 800000 in
-- base-changed tautological towers over the pair chart ring (the recorded hatch class)
set_option synthInstance.maxHeartbeats 400000 in
/-- **The corank-`g` law of the first fibre window** (`hKMrank`): its dimension plus
`g` is `h⁰(𝒪(N))` — the Grassmannian fibre corank at `pairTautFst`, transported through
the (injective) boundary congruence and `Φ`, matched against the window size transport
`h0_windowN`. -/
theorem finrank_divUniversalFibreKM_add
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    Module.finrank K ↥(divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K) + g
      = Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g)) := by
  have hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ) :=
    chi_relCurve_baseField C K g hχ
  -- Φ and the boundary congruence preserve the dimension
  have h1 : Module.finrank K ↥(divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K)
      = Module.finrank K
          ↥(LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
            (pairTautFst k g r₁ r₂ i j).toSubmodule)) := by
    rw [divUniversalFibreKM, finrank_map_divFamPhi]
    exact (LinearEquiv.finrank_map_eq _ _).trans rfl
  -- the Grassmannian fibre corank at the first tautological point
  have h2 := Grassmannian.finrank_ker_baseChangeMkQ_add_of_field
    (pairTautFst k g r₁ r₂ i j) K
  have h3 : Module.finrank k (Fin r₁ → k) = r₁ := Module.finrank_fin_fun k
  -- the window size transport and the boundary basis count
  have h4 : Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g))
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)) :=
    h0_windowN C K hπ g hχ hχK
  have h5 : Module.finrank k
      ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)
      = r₁ := by
    rw [Module.finrank_eq_card_basis b₁, Fintype.card_fin]
  have h6 := finrank_divisorSections_top k
    (windowM_choice π hπ g • fiberWeilDivisor π) (X := C.left)
  omega

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The decoupled first-window corank law.**  The tautological Grassmannian has
corank `g`, while the base and fibre Euler characteristics use `gamma`. -/
theorem finrank_divUniversalFibreKM_add_at {gamma : ℕ}
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    Module.finrank K ↥(divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K) + g
      = Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g)) := by
  have hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (gamma : ℤ) :=
    chi_relCurve_baseField C K gamma hχ
  have h1 : Module.finrank K ↥(divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K)
      = Module.finrank K
          ↥(LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
            (pairTautFst k g r₁ r₂ i j).toSubmodule)) := by
    rw [divUniversalFibreKM, finrank_map_divFamPhi]
    exact (LinearEquiv.finrank_map_eq _ _).trans rfl
  have h2 := Grassmannian.finrank_ker_baseChangeMkQ_add_of_field
    (pairTautFst k g r₁ r₂ i j) K
  have h3 : Module.finrank k (Fin r₁ → k) = r₁ := Module.finrank_fin_fun k
  have h4 : Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g))
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)) :=
    h0_windowN_at C K hπ g hχ hχK
  have h5 : Module.finrank k
      ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)
      = r₁ := by
    rw [Module.finrank_eq_card_basis b₁, Fintype.card_fin]
  have h6 := finrank_divisorSections_top k
    (windowM_choice π hπ g • fiberWeilDivisor π) (X := C.left)
  omega

set_option maxHeartbeats 800000 in
-- base-changed tautological towers over the pair chart ring (the recorded hatch class)
set_option synthInstance.maxHeartbeats 400000 in
/-- **The corank-`g` law of the second fibre window** (`hK'rank`): its dimension plus
`g` is `h⁰(𝒪(N + S))` — the fibre corank at `pairTautSnd` matched against the
coherence-unit translation and Riemann–Roch at both fields. -/
theorem finrank_divUniversalFibreK'_add
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    Module.finrank K ↥(divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K) + g
      = Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowN C K hπ g + windowS C K hπ g)) := by
  have hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ) :=
    chi_relCurve_baseField C K g hχ
  have hwinj : Function.Injective
      (Scheme.mulLinear K ((msCoherenceUnit C K hπ g :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField)) :=
    fun u v huv => mul_left_cancel₀ (Units.ne_zero (msCoherenceUnit C K hπ g)) huv
  -- the maps preserve the dimension down to the kernel
  have h1 : Module.finrank K ↥(divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K)
      = Module.finrank K
          ↥(LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
            (pairTautSnd k g r₁ r₂ i j).toSubmodule)) := by
    rw [divUniversalFibreK',
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hwinj _)).symm,
      finrank_map_divFamPhi]
    exact (LinearEquiv.finrank_map_eq _ _).trans rfl
  have h2 := Grassmannian.finrank_ker_baseChangeMkQ_add_of_field
    (pairTautSnd k g r₁ r₂ i j) K
  have h3 : Module.finrank k (Fin r₂ → k) = r₂ := Module.finrank_fin_fun k
  -- `h⁰(𝒪(N+S)) = h⁰(𝒪(T(M+s)))` through the coherence-unit translation
  have h4 : Sheaf.h0 ((relCurve C K).divisorSheaf K
        (windowN C K hπ g + windowS C K hπ g))
      = Sheaf.h0 ((relCurve C K).divisorSheaf K (windowTransportDivisor C K π
          (windowM_choice π hπ g + windowS_choice π hπ g))) := by
    rw [← finrank_divisorSections_top K, ← finrank_divisorSections_top K,
      ← map_mulLinear_msCoherenceUnit_top C K hπ g,
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hwinj _)).symm]
  -- Riemann–Roch at `K` for the transported shifted window
  have h5 : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowTransportDivisor C K π
        (windowM_choice π hπ g + windowS_choice π hπ g))) : ℤ)
      = ((windowM_choice π hπ g + windowS_choice π hπ g : ℕ) : ℤ) * windowδ π
        + 1 - (g : ℤ) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
        (subsingleton_h1_windowTransportDivisor C K π _
          (relThetaPairH1_windowMS C π hπ g)),
      deg_windowTransportDivisor, hχK]
    ring
  -- Riemann–Roch at `k` for the shifted embedding window, through the regluing
  have hAB : (windowS_choice π hπ g • fiberWeilDivisor π)
        + (windowM_choice π hπ g • fiberWeilDivisor π)
      = (windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π := by
    rw [add_nsmul]; exact add_comm _ _
  have h6 : (r₂ : ℤ)
      = ((windowM_choice π hπ g + windowS_choice π hπ g : ℕ) : ℤ) * windowδ π
        + 1 - (g : ℤ) := by
    have hb : Module.finrank k
        ↥(Scheme.divisorSections k ((windowS_choice π hπ g • fiberWeilDivisor π)
          + (windowM_choice π hπ g • fiberWeilDivisor π)) ⊤) = r₂ := by
      rw [Module.finrank_eq_card_basis b₂, Fintype.card_fin]
    have hfr := finrank_divisorSections_top k
      ((windowS_choice π hπ g • fiberWeilDivisor π)
        + (windowM_choice π hπ g • fiberWeilDivisor π)) (X := C.left)
    have hRR : (Sheaf.h0 (C.left.divisorSheaf k
          ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π)) : ℤ)
        = ((windowM_choice π hπ g + windowS_choice π hπ g : ℕ) : ℤ) * windowδ π
          + 1 - (g : ℤ) := by
      rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
          (window_embedding_shift π hπ g),
        Scheme.CurveDivisor.deg_nsmul' k, deg_fiberWeilDivisor_windowδ, hχ]
      ring
    have hcongr : Sheaf.h0 (C.left.divisorSheaf k
          ((windowS_choice π hπ g • fiberWeilDivisor π)
            + (windowM_choice π hπ g • fiberWeilDivisor π)))
        = Sheaf.h0 (C.left.divisorSheaf k
            ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π)) :=
      congrArg (fun D => Sheaf.h0 (C.left.divisorSheaf k D)) hAB
    omega
  have hcast : (Module.finrank K
        ↥(divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K) : ℤ) + (g : ℤ)
      = (Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowN C K hπ g + windowS C K hπ g)) : ℤ) := by
    have h23 : Module.finrank K
        ↥(LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
          (pairTautSnd k g r₁ r₂ i j).toSubmodule)) + g = r₂ := by omega
    have h23' : (Module.finrank K
        ↥(LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
          (pairTautSnd k g r₁ r₂ i j).toSubmodule)) : ℤ) + (g : ℤ) = (r₂ : ℤ) := by
      exact_mod_cast h23
    rw [h1, h4, h5]
    linarith [h23', h6]
  exact_mod_cast hcast

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The decoupled second-window corank law.**  The tautological corank is the
divisor degree `g`; all Riemann--Roch constants use the independent `gamma`. -/
theorem finrank_divUniversalFibreK'_add_at {gamma : ℕ}
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    Module.finrank K ↥(divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K) + g
      = Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowN C K hπ g + windowS C K hπ g)) := by
  have hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (gamma : ℤ) :=
    chi_relCurve_baseField C K gamma hχ
  have hwinj : Function.Injective
      (Scheme.mulLinear K ((msCoherenceUnit C K hπ g :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField)) :=
    fun u v huv => mul_left_cancel₀ (Units.ne_zero (msCoherenceUnit C K hπ g)) huv
  have h1 : Module.finrank K ↥(divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K)
      = Module.finrank K
          ↥(LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
            (pairTautSnd k g r₁ r₂ i j).toSubmodule)) := by
    rw [divUniversalFibreK',
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hwinj _)).symm,
      finrank_map_divFamPhi]
    exact (LinearEquiv.finrank_map_eq _ _).trans rfl
  have h2 := Grassmannian.finrank_ker_baseChangeMkQ_add_of_field
    (pairTautSnd k g r₁ r₂ i j) K
  have h3 : Module.finrank k (Fin r₂ → k) = r₂ := Module.finrank_fin_fun k
  have h4 : Sheaf.h0 ((relCurve C K).divisorSheaf K
        (windowN C K hπ g + windowS C K hπ g))
      = Sheaf.h0 ((relCurve C K).divisorSheaf K (windowTransportDivisor C K π
          (windowM_choice π hπ g + windowS_choice π hπ g))) := by
    rw [← finrank_divisorSections_top K, ← finrank_divisorSections_top K,
      ← map_mulLinear_msCoherenceUnit_top C K hπ g,
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hwinj _)).symm]
  have h5 : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowTransportDivisor C K π
        (windowM_choice π hπ g + windowS_choice π hπ g))) : ℤ)
      = ((windowM_choice π hπ g + windowS_choice π hπ g : ℕ) : ℤ) * windowδ π
        + 1 - (gamma : ℤ) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
        (subsingleton_h1_windowTransportDivisor C K π _
          (relThetaPairH1_windowMS C π hπ g)),
      deg_windowTransportDivisor, hχK]
    ring
  have hAB : (windowS_choice π hπ g • fiberWeilDivisor π)
        + (windowM_choice π hπ g • fiberWeilDivisor π)
      = (windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π := by
    rw [add_nsmul]
    exact add_comm _ _
  have h6 : (r₂ : ℤ)
      = ((windowM_choice π hπ g + windowS_choice π hπ g : ℕ) : ℤ) * windowδ π
        + 1 - (gamma : ℤ) := by
    have hb : Module.finrank k
        ↥(Scheme.divisorSections k ((windowS_choice π hπ g • fiberWeilDivisor π)
          + (windowM_choice π hπ g • fiberWeilDivisor π)) ⊤) = r₂ := by
      rw [Module.finrank_eq_card_basis b₂, Fintype.card_fin]
    have hfr := finrank_divisorSections_top k
      ((windowS_choice π hπ g • fiberWeilDivisor π)
        + (windowM_choice π hπ g • fiberWeilDivisor π)) (X := C.left)
    have hRR : (Sheaf.h0 (C.left.divisorSheaf k
          ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π)) : ℤ)
        = ((windowM_choice π hπ g + windowS_choice π hπ g : ℕ) : ℤ) * windowδ π
          + 1 - (gamma : ℤ) := by
      rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _
          (window_embedding_shift π hπ g),
        Scheme.CurveDivisor.deg_nsmul' k, deg_fiberWeilDivisor_windowδ, hχ]
      ring
    have hcongr : Sheaf.h0 (C.left.divisorSheaf k
          ((windowS_choice π hπ g • fiberWeilDivisor π)
            + (windowM_choice π hπ g • fiberWeilDivisor π)))
        = Sheaf.h0 (C.left.divisorSheaf k
            ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π)) :=
      congrArg (fun D => Sheaf.h0 (C.left.divisorSheaf k D)) hAB
    omega
  have hcast : (Module.finrank K
        ↥(divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K) : ℤ) + (g : ℤ)
      = (Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowN C K hπ g + windowS C K hπ g)) : ℤ) := by
    have h23 : Module.finrank K
        ↥(LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
          (pairTautSnd k g r₁ r₂ i j).toSubmodule)) + g = r₂ := by omega
    have h23' : (Module.finrank K
        ↥(LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
          (pairTautSnd k g r₁ r₂ i j).toSubmodule)) : ℤ) + (g : ℤ) = (r₂ : ℤ) := by
      exact_mod_cast h23
    rw [h1, h4, h5]
    linarith [h23', h6]
  exact_mod_cast hcast

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
  (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
    ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K))

set_option maxHeartbeats 800000 in
-- base-changed tautological towers over the pair chart ring (the recorded hatch class)
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
/-- **The elementwise hcarve of the fibre windows** (worksheet §1.5, the I-0241
bridge): whenever `K` kills the carve ideal, every multiplier `h ∈ H⁰(𝒪(S))` carries
`K_M`-fibre into `K'`-fibre.  Every `h` is a `Φ_s`-value; on pure tensors the `Φ`
product law converts the product into the coherence unit times the `Φ_{M+s}`-value of
the `windowShiftMul`-multiplied element, which the universal carve law places in the
second kernel through the boundary seam `windowShiftMul_comp_divCarveMul`. -/
theorem divUniversalFibre_carve
    (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K)) :
    ∀ h ∈ Scheme.divisorSections K (windowS C K hπ g) ⊤,
      ∀ f ∈ divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K,
        h * f ∈ divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K := by
  intro h hh f hf
  obtain ⟨y, rfl⟩ := exists_divFamPhi_eq C K π (windowS_choice π hπ g)
    (relThetaPairH1_windowS C hπ g) hh
  obtain ⟨y₁, hy₁, rfl⟩ := hf
  obtain ⟨x, hx, rfl⟩ := hy₁
  clear hh
  induction y using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, zero_mul]
    exact Submodule.zero_mem _
  | add y₁ y₂ ih₁ ih₂ =>
    rw [map_add, add_mul]
    exact Submodule.add_mem _ ih₁ ih₂
  | tmul c a =>
    have hcore : divFamPhi C K π (windowS_choice π hπ g)
          (relThetaPairH1_windowS C hπ g) (1 ⊗ₜ a)
        * divFamPhi C K π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
            ((LinearEquiv.baseChange k K _ _ b₁.equivFun.symm).toLinearMap x)
        ∈ divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K := ?_
    case tmul =>
      have hsm : (c ⊗ₜ a : K ⊗[k]
          ↥(Scheme.divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
          = c • ((1 : K) ⊗ₜ a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hsm, map_smul, functionFieldOverModule_smul_def, mul_assoc,
        ← functionFieldOverModule_smul_def]
      exact Submodule.smul_mem _ c hcore
    rw [divFamPhi_one_tmul_mul C K hπ g (relThetaPairH1_windowS C hπ g)
      (relThetaPairH1_windowM C π hπ g) (relThetaPairH1_windowMS C π hπ g) a _]
    -- the multiplied element is the boundary image of the carve output
    have hbc : LinearMap.baseChange K (windowShiftMul hπ g a)
        ((LinearEquiv.baseChange k K _ _ b₁.equivFun.symm).toLinearMap x)
        = (LinearEquiv.baseChange k K _ _
            (b₂.equivFun.symm.trans (seedWindowShiftEquiv C π hπ g))).toLinearMap
            (LinearMap.baseChange K
              (divCarveMul k (windowS_choice π hπ g • fiberWeilDivisor π)
                (windowM_choice π hπ g • fiberWeilDivisor π) r₁ r₂ b₁ b₂ a) x) := by
      have hcomp := congrArg (LinearMap.baseChange K)
        (windowShiftMul_comp_divCarveMul C hπ g r₁ r₂ b₁ b₂ a)
      rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hcomp
      exact LinearMap.congr_fun hcomp x
    rw [hbc]
    -- the universal carve law places the output in the second kernel
    have hmem : LinearMap.baseChange K
        (divCarveMul k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) r₁ r₂ b₁ b₂ a) x
        ∈ LinearMap.ker (Module.Grassmannian.baseChangeMkQ K
            (pairTautSnd k g r₁ r₂ i j).toSubmodule) :=
      (carvePairArrow_eq_zero_iff _ _ _).mp
        ((carveIdeal_le_ker_iff_carve_map k g r₁ r₂
          (divCarveMul k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) r₁ r₂ b₁ b₂) i j K).mp
          hker a) x hx
    exact Submodule.mem_map_of_mem
      (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hmem))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
/-- **The decoupled κ-assembly keystone.**  At a carve-killing field point, the
universal pair of corank-`g` windows cuts a unique effective divisor of degree `g`,
using the curve normalization `chi(O) = 1 - gamma` and `gamma ≤ g`. -/
theorem existsUnique_effective_divisor_divUniversalFibre_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K)) :
    ∃! D : (relCurve C K).CurveDivisor, 0 ≤ D ∧ CurveDivisor.deg K D = (g : ℤ) ∧
      divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K
        = Scheme.divisorSections K (windowN C K hπ g - D) ⊤ ∧
      divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K
        = Scheme.divisorSections K (windowN C K hπ g + windowS C K hπ g - D) ⊤ :=
  existsUnique_effective_divisor_of_carve_windowN_at C K hπ g hgamma
    (h0_relCurve_baseField C K) (chi_relCurve_baseField C K gamma hχ)
    (divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K)
    (divUniversalFibreKM_le C hπ g r₁ r₂ b₁ i j K)
    (finrank_divUniversalFibreKM_add_at C hπ g r₁ r₂ b₁ i j K hχ)
    (divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K)
    (divUniversalFibreK'_le C hπ g r₁ r₂ b₂ i j K)
    (finrank_divUniversalFibreK'_add_at C hπ g r₁ r₂ b₂ i j K hχ)
    (divUniversalFibre_carve C hπ g r₁ r₂ b₁ b₂ i j K hker)

set_option maxHeartbeats 800000 in
-- base-changed tautological towers over the pair chart ring (the recorded hatch class)
set_option synthInstance.maxHeartbeats 400000 in
include hO hχ hker in
/-- **THE κ-ASSEMBLY KEYSTONE** (worksheet §1.5, I-0241 gap 1): at any `k`-algebra
field `K` under the pair chart ring killing the carve ideal, the fibre windows of the
universal tautological pair cut a **unique effective divisor of degree `g`** with both
window equalities — `existsUnique_effective_divisor_of_carve_windowN` fired with every
hypothesis discharged from the universal carve and the transported window facts. -/
theorem existsUnique_effective_divisor_divUniversalFibre :
    ∃! D : (relCurve C K).CurveDivisor, 0 ≤ D ∧ CurveDivisor.deg K D = (g : ℤ) ∧
      divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K
        = Scheme.divisorSections K (windowN C K hπ g - D) ⊤ ∧
      divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K
        = Scheme.divisorSections K (windowN C K hπ g + windowS C K hπ g - D) ⊤ :=
  existsUnique_effective_divisor_of_carve_windowN C K hπ g hO hχ
    (h0_relCurve_baseField C K) (chi_relCurve_baseField C K g hχ)
    (divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K)
    (divUniversalFibreKM_le C hπ g r₁ r₂ b₁ i j K)
    (finrank_divUniversalFibreKM_add C hπ g r₁ r₂ b₁ i j K hχ)
    (divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K)
    (divUniversalFibreK'_le C hπ g r₁ r₂ b₂ i j K)
    (finrank_divUniversalFibreK'_add C hπ g r₁ r₂ b₂ i j K hχ)
    (divUniversalFibre_carve C hπ g r₁ r₂ b₁ b₂ i j K hker)

/-- **The universal fibre divisor** `d` at a carve-killing field point: the unique
effective degree-`g` divisor cutting both fibre windows. -/
noncomputable def divUniversalFibreDivisor :
    (relCurve C K).CurveDivisor :=
  (existsUnique_effective_divisor_divUniversalFibre
    C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker).exists.choose

include hO hχ hker in
/-- The defining property of the universal fibre divisor: effective, of degree `g`,
cutting both fibre windows. -/
theorem divUniversalFibreDivisor_spec :
    0 ≤ divUniversalFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker ∧
      CurveDivisor.deg K (divUniversalFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker)
        = (g : ℤ) ∧
      divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K
        = Scheme.divisorSections K (windowN C K hπ g
            - divUniversalFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker) ⊤ ∧
      divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K
        = Scheme.divisorSections K (windowN C K hπ g + windowS C K hπ g
            - divUniversalFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker) ⊤ :=
  (existsUnique_effective_divisor_divUniversalFibre
    C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker).exists.choose_spec

include hO hχ hker in
/-- **Uniqueness** of the universal fibre divisor: any effective degree-`g` divisor
cutting both fibre windows is `divUniversalFibreDivisor`. -/
theorem divUniversalFibreDivisor_unique
    {D : (relCurve C K).CurveDivisor} (h0D : 0 ≤ D)
    (hdeg : CurveDivisor.deg K D = (g : ℤ))
    (hKM : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K
      = Scheme.divisorSections K (windowN C K hπ g - D) ⊤)
    (hK' : divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K
      = Scheme.divisorSections K (windowN C K hπ g + windowS C K hπ g - D) ⊤) :
    D = divUniversalFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker :=
  ((existsUnique_effective_divisor_divUniversalFibre
      C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker).unique ⟨h0D, hdeg, hKM, hK'⟩
    (divUniversalFibreDivisor_spec C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker))

/-- The universal fibre divisor at independent curve parameter `gamma ≤ g`. -/
noncomputable def divUniversalFibreDivisor_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K)) :
    (relCurve C K).CurveDivisor :=
  (existsUnique_effective_divisor_divUniversalFibre_at
    C hπ g r₁ r₂ b₁ b₂ i j K hgamma hχ hker).exists.choose

/-- The defining effective-degree and two-window properties of the decoupled universal
fibre divisor. -/
theorem divUniversalFibreDivisor_spec_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K)) :
    0 ≤ divUniversalFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j K hgamma hχ hker ∧
      CurveDivisor.deg K
          (divUniversalFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j K hgamma hχ hker)
        = (g : ℤ) ∧
      divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K
        = Scheme.divisorSections K (windowN C K hπ g
            - divUniversalFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j K hgamma hχ hker) ⊤ ∧
      divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K
        = Scheme.divisorSections K (windowN C K hπ g + windowS C K hπ g
            - divUniversalFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j K hgamma hχ hker) ⊤ :=
  (existsUnique_effective_divisor_divUniversalFibre_at
    C hπ g r₁ r₂ b₁ b₂ i j K hgamma hχ hker).exists.choose_spec

/-- Uniqueness of the decoupled universal fibre divisor. -/
theorem divUniversalFibreDivisor_unique_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K))
    {D : (relCurve C K).CurveDivisor} (h0D : 0 ≤ D)
    (hdeg : CurveDivisor.deg K D = (g : ℤ))
    (hKM : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K
      = Scheme.divisorSections K (windowN C K hπ g - D) ⊤)
    (hK' : divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K
      = Scheme.divisorSections K (windowN C K hπ g + windowS C K hπ g - D) ⊤) :
    D = divUniversalFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j K hgamma hχ hker :=
  ((existsUnique_effective_divisor_divUniversalFibre_at
      C hπ g r₁ r₂ b₁ b₂ i j K hgamma hχ hker).unique ⟨h0D, hdeg, hKM, hK'⟩
    (divUniversalFibreDivisor_spec_at C hπ g r₁ r₂ b₁ b₂ i j K hgamma hχ hker))

set_option synthInstance.maxHeartbeats 800000 in
-- the canonical residue-field tower `k → R_{I,J} → κ(q)` exceeds the default search
-- budget and the project-default pending depth (the recorded
-- `divUniversal_carve_residueField` escape hatch)
set_option maxSynthPendingDepth 8 in
include hO hχ in
/-- **The κ(q) assembly** (the `Z(♦)`-point spelling, on the pair chart ring): at every
prime `q` of the pair chart ring containing the carve ideal, the universal fibre
windows at the residue field `κ(q)` cut a unique effective divisor of degree `g` with
both window equalities — the fibre divisor `d_q` of the universal seed. -/
theorem existsUnique_effective_divisor_divUniversalFibre_residueField
    (q : PrimeSpectrum (PairChartRing k g r₁ g r₂ i j))
    (hq : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j ≤ q.asIdeal) :
    ∃! D : (relCurve C q.asIdeal.ResidueField).CurveDivisor,
      0 ≤ D ∧ CurveDivisor.deg q.asIdeal.ResidueField D = (g : ℤ) ∧
      divUniversalFibreKM C hπ g r₁ r₂ b₁ i j q.asIdeal.ResidueField
        = Scheme.divisorSections q.asIdeal.ResidueField
            (windowN C q.asIdeal.ResidueField hπ g - D) ⊤ ∧
      divUniversalFibreK' C hπ g r₁ r₂ b₂ i j q.asIdeal.ResidueField
        = Scheme.divisorSections q.asIdeal.ResidueField
            (windowN C q.asIdeal.ResidueField hπ g
              + windowS C q.asIdeal.ResidueField hπ g - D) ⊤ :=
  existsUnique_effective_divisor_divUniversalFibre C hπ g r₁ r₂ b₁ b₂ i j
    q.asIdeal.ResidueField hO hχ
    (hq.trans (Ideal.ker_algebraMap_residueField (I := q.asIdeal)).symm.le)

end Kappa

end AlgebraicGeometry
