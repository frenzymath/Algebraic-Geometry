/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignCarvePinFibreKM
import AlgebraicJacobian.Picard.DivSchemeRedesignHsubChart

/-!
# DD-4 — the carve pin `hsub_chart`: R1 (range finrank) + R2 (injective assembly)

Assembles the landed source rank (`finrank_baseChange_divUniversalSeedK_add`, the SOURCE
fibre dim `r₁ − g`) with the range-side finrank (R1) into the constant-rank injectivity
pin, discharging the carve fibre non-collapse `hsub_chart`.

This file collects, at the bottom, the reusable field-generic linear-algebra facts (R2
core): rank-nullity injectivity and the `baseChange → rTensor` injectivity transfer needed
to move a fibre injectivity computed on the natural left tensor `κ(p) ⊗ M` onto the
`.rTensor κ(p)` shape the framework consumes.
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

/-! ## R2 core — reusable field/ring-generic linear algebra -/

section LinearAlgebra

/-- **`baseChange ⟹ rTensor` injectivity transfer**: the left base change `A ⊗ g` and the
right tensor `g ⊗ A` are conjugate by `TensorProduct.comm` (an `R`-linear equivalence), so
injectivity of the former transfers to the latter.  Used to move a residue-fibre
injectivity computed on the natural `κ(p)`-space `κ(p) ⊗ M` onto the `.rTensor κ(p)` shape
the carve framework consumes. -/
theorem rTensor_injective_of_baseChange_injective
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (A : Type*) [CommRing A] [Algebra R A]
    (g : M →ₗ[R] N) (h : Function.Injective (LinearMap.baseChange A g)) :
    Function.Injective (g.rTensor A) := by
  have key : ∀ z : M ⊗[R] A, (TensorProduct.comm R N A) (g.rTensor A z)
      = (LinearMap.baseChange A g) ((TensorProduct.comm R M A) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul m a =>
        simp [LinearMap.rTensor_tmul, TensorProduct.comm_tmul, LinearMap.baseChange_tmul]
    | add x y hx hy => simp [hx, hy]
  intro x y hxy
  have hbc : (LinearMap.baseChange A g) ((TensorProduct.comm R M A) x)
      = (LinearMap.baseChange A g) ((TensorProduct.comm R M A) y) := by
    rw [← key, ← key, hxy]
  exact (TensorProduct.comm R M A).injective (h hbc)

/-- **The range-inclusion residue fibre stays injective**: from injectivity of the left
base change `A ⊗ f`, the residue fibre `(range f).subtype ⊗ A` is injective.  Factor
`f = (range f).subtype ∘ f.rangeRestrict` with `f.rangeRestrict` surjective, tensor by `A`,
and cancel the surjective factor. -/
theorem range_subtype_rTensor_injective_of_baseChange_injective
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (A : Type*) [CommRing A] [Algebra R A]
    (f : M →ₗ[R] N) (h : Function.Injective (LinearMap.baseChange A f)) :
    Function.Injective ((LinearMap.range f).subtype.rTensor A) := by
  have hfrT : Function.Injective (f.rTensor A) :=
    rTensor_injective_of_baseChange_injective A f h
  have hcomp_eq : (LinearMap.range f).subtype ∘ₗ f.rangeRestrict = f :=
    LinearMap.subtype_comp_codRestrict _ _ _
  have hfac : f.rTensor A
      = (LinearMap.range f).subtype.rTensor A ∘ₗ f.rangeRestrict.rTensor A := by
    rw [← LinearMap.rTensor_comp, hcomp_eq]
  have hQsurj : Function.Surjective (f.rangeRestrict.rTensor A) :=
    LinearMap.rTensor_surjective A f.surjective_rangeRestrict
  rw [hfac, LinearMap.coe_comp] at hfrT
  intro x y hxy
  obtain ⟨x', rfl⟩ := hQsurj x
  obtain ⟨y', rfl⟩ := hQsurj y
  exact congrArg _ (hfrT hxy)

/-- **Base change commutes with `range`**: the range of a base-changed linear map is the
base change of its range. -/
theorem range_baseChange {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (A : Type*) [CommRing A] [Algebra R A] (φ : M →ₗ[R] N) :
    LinearMap.range (LinearMap.baseChange A φ) = Submodule.baseChange A (LinearMap.range φ) := by
  apply le_antisymm
  · rw [LinearMap.range_le_iff_comap, eq_top_iff]
    rintro z -
    induction z with
    | zero => simp
    | tmul a m =>
        rw [Submodule.mem_comap, LinearMap.baseChange_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem a (LinearMap.mem_range_self φ m)
    | add x y hx hy =>
        rw [Submodule.mem_comap, map_add]
        exact Submodule.add_mem _ (Submodule.mem_comap.1 hx) (Submodule.mem_comap.1 hy)
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨m, rfl⟩ := hy
    exact ⟨(1 : A) ⊗ₜ[R] m, by rw [LinearMap.baseChange_tmul, TensorProduct.mk_apply]⟩

/-- An injective linear map preserves the rank of a submodule mapped through it. -/
theorem finrank_map_of_injective {K : Type*} [Field K] {M N : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup N] [Module K N] (φ : M →ₗ[K] N) (hφ : Function.Injective φ)
    (X : Submodule K M) : Module.finrank K ↥(Submodule.map φ X) = Module.finrank K ↥X :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective φ hφ X)).symm

/-- **Rank-nullity injectivity**: over a field, a linear map out of a finite-dimensional
space whose range has the full source dimension is injective (its kernel has dimension `0`,
hence is `⊥`). -/
theorem injective_of_finrank_range_eq {K : Type*} [Field K] {M N : Type*}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N)
    (h : Module.finrank K (LinearMap.range f) = Module.finrank K M) :
    Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hker : Module.finrank K (LinearMap.ker f) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp hker

end LinearAlgebra

/-! ## Chart reading range -/

section ChartRead

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R] [Algebra k R]
  {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}

/-- The range of the chart reading map is the image of the seed under the side reading. -/
theorem range_chartReadMap (W : Submodule R (relThetaSections C R π a)) (b : Bool) :
    LinearMap.range (chartReadMap W b)
      = Submodule.map (relThetaResSide a b le_rfl) W := by
  rw [chartReadMap, LinearMap.range_comp, Submodule.range_subtype]

end ChartRead

/-! ## R1 — the range-side finrank, over a general field `K` of the tower

Built over a general field `K` (the residue-field synthesis enters only at instantiation),
mirroring the `CarvePinFibreKM` tower context.  The `κ(p)` assembly instantiates at
`K := κ(p)`.
-/

section R1

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftR1 : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

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
  [Algebra (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]
  [IsScalarTower k (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]
  [IsScalarTower (PairChartRing k g r₁ g r₂ i j)
    (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]

-- The fibre-curve package at every field extension (the `DivSchemeMonoBridgeRel` pack).
noncomputable local instance instIsIntegralRelCurveR1 (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveR1 (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveR1 (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveR1 (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveR1 (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveR1 (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 2400000 in
-- the `.trans` of the two landed transport lemmas over the general-field window tensor types
-- exceeds the default budget (the `κ(p)` analogue used 2M; general `K` is comparable)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option linter.unusedSectionVars false in
/-- **(R1, step 1 at a general field `K`)** The element-level window transport: the
chart-ring base change `β` of the reading of a relative window section is the fibre reading
of the compared vector.  General-field analogue of `relPinnedTermBaseChangeAlg_reading_windowEquiv`
(the `κ(p)` spelling in `DivSchemeRedesignCarvePin.lean`). -/
theorem relPinnedTermBaseChangeAlg_reading_windowEquiv_field (b : Bool)
    (x : (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) ⊗[k]
      ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    (relPinnedTermBaseChangeAlg C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) K π b).toLinearMap
        ((1 : K) ⊗ₜ[seedChartRing C hπ g r₁ r₂ b₁ b₂ i j]
          (relThetaResSide (windowM_choice π hπ g) b le_rfl
            (relThetaWindowEquiv C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) π
              (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x)))
      = relThetaResSide (windowM_choice π hπ g) b le_rfl
          (relThetaWindowEquiv C K π (windowM_choice π hπ g)
            (relThetaPairH1_windowM C π hπ g)
            (windowCompare (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) K x)) :=
  (relPinnedTermBaseChangeAlg_one_tmul C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) K π b _).trans
    (relPinnedSectionsMap_relThetaResSide_windowEquiv C
      (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) K π (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) b x)

set_option maxHeartbeats 1600000 in
-- the localized `conv`-rewrites reduce the base-changed reading range over the giant relCurve
-- section types on both sides to a common span; the many structural rewrites exceed the default
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
/-- **(R1, ★) The submodule-level window transport**: the range of the base-changed chart
reading `f_V ⊗ K`, transported through the chart-ring base-change iso `β`, is exactly the
range of the fibre-seed chart reading `chartReadMap (Θ_K W_κ) b`.  This lifts the
element-level window transport to the submodule/range level. -/
theorem map_relPinnedTermBaseChangeAlg_range_baseChange_chartReadMap (b : Bool) :
    Submodule.map (relPinnedTermBaseChangeAlg C
        (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) K π b).toLinearMap
        (LinearMap.range (LinearMap.baseChange K
          (chartReadMap (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b)))
      = LinearMap.range (chartReadMap
          (Submodule.map (relThetaWindowEquiv C K π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g)).toLinearMap
            (divUniversalFibreSeedW C hπ g r₁ r₂ b₁ b₂ i j K)) b) := by
  -- reduce the RHS to a span over `↑W₀` (localized to avoid whnf on the LHS base change)
  conv_rhs => rw [range_chartReadMap, ← Submodule.map_comp, divUniversalFibreSeedW,
    Submodule.map_span, ← Set.image_comp]
  -- reduce the LHS to a span over `↑W₀`
  conv_lhs => rw [range_baseChange, range_chartReadMap, divUniversalSeedK,
    ← Submodule.map_comp, Submodule.baseChange_eq_span, Submodule.map_coe, Submodule.map_span,
    ← Set.image_comp, Submodule.map_coe, ← Set.image_comp]
  -- match the two spanning sets pointwise via `step1`
  refine congrArg (Submodule.span K) (Set.image_congr fun x _ => ?_)
  simp only [Function.comp_apply, LinearMap.coe_comp, TensorProduct.mk_apply]
  exact relPinnedTermBaseChangeAlg_reading_windowEquiv_field C hπ g r₁ r₂ b₁ b₂ i j K b x

set_option maxHeartbeats 4000000 in
-- the chart-ring iso `β`, germ bridge, corank law and window-size transport all mention the
-- heavy relCurve/base-change section types; assembling their finrank chain exceeds the default
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- **(R1) The range-side finrank**: at a general field `K` of the tower (with the generic
point of the fibre curve in the pinned chart), the base-changed chart reading `f_V ⊗ K` has
range of constant dimension `r₁ − g` (spelled `+ g = dim_k (Fin r₁ → k)`).  Combines the
submodule window transport `★` (through the finrank-preserving chart-ring iso `β`) with the
germ bridge (`germGenericLinear`/`mulLinear u` injective) onto the corank-`g` fibre window
`divUniversalFibreKM`, whose dimension is pinned by `finrank_divUniversalFibreKM_add`. -/
theorem finrank_range_baseChange_chartReadMap_divUniversalSeedK_add (b : Bool)
    (hηV : genericPoint (relCurve C K) ∈ relPinnedChart C K π b)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    Module.finrank K ↥(LinearMap.range (LinearMap.baseChange K
        (chartReadMap (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b))) + g
      = Module.finrank k (Fin r₁ → k) := by
  obtain ⟨u, hu⟩ := exists_unit_map_germGenericLinear_range_chartReadMap_divUniversalFibreKM
    C hπ g r₁ r₂ b₁ b₂ i j K b hηV
  -- `β` (the chart-ring base change) preserves the range's dimension; apply `★`
  have hβinj : Function.Injective ⇑(relPinnedTermBaseChangeAlg C
      (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) K π b).toLinearMap :=
    (relPinnedTermBaseChangeAlg C (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) K π b).injective
  have hβ : Module.finrank K ↥(LinearMap.range (LinearMap.baseChange K
        (chartReadMap (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b)))
      = Module.finrank K ↥(Submodule.map (relPinnedTermBaseChangeAlg C
          (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) K π b).toLinearMap
          (LinearMap.range (LinearMap.baseChange K
            (chartReadMap (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b)))) :=
    (finrank_map_of_injective _ hβinj _).symm
  rw [hβ, map_relPinnedTermBaseChangeAlg_range_baseChange_chartReadMap]
  -- `germGenericLinear` and `mulLinear u` are injective, so `range chartRead ≃ divUniversalFibreKM`
  have hgi : Function.Injective (Scheme.germGenericLinear K hηV) :=
    germ_injective_of_isIntegral (relCurve C K) (genericPoint (relCurve C K)) hηV
  have hmi : Function.Injective
      (Scheme.mulLinear K ((u : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField)) :=
    fun x y hxy => mul_left_cancel₀ (Units.ne_zero u) hxy
  have hfr : Module.finrank K ↥(LinearMap.range (chartReadMap
        (Submodule.map (relThetaWindowEquiv C K π (windowM_choice π hπ g)
            (relThetaPairH1_windowM C π hπ g)).toLinearMap
          (divUniversalFibreSeedW C hπ g r₁ r₂ b₁ b₂ i j K)) b))
      = Module.finrank K ↥(divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K) := by
    have e1 := finrank_map_of_injective (Scheme.germGenericLinear K hηV) hgi
      (LinearMap.range (chartReadMap (Submodule.map (relThetaWindowEquiv C K π
        (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)).toLinearMap
        (divUniversalFibreSeedW C hπ g r₁ r₂ b₁ b₂ i j K)) b))
    rw [hu, finrank_map_of_injective _ hmi] at e1
    exact e1.symm
  rw [hfr, finrank_divUniversalFibreKM_add C hπ g r₁ r₂ b₁ i j K hχ]
  -- `h⁰(𝒪(N)) = dim_k H⁰(windowM) = r₁`
  have hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ) :=
    chi_relCurve_baseField C K g hχ
  rw [h0_windowN C K hπ g hχ hχK,
    ← finrank_divisorSections_top k (windowM_choice π hπ g • fiberWeilDivisor π) (X := C.left),
    Module.finrank_eq_card_basis b₁, Module.finrank_fin_fun, Fintype.card_fin]

end R1

/-! ## R2 + `hsub_chart` — the constant-rank injectivity pin at `κ(p)`

Instantiates R1 at the residue field `κ(p)` of every prime `p` of `R_Z` and combines with the
landed source rank to pin `finrank(range) = finrank(source)`, hence `f_V ⊗ κ(p)` injective;
the transfer lemma moves this onto the `.rTensor κ(p)` shape of `hsub_chart`.
-/

section HsubChart

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftHsub : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

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

-- The fibre-curve package at every field extension.
noncomputable local instance instIsIntegralRelCurveHsub (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveHsub (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveHsub (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveHsub (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveHsub (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveHsub (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 2000000 in
-- instantiating R1 at the native residue field `κ(p)` over `R_Z` (the composite pair-chart
-- tower) plus the landed source rank exceeds the default whnf/synth budgets (I-0295 class)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- **The carve fibre non-collapse `hsub_chart`** (chart level, `h z`-free): at every base
prime `p` of `R_Z`, the residue fibre of the chart base ideal inclusion
`N_V = range (chartReadMap K_univ b) ↪ Γ(V)` is injective — no fibre of the seed reading
collapses.  Proof (the constant-rank pin): the landed source rank
`finrank κ(p) (κ(p) ⊗ K_univ) = r₁ − g` and the range rank R1
`finrank κ(p) (range (f_V ⊗ κ(p))) = r₁ − g` agree, so `f_V ⊗ κ(p)` (on the natural left
tensor `κ(p) ⊗ K_univ`) has zero kernel, hence is injective; the `baseChange → rTensor`
transfer moves this onto the `.rTensor κ(p)` inclusion.  `hη` (the generic point of every
residue-fibre curve lies in the pinned chart) is threaded as a hypothesis. -/
theorem hsub_chart (b : Bool)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hη : ∀ p : PrimeSpectrum (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j),
      genericPoint (relCurve C p.asIdeal.ResidueField)
        ∈ relPinnedChart C p.asIdeal.ResidueField π b) :
    ∀ p : PrimeSpectrum (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j),
      Function.Injective ((LinearMap.range (chartReadMap
        (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b)).subtype.rTensor
          p.asIdeal.ResidueField) := by
  intro p
  letI : Algebra (PairChartRing k g r₁ g r₂ i j) p.asIdeal.ResidueField :=
    ((algebraMap (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) p.asIdeal.ResidueField).comp
      (algebraMap (PairChartRing k g r₁ g r₂ i j)
        (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j))).toAlgebra
  letI : IsScalarTower (PairChartRing k g r₁ g r₂ i j)
      (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j) p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k (PairChartRing k g r₁ g r₂ i j) p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)
          p.asIdeal.ResidueField,
        IsScalarTower.algebraMap_apply k (PairChartRing k g r₁ g r₂ i j)
          (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)]
      rfl
  haveI : Module.Finite (seedChartRing C hπ g r₁ r₂ b₁ b₂ i j)
      ↥(divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) :=
    finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  haveI : Module.Finite p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[seedChartRing C hπ g r₁ r₂ b₁ b₂ i j]
        ↥(divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)) :=
    Module.Finite.base_change _ _ _
  have hsrc := finrank_baseChange_divUniversalSeedK_add C hπ g r₁ r₂ b₁ b₂ i j p
  have hrng := finrank_range_baseChange_chartReadMap_divUniversalSeedK_add
    C hπ g r₁ r₂ b₁ b₂ i j p.asIdeal.ResidueField b (hη p) hχ
  exact range_subtype_rTensor_injective_of_baseChange_injective p.asIdeal.ResidueField
    (chartReadMap (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b)
    (injective_of_finrank_range_eq _ (Nat.add_right_cancel (hrng.trans hsrc.symm)))

end HsubChart

end ThetaGeneratorSeed

end AlgebraicGeometry
