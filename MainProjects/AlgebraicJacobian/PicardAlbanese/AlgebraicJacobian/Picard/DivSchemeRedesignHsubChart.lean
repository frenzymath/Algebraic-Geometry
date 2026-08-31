/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUniv
import AlgebraicJacobian.Picard.DivCarveKit

/-!
# DD-4 — the carve pin `hsub_chart`: the κ(p) base-change assembly

The heavy native-`κ(p)` base-change declaration that closes the carve fibre non-collapse
`hsub_chart` at the universal seed.  This file assembles the landed inputs at
`K := κ(p) = p.asIdeal.ResidueField` over `R_Z = DivCarveChartRing` (the native residue-field
tower, I-0295 verdict) into the constant-rank pin.

The mathematical skeleton (both sides have the constant fibre dimension `r₁ − g`, so the
base-changed chart reading map is injective on every residue fibre):

* the **source rank** `finrank κ(p) (κ(p) ⊗ K_univ) = r₁ − g` — `K_univ = divUniversalSeedK`
  is linearly the tautological Grassmannian subbundle `divUniversalFst` (corank `g`), so its
  residue fibre has constant dimension `r₁ − g` (`finrank_ker_baseChangeMkQ_add_of_field`);
  this file lands it as `finrank_baseChange_divUniversalSeedK_add`.
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

section HsubChart

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftHsubChart : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

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
abbrev seedChartRing' : Type u :=
  DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j

set_option maxHeartbeats 4000000 in
-- the heavy seed section-ring type `↥divUniversalSeedK` drives the base-changed linear
-- equivalence past the default budget (isolated so the assembly stays light)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- (Implementation) The residue fibre of the seed `K_univ` and of the tautological subbundle
`divUniversalFst` have the same `κ(p)`-dimension: they are `R_Z`-linearly identified through
`divUniversalFstWindowEquiv.trans divUniversalSeedKEquiv`, and base change preserves that
identification.  Isolated with its own budget — the heavy `relThetaSections` seed type is only
touched here. -/
private theorem finrank_baseChange_divUniversalSeedK_eq
    (p : PrimeSpectrum (seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j)) :
    Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j]
          ↥(divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j))
      = Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j]
          ↥(divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule) :=
  (LinearEquiv.finrank_eq (LinearEquiv.baseChange
    (seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j) p.asIdeal.ResidueField _ _
    ((divUniversalFstWindowEquiv C π hπ g r₁ r₂ b₁ b₂ i j).trans
      (divUniversalSeedKEquiv C π hπ g r₁ r₂ b₁ b₂ i j)))).symm

set_option maxHeartbeats 2400000 in
-- the native residue-field tower `k → R_{I,J} → R_Z → κ(p)` synthesis (I-0295 verdict)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- (Implementation) The corank-`g` law of the tautological subbundle `divUniversalFst` at the
residue field `κ(p)`: its `κ(p)`-fibre has dimension `r₁ − g` (spelled `+ g = dim_k (Fin r₁ →
k)`).  Light — all objects live over the free ambient `Fin r₁ → k`.  The fibre `κ(p) ⊗ N` of the
subbundle `N` is `ker (baseChangeMkQ κ(p) N)` (`N.subtype` split-injective via `quotRetract`,
`ker_baseChangeMkQ_eq_map_baseChange`), whose dimension `finrank_ker_baseChangeMkQ_add_of_field`
pins at `r₁ − g`. -/
private theorem finrank_baseChange_divUniversalFst_toSubmodule_add
    (p : PrimeSpectrum (seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j)) :
    Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j]
          ↥(divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule) + g
      = Module.finrank k (Fin r₁ → k) := by
  set κ := p.asIdeal.ResidueField with hκ
  set N := (divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule with hN
  haveI hproj : Module.Projective (seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j)
      (TensorProduct k (seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j) (Fin r₁ → k) ⧸ N) :=
    (divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).projective_quotient
  -- `N.subtype` is split-injective (`quotRetract`), so its base change is injective
  have hsplit : quotRetract N ∘ₗ N.subtype = LinearMap.id :=
    LinearMap.ext fun x => quotRetract_apply_of_mem N x.2
  have hinj : Function.Injective (LinearMap.baseChange κ N.subtype) := by
    have hli : LinearMap.baseChange κ (quotRetract N) ∘ₗ LinearMap.baseChange κ N.subtype
        = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hsplit, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective
      (g := LinearMap.baseChange κ (quotRetract N))
      fun x => by rw [← LinearMap.comp_apply, hli, LinearMap.id_apply]
  -- `κ ⊗ N ≅ N.baseChange κ ≅ ker (baseChangeMkQ κ N)` (linear equivs)
  have hfr2 : Module.finrank κ (κ ⊗[seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j] ↥N)
      = Module.finrank κ ↥(N.baseChange κ) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofInjective (LinearMap.baseChange κ N.subtype) hinj)
  have hfr3 : Module.finrank κ ↥(N.baseChange κ)
      = Module.finrank κ ↥(LinearMap.ker (Module.Grassmannian.baseChangeMkQ κ N)) := by
    rw [ker_baseChangeMkQ_eq_map_baseChange (k := k) κ N]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k
        (seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j) κ κ (Fin r₁ → k)).injective (N.baseChange κ))
  -- the corank-`g` law of the tautological point at the field `κ`
  have hcorank := Grassmannian.finrank_ker_baseChangeMkQ_add_of_field
    (divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) κ
  rw [← hN] at hcorank
  rw [hfr2, hfr3]
  exact hcorank

/-- **The source rank of the carve seed at `κ(p)`**: the universal seed `K_univ`, base-changed
to the residue field `κ(p)` of any prime `p` of `R_Z`, has constant `κ(p)`-dimension `r₁ − g`
(spelled `+ g = dim_k (Fin r₁ → k)`).  `K_univ` is `R_Z`-linearly the tautological Grassmannian
subbundle `divUniversalFst` (through `finrank_baseChange_divUniversalSeedK_eq`), so its residue
fibre is the corank-`g` fibre of that subbundle
(`finrank_baseChange_divUniversalFst_toSubmodule_add`) — no fibre of `K_univ` gains or loses
dimension over any prime.  This is the source half of the constant-rank pin that discharges the
carve fibre non-collapse `hsub_chart`. -/
theorem finrank_baseChange_divUniversalSeedK_add
    (p : PrimeSpectrum (seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j)) :
    Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[seedChartRing' C hπ g r₁ r₂ b₁ b₂ i j]
          ↥(divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)) + g
      = Module.finrank k (Fin r₁ → k) :=
  (congrArg (· + g)
      (finrank_baseChange_divUniversalSeedK_eq C hπ g r₁ r₂ b₁ b₂ i j p)).trans
    (finrank_baseChange_divUniversalFst_toSubmodule_add C hπ g r₁ r₂ b₁ b₂ i j p)

end HsubChart

end ThetaGeneratorSeed

end AlgebraicGeometry
