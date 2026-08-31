/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeClassifyBridgeIff

/-!
# DDR-6 §3b — `divClassifyAff` (split from `DivSchemeClassify.lean`)

The campaign classification keystone: a divisor family over an affine test whose
ε-pair satisfies the carve in DDR-2's spelling and is chart-framed through the DD-4
boundary bases factors uniquely through `divSchemeι`.  See the parent files for §1/§2
and the multiplier bridge; split into its own compilation unit for memory.

The chart-frame data (`hw₁`/`hw₂`) is honest *input*: producing it from the finite
projective ε-certificates over a basic-open cover of `Spec S` is the DDR-9 assembly
seam (`informal/spec-w4-gates.md` G-5), where ε-naturality (G-2) enters.
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

/-! ## §3 The campaign spelling: `divClassifyAff` -/

section Curve

open Scheme

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftClassifyAff :
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

/-- **`divClassifyAff` — DDR-6, classify + factor** (`informal/spec-dd-r.md` §3 item 6):
a divisor family `F` of degree `g` over an affine test `S` whose ε-pair

* satisfies the carve `(♦)` in DDR-2's spelling
  (`carvePairArrow (windowShiftMul hπ g a) ε₁ ε₂ = 0` for every multiplier section
  `a ∈ H⁰(𝒪(s·F))`), and
* is **chart-framed**: a pair-chart map `w : R_{I,J} →ₐ[k] S` pulls the tautological
  pair back to the coordinate images of `(ε₁, ε₂)` under the DD-4 boundary bases,

factors **uniquely** through the closed immersion `divSchemeι : DivScheme g ⟶ grPair`,
over the pair chart `(I, J)`.  Existence is DDR-1's universal property; uniqueness is
DDR-7's hom-ext (`divScheme_hom_ext`).

The chart-frame data `hw₁`/`hw₂` is honest input — the affine-global frame-locus cover
producing it (frame loci of the finite projective ε-certificates,
`matrixPoint_factors_chart_iff`, morphism gluing) is the DDR-9 assembly seam, where
ε-naturality along localizations (DD-4 Task 7) enters.  Setoid-invariance is free:
the statement lives on `DivFam`. -/
theorem divClassifyAff (F : DivFam C S π g)
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] S)
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange S b₁.equivFun.toLinearMap)
          (divFamEps hπ g F).1)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange S b₂.equivFun.toLinearMap)
          (divFamEps hπ g F).2)
    (hcarve : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g F).1 (divFamEps hπ g F).2 = 0) :
    ∃! v : Spec (CommRingCat.of S) ⟶
        DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm),
      v ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
        = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j := by
  refine existsUnique_carveScheme_factor_of_map_pairTaut k g r₁ r₂
    (divCarveMul k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) r₁ r₂ b₁
      (b₂.map (windowShiftEquiv hπ g).symm)) i j w hw₁ hw₂ ?_
  intro a
  exact (carvePairArrow_divCarveMul_eq_zero_iff hπ g r₁ r₂ b₁ b₂ _ _ a).mpr (hcarve a)

end Curve

end AlgebraicGeometry
