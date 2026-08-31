/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignSeedUniv

/-!
# DD-4 redesign: retain the old fibre-regularity factor in the ann-cutter

The ann-cutter produced from RD-N gives the direct divisibility statement, but by itself it
does not carry the old base-locus information used by `seedUniv_hfib`.  Multiplying it by the
old seed's `h` retains that information: the product basic open is contained in the old one,
and the ann containment is stable under multiplication by the old factor.
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

section ProductCutter

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
variable {K : Submodule R (relThetaSections C R π a)}

/-- Multiply a seed's existing cutter by a second point-containing chart section. -/
noncomputable def productCutter (D : ThetaGeneratorSeed C R π a K)
    (c : ∀ z : relCurve C R, Γ(relCurve C R, relPinnedChart C R π (D.side z)))
    (hc : ∀ z : relCurve C R, z ∈ (relCurve C R).basicOpen (c z)) :
    ThetaGeneratorSeed C R π a K where
  side := D.side
  h := fun z => c z * D.h z
  mem_basicOpen := fun z => by
    rw [(relCurve C R).basicOpen_mul]
    exact ⟨hc z, D.mem_basicOpen z⟩
  sec := D.sec
  sec_mem := D.sec_mem

variable [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- Multiplying an ann-cutter by a seed whose fibre nonvanishing is already known preserves
both inputs of `isGenerator_of_ann_cutter`. -/
theorem isGenerator_productCutter (D : ThetaGeneratorSeed C R π a K)
    (c : ∀ z : relCurve C R, Γ(relCurve C R, relPinnedChart C R π (D.side z)))
    (hc : ∀ z : relCurve C R, z ∈ (relCurve C R).basicOpen (c z))
    (hann : ∀ (z : relCurve C R) ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
      c z * relThetaResSide a (D.side z) le_rfl ψ
        ∈ Ideal.span {relThetaResSide a (D.side z) le_rfl (D.sec z)})
    (hfib : ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      ((relCurve C p.asIdeal.ResidueField).basicOpen
          (relPinnedSectionsMap C R p.asIdeal.ResidueField π (D.side z) (D.h z)) :
        (relCurve C p.asIdeal.ResidueField).Opens) ≠ ⊥ →
      relPinnedSectionsMap C R p.asIdeal.ResidueField π (D.side z)
        (relThetaResSide a (D.side z) le_rfl (D.sec z)) ≠ 0) :
    (productCutter D c hc).IsGenerator := by
  apply isGenerator_of_ann_cutter (productCutter D c hc)
  · intro z ψ hψ
    dsimp only [productCutter]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (Ideal.mul_mem_left _ (D.h z) (hann z hψ))
  · intro z p hne
    apply hfib z p
    intro hbot
    apply hne
    change (relCurve C p.asIdeal.ResidueField).basicOpen
        (relPinnedSectionsMap C R p.asIdeal.ResidueField π (D.side z)
          (c z * D.h z)) = ⊥
    rw [(relPinnedSectionsMap C R p.asIdeal.ResidueField π (D.side z)).map_mul,
      (relCurve C p.asIdeal.ResidueField).basicOpen_mul, hbot, inf_bot_eq]

end ProductCutter

section SeedUnivProduct

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftSeedUnivProduct : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

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

local notation "RZ" => seedChartRing C hπ g r₁ r₂ b₁ b₂ i j
local notation "X" => relCurve C RZ

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The product of the RD-N ann-cutter and the old coherent base-locus factor. -/
noncomputable def seedUnivProduct
    (hrdn : SeedUnivRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ) :
    ThetaGeneratorSeed C RZ π (windowM_choice π hπ g)
      (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) :=
  productCutter (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ)
    (fun z => (exists_seedUniv'_h C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose)
    (fun z => (exists_seedUniv'_h C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose_spec.1)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The product-cutter seed is a generator with no external `hfib` argument. -/
theorem isGenerator_seedUnivProduct
    (hrdn : SeedUnivRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ) :
    (seedUnivProduct C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).IsGenerator :=
  isGenerator_productCutter
    (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ)
    (fun z => (exists_seedUniv'_h C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose)
    (fun z => (exists_seedUniv'_h C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose_spec.1)
    (fun z _ψ hψ =>
      (exists_seedUniv'_h C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose_spec.2 hψ)
    (seedUniv_hfib C hπ g r₁ r₂ b₁ b₂ i j hO hχ)

end SeedUnivProduct

end ThetaGeneratorSeed

end AlgebraicGeometry
