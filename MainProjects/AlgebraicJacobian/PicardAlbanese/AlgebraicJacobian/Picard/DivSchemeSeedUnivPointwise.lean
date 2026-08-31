/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignPointwiseGeneric
import AlgebraicJacobian.Picard.DivSchemeRedesignKappaZ

/-!
# The pointwise universal seed and its RD-N reduction

The original universal seed chooses a section only from a base-prime nonvanishing
condition.  The redesigned pointwise section instead chooses an achiever at every
non-generic point of the residue fibre, and a nonzero section at the fibre generic point.

This file installs that section into a `ThetaGeneratorSeed`, defines the corresponding
chart colength and RD-N condition, and constructs the ann-cutter seed whenever RD-N is
available.  It also closes the fibre-generic part of RD-N.  Thus the remaining RD-N input
is isolated exactly to non-generic residue-fibre points, where the achiever must be lifted
from fibre divisibility to the total stalk.
-/

set_option autoImplicit false
set_option quotPrecheck false
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

namespace PointwiseAchiever

section SeedContext

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftPointwiseSeed :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
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

noncomputable local instance instIsIntegralRelCurvePointwiseSeed
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointwiseSeed
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointwiseSeed
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

local notation "RZ" => seedChartRing C hπ g r₁ r₂ b₁ b₂ i j

/-! ## The pointwise section as a seed -/

/-- Choose a pinned chart containing each total-space point. -/
noncomputable def pointwiseSide (z : relCurve C RZ) : Bool :=
  (exists_mem_relPinnedChart (C := C) (π := π) z).choose

set_option linter.unusedSectionVars false in
/-- The chosen pointwise side contains the point. -/
theorem pointwiseSide_mem (z : relCurve C RZ) :
    z ∈ relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) :=
  (exists_mem_relPinnedChart (C := C) (π := π) z).choose_spec

set_option maxHeartbeats 2400000 in
-- The dependent seed fields re-elaborate the residue-field and theta-window towers.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The pointwise section installed in a seed with the full chosen chart as its initial
piece.  The ann-cutter below shrinks this seed after RD-N is established. -/
noncomputable def pointwiseWideSeed :
    ThetaGeneratorSeed C RZ π (windowM_choice π hπ g)
      (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) where
  side := pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j
  h := fun _ => 1
  mem_basicOpen := fun z => by
    rw [Scheme.basicOpen_one]
    exact pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z
  sec := pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ
  sec_mem := pointwiseSection_mem C hπ g r₁ r₂ b₁ b₂ i j hO hχ

set_option maxHeartbeats 2400000 in
-- Unfolding the dependent seed projection re-elaborates its theta-window tower.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The pointwise seed's section is definitionally the redesigned pointwise section. -/
theorem pointwiseWideSeed_sec (z : relCurve C RZ) :
    (pointwiseWideSeed C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z =
      pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z :=
  rfl

/-! ## Pointwise RD-N and the ann-cutter seed -/

set_option maxHeartbeats 2400000 in
-- The chart colength type contains the full seed ring and dependent chart section ring.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The chart colength attached to the pointwise section at `z`. -/
noncomputable def pointwiseSeedColength (z : relCurve C RZ) :=
  chartColengthModule (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)
    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)
    (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)

set_option maxHeartbeats 2400000 in
-- The support predicate re-elaborates the dependent chart-colength module at each point.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- RD-N for the pointwise seed: its chart colength avoids the prime of every total point. -/
abbrev PointwiseSeedRDN : Prop :=
  ∀ z : relCurve C RZ,
    (isAffineOpen_relPinnedChart C RZ π
        (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)).primeIdealOf
        ⟨z, pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z⟩ ∉
      Module.support
        Γ(relCurve C RZ,
          relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z))
        ↥(pointwiseSeedColength C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)

set_option maxHeartbeats 2400000 in
-- Applying the ann-cutter reconstructs finiteness over the dependent chart section ring.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- RD-N supplies an ann-cutter for the pointwise section at every point. -/
theorem exists_pointwiseAnnCutter
    (hrdn : PointwiseSeedRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ)
    (z : relCurve C RZ) :
    ∃ h : Γ(relCurve C RZ,
        relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)),
      z ∈ (relCurve C RZ).basicOpen h ∧
      ∀ ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄,
        ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j →
        h * relThetaResSide (windowM_choice π hπ g)
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl ψ
          ∈ Ideal.span {relThetaResSide (windowM_choice π hπ g)
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl
            (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)} := by
  haveI := finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  exact exists_h_mem_basicOpen_forall_mul_read_mem_span
    (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)
    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)
    (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)
    (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z) (hrdn z)

set_option maxHeartbeats 2400000 in
-- The seed structure substitutes the chosen ann-cutter through dependent chart fields.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The pointwise seed shrunk by its RD-N ann-cutter. -/
noncomputable def pointwiseAnnSeed
    (hrdn : PointwiseSeedRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ) :
    ThetaGeneratorSeed C RZ π (windowM_choice π hπ g)
      (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) where
  side := pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j
  h := fun z =>
    (exists_pointwiseAnnCutter C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose
  mem_basicOpen := fun z =>
    (exists_pointwiseAnnCutter C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose_spec.1
  sec := pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ
  sec_mem := pointwiseSection_mem C hπ g r₁ r₂ b₁ b₂ i j hO hχ

set_option maxHeartbeats 2400000 in
-- Projecting the ann-cutter seed re-elaborates its dependent side and section fields.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The ann-cutter seed has the direct chart-reading containment needed by the redesigned
generator theorem. -/
theorem pointwiseAnnSeed_mul_read_mem_span
    (hrdn : PointwiseSeedRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ)
    (z : relCurve C RZ)
    ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄
    (hψ : ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) :
    (pointwiseAnnSeed C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).h z *
        relThetaResSide (windowM_choice π hπ g)
          ((pointwiseAnnSeed C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).side z)
          le_rfl ψ
      ∈ Ideal.span {relThetaResSide (windowM_choice π hπ g)
        ((pointwiseAnnSeed C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).side z)
        le_rfl
        ((pointwiseAnnSeed C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn).sec z)} :=
  (exists_pointwiseAnnCutter C hπ g r₁ r₂ b₁ b₂ i j hO hχ hrdn z).choose_spec.2 hψ

/-! ## RD-N from germ generation -/

set_option maxHeartbeats 2400000 in
-- The germ-support reduction carries the full seed ring and dependent stalk types.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Pointwise RD-N follows from germ-level local generation by the pointwise section. -/
theorem pointwiseSeedRDN_of_forall_germ_mem_span
    (hgerm : ∀ (z : relCurve C RZ)
      ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄,
      ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j →
        ((relCurve C RZ).presheaf.germ
            (relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)) z
            (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z)).hom
          (relThetaResSide (windowM_choice π hπ g)
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl ψ)
        ∈ Ideal.span {((relCurve C RZ).presheaf.germ
            (relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)) z
            (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z)).hom
          (relThetaResSide (windowM_choice π hπ g)
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl
            (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z))}) :
    PointwiseSeedRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ := by
  intro z
  haveI := finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  exact notMem_support_chartColengthModule_of_forall_germ_mem_span
    (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)
    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)
    (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)
    (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z) (hgerm z)

/-! ## The fibre-generic branch -/

set_option maxHeartbeats 2400000 in
-- The fibre-generic germ theorem reconstructs the residue-field tower at the total point.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- At a fibre-generic point, the pointwise seed section generates every seed reading in
the total stalk. -/
theorem germ_mem_span_pointwiseSeed_of_residuePoint_generic
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z =
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄
    (hψ : ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) :
    ((relCurve C RZ).presheaf.germ
        (relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)) z
        (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z)).hom
      (relThetaResSide (windowM_choice π hπ g)
        (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl ψ)
      ∈ Ideal.span {((relCurve C RZ).presheaf.germ
        (relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)) z
        (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z)).hom
      (relThetaResSide (windowM_choice π hπ g)
        (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl
        (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z))} :=
  germ_relThetaResSide_mem_span_pointwiseSection_of_residuePoint_generic
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ z
    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)
    (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z) hzg hψ

set_option maxHeartbeats 2400000 in
-- Combining generic germ generation with support avoidance re-elaborates both stalk towers.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- RD-N holds at every point which is generic in its residue fibre. -/
theorem pointwiseSeedRDN_at_residuePoint_generic
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z =
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :
    (isAffineOpen_relPinnedChart C RZ π
        (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)).primeIdealOf
        ⟨z, pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z⟩ ∉
      Module.support
        Γ(relCurve C RZ,
          relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z))
        ↥(pointwiseSeedColength C hπ g r₁ r₂ b₁ b₂ i j hO hχ z) := by
  haveI := finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  exact notMem_support_chartColengthModule_of_forall_germ_mem_span
    (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)
    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)
    (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)
    (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z)
    (fun _ψ hψ =>
      germ_mem_span_pointwiseSeed_of_residuePoint_generic
        C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg hψ)

set_option maxHeartbeats 2400000 in
-- The closed-branch predicate contains the full dependent chart-support expression.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The only remaining pointwise RD-N input: support avoidance at non-generic points of
residue fibres. -/
abbrev PointwiseSeedClosedRDN : Prop :=
  ∀ (z : relCurve C RZ),
    relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField) →
    (isAffineOpen_relPinnedChart C RZ π
        (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)).primeIdealOf
        ⟨z, pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z⟩ ∉
      Module.support
        Γ(relCurve C RZ,
          relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z))
        ↥(pointwiseSeedColength C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)

set_option maxHeartbeats 2400000 in
-- The branch split re-elaborates the residue-field generic point and support predicates.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The fibre-generic theorem reduces full pointwise RD-N to the non-generic branch. -/
theorem pointwiseSeedRDN_of_closed
    (hclosed : PointwiseSeedClosedRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ) :
    PointwiseSeedRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ := by
  intro z
  by_cases hzg : relCurveResiduePoint C RZ z =
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)
  · exact pointwiseSeedRDN_at_residuePoint_generic
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg
  · exact hclosed z hzg

/-! ## Decoupled pointwise seed -/

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The wide pointwise seed at divisor degree `g` and curve parameter `gamma ≤ g`. -/
noncomputable def pointwiseWideSeed_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    ThetaGeneratorSeed C RZ π (windowM_choice π hπ g)
      (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) where
  side := pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j
  h := fun _ => 1
  mem_basicOpen := fun z => by
    rw [Scheme.basicOpen_one]
    exact pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z
  sec := pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ
  sec_mem := pointwiseSection_mem_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The decoupled wide seed selects the decoupled pointwise section. -/
theorem pointwiseWideSeed_sec_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) :
    (pointwiseWideSeed_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ).sec z =
      pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z :=
  rfl

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The chart colength of the decoupled pointwise section. -/
noncomputable def pointwiseSeedColength_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) :=
  chartColengthModule (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)
    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)
    (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- RD-N for the decoupled pointwise seed. -/
abbrev PointwiseSeedRDNAt {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) : Prop :=
  ∀ z : relCurve C RZ,
    (isAffineOpen_relPinnedChart C RZ π
        (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)).primeIdealOf
        ⟨z, pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z⟩ ∉
      Module.support
        Γ(relCurve C RZ,
          relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z))
        ↥(pointwiseSeedColength_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- RD-N supplies an ann-cutter for each decoupled pointwise section. -/
theorem exists_pointwiseAnnCutter_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hrdn : PointwiseSeedRDNAt C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ)
    (z : relCurve C RZ) :
    ∃ h : Γ(relCurve C RZ,
        relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)),
      z ∈ (relCurve C RZ).basicOpen h ∧
      ∀ ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄,
        ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j →
        h * relThetaResSide (windowM_choice π hπ g)
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl ψ
          ∈ Ideal.span {relThetaResSide (windowM_choice π hπ g)
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl
            (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)} := by
  haveI := finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  exact exists_h_mem_basicOpen_forall_mul_read_mem_span
    (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)
    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)
    (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)
    (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z) (hrdn z)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The decoupled pointwise seed shrunk by its RD-N ann-cutter. -/
noncomputable def pointwiseAnnSeed_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hrdn : PointwiseSeedRDNAt C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ) :
    ThetaGeneratorSeed C RZ π (windowM_choice π hπ g)
      (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) where
  side := pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j
  h := fun z =>
    (exists_pointwiseAnnCutter_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ hrdn z).choose
  mem_basicOpen := fun z =>
    (exists_pointwiseAnnCutter_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ hrdn z).choose_spec.1
  sec := pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ
  sec_mem := pointwiseSection_mem_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The decoupled ann-cutter seed satisfies the direct chart-reading containment. -/
theorem pointwiseAnnSeed_mul_read_mem_span_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hrdn : PointwiseSeedRDNAt C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ)
    (z : relCurve C RZ)
    ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄
    (hψ : ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) :
    (pointwiseAnnSeed_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ hrdn).h z *
        relThetaResSide (windowM_choice π hπ g)
          ((pointwiseAnnSeed_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ hrdn).side z)
          le_rfl ψ
      ∈ Ideal.span {relThetaResSide (windowM_choice π hπ g)
        ((pointwiseAnnSeed_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ hrdn).side z)
        le_rfl
        ((pointwiseAnnSeed_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ hrdn).sec z)} :=
  (exists_pointwiseAnnCutter_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ hrdn z).choose_spec.2 hψ

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Germ-level local generation implies decoupled pointwise RD-N. -/
theorem pointwiseSeedRDNAt_of_forall_germ_mem_span {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hgerm : ∀ (z : relCurve C RZ)
      ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄,
      ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j →
        ((relCurve C RZ).presheaf.germ
            (relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)) z
            (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z)).hom
          (relThetaResSide (windowM_choice π hπ g)
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl ψ)
        ∈ Ideal.span {((relCurve C RZ).presheaf.germ
            (relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)) z
            (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z)).hom
          (relThetaResSide (windowM_choice π hπ g)
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl
            (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z))}) :
    PointwiseSeedRDNAt C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ := by
  intro z
  haveI := finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  exact notMem_support_chartColengthModule_of_forall_germ_mem_span
    (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)
    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)
    (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)
    (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z) (hgerm z)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Fibre-generic germ generation for the decoupled pointwise seed. -/
theorem germ_mem_span_pointwiseSeed_of_residuePoint_generic_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z =
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄
    (hψ : ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) :
    ((relCurve C RZ).presheaf.germ
        (relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)) z
        (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z)).hom
      (relThetaResSide (windowM_choice π hπ g)
        (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl ψ)
      ∈ Ideal.span {((relCurve C RZ).presheaf.germ
        (relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)) z
        (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z)).hom
      (relThetaResSide (windowM_choice π hπ g)
        (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl
        (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z))} :=
  germ_relThetaResSide_mem_span_pointwiseSection_of_residuePoint_generic_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z
    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)
    (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z) hzg hψ

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- RD-N holds at every fibre-generic point for the decoupled section. -/
theorem pointwiseSeedRDNAt_residuePoint_generic {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z =
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :
    (isAffineOpen_relPinnedChart C RZ π
        (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)).primeIdealOf
        ⟨z, pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z⟩ ∉
      Module.support
        Γ(relCurve C RZ,
          relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z))
        ↥(pointwiseSeedColength_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z) := by
  haveI := finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  exact notMem_support_chartColengthModule_of_forall_germ_mem_span
    (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j)
    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)
    (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)
    (pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z)
    (fun _ψ hψ => germ_mem_span_pointwiseSeed_of_residuePoint_generic_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg hψ)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The closed-point part of decoupled pointwise RD-N. -/
abbrev PointwiseSeedClosedRDNAt {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) : Prop :=
  ∀ (z : relCurve C RZ),
    relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField) →
    (isAffineOpen_relPinnedChart C RZ π
        (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)).primeIdealOf
        ⟨z, pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z⟩ ∉
      Module.support
        Γ(relCurve C RZ,
          relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z))
        ↥(pointwiseSeedColength_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The fibre-generic theorem reduces decoupled pointwise RD-N to the closed branch. -/
theorem pointwiseSeedRDNAt_of_closed {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hclosed : PointwiseSeedClosedRDNAt C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ) :
    PointwiseSeedRDNAt C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ := by
  intro z
  by_cases hzg : relCurveResiduePoint C RZ z =
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)
  · exact pointwiseSeedRDNAt_residuePoint_generic
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg
  · exact hclosed z hzg

end SeedContext

end PointwiseAchiever

end AlgebraicGeometry
