/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowMulConjugacy
import AlgebraicJacobian.Picard.DivSchemeHighWindowConjugacy
import AlgebraicJacobian.Picard.DivSchemeHighWindowFibreModel
import AlgebraicJacobian.Picard.DivSchemeHighWindowRelativeKoszulRelation
import AlgebraicJacobian.Picard.DivSchemeHighWindowPencilFibre

/-!
# Fibre conjugacy for the relative high-window Koszul boundary

The relative rows-minus-columns boundary is transported to the canonical
Koszul boundary on every field-valued carve-chart fibre.  Together with the
field exactness theorem, this is the non-circular input to finite-stage
flatness over the nonreduced carve ring.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowRelationKoszulConjugacy

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowRelationKoszulConjugacy :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k
    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k
    ((windowS_choice pi hpi g • fiberWeilDivisor pi) +
      (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
local notation "HS0" => ↥(Scheme.divisorSections k
  (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)
local notation "HI" => Fin (Module.finrank k HS0)
local notation "Amb[" n "]" => divUniversalHighWindowAmbient
  (C := C) (pi := pi) (hpi := hpi) (g := g)
    (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n
local notation "Kr[" n "]" => divUniversalHighWindowRelation
  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n

variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r1 g r2 i j) K]
  [IsScalarTower k (PairChartRing k g r1 g r2 i j) K]
  [Algebra (DivCarveChartRing k
    (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi)
    g r1 r2 b1 b2 i j) K]
  [IsScalarTower (PairChartRing k g r1 g r2 i j)
    (DivCarveChartRing k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j) K]
  [IsScalarTower k (DivCarveChartRing k
    (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi)
    g r1 r2 b1 b2 i j) K]

noncomputable local instance instIsIntegralRelCurveHighWindowRelationKoszulConjugacy :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveHighWindowRelationKoszulConjugacy :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveHighWindowRelationKoszulConjugacy :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveHighWindowRelationKoszulConjugacy :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveHighWindowRelationKoszulConjugacy :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveHighWindowRelationKoszulConjugacy :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
  (hker : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))

local notation "HF[" n "]" => divUniversalFibreHighWindow
  C hpi g r1 r2 b1 b2 i j K hO hchi hker n
local notation "Dᵤ" => divUniversalFibreDivisor
  C hpi g r1 r2 b1 b2 i j K hO hchi hker

set_option maxHeartbeats 2400000 in
-- The pair-indexed product and projective relation fibre are reduction-heavy.
set_option synthInstance.maxHeartbeats 800000 in
-- The carve-ring scalar tower is synthesized for every product component.
/-- Scalar extension distributes over the pair-indexed Koszul source, and
each relation component is read in its canonical divisor fibre window. -/
noncomputable def divUniversalHighWindowRelationKoszulSourceFibreEquiv (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n) :
    K ⊗[RZ] (HI × HI → ↥Kr[n]) ≃ₗ[K] (HI × HI → ↥HF[n]) :=
  (TensorProduct.piRight RZ K K (fun _ : HI × HI => ↥Kr[n])).trans
    (LinearEquiv.piCongrRight fun _ : HI × HI =>
      divUniversalHighWindowRelationFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage)

set_option maxHeartbeats 2400000 in
-- Reducing the pair-indexed composite equivalence exceeds the default budget.
set_option synthInstance.maxHeartbeats 800000 in
-- The pointwise relation-fibre equivalence retains the carve-ring scalar tower.
@[simp]
theorem divUniversalHighWindowRelationKoszulSourceFibreEquiv_apply (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)
    (x : K ⊗[RZ] (HI × HI → ↑Kr[n])) (q : HI × HI) :
    divUniversalHighWindowRelationKoszulSourceFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage x q =
      divUniversalHighWindowRelationFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage
        (TensorProduct.piRightHom RZ K K (fun _ : HI × HI => ↑Kr[n]) x q) := by
  rw [divUniversalHighWindowRelationKoszulSourceFibreEquiv,
    LinearEquiv.trans_apply, TensorProduct.piRight_apply]
  rfl

set_option maxHeartbeats 4000000 in
-- Comparing the corestricted relation step with the ambient row is reduction-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
-- Both consecutive projective relation fibres carry the full scalar tower.
set_option maxRecDepth 20000 in
/-- One relative relation-basis step becomes multiplication by the corresponding
member of the scalar-extended multiplier basis on canonical fibre windows. -/
theorem divUniversalHighWindowRelationBasisStep_fibre_conjugacy (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    [Module.Projective RZ (Amb[n + 1] ⧸ Kr[n + 1])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)
    (himageNext : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1))
    (t : HI) (x : K ⊗[RZ] ↥Kr[n]) :
    divUniversalHighWindowRelationFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1) himageNext
        (LinearMap.baseChange K
          (divUniversalHighWindowRelationBasisStep (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n t) x) =
      Scheme.finiteMulStepTo
        (Scheme.divisorSections K (windowS C K hpi g) ⊤) HF[n] HF[n + 1]
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
        (fun s z => Scheme.mul_mem_divisorSections_highWindow
          (windowN C K hpi g) (windowS C K hpi g) Dᵤ n
          (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K s) z)
        t
        (divUniversalHighWindowRelationFibreEquiv
          C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage x) := by
  have hsub :
      Kr[n + 1].subtype.comp
          (divUniversalHighWindowRelationBasisStep (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n t) =
        divUniversalHighWindowMulRow (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n Kr[n] t := by
    apply LinearMap.ext
    intro z
    rfl
  have hbcx := LinearMap.congr_fun (congrArg (LinearMap.baseChange K) hsub) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hbcx
  apply Subtype.ext
  rw [divUniversalHighWindowRelationFibreEquiv_coe, hbcx]
  simpa only [divUniversalHighWindowClosedAmbientFibreRead_apply,
    Scheme.finiteMulStepTo_apply] using
    (divUniversalHighWindowMulRow_fibre_conjugacy
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hO hchi hker
        n himage t x)

set_option maxHeartbeats 4800000 in
-- The map equation combines two dependent finite-product conjugacy squares.
set_option synthInstance.maxHeartbeats 1200000 in
-- Consecutive projective fibres and their Koszul sources share a deep scalar tower.
set_option maxRecDepth 24000 in
/-- The scalar extension of the relative relation Koszul boundary is conjugate
to the canonical high-window Koszul boundary on the divisor fibre. -/
theorem divUniversalHighWindowRelationKoszulBoundary_fibre_conjugacy (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    [Module.Projective RZ (Amb[n + 1] ⧸ Kr[n + 1])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)
    (himageNext : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1)) :
    (divUniversalHighWindowMulSourceFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1) himageNext).toLinearMap.comp
      (LinearMap.baseChange K
        (divUniversalHighWindowRelationKoszulBoundary (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n)) =
    (Scheme.highWindowMulKoszulBoundary
        (windowN C K hpi g) (windowS C K hpi g) Dᵤ n
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)).comp
      (divUniversalHighWindowRelationKoszulSourceFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage).toLinearMap := by
  let stepR : HI → ↑Kr[n] →ₗ[RZ] ↑Kr[n + 1] := fun t =>
    divUniversalHighWindowRelationBasisStep (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n t
  let stepF : HI → ↑HF[n] →ₗ[K] ↑HF[n + 1] := fun t =>
    Scheme.finiteMulStepTo
      (Scheme.divisorSections K (windowS C K hpi g) ⊤) HF[n] HF[n + 1]
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
      (fun s z => Scheme.mul_mem_divisorSections_highWindow
        (windowN C K hpi g) (windowS C K hpi g) Dᵤ n
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K s) z) t
  let eNow : (K ⊗[RZ] ↑Kr[n]) ≃ₗ[K] ↑HF[n] :=
    divUniversalHighWindowRelationFibreEquiv
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage
  let eNext : (K ⊗[RZ] ↑Kr[n + 1]) ≃ₗ[K] ↑HF[n + 1] :=
    divUniversalHighWindowRelationFibreEquiv
      C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1) himageNext
  have hbase := piRightHom_comp_baseChange_finiteKoszulBoundary
    (R := RZ) (S := K) stepR
  have hstep : ∀ (t : HI) (x : K ⊗[RZ] ↑Kr[n]),
      eNext (LinearMap.baseChange K (stepR t) x) = stepF t (eNow x) := by
    intro t x
    simpa only [stepR, stepF, eNow, eNext] using
      divUniversalHighWindowRelationBasisStep_fibre_conjugacy
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hO hchi hker
          n himage himageNext t x
  have hconj := piCongrRight_comp_finiteKoszulBoundary_of_conjugate
    (step := fun t => LinearMap.baseChange K (stepR t))
    (step' := stepF) eNow eNext hstep
  change
    ((LinearEquiv.piCongrRight fun _ : HI => eNext).toLinearMap.comp
        (TensorProduct.piRightHom RZ K K (fun _ : HI => ↑Kr[n + 1]))).comp
      (LinearMap.baseChange K (finiteKoszulBoundary stepR)) =
    (finiteKoszulBoundary stepF).comp
      ((LinearEquiv.piCongrRight fun _ : HI × HI => eNow).toLinearMap.comp
        (TensorProduct.piRightHom RZ K K (fun _ : HI × HI => ↑Kr[n])))
  rw [LinearMap.comp_assoc, hbase, ← LinearMap.comp_assoc, hconj,
    LinearMap.comp_assoc]

set_option maxHeartbeats 4800000 in
-- The criterion instantiates three large base-change equivalences simultaneously.
set_option synthInstance.maxHeartbeats 1200000 in
-- The successor multiplication map and preceding boundary use adjacent stages.
set_option maxRecDepth 24000 in
/-- Adjacent projective fibre models make the injectivization of the successor
relation multiplication map remain injective after tensoring with the field. -/
theorem divUniversalHighWindowRelationMul_liftQ_rTensor_injective_of_fibre_models
    (hb : 0 < windowBound pi hpi) (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    [Module.Projective RZ (Amb[n + 1] ⧸ Kr[n + 1])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)
    (himageNext : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1)) :
    Function.Injective
      (((LinearMap.ker
          (divUniversalHighWindowMulMap (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1])).liftQ
        (divUniversalHighWindowMulMap (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]) le_rfl).rTensor K) := by
  apply liftQ_rTensor_injective_of_conjugate_boundary
    (f := divUniversalHighWindowMulMap (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1])
    (d := divUniversalHighWindowRelationKoszulBoundary (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n)
    (hfd := divUniversalHighWindowMulMap_comp_relationKoszulBoundary_eq_zero
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n)
    (f' := Scheme.finiteMulMap
      (Scheme.divisorSections K (windowS C K hpi g) ⊤) HF[n + 1]
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K))
    (d' := Scheme.highWindowMulKoszulBoundary
      (windowN C K hpi g) (windowS C K hpi g) Dᵤ n
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K))
    (eM := divUniversalHighWindowMulSourceFibreEquiv
      C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1) himageNext)
    (eN := divUniversalHighWindowClosedAmbientFibreRead
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 2))
    (eP := divUniversalHighWindowRelationKoszulSourceFibreEquiv
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage)
  · intro x
    exact divUniversalHighWindowMulMap_fibre_conjugacy
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hO hchi hker
        (n + 1) himageNext x
  · intro y
    exact LinearMap.congr_fun
      (divUniversalHighWindowRelationKoszulBoundary_fibre_conjugacy
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hO hchi hker
          n himage himageNext) y
  · exact (divUniversalFibreHighWindow_ker_finiteMulMap_eq_range_koszul
      C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)).le

set_option maxHeartbeats 4800000 in
-- Quantifying the injectivity theorem over all residue fields is elaboration-heavy.
set_option synthInstance.maxHeartbeats 1200000 in
-- Each prime reconstructs the four-step carve-ring scalar tower.
set_option maxRecDepth 24000 in
/-- Adjacent projective fibre models make the actual kernel of the successor
multiplication presentation span every residue-field kernel. -/
theorem divUniversalHighWindowKernelSyzygySpans_of_adjacent_fibreModels
    (hb : 0 < windowBound pi hpi) (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    [Module.Projective RZ (Amb[n + 1] ⧸ Kr[n + 1])]
    (hmodel : DivUniversalHighWindowFibreModel
      C hpi g r1 r2 b1 b2 i j hO hchi n)
    (hmodelNext : DivUniversalHighWindowFibreModel
      C hpi g r1 r2 b1 b2 i j hO hchi (n + 1)) :
    DivUniversalHighWindowSyzygySpans (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]
      (divUniversalHighWindowKernelSyzygy (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]) := by
  apply (divUniversalHighWindowKernelSyzygySpans_iff
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]).2
  intro p
  exact divUniversalHighWindowRelationMul_liftQ_rTensor_injective_of_fibre_models
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField hO hchi
      (divCarveIdeal_le_ker_of_tower k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j p.asIdeal.ResidueField)
      hb n (hmodel p) (hmodelNext p)

set_option maxHeartbeats 3200000 in
-- Rewriting the recursive stage and synthesizing its finite relation is expensive.
set_option synthInstance.maxHeartbeats 800000 in
-- The projective quotient consumer unfolds the dependent multiplication source.
/-- Adjacent projective fibre models force the relation quotient two stages
later to be finite projective over the possibly nonreduced carve ring. -/
theorem projective_divUniversalHighWindowRelationQuotient_succ_succ_of_fibreModels
    (hb : 0 < windowBound pi hpi) (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    [Module.Projective RZ (Amb[n + 1] ⧸ Kr[n + 1])]
    (hmodel : DivUniversalHighWindowFibreModel
      C hpi g r1 r2 b1 b2 i j hO hchi n)
    (hmodelNext : DivUniversalHighWindowFibreModel
      C hpi g r1 r2 b1 b2 i j hO hchi (n + 1)) :
    Module.Projective RZ
      (divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 2)) := by
  let L := divUniversalHighWindowKernelSyzygy (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]
  have hL : DivUniversalHighWindowSyzygySpans (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1] L :=
    divUniversalHighWindowKernelSyzygySpans_of_adjacent_fibreModels
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi
        hb n hmodel hmodelNext
  letI := finite_divUniversalHighWindowRelation
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1)
  change Module.Projective RZ
    (Amb[n + 2] ⧸ divUniversalHighWindowMulSpan (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1])
  exact projective_divUniversalHighWindowMulSpanQuotient_of_syzygies
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1] L hL

/-! ## Decoupled curve parameter -/

variable {gamma : Nat} (hgamma : gamma ≤ g)
  (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))

local notation "HFγ[" n "]" => divUniversalFibreHighWindow_at
  C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n
local notation "Dγ" => divUniversalFibreDivisor_at
  C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker

set_option maxHeartbeats 2400000 in
-- The pair-indexed tensor equivalence retains every relation-fibre scalar tower.
set_option synthInstance.maxHeartbeats 800000 in
/-- Scalar extension distributes over the pair-indexed Koszul source at
independent curve parameter `gamma ≤ g`. -/
noncomputable def divUniversalHighWindowRelationKoszulSourceFibreEquiv_at (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n) :
    K ⊗[RZ] (HI × HI → ↥Kr[n]) ≃ₗ[K] (HI × HI → ↥HFγ[n]) :=
  (TensorProduct.piRight RZ K K (fun _ : HI × HI => ↥Kr[n])).trans
    (LinearEquiv.piCongrRight fun _ : HI × HI =>
      divUniversalHighWindowRelationFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n himage)

set_option maxHeartbeats 2400000 in
-- Reducing the pair-indexed tensor equivalence at one component is expensive.
set_option synthInstance.maxHeartbeats 800000 in
@[simp]
theorem divUniversalHighWindowRelationKoszulSourceFibreEquiv_apply_at (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n)
    (x : K ⊗[RZ] (HI × HI → ↑Kr[n])) (q : HI × HI) :
    divUniversalHighWindowRelationKoszulSourceFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma n himage x q =
      divUniversalHighWindowRelationFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n himage
        (TensorProduct.piRightHom RZ K K (fun _ : HI × HI => ↑Kr[n]) x q) := by
  rw [divUniversalHighWindowRelationKoszulSourceFibreEquiv_at,
    LinearEquiv.trans_apply, TensorProduct.piRight_apply]
  rfl

set_option maxHeartbeats 4000000 in
-- Comparing the corestricted relation step with fibre multiplication is reduction-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- One relative relation-basis step becomes multiplication on the canonical
off-diagonal fibre windows. -/
theorem divUniversalHighWindowRelationBasisStep_fibre_conjugacy_at (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    [Module.Projective RZ (Amb[n + 1] ⧸ Kr[n + 1])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n)
    (himageNext : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker (n + 1))
    (t : HI) (x : K ⊗[RZ] ↥Kr[n]) :
    divUniversalHighWindowRelationFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker (n + 1) himageNext
        (LinearMap.baseChange K
          (divUniversalHighWindowRelationBasisStep (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n t) x) =
      Scheme.finiteMulStepTo
        (Scheme.divisorSections K (windowS C K hpi g) ⊤) HFγ[n] HFγ[n + 1]
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
        (fun s z => Scheme.mul_mem_divisorSections_highWindow
          (windowN C K hpi g) (windowS C K hpi g) Dγ n
          (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K s) z)
        t
        (divUniversalHighWindowRelationFibreEquiv_at
          C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n himage x) := by
  have hsub :
      Kr[n + 1].subtype.comp
          (divUniversalHighWindowRelationBasisStep (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j n t) =
        divUniversalHighWindowMulRow (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n Kr[n] t := by
    apply LinearMap.ext
    intro z
    rfl
  have hbcx := LinearMap.congr_fun (congrArg (LinearMap.baseChange K) hsub) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hbcx
  apply Subtype.ext
  rw [divUniversalHighWindowRelationFibreEquiv_coe_at, hbcx]
  simpa only [divUniversalHighWindowClosedAmbientFibreRead_apply,
    Scheme.finiteMulStepTo_apply] using
    (divUniversalHighWindowMulRow_fibre_conjugacy_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker
        n himage t x)

set_option maxHeartbeats 4800000 in
-- The boundary equation combines two dependent finite-product conjugacy squares.
set_option synthInstance.maxHeartbeats 1200000 in
set_option maxRecDepth 24000 in
/-- The scalar extension of the relative relation Koszul boundary is conjugate
to the canonical off-diagonal high-window boundary. -/
theorem divUniversalHighWindowRelationKoszulBoundary_fibre_conjugacy_at (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    [Module.Projective RZ (Amb[n + 1] ⧸ Kr[n + 1])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n)
    (himageNext : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker (n + 1)) :
    (divUniversalHighWindowMulSourceFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker
          (n + 1) himageNext).toLinearMap.comp
      (LinearMap.baseChange K
        (divUniversalHighWindowRelationKoszulBoundary (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j n)) =
    (Scheme.highWindowMulKoszulBoundary
        (windowN C K hpi g) (windowS C K hpi g) Dγ n
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)).comp
      (divUniversalHighWindowRelationKoszulSourceFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma n himage).toLinearMap := by
  let stepR : HI → ↑Kr[n] →ₗ[RZ] ↑Kr[n + 1] := fun t =>
    divUniversalHighWindowRelationBasisStep (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n t
  let stepF : HI → ↑HFγ[n] →ₗ[K] ↑HFγ[n + 1] := fun t =>
    Scheme.finiteMulStepTo
      (Scheme.divisorSections K (windowS C K hpi g) ⊤) HFγ[n] HFγ[n + 1]
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
      (fun s z => Scheme.mul_mem_divisorSections_highWindow
        (windowN C K hpi g) (windowS C K hpi g) Dγ n
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K s) z) t
  let eNow : (K ⊗[RZ] ↑Kr[n]) ≃ₗ[K] ↑HFγ[n] :=
    divUniversalHighWindowRelationFibreEquiv_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n himage
  let eNext : (K ⊗[RZ] ↑Kr[n + 1]) ≃ₗ[K] ↑HFγ[n + 1] :=
    divUniversalHighWindowRelationFibreEquiv_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker (n + 1) himageNext
  have hbase := piRightHom_comp_baseChange_finiteKoszulBoundary
    (R := RZ) (S := K) stepR
  have hstep : ∀ (t : HI) (x : K ⊗[RZ] ↑Kr[n]),
      eNext (LinearMap.baseChange K (stepR t) x) = stepF t (eNow x) := by
    intro t x
    simpa only [stepR, stepF, eNow, eNext] using
      divUniversalHighWindowRelationBasisStep_fibre_conjugacy_at
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma
          n himage himageNext t x
  have hconj := piCongrRight_comp_finiteKoszulBoundary_of_conjugate
    (step := fun t => LinearMap.baseChange K (stepR t))
    (step' := stepF) eNow eNext hstep
  change
    ((LinearEquiv.piCongrRight fun _ : HI => eNext).toLinearMap.comp
        (TensorProduct.piRightHom RZ K K (fun _ : HI => ↑Kr[n + 1]))).comp
      (LinearMap.baseChange K (finiteKoszulBoundary stepR)) =
    (finiteKoszulBoundary stepF).comp
      ((LinearEquiv.piCongrRight fun _ : HI × HI => eNow).toLinearMap.comp
        (TensorProduct.piRightHom RZ K K (fun _ : HI × HI => ↑Kr[n])))
  rw [LinearMap.comp_assoc, hbase, ← LinearMap.comp_assoc, hconj,
    LinearMap.comp_assoc]

set_option maxHeartbeats 4800000 in
-- The injectivity criterion instantiates both adjacent projective fibre equivalences.
set_option synthInstance.maxHeartbeats 1200000 in
set_option maxRecDepth 24000 in
/-- Adjacent off-diagonal fibre models make the injectivized successor map
remain injective after tensoring with the field. -/
theorem divUniversalHighWindowRelationMul_liftQ_rTensor_injective_of_fibre_models_at
    (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    [Module.Projective RZ (Amb[n + 1] ⧸ Kr[n + 1])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n)
    (himageNext : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker (n + 1)) :
    Function.Injective
      (((LinearMap.ker
          (divUniversalHighWindowMulMap (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1])).liftQ
        (divUniversalHighWindowMulMap (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]) le_rfl).rTensor K) := by
  apply liftQ_rTensor_injective_of_conjugate_boundary
    (f := divUniversalHighWindowMulMap (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1])
    (d := divUniversalHighWindowRelationKoszulBoundary (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n)
    (hfd := divUniversalHighWindowMulMap_comp_relationKoszulBoundary_eq_zero
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n)
    (f' := Scheme.finiteMulMap
      (Scheme.divisorSections K (windowS C K hpi g) ⊤) HFγ[n + 1]
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K))
    (d' := Scheme.highWindowMulKoszulBoundary
      (windowN C K hpi g) (windowS C K hpi g) Dγ n
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K))
    (eM := divUniversalHighWindowMulSourceFibreEquiv_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker (n + 1) himageNext)
    (eN := divUniversalHighWindowClosedAmbientFibreRead
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 2))
    (eP := divUniversalHighWindowRelationKoszulSourceFibreEquiv_at
      C hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma n himage)
  · intro x
    exact divUniversalHighWindowMulMap_fibre_conjugacy_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker
        (n + 1) himageNext x
  · intro y
    exact LinearMap.congr_fun
      (divUniversalHighWindowRelationKoszulBoundary_fibre_conjugacy_at
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hker hgamma hchiGamma
          n himage himageNext) y
  · exact (divUniversalFibreHighWindow_ker_finiteMulMap_eq_range_koszul_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hker n
        (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)).le

set_option maxHeartbeats 4800000 in
-- Quantifying over residue fields reconstructs the full carve-ring scalar tower.
set_option synthInstance.maxHeartbeats 1200000 in
set_option maxRecDepth 24000 in
/-- Adjacent projective off-diagonal fibre models span every residue-field
kernel of the successor presentation. -/
theorem divUniversalHighWindowKernelSyzygySpans_of_adjacent_fibreModels_at
    (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    [Module.Projective RZ (Amb[n + 1] ⧸ Kr[n + 1])]
    (hmodel : DivUniversalHighWindowFibreModel_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma n)
    (hmodelNext : DivUniversalHighWindowFibreModel_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma (n + 1)) :
    DivUniversalHighWindowSyzygySpans (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]
      (divUniversalHighWindowKernelSyzygy (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]) := by
  apply (divUniversalHighWindowKernelSyzygySpans_iff
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]).2
  intro p
  exact
    divUniversalHighWindowRelationMul_liftQ_rTensor_injective_of_fibre_models_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField
        (divCarveIdeal_le_ker_of_tower k
          (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi)
          g r1 r2 b1 b2 i j p.asIdeal.ResidueField)
        hgamma hchiGamma n (hmodel p) (hmodelNext p)

set_option maxHeartbeats 3200000 in
-- The projectivity consumer unfolds the dependent successor relation quotient.
set_option synthInstance.maxHeartbeats 800000 in
/-- Adjacent off-diagonal fibre models force the relation quotient two stages
later to be finite projective. -/
theorem projective_divUniversalHighWindowRelationQuotient_succ_succ_of_fibreModels_at
    (n : Nat)
    [Module.Projective RZ (Amb[n] ⧸ Kr[n])]
    [Module.Projective RZ (Amb[n + 1] ⧸ Kr[n + 1])]
    (hmodel : DivUniversalHighWindowFibreModel_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma n)
    (hmodelNext : DivUniversalHighWindowFibreModel_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma (n + 1)) :
    Module.Projective RZ
      (divUniversalHighWindowRelationQuotient (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 2)) := by
  let L := divUniversalHighWindowKernelSyzygy (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1]
  have hL : DivUniversalHighWindowSyzygySpans (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1] L :=
    divUniversalHighWindowKernelSyzygySpans_of_adjacent_fibreModels_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma
        n hmodel hmodelNext
  letI := finite_divUniversalHighWindowRelation
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1)
  change Module.Projective RZ
    (Amb[n + 2] ⧸ divUniversalHighWindowMulSpan (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1])
  exact projective_divUniversalHighWindowMulSpanQuotient_of_syzygies
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j (n + 1) Kr[n + 1] L hL

end HighWindowRelationKoszulConjugacy

end AlgebraicGeometry
