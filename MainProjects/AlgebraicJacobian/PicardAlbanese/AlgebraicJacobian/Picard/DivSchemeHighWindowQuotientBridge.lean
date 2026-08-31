/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowFibreModelInduction
import AlgebraicJacobian.Picard.DivSchemeHighWindowTransitionSaturation
import AlgebraicJacobian.Picard.DivSchemeSeedUnivPointwiseFibre

/-!
# The high-window quotient bridge

The all-stage relative Koszul induction supplies the only missing hypothesis in
the shifted-colimit criterion.  Consequently the genuine pinned-chart quotient
by the universal seed reading ideal is flat over the possibly nonreduced carve
ring.  This is the flatness input for the pointwise RD-N/Nakayama consumer.
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

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowQuotientBridge

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowQuotientBridge :
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
local notation "G" n => divUniversalHighWindowAmbient (C := C) (pi := pi)
  (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
  (i := i) (j := j) n
local notation "Kr" n => divUniversalHighWindowRelation (C := C) (pi := pi)
  hpi g r1 r2 b1 b2 i j n

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

set_option maxHeartbeats 3200000 in
-- Installing the all-stage dependent flatness family unfolds each relation quotient.
set_option synthInstance.maxHeartbeats 800000 in
-- The saturation consumer retains the full chart-ring and shifted-colimit instance graph.
set_option maxRecDepth 20000 in
include hO hchi in
/-- The genuine universal-seed reading quotient on either pinned chart is flat
over the possibly nonreduced carve ring. -/
theorem flat_chartReadIdeal_divUniversalSeedK
    (hb : 0 < windowBound pi hpi) (side : Bool) :
    Module.Flat RZ
      (Γ(relCurve C RZ, relPinnedChart C RZ pi side) ⧸
        chartReadIdeal (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) side) := by
  letI : ∀ n, Module.Flat RZ ((G(n + 1)) ⧸ Kr(n + 1)) := fun n =>
    flat_divUniversalHighWindowRelationQuotient_all
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb (n + 1)
  exact flat_chartReadIdeal_divUniversalSeedK_of_all_stage
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side hO hchi hb

set_option maxHeartbeats 3200000 in
-- Installing the decoupled all-stage flatness family unfolds each relation quotient.
set_option synthInstance.maxHeartbeats 800000 in
-- The saturation consumer retains the full chart-ring and shifted-colimit instance graph.
set_option maxRecDepth 20000 in
/-- At independent Euler parameter `gamma ≤ g`, the genuine degree-`g`
universal-seed reading quotient on either pinned chart is flat over the carve ring. -/
theorem flat_chartReadIdeal_divUniversalSeedK_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (side : Bool) :
    Module.Flat RZ
      (Γ(relCurve C RZ, relPinnedChart C RZ pi side) ⧸
        chartReadIdeal (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) side) := by
  letI : ∀ n, Module.Flat RZ ((G(n + 1)) ⧸ Kr(n + 1)) := fun n =>
    flat_divUniversalHighWindowRelationQuotient_all_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma (n + 1)
  exact flat_chartReadIdeal_divUniversalSeedK_of_all_stage_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j side hgamma hchiGamma

set_option maxHeartbeats 3200000 in
-- The pointwise support predicate contains the dependent chart-colength module at every point.
set_option synthInstance.maxHeartbeats 800000 in
-- Both pinned charts are discharged by the unconditional quotient theorem above.
set_option maxRecDepth 20000 in
/-- The non-generic residue-fibre branch of pointwise RD-N follows from the
high-window quotient bridge on the two pinned charts. -/
theorem pointwiseSeedClosedRDN_of_highWindow
    (hb : 0 < windowBound pi hpi) :
    PointwiseAchiever.PointwiseSeedClosedRDN
      C hpi g r1 r2 b1 b2 i j hO hchi :=
  PointwiseAchiever.pointwiseSeedClosedRDN_of_flat_chartReadIdeal_quotient
    C hpi g r1 r2 b1 b2 i j hO hchi
      (fun side => flat_chartReadIdeal_divUniversalSeedK
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb side)

set_option maxHeartbeats 3200000 in
-- The pointwise support predicate contains the dependent chart-colength module at every point.
set_option synthInstance.maxHeartbeats 800000 in
-- Both pinned charts are discharged by the decoupled quotient theorem above.
set_option maxRecDepth 20000 in
/-- The non-generic residue-fibre branch of pointwise RD-N at independent Euler
parameter `gamma ≤ g` follows from the high-window quotient bridge. -/
theorem pointwiseSeedClosedRDN_of_highWindow_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    PointwiseAchiever.PointwiseSeedClosedRDNAt
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma :=
  PointwiseAchiever.pointwiseSeedClosedRDNAt_of_flat_chartReadIdeal_quotient
    C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
      (fun side => flat_chartReadIdeal_divUniversalSeedK_at
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma side)

set_option maxHeartbeats 2400000 in
-- The generic/non-generic branch split re-elaborates the residue-point predicate.
set_option synthInstance.maxHeartbeats 800000 in
-- The closed branch is supplied by the high-window quotient theorem above.
set_option maxRecDepth 16000 in
/-- The pointwise universal seed satisfies RD-N at every total-space point. -/
theorem pointwiseSeedRDN_of_highWindow
    (hb : 0 < windowBound pi hpi) :
    PointwiseAchiever.PointwiseSeedRDN
      C hpi g r1 r2 b1 b2 i j hO hchi :=
  PointwiseAchiever.pointwiseSeedRDN_of_closed
    C hpi g r1 r2 b1 b2 i j hO hchi
      (pointwiseSeedClosedRDN_of_highWindow
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb)

set_option maxHeartbeats 2400000 in
-- The generic/non-generic branch split re-elaborates the residue-point predicate.
set_option synthInstance.maxHeartbeats 800000 in
-- The closed branch is supplied by the decoupled high-window quotient theorem above.
set_option maxRecDepth 16000 in
/-- The degree-`g` universal seed satisfies RD-N at every total-space point when
the Euler parameter is any `gamma ≤ g`. -/
theorem pointwiseSeedRDN_of_highWindow_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    PointwiseAchiever.PointwiseSeedRDNAt
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma :=
  PointwiseAchiever.pointwiseSeedRDNAt_of_closed
    C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
      (pointwiseSeedClosedRDN_of_highWindow_at
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma)

end HighWindowQuotientBridge

end AlgebraicGeometry
