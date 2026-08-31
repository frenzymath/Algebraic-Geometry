/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivPointwiseGenerator
import AlgebraicJacobian.Picard.DivSchemeHighWindowQuotientBridge

/-!
# The high-window pointwise generator

The all-stage high-window theorem gives pointwise RD-N over the nonreduced universal
carve ring.  This file feeds that theorem into the reusable pointwise generator
construction.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace PointwiseAchiever

section HighWindowPointwiseGenerator

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowPointwiseGenerator :
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
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j

set_option maxHeartbeats 2400000 in
-- The wrapper elaborates the high-window RD-N proof through the dependent seed type.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The generator seed obtained directly from the all-stage high-window theorem. -/
noncomputable def highWindowPointwiseGeneratorSeed (hb : 0 < windowBound pi hpi) :
    ThetaGeneratorSeed C RZ pi (windowM_choice pi hpi g)
      (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) :=
  pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi
    (pointwiseSeedRDN_of_highWindow
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb)

set_option maxHeartbeats 2400000 in
-- The final theorem reuses both the high-window RD-N and pointwise generator endpoints.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- All-stage high-window flatness supplies an unconditional pointwise theta generator
over the nonreduced universal carve ring. -/
theorem isGenerator_highWindowPointwiseGeneratorSeed (hb : 0 < windowBound pi hpi) :
    (highWindowPointwiseGeneratorSeed
      C hpi g r1 r2 b1 b2 i j hO hchi hb).IsGenerator :=
  isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi
    (pointwiseSeedRDN_of_highWindow
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb)

set_option maxHeartbeats 2400000 in
-- The wrapper elaborates decoupled high-window RD-N through the dependent seed type.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The degree-`g` generator seed obtained from the all-stage high-window theorem
at independent Euler parameter `gamma ≤ g`. -/
noncomputable def highWindowPointwiseGeneratorSeed_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    ThetaGeneratorSeed C RZ pi (windowM_choice pi hpi g)
      (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) :=
  pointwiseGeneratorSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
    (pointwiseSeedRDN_of_highWindow_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma)

set_option maxHeartbeats 2400000 in
-- The final theorem reuses both decoupled RD-N and pointwise generator endpoints.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- All-stage high-window flatness supplies the degree-`g` pointwise theta
generator at every independent Euler parameter `gamma ≤ g`. -/
theorem isGenerator_highWindowPointwiseGeneratorSeed_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    (highWindowPointwiseGeneratorSeed_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).IsGenerator :=
  isGenerator_pointwiseGeneratorSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchiGamma
    (pointwiseSeedRDN_of_highWindow_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma)

end HighWindowPointwiseGenerator

end PointwiseAchiever

end AlgebraicGeometry
