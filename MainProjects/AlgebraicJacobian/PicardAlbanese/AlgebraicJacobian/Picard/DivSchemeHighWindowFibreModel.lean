/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowFibreImage

/-!
# Residue-prime models for the recursive high-window relations

The fieldwise image predicate is promoted here to a condition at every prime
of the carve-chart ring.  The canonical quotient tower supplies the required
carve-ideal kernel hypothesis at each residue field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowFibreModel

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowFibreModel :
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

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

set_option maxHeartbeats 2000000 in
-- Expanding the residue-field campaign parameters exceeds the default elaboration budget.
set_option synthInstance.maxHeartbeats 800000 in
-- The canonical four-step scalar tower at each residue field needs the campaign budget.
/-- The fibre-model condition at a relative stage: the expected image equality
holds over the residue field of every prime of the carve-chart ring. -/
def DivUniversalHighWindowFibreModel (n : Nat) : Prop :=
  ∀ p : PrimeSpectrum RZ,
    DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField hO hchi
        (divCarveIdeal_le_ker_of_tower k
          (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi)
          g r1 r2 b1 b2 i j p.asIdeal.ResidueField) n

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The decoupled fibre-model condition at a relative stage, with divisor
degree `g` and independent curve parameter `gamma ≤ g`. -/
def DivUniversalHighWindowFibreModel_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (n : Nat) : Prop :=
  ∀ p : PrimeSpectrum RZ,
    DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField hgamma hchiGamma
        (divCarveIdeal_le_ker_of_tower k
          (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi)
          g r1 r2 b1 b2 i j p.asIdeal.ResidueField) n

end HighWindowFibreModel

end AlgebraicGeometry
