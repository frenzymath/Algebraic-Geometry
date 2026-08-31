/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowRelativeKoszul
import AlgebraicJacobian.Picard.DivSchemeHighWindowTransitionRelationZero

/-!
# The relative Koszul boundary on the canonical relation tower

The transition-relation files prove that every multiplier-basis section sends
the canonical relation module at stage `n` into the canonical relation module
at stage `n + 1`, including the exceptional seed transition.  This file feeds
that preservation statement into the relative Koszul construction and records
the resulting canonical boundary and its vanishing under the next multiplication
map.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowRelativeKoszulRelation

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowRelativeKoszulRelation :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k ((windowS_choice pi hpi g • fiberWeilDivisor pi)
    + (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
local notation "HS" => ↥(Scheme.divisorSections k
  (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)
local notation "HI" => Fin (Module.finrank k HS)
local notation "K" n => divUniversalHighWindowRelation (C := C) (pi := pi)
  hpi g r1 r2 b1 b2 i j n

set_option maxHeartbeats 1600000 in
-- The relation inclusion unfolds the dependent stage family and the seed map.
/-- The canonical relation tower satisfies the multiplier preservation
condition at every stage, including stage zero. -/
theorem divUniversalHighWindowRelation_mulPreserves (n : Nat) :
    DivUniversalHighWindowMulPreserves (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n (K n) (K (n + 1)) := by
  intro t z
  have hz := map_divUniversalHighWindowBaseMultiplierTransition_relation_le
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n
      ((Module.finBasis k HS) t)
      ⟨(K n).subtype z, z.property, rfl⟩
  change divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n ((Module.finBasis k HS) t)
      ((K n).subtype z) ∈ K (n + 1) at hz
  change divUniversalHighWindowBaseMultiplierTransition (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n ((Module.finBasis k HS) t)
      ((K n).subtype z) ∈ K (n + 1)
  exact hz

/-- The basis-indexed multiplication step on the canonical relation tower. -/
noncomputable def divUniversalHighWindowRelationBasisStep (n : Nat) (t : HI) :
    (K n) →ₗ[RZ] (K (n + 1)) :=
  divUniversalHighWindowBasisStep (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j n (K n) (K (n + 1))
    (divUniversalHighWindowRelation_mulPreserves (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n) t

/-- The canonical relative Koszul boundary
`(I × I → K_n) → (I → K_(n+1))`. -/
noncomputable def divUniversalHighWindowRelationKoszulBoundary (n : Nat) :
    (HI × HI → K n) →ₗ[RZ] (HI → K (n + 1)) :=
  divUniversalHighWindowKoszulBoundary (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j n (K n) (K (n + 1))
    (divUniversalHighWindowRelation_mulPreserves (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j n)

set_option maxHeartbeats 1600000 in
-- The next map and the relation boundary carry consecutive dependent stages.
/-- The next canonical multiplication map kills the canonical relation
Koszul boundary. -/
theorem divUniversalHighWindowMulMap_comp_relationKoszulBoundary_eq_zero
    (n : Nat) :
    (divUniversalHighWindowMulMap (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j (n + 1) (K (n + 1))).comp
      (divUniversalHighWindowRelationKoszulBoundary (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n) = 0 := by
  exact divUniversalHighWindowMulMap_comp_koszulBoundary_eq_zero
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n (K n) (K (n + 1))
      (divUniversalHighWindowRelation_mulPreserves (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j n)

end HighWindowRelativeKoszulRelation

end AlgebraicGeometry
