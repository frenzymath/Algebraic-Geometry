/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageStableGluePackage

/-!
# Stable scheme-level restrictions for finite-stage gluing

The affine restriction maps are already stored in the selected `AffineRingGluePresentation`.
This module exposes those scheme maps and their structural laws directly.  It deliberately
does not restate them as package-indexed `AlgHom`s: such a type would ask instance search to
reconstruct the dependent tensor algebras and would reintroduce the instability this facade
is meant to remove.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageStableGluePackage

variable {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]

/-- The selected restriction leg between two finite-stage charts. -/
def restriction
    (P : Pic0FiniteStageStableGluePackage C F)
    (U V : P.presentation.glueData.J) :
    P.presentation.glueData.V (U, V) ⟶ P.presentation.glueData.U U :=
  P.presentation.glueData.f U V

/-- The selected transition on an ordered overlap. -/
def transition
    (P : Pic0FiniteStageStableGluePackage C F)
    (U V : P.presentation.glueData.J) :
    P.presentation.glueData.V (U, V) ⟶ P.presentation.glueData.V (V, U) :=
  P.presentation.glueData.t U V

@[simp]
theorem restriction_eq
    (P : Pic0FiniteStageStableGluePackage C F)
    (U V : P.presentation.glueData.J) :
    P.restriction C U V = P.presentation.glueData.f U V :=
  rfl

@[simp]
theorem transition_eq
    (P : Pic0FiniteStageStableGluePackage C F)
    (U V : P.presentation.glueData.J) :
    P.transition C U V = P.presentation.glueData.t U V :=
  rfl

theorem restriction_open
    (P : Pic0FiniteStageStableGluePackage C F)
    (U V : P.presentation.glueData.J) :
    IsOpenImmersion (P.restriction C U V) :=
  P.presentation.glueData.f_open U V

theorem restriction_mono
    (P : Pic0FiniteStageStableGluePackage C F)
    (U V : P.presentation.glueData.J) :
    Mono (P.restriction C U V) :=
  P.presentation.glueData.f_mono U V

@[simp]
theorem transition_self
    (P : Pic0FiniteStageStableGluePackage C F)
    (U : P.presentation.glueData.J) :
    P.transition C U U = 𝟙 _ :=
  P.presentation.glueData.t_id U

end Pic0FiniteStageStableGluePackage

end

end AlgebraicGeometry
