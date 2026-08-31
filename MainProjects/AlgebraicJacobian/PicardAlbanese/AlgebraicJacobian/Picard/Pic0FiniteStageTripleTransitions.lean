/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleOverlapRings

/-!
# Cyclic transitions on triple overlaps in the finite-stage Picard atlas

The three tensor presentations of a triple overlap are section rings of the same literal
open in the separably closed `Pic^0` representer.  Restriction along the corresponding
open equality therefore gives the cyclic ring map dual to the `t'` field of a scheme
gluing datum.  This file records its face equation and three-cycle identity before any
finite-stage descent is performed.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-- The literal triple open with cyclically rotated chart labels is the same open. -/
theorem pic0FiniteStageTripleOpen_le_rotate
    (U V W : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageTripleOpen C U V W <=
      Pic0FiniteStageTripleOpen C V W U := by
  change (U.1.1 ⊓ V.1.1) ⊓ (U.1.1 ⊓ W.1.1) <=
    (V.1.1 ⊓ W.1.1) ⊓ (V.1.1 ⊓ U.1.1)
  refine le_inf (le_inf ?_ ?_) (le_inf ?_ ?_)
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_right.trans inf_le_right
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_left.trans inf_le_left

/-- The ring map dual to cyclic rotation of the triple intersection. -/
noncomputable def pic0FiniteStageTripleTransition
    (U V W : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageTripleRing C V W U →ₐ[k]
      Pic0FiniteStageTripleRing C U V W := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  exact
    { J.left.resHom (pic0FiniteStageTripleOpen_le_rotate C U V W) with
      commutes' := fun r => J.left.overAlgebraMap_apply_res k
        (homOfLE (pic0FiniteStageTripleOpen_le_rotate C U V W)).op r }

/-- The cyclic triple transition carries the right face of the rotated presentation to
the left face of the original presentation. -/
theorem pic0FiniteStageTripleTransition_fac
    (U V W : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageTripleTransition C U V W).comp
        (pic0FiniteStageOverlapToTripleRight C V W U) =
      (pic0FiniteStageOverlapToTripleLeft C U V W).comp
        (pic0FiniteStageTransition C (U, V)) := by
  apply DFunLike.ext _ _
  intro x
  change
    ((pic0_sepClosed_representableBy (C := C)).1.left.resHom
      (pic0FiniteStageTripleOpen_le_rotate C U V W))
      (((pic0_sepClosed_representableBy (C := C)).1.left.resHom
        (show Pic0FiniteStageTripleOpen C V W U <= V.1.1 ⊓ U.1.1 from
          inf_le_right)) x) =
    ((pic0_sepClosed_representableBy (C := C)).1.left.resHom
      (show Pic0FiniteStageTripleOpen C U V W <= U.1.1 ⊓ V.1.1 from
        inf_le_left))
      (((pic0_sepClosed_representableBy (C := C)).1.left.resHom
        (show U.1.1 ⊓ V.1.1 <= V.1.1 ⊓ U.1.1 by rw [inf_comm])) x)
  rw [Scheme.resHom_resHom, Scheme.resHom_resHom]

/-- Three cyclic rotations of a triple intersection compose to the identity. -/
theorem pic0FiniteStageTripleTransition_cocycle
    (U V W : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageTripleTransition C U V W).comp
        ((pic0FiniteStageTripleTransition C V W U).comp
          (pic0FiniteStageTripleTransition C W U V)) =
      AlgHom.id k (Pic0FiniteStageTripleRing C U V W) := by
  apply DFunLike.ext _ _
  intro x
  change
    ((pic0_sepClosed_representableBy (C := C)).1.left.resHom
      (pic0FiniteStageTripleOpen_le_rotate C U V W))
      (((pic0_sepClosed_representableBy (C := C)).1.left.resHom
        (pic0FiniteStageTripleOpen_le_rotate C V W U))
        (((pic0_sepClosed_representableBy (C := C)).1.left.resHom
          (pic0FiniteStageTripleOpen_le_rotate C W U V)) x)) = x
  rw [Scheme.resHom_resHom, Scheme.resHom_resHom, Scheme.resHom_self]

/-- The pair-transition map on a diagonal overlap is the identity. -/
theorem pic0FiniteStageTransition_self
    (U : Pic0FiniteStageChartIndex C) :
    pic0FiniteStageTransition C (U, U) =
      AlgHom.id k (Pic0FiniteStageOverlapRing C U U) := by
  apply DFunLike.ext _ _
  intro x
  change ((pic0_sepClosed_representableBy (C := C)).1.left.resHom
    (show U.1.1 ⊓ U.1.1 <= U.1.1 ⊓ U.1.1 by rw [inf_comm])) x = x
  rw [Scheme.resHom_self]

end

end AlgebraicGeometry
