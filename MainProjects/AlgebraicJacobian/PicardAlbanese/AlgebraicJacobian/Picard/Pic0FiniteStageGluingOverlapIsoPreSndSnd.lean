/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoPreSndSndSource
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoPreSndSndTarget

/-!
# The second projection of the right gluing-leg source factorization

This module proves the second pullback projection equation before the final
comparison with the canonical separably closed atlas.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageGluePackage

set_option synthInstance.maxHeartbeats 3200000 in
-- The second projection keeps the chart/base pullback transport abstract.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
@[irreducible] def gluingOverlapIso_pre_snd_snd
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :=
  (gluingOverlapIso_pre_snd_snd_source
      (C := C) (P := P) (U := U) (V := V)).trans
    (gluingOverlapIso_pre_snd_snd_target
      (C := C) (P := P) (U := U) (V := V)).symm

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
