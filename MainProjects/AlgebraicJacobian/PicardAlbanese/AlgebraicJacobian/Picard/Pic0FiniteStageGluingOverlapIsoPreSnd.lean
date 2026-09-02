/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoPreSndFst
import AlgebraicJacobian.Picard.Pic0FiniteStageGluingOverlapIsoPreSndSnd

/-!
# The source factorization for the right gluing leg

This module assembles the two projection equations for the right leg of the
base-changed gluing diagram before the final comparison with the canonical
separably closed atlas.
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
-- Assemble the separately cached projection factorizations.
set_option maxHeartbeats 12800000 in
theorem gluingOverlapIso_pre_snd
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    ((Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).t U V ≫
        (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f V U) ≫
        (pullback.congrHom (glueData_ι_gluedMap C P V) rfl).hom =
      (gluingOverlapFlatteningIso C P U V).hom ≫
        (pullback.congrHom
          (glueData_f_comp_inclusion_comp_gluedMap C P U V) rfl).hom ≫
        rightRestrictionBaseChangeMap C P U V := by
  apply pullback.hom_ext
    (f := chartBaseChangeMap C P V)
    (g := Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))
  · simpa only [Category.assoc] using
      gluingOverlapIso_pre_snd_fst C P U V
  · simpa only [Category.assoc] using
      gluingOverlapIso_pre_snd_snd C P U V

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
