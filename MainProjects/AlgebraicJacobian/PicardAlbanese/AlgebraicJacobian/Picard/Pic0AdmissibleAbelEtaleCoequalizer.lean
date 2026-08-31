/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSheafification
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjective

/-!
# The admissible Abel quotient in big-etale sheaves

Etale-local surjectivity of the concrete admissible Abel transformation makes its image
the full sheafified Picard Sigma target. Consequently that target is the effective
coequalizer of the map's kernel pair in big-etale sheaves.

This is not yet a quotient in `Scheme`: representing the kernel pair by a scheme, proving
effectivity of its geometric quotient, and identifying `pic0SigmaEtaleSheafification C`
with the original `pic0TypeFunctor C` remain separate steps.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

/-- The sheafified concrete admissible Abel map is locally surjective on the big-etale
site. -/
instance admissibleAbelEtaleSheafMap_isLocallySurjective :
    Sheaf.IsLocallySurjective (admissibleAbelEtaleSheafMap C) := by
  letI : Presheaf.IsLocallySurjective Scheme.etaleTopology
      (abelSigmaChartAffAdmissible C) :=
    isLocallySurjective_abelSigmaChartAffAdmissible C
  letI : Presheaf.IsLocallySurjective Scheme.etaleTopology
      (Functor.whiskerRight (abelSigmaChartAffAdmissible C)
        uliftFunctor.{u + 1}) :=
    Presheaf.isLocallySurjective_whiskerRight_ulift
      Scheme.etaleTopology (abelSigmaChartAffAdmissible C)
  haveI : Sheaf.IsLocallySurjective
      ((presheafToSheaf Scheme.etaleTopology (Type (u + 1))).map
        (Functor.whiskerRight (abelSigmaChartAffAdmissible C)
          uliftFunctor.{u + 1})) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      Scheme.etaleTopology _).2 inferInstance
  haveI : Sheaf.IsLocallySurjective
      (admissibleAbelEtaleSourceIso C).hom := by infer_instance
  exact Sheaf.isLocallySurjective_comp
    (admissibleAbelEtaleSourceIso C).hom
    ((presheafToSheaf Scheme.etaleTopology (Type (u + 1))).map
      (Functor.whiskerRight (abelSigmaChartAffAdmissible C)
        uliftFunctor.{u + 1}))

/-- The image of the sheafified admissible Abel map is the full sheafified Picard Sigma
target. -/
noncomputable def admissibleAbelEtaleImageIsoTarget :
    admissibleAbelEtaleImage C ≅ pic0SigmaEtaleSheafification C := by
  haveI : IsIso (Sheaf.imageι (admissibleAbelEtaleSheafMap C)) :=
    (Sheaf.isLocallySurjective_iff_isIso _).mp inferInstance
  exact asIso (Sheaf.imageι (admissibleAbelEtaleSheafMap C))

/-- The full sheafified Picard Sigma target is the effective coequalizer of the kernel
pair of the concrete admissible Abel map. -/
noncomputable def admissibleAbelEtaleTargetCoequalizer :
    IsColimit (Cofork.ofπ (admissibleAbelEtaleSheafMap C)
      (IsKernelPair.of_hasPullback (admissibleAbelEtaleSheafMap C)).w) := by
  haveI : IsRegularEpi (admissibleAbelEtaleSheafMap C) :=
    IsRegularEpiCategory.regularEpiOfEpi _
  exact (IsKernelPair.of_hasPullback
    (admissibleAbelEtaleSheafMap C)).toCoequalizer'

end AlgebraicGeometry
