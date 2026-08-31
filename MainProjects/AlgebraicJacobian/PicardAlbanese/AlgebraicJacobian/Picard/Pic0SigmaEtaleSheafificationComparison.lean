/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSheafification
import AlgebraicJacobian.Picard.Pic0SigmaEtaleSheaf

/-!
# Comparing raw Pic0 Sigma with its big-etale sheafification

The raw Pic0 Sigma functor is already a sheaf for the big-etale topology. After the
universe lift required by the Scheme site, the sheafification unit is therefore an
isomorphism. This file bundles that sheaf and records the canonical comparison used by
the quotient-Yoneda step.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

/-- The universe-raised raw Pic0 Sigma presheaf satisfies the big-etale sheaf
condition in its sieve form. -/
theorem pic0SigmaFunctor_ulift_isSheaf_etale :
    Presieve.IsSheaf Scheme.etaleTopology
      (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1}) :=
  Presieve.isSheaf_comp_uliftFunctor Scheme.etaleTopology
    (pic0SigmaFunctor_isSheaf_etale C)

/-- The universe-raised raw Pic0 Sigma presheaf is a big-etale sheaf. -/
theorem pic0SigmaFunctor_ulift_presheafIsSheaf_etale :
    Presheaf.IsSheaf Scheme.etaleTopology
      (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1}) :=
  (isSheaf_iff_isSheaf_of_type _ _).mpr
    (pic0SigmaFunctor_ulift_isSheaf_etale C)

/-- The universe-raised raw Pic0 Sigma functor bundled as a big-etale sheaf. -/
noncomputable def pic0SigmaEtaleSheaf :
    Sheaf Scheme.etaleTopology.{u} (Type (u + 1)) :=
  ⟨pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1},
    pic0SigmaFunctor_ulift_presheafIsSheaf_etale C⟩

/-- The natural isomorphism from universe-raised raw Pic0 Sigma to the underlying
presheaf of the sheafification used as the admissible Abel target. -/
noncomputable def pic0SigmaEtaleSheafificationIso :
    (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1}) ≅
      (pic0SigmaEtaleSheafification C).obj :=
  isoSheafify Scheme.etaleTopology
    (pic0SigmaFunctor_ulift_presheafIsSheaf_etale C)

/-- The same canonical comparison bundled in the category of big-etale sheaves. -/
noncomputable def pic0SigmaEtaleSheafIso :
    pic0SigmaEtaleSheaf C ≅ pic0SigmaEtaleSheafification C :=
  sheafificationIso (pic0SigmaEtaleSheaf C)

/-- The underlying hom of the comparison is exactly the sheafification unit. -/
@[simp]
theorem pic0SigmaEtaleSheafificationIso_hom :
    (pic0SigmaEtaleSheafificationIso C).hom =
      toSheafify Scheme.etaleTopology
        (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1}) :=
  rfl

/-- The bundled and unbundled comparisons have the same underlying natural map. -/
@[simp]
theorem pic0SigmaEtaleSheafIso_hom :
    (pic0SigmaEtaleSheafIso C).hom.hom =
      (pic0SigmaEtaleSheafificationIso C).hom :=
  rfl

/-- Component form of the canonical-map identification. -/
@[simp]
theorem pic0SigmaEtaleSheafificationIso_hom_app (T : Scheme.{u}ᵒᵖ) :
    (pic0SigmaEtaleSheafificationIso C).hom.app T =
      (toSheafify Scheme.etaleTopology
        (pic0SigmaFunctor C ⋙ uliftFunctor.{u + 1})).app T := by
  rw [pic0SigmaEtaleSheafificationIso_hom]

end

end AlgebraicGeometry
