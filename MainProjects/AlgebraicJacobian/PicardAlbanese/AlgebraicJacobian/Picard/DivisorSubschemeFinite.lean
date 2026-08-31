/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorSubscheme
import AlgebraicJacobian.Picard.SupportTubeFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness of the intrinsic divisor subscheme

The colength spectra in `AffAdaptation.divisorPieceCover` are finite over the affine test
base by the existing certificate.  Since locally quasi-finite morphisms are local on the
source, the cover makes the intrinsic divisor locally quasi-finite over the base.  It is
also proper, as a closed subscheme of the proper relative curve, and hence finite.

This is the certificate-only geometric producer needed to regard the existing colength
equalizer as global functions on an affine divisor.  No containment, fixed-chart, or
`SwallowedBy` hypothesis occurs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

/-- On a colength chart, the intrinsic divisor's structure morphism is the spectrum of
the original `R`-algebra structure on that colength ring. -/
theorem divisorPieceMap_over [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    A.divisorPieceMap i ≫ A.divisorSubschemeOver.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (A.colength i))) := by
  change (Spec.map
      (A.divisorPieceQuotientEquiv i).toRingEquiv.toCommRingCatIso.hom ≫
    A.cartierIdeal.subschemeCover.f ⟨D.pieces i, D.isAffineOpen i⟩) ≫
      (A.cartierIdeal.subschemeι ≫ (relCurve C R ↘ Spec (.of R))) = _
  rw [Category.assoc]
  rw [← Category.assoc
    (A.cartierIdeal.subschemeCover.f ⟨D.pieces i, D.isAffineOpen i⟩)
    A.cartierIdeal.subschemeι (relCurve C R ↘ Spec (.of R))]
  rw [A.cartierIdeal.subschemeCover_map_subschemeι]
  rw [A.cartierIdeal.glueDataObjι_ι]
  rw [Category.assoc]
  rw [(D.isAffineOpen i).specMap_quotient_mk_fromSpec_over
    (A.cartierIdeal.ideal ⟨D.pieces i, D.isAffineOpen i⟩)]
  rw [← Spec.map_comp]
  congr 1

/-- The intrinsic divisor of a certified widened adaptation is finite over the affine
test base.  The proof uses precisely certificate clause (c1), locally on the arbitrary
adapted affine cover. -/
theorem isFinite_divisorSubschemeOver [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n) :
    IsFinite A.divisorSubschemeOver.hom := by
  have hpiece (i : D.index) :
      LocallyQuasiFinite
        (A.divisorPieceMap i ≫ A.divisorSubschemeOver.hom) := by
    rw [A.divisorPieceMap_over i]
    have hf : (algebraMap R (A.colength i)).Finite :=
      RingHom.finite_algebraMap.mpr (hc.finite_colength i)
    haveI : IsFinite
        (Spec.map (CommRingCat.ofHom (algebraMap R (A.colength i)))) :=
      (IsFinite.SpecMap_iff _).mpr hf
    infer_instance
  have hqf : LocallyQuasiFinite A.divisorSubschemeOver.hom :=
    IsZariskiLocalAtSource.of_openCover (A.divisorPieceCover.openCover) hpiece
  haveI : IsProper A.divisorSubschemeι := inferInstance
  haveI : IsProper (relCurve C R ↘ Spec (.of R)) :=
    instIsProperRelCurveHom C R
  have hp : IsProper A.divisorSubschemeOver.hom := by
    change IsProper (A.divisorSubschemeι ≫ (relCurve C R ↘ Spec (.of R)))
    infer_instance
  exact @IsFinite.of_isProper_of_locallyQuasiFinite _ _
    A.divisorSubschemeOver.hom hp hqf

/-- A certified intrinsic divisor is affine.  Its global section ring can therefore be
used as an honest affine descent base for the local theta quotients. -/
theorem isAffine_divisorSubscheme [IsProper C.hom]
    (A : AffAdaptation D d) {n : ℕ} (hc : A.IsCertified n) :
    IsAffine A.divisorSubscheme := by
  haveI : IsFinite A.divisorSubschemeOver.hom :=
    A.isFinite_divisorSubschemeOver hc
  exact isAffine_of_isAffineHom A.divisorSubschemeOver.hom

end AffAdaptation

end AlgebraicGeometry
