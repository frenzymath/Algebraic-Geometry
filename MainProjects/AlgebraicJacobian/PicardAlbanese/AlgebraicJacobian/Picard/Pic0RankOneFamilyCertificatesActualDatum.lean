/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Cohomology.RankOneFamilyCertificatesActualDatum
import AlgebraicJacobian.Picard.Pic0RankOneFamilyCertificates
import AlgebraicJacobian.Picard.Pic0RankOneFamilyCertificatesH0BaseChange
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentationDatum

/-!
# Native rank-one certificates for the lambda-tied datum

This file closes the Picard-side consumer boundary.  A `PicRankOneNativeDatum` already records
that its etale representative presents the displayed lambda and that its basic-open cocycle datum
represents that same relative Picard class.  Residue-field split witnesses therefore produce the
four cohomological certificates for this exact datum over its arbitrary affine coefficient ring.

The returned package uses the canonical `h0BaseChange` and `scalarExtension` operations from
`RankOneFamilyCertificates`; `h0BaseChange_tower` proves their coherence along every affine
coefficient tower.  The final constructor passes the package directly to
`PicRankOneNativePresentation.ofCertificates`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {A : Type u} [CommRing A] [Algebra k A]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

namespace PicRankOneNativeDatum

/-- The pointwise split condition on the displayed lambda representative carried by `P`. -/
abbrev ResidueSplitWitnesses (P : PicRankOneNativeDatum pi lam) : Prop :=
  ∀ t : (overSpec k P.cover.Carrier).left,
    IsSplitWitness C
      (picEtMap C (Over.testPoint t)
        (relPicToPicEt C (overSpec k P.cover.Carrier)
          (P.representative : relPic C (overSpec k P.cover.Carrier))))

/-- Produce the complete arbitrary-affine certificate package for the lambda-tied datum `P`.

The H1 input is converted from split witnesses for `P.representative`; the degree law is derived
from `P.represents` and `P.datum_class`.  Finiteness and projectivity are constructed at a genuine
finite Noetherian stage and transported back, rather than supplied by the caller. -/
noncomputable def familyCertificates
    (P : PicRankOneNativeDatum pi lam)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hsplit : P.ResidueSplitWitnesses) :
    RankOneFamilyCertificates P.datum :=
  RankOneFamilyCertificates.ofActualDatum P.datum hpi
    (P.residueH1Witness_of_isSplitWitness hsplit)
    (fun L ↦ P.classDeg_baseChange L)

/-- Canonically extend the lambda-tied certificate package to any affine coefficient algebra. -/
noncomputable def familyCertificatesBaseChange
    (P : PicRankOneNativeDatum pi lam)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hsplit : P.ResidueSplitWitnesses)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] :
    RankOneFamilyCertificates (P.datum.baseChange B) :=
  (P.familyCertificates hpi hsplit).scalarExtension B

end PicRankOneNativeDatum

namespace PicRankOneNativePresentation

/-- Assemble a native rank-one presentation from the actual lambda-tied datum and its split
witnesses.  The only remaining independent input is the native pushforward base-change theorem. -/
noncomputable def ofNativeDatum
    (P : PicRankOneNativeDatum pi lam)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hsplit : P.ResidueSplitWitnesses)
    (hpush :
      ∀ {T' X' : Scheme.{u}}
        (g : T' ⟶ Spec (.of P.cover.Carrier)) (f' : X' ⟶ T')
        (g' : X' ⟶ relCurve C P.cover.Carrier)
        (sq : IsPullback g' f'
          (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) g),
        IsIso ((canonicalBaseChangeMap sq).app P.datum.nativeModule)) :
    PicRankOneNativePresentation pi lam :=
  PicRankOneNativePresentation.ofCertificates
    P.cover P.representative P.represents P.datum P.datum_class hpush
      (P.familyCertificates hpi hsplit)

end PicRankOneNativePresentation

end AlgebraicGeometry
