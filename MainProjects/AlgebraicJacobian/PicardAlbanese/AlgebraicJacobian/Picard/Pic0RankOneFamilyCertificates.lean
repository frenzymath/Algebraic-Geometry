/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Cohomology.RankOneFamilyCertificatesDescent
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentation

/-!
# Lambda-tied assembly of rank-one family certificates

This file is the Picard-side consumer of `RankOneFamilyCertificates`.  It does not choose a
module: the certificate and the native presentation are both attached to the displayed cocycle
datum.  The cover representative and its equality with the displayed lambda class provide the
Picard tie, while arbitrary-cartesian native pushforward base change remains a separate geometric
input.
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
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

namespace PicRankOneNativePresentation

variable {pi} {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

/-! ## The literal native consumer -/

/-- Assemble the native presentation from certificates for the same displayed cocycle datum.

The equalities `hrep` and `hclass` tie the datum to the requested lambda class.  All four
cohomological fields are projected from `cert`, whose modules are definitionally the H-modules
of `D.sheaf`; no unrelated or pre-certified target module can enter.  The all-cartesian native
pushforward comparison is intentionally an explicit argument until its protected producer lands.
-/
noncomputable def ofCertificates
    (E : Algebra.EtaleCover A)
    (x : descentClasses C E)
    (hrep : PicEtAff.mk C E x = picEtAffineEquiv C A lam.1)
    (D : BasicOpenCocycleDatum C E.Carrier pi)
    (hclass :
      (x : relPic C (overSpec k E.Carrier)) =
        relPicMk C (overSpec k E.Carrier) D.cechPicClass)
    (hpush :
      ∀ {T' X' : Scheme.{u}}
        (g : T' ⟶ Spec (.of E.Carrier)) (f' : X' ⟶ T')
        (g' : X' ⟶ relCurve C E.Carrier)
        (sq : IsPullback g' f'
          (relCurve C E.Carrier ↘ Spec (.of E.Carrier)) g),
        IsIso ((canonicalBaseChangeMap sq).app D.nativeModule))
    (cert : RankOneFamilyCertificates D) :
    PicRankOneNativePresentation pi lam :=
  { cover := E
    representative := x
    represents := hrep
    datum := D
    datum_class := hclass
    native_pushforward_base_change := hpush
    h1_vanishing := cert.h1_vanishing
    h0_finite := cert.h0_finite
    h0_projective := cert.h0_projective
    h0_rank_one := cert.h0_rank_one }

end PicRankOneNativePresentation

end AlgebraicGeometry
