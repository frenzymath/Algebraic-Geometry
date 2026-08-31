/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0RankOneNativeBaseChangeCartesian

/-!
# Canonicalize an existing rank-one presentation

`PicRankOneLocalPresentation` is the public producer contract, but its `module` field is an
auxiliary presentation of the cocycle sheaf.  The native rank-one consumer needs the canonical
`BasicOpenCocycleDatum.nativeModule` instead.  This file supplies the honest bridge: it keeps the
same cover, representative, and cocycle datum, copies the cohomology/rank certificates, and
derives native pushforward base change from the actual datum's vanishing theorem.  No new witness
or unrelated module is introduced.
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
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

namespace PicRankOneNativePresentation

variable {A : Type u} [CommRing A] [Algebra k A]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

/-- Replace the auxiliary module in a local presentation by the datum's canonical native module.

The native pushforward comparison is obtained from the same datum and its `H¹` certificate, so
the resulting structure remains tied to the original lambda value and does not assume a new
base-change theorem.
-/
noncomputable def ofLocalPresentation
    (P : PicRankOneLocalPresentation pi lam) :
    PicRankOneNativePresentation pi lam :=
  { cover := P.cover
    representative := P.representative
    represents := P.represents
    datum := P.datum
    datum_class := P.datum_class
    native_pushforward_base_change := fun g f' g' sq =>
      P.datum.isIso_canonicalBaseChangeMap_nativeModule
        ((subsingleton_datumPair_h1_iff P.datum).mpr P.h1_vanishing)
        g f' g' sq
    h1_vanishing := P.h1_vanishing
    h0_finite := P.h0_finite
    h0_projective := P.h0_projective
    h0_rank_one := P.h0_rank_one }

/-- A local presentation always yields a nonempty canonical native presentation. -/
theorem nonempty_of_localPresentation
    (P : PicRankOneLocalPresentation pi lam) :
    Nonempty (PicRankOneNativePresentation pi lam) :=
  ⟨ofLocalPresentation pi P⟩

/-- Convert the complete affine-pullback producer contract to its native form.

The conversion is pointwise but preserves the exact pulled-back lambda and the actual datum at
each test algebra; it is therefore suitable for a later native `FibrePresented` consumer.
-/
theorem nonempty_of_localPresentations
    {T : (Over (Spec (.of k)))ᵒᵖ}
    {lam : (picDegLayerFunctor C (genus C : ℤ)).obj T}
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A]
        (t : overSpec k A ⟶ T.unop),
        Nonempty (PicRankOneLocalPresentation pi
          ((picDegLayerFunctor C (genus C : ℤ)).map t.op lam))) :
    ∀ (A : Type u) [CommRing A] [Algebra k A]
      (t : overSpec k A ⟶ T.unop),
      Nonempty (PicRankOneNativePresentation pi
        ((picDegLayerFunctor C (genus C : ℤ)).map t.op lam)) := by
  intro A _ _ t
  obtain ⟨P⟩ := h A t
  exact PicRankOneNativePresentation.nonempty_of_localPresentation pi P

end PicRankOneNativePresentation

end AlgebraicGeometry
