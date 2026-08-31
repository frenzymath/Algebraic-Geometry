/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneLocusNative

/-!
# The canonical native rank-one presentation contract

`PicRankOneLocalPresentation` deliberately leaves the geometric producer fields explicit.
This file fixes the module part of that contract: for a tied cocycle datum `D`, the module is
always `D.nativeModule` and its base-ring comparison is always
`D.nativeModuleKSheafIso`.  The native piece trivializations supply the line-bundle field;
arbitrary-cartesian pushforward base change and the cohomology/rank certificates stay as
explicit obligations.

The resulting contract is therefore an adapter interface for a future producer, rather than a
second choice of a line bundle.  Its conversion is consumed directly by the public
`PicRankOneOpen` membership theorem below; no unrelated module or untied class can enter
through this bridge, and the adapter itself does not provide the geometric certificates.
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

/-! ## The native adapter contract -/

/--
A lambda-tied rank-one presentation whose module is canonically the native module of its
cocycle datum.

The fields after `datum_class` are exactly the remaining producer obligations.  The line-bundle
certificate is derived from the canonical piece trivializations, so a field-level H⁰/H¹
calculation or an unrelated line bundle cannot be silently substituted for the native
evaluation module.
-/
structure PicRankOneNativePresentation
    (lam : picDegLayer C (genus C : ℤ) (overSpec k A)) : Type (u + 1) where
  cover : Algebra.EtaleCover A
  representative : descentClasses C cover
  represents :
    PicEtAff.mk C cover representative = picEtAffineEquiv C A lam.1
  datum : BasicOpenCocycleDatum C cover.Carrier pi
  datum_class :
    (representative : relPic C (overSpec k cover.Carrier)) =
      relPicMk C (overSpec k cover.Carrier) datum.cechPicClass
  native_pushforward_base_change :
    ∀ {T' X' : Scheme.{u}}
      (g : T' ⟶ Spec (.of cover.Carrier)) (f' : X' ⟶ T')
      (g' : X' ⟶ relCurve C cover.Carrier)
      (sq : IsPullback g' f'
        (relCurve C cover.Carrier ↘ Spec (.of cover.Carrier)) g),
      IsIso ((canonicalBaseChangeMap sq).app datum.nativeModule)
  h1_vanishing : Subsingleton (Sheaf.HModule datum.sheaf 1)
  h0_finite : Module.Finite cover.Carrier (Sheaf.HModule datum.sheaf 0)
  h0_projective : Module.Projective cover.Carrier (Sheaf.HModule datum.sheaf 0)
  h0_rank_one :
    ∀ p : PrimeSpectrum cover.Carrier,
      Module.rankAtStalk (Sheaf.HModule datum.sheaf 0) p = 1

namespace PicRankOneNativePresentation

variable {pi} {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

/-- Convert the native adapter contract to the existing local-presentation contract.

The two native bridge fields are inserted definitionally; all other fields are transported
without weakening or adding hypotheses.
-/
noncomputable def toLocalPresentation
    (P : PicRankOneNativePresentation pi lam) :
    PicRankOneLocalPresentation pi lam :=
  { cover := P.cover
    representative := P.representative
    represents := P.represents
    datum := P.datum
    datum_class := P.datum_class
    module := P.datum.nativeModule
    module_iso := P.datum.nativeModuleKSheafIso
    line_bundle := P.datum.nativeModule_isLineBundle
    native_pushforward_base_change := P.native_pushforward_base_change
    h1_vanishing := P.h1_vanishing
    h0_finite := P.h0_finite
    h0_projective := P.h0_projective
    h0_rank_one := P.h0_rank_one }

theorem nonempty_localPresentation
    (P : PicRankOneNativePresentation pi lam) :
    Nonempty (PicRankOneLocalPresentation pi lam) :=
  ⟨P.toLocalPresentation⟩

end PicRankOneNativePresentation

/-! ## Immediate rank-one-locus consumer -/

/--
An arbitrary-affine family of native contracts supplies the existing public rank-one-locus
consumer.  The family is quantified in exactly the same way as
`PicRankOneOpen.LocalPresentationCondition`; the conversion only canonicalizes the module
choice and does not manufacture any of the remaining geometric certificates.
-/
theorem mem_picRankOneOpen_of_nativePresentations
    {T : (Over (Spec (.of k)))ᵒᵖ}
    {lam : (picDegLayerFunctor C (genus C : ℤ)).obj T}
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A]
        (t : overSpec k A ⟶ T.unop),
        Nonempty (PicRankOneNativePresentation pi
          ((picDegLayerFunctor C (genus C : ℤ)).map t.op lam))) :
    lam ∈ (PicRankOneOpen pi).obj T := by
  apply mem_picRankOneOpen_of_localPresentations pi
  intro A _ _ t
  obtain ⟨P⟩ := h A t
  exact P.nonempty_localPresentation

end AlgebraicGeometry
