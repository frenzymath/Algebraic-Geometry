/-
Copyright (c) 2026 The StacksPart02Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart02Lib Contributors
-/

import Mathlib.AlgebraicGeometry.Limits

/-!
# Fiber products of schemes

This module exposes the existence and universal-property interface for fiber
products of schemes, together with the affine case used throughout the Stacks
Project's Schemes chapter.
-/

namespace StacksPart02

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The category of schemes has finite limits (Stacks, Tag 01JM). -/
theorem scheme_hasFiniteLimits : HasFiniteLimits Scheme.{u} := by
  infer_instance

/-- The two projections from a fiber product form a commutative square
(Stacks, Tag 01JP). -/
theorem scheme_fiberProduct_condition
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  exact pullback.condition

/-- The first projection of the canonical lift to a fiber product. -/
theorem scheme_fiberProduct_lift_fst
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (a : T ⟶ X) (b : T ⟶ Y) (h : a ≫ f = b ≫ g) :
    pullback.lift a b h ≫ pullback.fst f g = a :=
  pullback.lift_fst a b h

/-- The second projection of the canonical lift to a fiber product. -/
theorem scheme_fiberProduct_lift_snd
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (a : T ⟶ X) (b : T ⟶ Y) (h : a ≫ f = b ≫ g) :
    pullback.lift a b h ≫ pullback.snd f g = b :=
  pullback.lift_snd a b h

/-- Maps into a fiber product are determined by their two projections. -/
theorem scheme_fiberProduct_hom_ext
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {a b : T ⟶ pullback f g}
    (hfst : a ≫ pullback.fst f g = b ≫ pullback.fst f g)
    (hsnd : a ≫ pullback.snd f g = b ≫ pullback.snd f g) :
    a = b := by
  exact pullback.hom_ext hfst hsnd

/-- A fiber product of affine schemes over an affine scheme is affine
(Stacks, Tag 01JQ). -/
theorem scheme_fiberProduct_isAffine
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffine X] [IsAffine Y] [IsAffine S] :
    IsAffine (pullback f g) := by
  infer_instance

/-- The fiber product of affine spectra is the spectrum of the tensor product
(Stacks, Tag 01JQ). -/
noncomputable def scheme_affine_fiberProduct_iso
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅
      Spec (CommRingCat.of (TensorProduct R S T)) :=
  pullbackSpecIso R S T

/-- Under the affine fiber-product isomorphism, the first projection is
induced by the left tensor-factor inclusion. -/
theorem scheme_affine_fiberProduct_iso_inv_fst
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    (scheme_affine_fiberProduct_iso R S T).inv ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (algebraMap R T))) =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) :=
  pullbackSpecIso_inv_fst R S T

/-- Under the affine fiber-product isomorphism, the second projection is
induced by the right tensor-factor inclusion. -/
theorem scheme_affine_fiberProduct_iso_inv_snd
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    (scheme_affine_fiberProduct_iso R S T).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (algebraMap R T))) =
      Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : T →ₐ[R] TensorProduct R S T) :
          T →+* TensorProduct R S T)) :=
  pullbackSpecIso_inv_snd R S T

/-- Pulling an open subscheme back along a scheme morphism agrees with the
restriction of the source to the inverse-image open (Stacks, Tag 01JR). -/
noncomputable def scheme_pullback_open_restrict_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    pullback f U.ι ≅ (f ⁻¹ᵁ U).toScheme :=
  pullbackRestrictIsoRestrict f U

/-- Under the open-pullback isomorphism, the first projection is the canonical
open-subscheme inclusion. -/
theorem scheme_pullback_open_restrict_iso_inv_fst
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (scheme_pullback_open_restrict_iso f U).inv ≫ pullback.fst f U.ι =
      (f ⁻¹ᵁ U).ι :=
  pullbackRestrictIsoRestrict_inv_fst f U

/-- The open-pullback isomorphism commutes with the second projection. -/
theorem scheme_pullback_open_restrict_iso_hom_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (scheme_pullback_open_restrict_iso f U).hom ≫ f ∣_ U = pullback.snd f U.ι :=
  pullbackRestrictIsoRestrict_hom_morphismRestrict f U

end StacksPart02
