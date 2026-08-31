/-
Copyright (c) 2026 The StacksPart02Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart02Lib Contributors
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Foundational scheme constructions

This module records the local-ring and open-subscheme interfaces used in the
opening chapters of the Stacks Project's Schemes part.
-/

namespace StacksPart02

open CategoryTheory TopologicalSpace Topology Opposite
open AlgebraicGeometry

universe u

/-- Every stalk of a locally ringed space is a local ring.

This is the stalk condition in the definition of a locally ringed space
(Stacks, Tag 01HB).
-/
theorem locallyRingedSpace_stalk_isLocalRing
    (X : LocallyRingedSpace.{u}) (x : X) :
    IsLocalRing (X.presheaf.stalk x) := by
  infer_instance

/-- Stalk maps of locally ringed-space morphisms are local homomorphisms.

This is the localness clause in the morphism definition (Stacks, Tag 01HB).
-/
theorem locallyRingedSpace_stalkMap_isLocalHom
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.stalkMap x).hom := by
  infer_instance

/-- Stalk maps compose contravariantly under composition of morphisms. -/
theorem locallyRingedSpace_stalkMap_comp
    {X Y Z : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).stalkMap x = g.stalkMap (f.base x) ≫ f.stalkMap x := by
  exact LocallyRingedSpace.stalkMap_comp f g x

/-- A sheafed-space isomorphism between locally ringed spaces lifts to one
of locally ringed spaces (Stacks, Tag 01HC). -/
def locallyRingedSpaceIsoOfSheafedSpaceIso
    {X Y : LocallyRingedSpace.{u}}
    (e : X.toSheafedSpace ≅ Y.toSheafedSpace) : X ≅ Y :=
  LocallyRingedSpace.isoOfSheafedSpaceIso e

/-- The lifted isomorphism has local stalk maps in both directions. -/
theorem locallyRingedSpaceIsoOfSheafedSpaceIso_stalkMap_isLocalHom
    {X Y : LocallyRingedSpace.{u}}
    (e : X.toSheafedSpace ≅ Y.toSheafedSpace) (x : X) :
    IsLocalHom
      ((locallyRingedSpaceIsoOfSheafedSpaceIso e).hom.stalkMap x).hom := by
  infer_instance

/-- Every point of a scheme has a neighbourhood identified with an affine
spectrum (the local-affine clause in the definition of `Scheme`). -/
theorem scheme_exists_local_affine
    (X : Scheme.{u}) (x : X) :
    ∃ (U : OpenNhds x) (R : CommRingCat),
      Nonempty
        (X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅
          Spec.toLocallyRingedSpace.obj (op R)) :=
  X.local_affine x

/-- The scheme obtained by restricting to an open subset. -/
abbrev openSubscheme (X : Scheme.{u}) (U : X.Opens) : Scheme :=
  X.restrict U.isOpenEmbedding

/-- The canonical morphism from an open subscheme to the ambient scheme. -/
abbrev openSubschemeι (X : Scheme.{u}) (U : X.Opens) :
    openSubscheme X U ⟶ X :=
  X.ofRestrict U.isOpenEmbedding

instance openSubschemeι_isOpenImmersion
    (X : Scheme.{u}) (U : X.Opens) :
    IsOpenImmersion (openSubschemeι X U) := by
  infer_instance

/-- The image of the canonical open-subscheme morphism is the chosen open. -/
theorem openSubschemeι_range (X : Scheme.{u}) (U : X.Opens) :
    Set.range (openSubschemeι X U) = (U : Set X) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Pulling the chosen open back along its canonical inclusion gives the top
open of the restricted scheme. -/
theorem openSubschemeι_preimage (X : Scheme.{u}) (U : X.Opens) :
    (openSubschemeι X U) ⁻¹ᵁ U = ⊤ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact (openSubschemeι X U).mem_preimage.mpr x.property

/-- Scheme morphisms are continuous on underlying spaces. -/
theorem scheme_hom_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Continuous f := by
  exact Scheme.Hom.continuous f

/-- Scheme morphisms preserve arbitrary unions of opens by inverse image. -/
theorem scheme_hom_preimage_iSup {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type*} (U : ι → Y.Opens) :
    f ⁻¹ᵁ iSup U = ⨆ i, f ⁻¹ᵁ U i := by
  exact Scheme.Hom.preimage_iSup f U

/-- Inverse images of opens respect composition of scheme morphisms. -/
theorem scheme_hom_comp_preimage {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (U : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  exact Scheme.Hom.comp_preimage f g U

/-- A basic open defined by a section of a scheme's structure sheaf is open
(Stacks, Tag 01HZ). -/
theorem scheme_basicOpen_isOpen {X : Scheme.{u}} {U : X.Opens}
    (f : X.presheaf.obj (op U)) :
    IsOpen (X.basicOpen f : Set X) := by
  exact (X.basicOpen f).isOpen

/-- A section becomes a unit after restricting to the basic open it defines
(Stacks, Tag 01HZ). -/
theorem scheme_isUnit_res_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (f : X.presheaf.obj (op U)) :
    IsUnit (X.presheaf.map (@homOfLE (Opens X) _ _ _ (X.basicOpen_le f)).op f) := by
  exact X.toRingedSpace.isUnit_res_basicOpen f

end StacksPart02
