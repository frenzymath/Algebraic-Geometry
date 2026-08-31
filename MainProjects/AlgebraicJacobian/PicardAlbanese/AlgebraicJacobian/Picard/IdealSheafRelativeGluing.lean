/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Gluing ideal sheaves along a locally directed cover

A compatible family of ideal sheaves on the members of a locally directed open cover defines
a relative gluing datum of closed subschemes.  Its glued structure morphism is a closed immersion,
and its kernel restricts to the original ideal sheaf on every member of the cover.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Cover.RelativeGluingData

variable {S : Scheme.{u}}

private lemma le_map_of_comap_eq (𝒰 : S.OpenCover) [Category 𝒰.I₀]
    [𝒰.LocallyDirected] (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ {i j} (f : i ⟶ j), (I j).comap (𝒰.trans f) = I i)
    {i j : 𝒰.I₀} (f : i ⟶ j) : I j ≤ (I i).map (𝒰.trans f) := by
  rw [← hI f]
  exact (I j).le_map_comap (𝒰.trans f)

private noncomputable def subschemeFunctor (𝒰 : S.OpenCover) [Category 𝒰.I₀]
    [𝒰.LocallyDirected] (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ {i j} (f : i ⟶ j), (I j).comap (𝒰.trans f) = I i) :
    𝒰.I₀ ⥤ Scheme.{u} where
  obj i := (I i).subscheme
  map f := Scheme.IdealSheafData.subschemeMap _ _ (𝒰.trans f)
    (le_map_of_comap_eq 𝒰 I hI f)
  map_id i := by
    rw [← cancel_mono (I i).subschemeι]
    simp
  map_comp f g := by
    rw [← cancel_mono (I _).subschemeι]
    simp

private noncomputable def subschemeNatTrans (𝒰 : S.OpenCover) [Category 𝒰.I₀]
    [𝒰.LocallyDirected] (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ {i j} (f : i ⟶ j), (I j).comap (𝒰.trans f) = I i) :
    subschemeFunctor 𝒰 I hI ⟶ 𝒰.functorOfLocallyDirected where
  app i := (I i).subschemeι
  naturality i j f := by
    dsimp [subschemeFunctor]
    simp

private theorem subschemeNatTrans_equifibered (𝒰 : S.OpenCover) [Category 𝒰.I₀]
    [𝒰.LocallyDirected] (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ {i j} (f : i ⟶ j), (I j).comap (𝒰.trans f) = I i) :
    (subschemeNatTrans 𝒰 I hI).Equifibered := by
  intro i j f
  dsimp [subschemeFunctor, subschemeNatTrans]
  apply IsPullback.flip
  apply isPullback_of_isClosedImmersion
  · simp
  · rw [(I j).ker_subschemeι, (I i).ker_subschemeι]
    exact hI f

/-- Compatible ideal sheaves on a locally directed open cover, viewed as relative gluing data
for their associated closed subschemes. -/
noncomputable def ofIdealSheafData (𝒰 : S.OpenCover) [Category 𝒰.I₀]
    [𝒰.LocallyDirected] (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ {i j} (f : i ⟶ j), (I j).comap (𝒰.trans f) = I i) :
    𝒰.RelativeGluingData where
  functor := subschemeFunctor 𝒰 I hI
  natTrans := subschemeNatTrans 𝒰 I hI
  equifibered := subschemeNatTrans_equifibered 𝒰 I hI

/-- The structure morphism obtained by gluing compatible closed subschemes is a closed
immersion. -/
theorem isClosedImmersion_toBase_ofIdealSheafData (𝒰 : S.OpenCover) [Category 𝒰.I₀]
    [𝒰.LocallyDirected] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ {i j} (f : i ⟶ j), (I j).comap (𝒰.trans f) = I i) :
    IsClosedImmersion (ofIdealSheafData 𝒰 I hI).toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) 𝒰]
  intro i
  rw [Scheme.Cover.pullbackHom,
    ← ((ofIdealSheafData 𝒰 I hI).isPullback_natTrans_ι_toBase i).flip.isoPullback_inv_snd,
    MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]
  change IsClosedImmersion (I i).subschemeι
  infer_instance

end Scheme.Cover.RelativeGluingData

namespace Scheme.IdealSheafData

variable {S : Scheme.{u}}

/-- Glue compatible ideal sheaves along a locally directed open cover. -/
noncomputable def glueOfLocallyDirected (𝒰 : S.OpenCover) [Category 𝒰.I₀]
    [𝒰.LocallyDirected] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ {i j} (f : i ⟶ j), (I j).comap (𝒰.trans f) = I i) :
    S.IdealSheafData :=
  (Scheme.Cover.RelativeGluingData.ofIdealSheafData 𝒰 I hI).toBase.ker

/-- The glued ideal sheaf restricts to the specified ideal sheaf on every cover member. -/
theorem glueOfLocallyDirected_comap (𝒰 : S.OpenCover) [Category 𝒰.I₀]
    [𝒰.LocallyDirected] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ {i j} (f : i ⟶ j), (I j).comap (𝒰.trans f) = I i) (i : 𝒰.I₀) :
    (glueOfLocallyDirected 𝒰 I hI).comap (𝒰.f i) = I i := by
  let d := Scheme.Cover.RelativeGluingData.ofIdealSheafData 𝒰 I hI
  haveI : IsClosedImmersion d.toBase :=
    Scheme.Cover.RelativeGluingData.isClosedImmersion_toBase_ofIdealSheafData 𝒰 I hI
  change d.toBase.ker.comap (𝒰.f i) = I i
  rw [← (I i).ker_subschemeι,
    ← ker_fst_of_isClosedImmersion d.toBase (𝒰.f i),
    ← Scheme.Hom.ker_comp_of_isIso (d.isPullback_natTrans_ι_toBase i).isoPullback.hom,
    (d.isPullback_natTrans_ι_toBase i).isoPullback_hom_fst]
  change (I i).subschemeι.ker = (I i).subschemeι.ker
  rfl

end Scheme.IdealSheafData

end AlgebraicGeometry
