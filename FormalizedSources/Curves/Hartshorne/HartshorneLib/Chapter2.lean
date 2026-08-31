/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1Spectrum
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Hartshorne II.2: affine schemes and the structure sheaf

Mathlib supplies the affine scheme `Spec A` together with its locally ringed
space and structure sheaf.  This file records the source-facing interface:
the stalks are localizations, sections on a basic open are localizations away
from its defining element, and global sections recover the coordinate ring.
It also exposes the spectrum map attached to a ring homomorphism.
-/

namespace Hartshorne

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

/-! ### Affine schemes -/

/-- The affine scheme associated to an unbundled commutative ring. -/
abbrev affineSpec (R : Type u) [CommRing R] : Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of R)

/-- The structure sheaf on the affine spectrum of a commutative ring. -/
abbrev affineStructureSheaf (R : Type u) [CommRing R] :
    TopCat.Sheaf CommRingCat (PrimeSpectrum.Top R) :=
  Spec.structureSheaf R

theorem affineSpec_isAffine (R : Type u) [CommRing R] :
    IsAffine (affineSpec R) := by
  exact AlgebraicGeometry.isAffine_Spec (CommRingCat.of R)

theorem affineSpec_carrier (R : Type u) [CommRing R] :
    (affineSpec R).carrier = PrimeSpectrum R := by
  rfl

theorem affineSpec_presheaf (R : Type u) [CommRing R] :
    (affineSpec R).presheaf = (affineStructureSheaf R).obj := by
  rfl

/-! ### Spectrum maps -/

/-- The map on affine spectra induced by a ring homomorphism. -/
def affineSpecMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : affineSpec S ⟶ affineSpec R :=
  Spec.map (CommRingCat.ofHom f)

@[simp]
theorem affineSpecMap_apply {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : affineSpec S) :
    affineSpecMap f p = PrimeSpectrum.comap f p := by
  exact Spec.map_apply (CommRingCat.ofHom f) p

theorem affineSpecMap_continuous {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    Continuous (affineSpecMap f) := by
  exact Scheme.Hom.continuous (affineSpecMap f)

theorem affineSpecMap_id (R : CommRingCat) :
    Spec.map (𝟙 R) = 𝟙 (AlgebraicGeometry.Spec R) := by
  exact Spec.map_id R

theorem affineSpecMap_comp {R S T : CommRingCat}
    (f : R ⟶ S) (g : S ⟶ T) :
    Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f := by
  exact Spec.map_comp f g

/-- Ring maps and morphisms between affine schemes are equivalent. -/
def affineSpec_homEquiv (R S : CommRingCat) :
    (AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R) ≃ (R ⟶ S) :=
  Spec.homEquiv

theorem affineSpecMap_surjective {R S : CommRingCat} :
    Function.Surjective (Spec.map : (R ⟶ S) →
      (AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R)) := by
  exact Spec.map_surjective

theorem affineSpecMap_injective {R S : CommRingCat} :
    Function.Injective (Spec.map : (R ⟶ S) →
      (AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R)) := by
  exact Spec.map_injective

/-! ### Source-facing affine consequences -/

/-- The inverse image of a basic open under an affine spectrum map. -/
@[simp]
theorem affineSpecMap_preimage_basicOpen {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) :
    (affineSpecMap f) ⁻¹ᵁ (spectrumBasicOpen r) = spectrumBasicOpen (f r) := by
  exact AlgebraicGeometry.SpecMap_preimage_basicOpen (CommRingCat.ofHom f) r

/-- Basic opens in an affine spectrum are affine open subschemes. -/
theorem affineSpec_basicOpen_isAffineOpen {R : CommRingCat} (r : R) :
    IsAffineOpen (X := AlgebraicGeometry.Spec R) (PrimeSpectrum.basicOpen r) := by
  exact IsAffineOpen.Spec_basicOpen r

/-- Sections on a basic open of an affine spectrum form the expected localization. -/
theorem affineSpec_basicOpen_sections_isLocalization {R : CommRingCat} (r : R) :
    IsLocalization.Away r Γ(AlgebraicGeometry.Spec R, PrimeSpectrum.basicOpen r) := by
  infer_instance

/-- The two affine-spectrum constructions are inverse under the hom equivalence. -/
@[simp]
theorem affineSpec_homEquiv_map {R S : CommRingCat} (f : R ⟶ S) :
    affineSpec_homEquiv R S (Spec.map f) = f := by
  exact AlgebraicGeometry.Spec.preimage_map f

@[simp]
theorem affineSpec_map_homEquiv {R S : CommRingCat}
    (f : AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R) :
    Spec.map (affineSpec_homEquiv R S f) = f := by
  exact AlgebraicGeometry.Spec.map_preimage f

/-- The global-sections map of an affine spectrum morphism is the original ring map. -/
@[reassoc (attr := simp)]
theorem affineSpecMap_globalSections_naturality {R S : CommRingCat} (f : R ⟶ S) :
    (Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom =
      (Scheme.ΓSpecIso R).hom ≫ f := by
  exact Scheme.ΓSpecIso_naturality f

/-- Affine spectrum morphisms induce local maps on all stalks. -/
theorem affineSpecMap_stalkMap_isLocalHom {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum S) :
    IsLocalHom ((affineSpecMap f).stalkMap p).hom := by
  infer_instance

/-- Restriction of the affine structure sheaf to a basic open is functorial. -/
@[simp]
theorem affineStructureSheaf_comap_basicOpen {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) :
    StructureSheaf.comap f (PrimeSpectrum.basicOpen r) (PrimeSpectrum.basicOpen (f r))
      (PrimeSpectrum.comap_basicOpen f r).le =
      IsLocalization.map (M := .powers r) (T := .powers (f r)) _ f
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _)) := by
  exact StructureSheaf.comap_basicOpen f r

/-! ### Sections and stalks -/

/-- The stalk of the affine structure sheaf is localized at the corresponding prime. -/
theorem affineStructureSheaf_stalk_isLocalization
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    IsLocalization.AtPrime
      ((affineStructureSheaf R).presheaf.stalk p) p.asIdeal := by
  exact StructureSheaf.IsLocalization.to_stalk R p

/-- The canonical localization-to-stalk isomorphism. -/
noncomputable def affineStructureSheaf_stalk_iso
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    Localization.AtPrime p.asIdeal ≃ₐ[R]
      ((affineStructureSheaf R).presheaf.stalk p) :=
  StructureSheaf.stalkIso R p

/-- The stalk of `Spec R` is the localization of `R` at its point. -/
def affineSpec_stalk_iso
    (R : CommRingCat) (p : PrimeSpectrum R) :
    (AlgebraicGeometry.Spec R).presheaf.stalk p ≅
      CommRingCat.of (Localization.AtPrime p.asIdeal) := by
  exact Spec.stalkIso R p

/-! The affine stalk identifications are functorial for ring maps. -/

@[reassoc]
theorem affineSpecMap_stalkIso_naturality {R S : CommRingCat} (f : R ⟶ S)
    (p : PrimeSpectrum S) :
    (affineSpec_stalk_iso R (p.comap f.hom)).hom ≫
      (CommRingCat.ofHom <| Localization.localRingHom
        (p.comap f.hom).asIdeal p.asIdeal f.hom rfl) ≫
      (affineSpec_stalk_iso S p).inv = (Spec.map f).stalkMap p := by
  exact Scheme.localRingHom_comp_stalkIso f p

/-- Sections on a basic open are the localization away from its defining element. -/
theorem affineStructureSheaf_basicOpen_isLocalization
    (R : Type u) [CommRing R] (f : R) :
    IsLocalization.Away f
      ((affineStructureSheaf R).obj.obj
        (op (PrimeSpectrum.basicOpen f))) := by
  exact StructureSheaf.IsLocalization.to_basicOpen R f

/-- The canonical localization-to-sections isomorphism on a basic open. -/
noncomputable def affineStructureSheaf_basicOpen_iso
    (R : Type u) [CommRing R] (f : R) :
    Localization.Away f ≃ₐ[R]
      ((affineStructureSheaf R).obj.obj
        (op (PrimeSpectrum.basicOpen f))) :=
  IsLocalization.algEquiv (Submonoid.powers f) _ _

/-- The canonical map from `R` to sections on the whole affine spectrum is bijective. -/
theorem affineStructureSheaf_globalSections_bijective
    (R : Type u) [CommRing R] :
    Function.Bijective
      (algebraMap R ((affineStructureSheaf R).obj.obj (op (⊤ : Opens (PrimeSpectrum R))))) := by
  exact StructureSheaf.algebraMap_obj_top_bijective

/-- Global sections of the affine structure sheaf recover the coordinate ring. -/
def affineStructureSheaf_globalSectionsIso
    (R : Type u) [CommRing R] :
    CommRingCat.of R ≅
      (affineStructureSheaf R).obj.obj (op (⊤ : Opens (PrimeSpectrum R))) :=
  StructureSheaf.globalSectionsIso R

/-- The global-sections identification in scheme notation. -/
def affineSpec_globalSectionsIso (R : CommRingCat) :
    Γ(AlgebraicGeometry.Spec R, ⊤) ≅ R :=
  Scheme.ΓSpecIso R

/-- Every stalk on an affine scheme is a local ring. -/
theorem affineSpec_stalk_isLocalRing
    (R : CommRingCat) (p : PrimeSpectrum R) :
    IsLocalRing ((AlgebraicGeometry.Spec R).presheaf.stalk p) := by
  exact (AlgebraicGeometry.Spec R).toLocallyRingedSpace.isLocalRing p

end

end Hartshorne
