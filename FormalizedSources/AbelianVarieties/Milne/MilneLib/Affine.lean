/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Affine modules and global sections

On an affine scheme, a module and the global sections of its associated
quasi-coherent sheaf are canonically isomorphic.  These declarations expose
the affine instance used in Milne's module--sheaf discussion, together with
its functoriality and its finite-dimensional specialization over a field.
-/

open CategoryTheory
open AlgebraicGeometry
open Opposite

universe u

namespace MilneLib

/-- The quasi-coherent sheaf associated with a module on `Spec R`. -/
noncomputable def affineModuleSheaf
    (R : CommRingCat.{u}) (M : ModuleCat R) : (Spec R).Modules :=
  AlgebraicGeometry.tilde M

/-- The canonical identification of a module with the global sections of its
associated affine sheaf. -/
noncomputable def affineModuleGlobalSectionsIso
    (R : CommRingCat.{u}) (M : ModuleCat R) :
    M ≅ AlgebraicGeometry.moduleSpecΓFunctor.obj (affineModuleSheaf R M) :=
  AlgebraicGeometry.tilde.isoTop M

/- A finite generating family of the affine tilde gives finite generation of
   the underlying module.  This is the affine finite-type half needed before
   localizing to stalks; no arbitrary-scheme coherent-stalk theorem is used. -/
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 400000 in
-- The tilde--Γ adjunction instance chain needs extra synthesis headroom.
set_option maxHeartbeats 800000 in
theorem module_finite_of_tilde_genSections
    {R : CommRingCat.{u}} (N : ModuleCat.{u} R)
    (σ : (AlgebraicGeometry.tilde N).GeneratingSections) [σ.IsFiniteType] :
    Module.Finite R N := by
  haveI hσπ : Epi σ.π := σ.epi
  let π' : (AlgebraicGeometry.tilde.functor R).obj
      (ModuleCat.of R (σ.I →₀ R)) ⟶ AlgebraicGeometry.tilde N :=
    (AlgebraicGeometry.tildeFinsupp σ.I).hom ≫ σ.π
  haveI hπ' : Epi π' := epi_comp _ _
  let t : ModuleCat.of R (σ.I →₀ R) ⟶
      AlgebraicGeometry.moduleSpecΓFunctor.obj (AlgebraicGeometry.tilde N) :=
    (AlgebraicGeometry.tilde.adjunction.homEquiv _ _) π'
  have hfac : (AlgebraicGeometry.tilde.functor R).map t ≫
      AlgebraicGeometry.tilde.adjunction.counit.app (AlgebraicGeometry.tilde N) = π' :=
    (Adjunction.homEquiv_counit AlgebraicGeometry.tilde.adjunction _ _ t).symm.trans
      ((AlgebraicGeometry.tilde.adjunction.homEquiv _ _).symm_apply_apply π')
  haveI hu : IsIso (AlgebraicGeometry.tilde.adjunction.unit.app N) := inferInstance
  haveI hmu : IsIso ((AlgebraicGeometry.tilde.functor R).map
      (AlgebraicGeometry.tilde.adjunction.unit.app N)) := inferInstance
  haveI hcomp : IsIso ((AlgebraicGeometry.tilde.functor R).map
      (AlgebraicGeometry.tilde.adjunction.unit.app N) ≫
      AlgebraicGeometry.tilde.adjunction.counit.app
        ((AlgebraicGeometry.tilde.functor R).obj N)) := by
    rw [AlgebraicGeometry.tilde.adjunction.left_triangle_components N]
    infer_instance
  haveI hcu : IsIso (AlgebraicGeometry.tilde.adjunction.counit.app
      (AlgebraicGeometry.tilde N)) :=
    IsIso.of_isIso_comp_left
      ((AlgebraicGeometry.tilde.functor R).map
        (AlgebraicGeometry.tilde.adjunction.unit.app N))
      (AlgebraicGeometry.tilde.adjunction.counit.app
        ((AlgebraicGeometry.tilde.functor R).obj N))
  haveI hmt : Epi ((AlgebraicGeometry.tilde.functor R).map t) := by
    have hre : (AlgebraicGeometry.tilde.functor R).map t =
        π' ≫ inv (AlgebraicGeometry.tilde.adjunction.counit.app
          (AlgebraicGeometry.tilde N)) := by
      rw [← hfac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [hre]
    exact epi_comp _ _
  haveI ht : Epi t := (AlgebraicGeometry.tilde.functor R).epi_of_epi_map hmt
  haveI : Epi (t ≫ inv (AlgebraicGeometry.tilde.adjunction.unit.app N)) :=
    epi_comp _ _
  exact Module.Finite.of_surjective
    (ModuleCat.Hom.hom (t ≫ inv (AlgebraicGeometry.tilde.adjunction.unit.app N)))
    ((ModuleCat.epi_iff_surjective _).mp ‹_›)

/-- The affine global-sections identification is natural in the module. -/
theorem affineModuleGlobalSectionsIso_naturality
    (R : CommRingCat.{u}) {M N : ModuleCat R} (f : M ⟶ N) :
    f ≫ (affineModuleGlobalSectionsIso R N).hom =
      (affineModuleGlobalSectionsIso R M).hom ≫
        AlgebraicGeometry.moduleSpecΓFunctor.map
          ((AlgebraicGeometry.tilde.functor R).map f) := by
  exact (AlgebraicGeometry.tilde.toTildeΓNatIso (R := R)).hom.naturality f

/-- Pushforward preserves the underlying global-sections module at the top open. -/
@[simp]
theorem pushforward_globalSections_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    Γ((Scheme.Modules.pushforward f).obj M, (⊤ : Y.Opens)) =
      Γ(M, (⊤ : X.Opens)) := by
  rfl

/-- A quasi-coherent presentation cover on an affine scheme has a finite basic-open
refinement.  Each selected basic open is contained in one member of the cover,
which is the finite-cover input for affine section-localization arguments. -/
theorem exists_finite_basicOpen_cover_le_quasicoherentData {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) :
    ∃ t : Finset R, Ideal.span (t : Set R) = ⊤ ∧
      ∀ r ∈ t, ∃ i, (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ q.X i := by
  classical
  set G : Set R := {r | ∃ i, (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ q.X i} with hG
  have hspanG : Ideal.span G = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    rw [eq_top_iff]
    intro x _
    simp only [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨U, f, hf, hxU⟩ := q.coversTop ⊤ x (by trivial)
    rw [Sieve.mem_ofObjects_iff] at hf
    obtain ⟨i, ⟨hUi⟩⟩ := hf
    have hxXi : x ∈ q.X i := (leOfHom hUi) hxU
    obtain ⟨V, ⟨r, rfl⟩, hxV, hVle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hxXi
    exact ⟨r, ⟨i, hVle⟩, hxV⟩
  obtain ⟨t, htsub, htspan⟩ := (Ideal.span_eq_top_iff_finite G).mp hspanG
  exact ⟨t, htspan, fun r hr => htsub hr⟩

/-- A finite affine module has finite stalks after applying the tilde
construction.  The stalk is viewed as a module over the corresponding
structure-sheaf stalk. -/
theorem moduleFinite_tilde_stalk
    {R : CommRingCat.{u}} (M : ModuleCat R) [Module.Finite R M]
    (x : PrimeSpectrum.Top R) :
    Module.Finite
      ((AlgebraicGeometry.structurePresheafInCommRingCat R).stalk x)
      ((TopCat.Presheaf.stalk (C := Ab.{u})
        (AlgebraicGeometry.moduleStructurePresheaf R M).presheaf x) : Ab.{u}) := by
  exact Module.Finite.of_isLocalizedModule x.asIdeal.primeCompl
    (AlgebraicGeometry.StructureSheaf.toStalkₗ R M x)

/-- Finite generating sections of an affine tilde therefore give finite stalks. -/
theorem tilde_stalk_finite_of_finite_generating_sections
    {R : CommRingCat.{u}} {N : ModuleCat.{u} R}
    (σ : (AlgebraicGeometry.tilde N).GeneratingSections) [σ.IsFiniteType]
    (x : PrimeSpectrum.Top R) :
    Module.Finite
      ((AlgebraicGeometry.structurePresheafInCommRingCat R).stalk x)
      ((TopCat.Presheaf.stalk (C := Ab.{u})
        (AlgebraicGeometry.moduleStructurePresheaf R N).presheaf x) : Ab.{u}) := by
  letI : Module.Finite R N := module_finite_of_tilde_genSections N σ
  exact moduleFinite_tilde_stalk N x

/- The affine-module stalk finiteness statement with the scheme-module stalk
   instance made explicit for later residue-fibre arguments. -/
theorem moduleFinite_affineModuleSheaf_stalk
    {R : CommRingCat.{u}} (M : ModuleCat R) [Module.Finite R M]
    (x : Spec R) :
    letI : Module ((Spec R).presheaf.stalk x)
        ((TopCat.Presheaf.stalk (C := Ab.{u})
          ((affineModuleSheaf R M).val.presheaf) x) : Type u) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (affineModuleSheaf R M).val x
    Module.Finite ((Spec R).presheaf.stalk x)
      ((TopCat.Presheaf.stalk (C := Ab.{u})
        ((affineModuleSheaf R M).val.presheaf) x) : Ab.{u}) := by
  letI : Module ((Spec R).presheaf.stalk x)
      ((TopCat.Presheaf.stalk (C := Ab.{u})
        ((affineModuleSheaf R M).val.presheaf) x) : Type u) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (affineModuleSheaf R M).val x
  exact moduleFinite_tilde_stalk M x

/-- The preceding affine construction for a finite-dimensional vector space. -/
noncomputable def affineVectorSpaceSheaf
    {k : Type u} [Field k] (M : ModuleCat (CommRingCat.of k))
    [Module.Finite (CommRingCat.of k) M] :
    (Spec (CommRingCat.of k)).Modules :=
  affineModuleSheaf (CommRingCat.of k) M

/-- A finite-dimensional vector space is recovered from the global sections of
its associated sheaf on the one-point affine scheme. -/
noncomputable def affineVectorSpaceGlobalSectionsIso
    {k : Type u} [Field k] (M : ModuleCat (CommRingCat.of k))
    [Module.Finite (CommRingCat.of k) M] :
    M ≅ AlgebraicGeometry.moduleSpecΓFunctor.obj (affineVectorSpaceSheaf M) :=
  affineModuleGlobalSectionsIso (CommRingCat.of k) M

end MilneLib
