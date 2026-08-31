/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.LocallySurjective
import MilneLib.Affine
import MilneLib.Coherent
import MilneLib.LinearAlgebra
import MilneLib.Tensor

/-!
# Sheaf evaluation

For a morphism of schemes, the pullback--pushforward adjunction supplies the
canonical evaluation morphism on sheaves of modules.  We expose its counit at
the functor and object levels.
-/

open CategoryTheory
open AlgebraicGeometry
open Opposite
open scoped TensorProduct

universe u

namespace MilneLib

/-- A morphism of sheaves of modules that is surjective on every stalk is an
epimorphism. -/
theorem schemeModule_epi_of_surjective_on_stalks {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N)
    (hf : ∀ x : X, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.mapPresheaf)) :
    Epi f := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hlocal : TopCat.Presheaf.IsLocallySurjective (F.map f).hom :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).2 hf
  have : Epi (F.map f) := by
    letI : CategoryTheory.Sheaf.IsLocallySurjective (F.map f) := hlocal
    infer_instance
  exact F.epi_of_epi_map this

/-- A morphism of scheme modules whose additive stalk maps are bijective is an
isomorphism.  This stalk-level criterion is useful for the invertible-sheaf
conclusion in Milne I.5.11 without assuming a separate formalization of
coherence or local freeness. -/
theorem schemeModule_isIso_of_bijective_on_stalks
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x : X, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.mapPresheaf)) :
    IsIso f := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
    ((SheafOfModules.toSheaf X.ringCatSheaf).map f) U
    (fun x _ => hf x)

/-- A morphism of scheme modules is an isomorphism exactly when all of its
additive stalk maps are isomorphisms. -/
theorem schemeModule_isIso_iff_isIso_on_stalks
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    IsIso f ↔ ∀ x : X, IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.mapPresheaf) := by
  constructor
  · intro h x
    letI : IsIso f := h
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((Scheme.Modules.toPresheaf X).map f))
    infer_instance
  · intro h
    apply schemeModule_isIso_of_bijective_on_stalks f
    intro x
    letI : IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.mapPresheaf) := h x
    exact ConcreteCategory.bijective_of_isIso _

/-- A scheme module is *stalkwise finite* when each of its scheme-module
stalks is a finitely generated module over the corresponding structure-sheaf
stalk.  The `letI` binder records the canonical module structure explicitly;
this predicate does not assert finiteness from coherence or any other
unstated geometric hypothesis. -/
def SchemeModule.IsStalkwiseFinite {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∀ x : X,
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      schemeModuleStalkModule F x
    Module.Finite (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u)

/-- Stalkwise finite modules have finite residue-field fibres. -/
theorem SchemeModule.IsStalkwiseFinite.residueFieldTensor
    {X : Scheme.{u}} (F : X.Modules)
    (hF : SchemeModule.IsStalkwiseFinite F) :
    ∀ x : X,
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
        schemeModuleStalkModule F x
      Module.Finite (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u)) := by
  intro x
  exact moduleFinite_schemeModuleStalk_residueTensor F x (hF x)

/-- A finite family spanning the stalk of a scheme module at a point.  The
canonical stalk module structure is recorded explicitly so this predicate can
be used as an interface between geometric generators and algebraic finiteness. -/
def SchemeModule.HasFiniteStalkGenerators {X : Scheme.{u}} (F : X.Modules)
    (x : X) : Prop :=
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    schemeModuleStalkModule F x
  ∃ (ι : Type u), ∃ (_ : Fintype ι),
    ∃ (g : ι → (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u)),
      Submodule.span (X.presheaf.stalk x) (Set.range g) = ⊤

/-- A finite family of sections is a local generating family at a point when
every section on a neighbourhood of that point becomes a linear combination
of the family's restrictions after shrinking once more.  The predicate is
deliberately stated with the scheme-module scalar ring so it can be used
without transporting typeclass instances through `ringCatSheaf`. -/
def SchemeModule.HasFiniteLocalGenerators {X : Scheme.{u}} (F : X.Modules)
    (x : X) : Prop :=
  ∃ (ι : Type u), ∃ (_ : Fintype ι), ∃ (U : X.Opens) (_ : x ∈ U)
    (s : ι → (F.val.obj (op U) : Type u)),
    ∀ (V : X.Opens) (hVU : V ≤ U) (_ : x ∈ V)
      (t : (F.val.obj (op V) : Type u)), ∃ (W : X.Opens) (_ : x ∈ W)
      (hWV : W ≤ V) (c : ι → (X.ringCatSheaf.obj.obj (op W) : Type u)),
      (ConcreteCategory.hom (F.val.map (homOfLE hWV).op)) t =
        ∑ i, c i • (ConcreteCategory.hom
          (F.val.map (homOfLE (hWV.trans hVU)).op)) (s i)

/-- Local generating sections produce a finite spanning family in the stalk. -/
theorem SchemeModule.HasFiniteStalkGenerators.of_hasFiniteLocalGenerators
    {X : Scheme.{u}} (F : X.Modules) (x : X)
    (hgen : SchemeModule.HasFiniteLocalGenerators F x) :
    SchemeModule.HasFiniteStalkGenerators F x := by
  obtain ⟨ι, hι, U, hxU, s, hs⟩ := hgen
  letI : Fintype ι := hι
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    schemeModuleStalkModule F x
  letI : Module.Finite (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    moduleFinite_stalk_of_local_generators F.val hxU s hs
  obtain ⟨ι' : Type u, hι', g, hg⟩ :=
    (Submodule.fg_iff_exists_finite_generating_family
      (A := X.presheaf.stalk x)
      (M := (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u))).mp
      Module.Finite.fg_top
  letI : Fintype ι' := Fintype.ofFinite ι'
  exact ⟨ι', inferInstance, g, hg⟩

/-- A finite spanning family in every stalk gives stalkwise finiteness. -/
theorem SchemeModule.IsStalkwiseFinite.of_hasFiniteStalkGenerators
    {X : Scheme.{u}} (F : X.Modules)
    (hgen : ∀ x : X, SchemeModule.HasFiniteStalkGenerators F x) :
    SchemeModule.IsStalkwiseFinite F := by
  intro x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    schemeModuleStalkModule F x
  dsimp [SchemeModule.HasFiniteStalkGenerators] at hgen
  obtain ⟨ι, hι, g, hg⟩ := hgen x
  letI : Fintype ι := hι
  exact moduleFinite_of_finite_generating_family g hg

/-- Finite local generating families give finite scheme-module stalks.  This
is the explicit local-generation route needed before a general coherence
instance can be connected to stalk finiteness. -/
theorem SchemeModule.IsStalkwiseFinite.of_hasFiniteLocalGenerators
    {X : Scheme.{u}} (F : X.Modules)
    (hgen : ∀ x : X, SchemeModule.HasFiniteLocalGenerators F x) :
    SchemeModule.IsStalkwiseFinite F := by
  apply SchemeModule.IsStalkwiseFinite.of_hasFiniteStalkGenerators F
  intro x
  exact SchemeModule.HasFiniteStalkGenerators.of_hasFiniteLocalGenerators F x
    (hgen x)

/-- Local generators therefore have finite residue-field fibres pointwise. -/
theorem SchemeModule.HasFiniteLocalGenerators.residueFieldTensor
    {X : Scheme.{u}} (F : X.Modules) (x : X)
    (hgen : SchemeModule.HasFiniteLocalGenerators F x) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      schemeModuleStalkModule F x
    Module.Finite (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u)) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    schemeModuleStalkModule F x
  apply moduleFinite_schemeModuleStalk_residueTensor F x
  obtain ⟨ι, hι, g, hg⟩ :=
    SchemeModule.HasFiniteStalkGenerators.of_hasFiniteLocalGenerators F x hgen
  letI : Fintype ι := hι
  exact moduleFinite_of_finite_generating_family g hg

/-- Stalkwise finiteness can be represented by a finite spanning family at
each point. -/
theorem SchemeModule.HasFiniteStalkGenerators.of_isStalkwiseFinite
    {X : Scheme.{u}} {F : X.Modules}
    (hF : SchemeModule.IsStalkwiseFinite F) (x : X) :
    SchemeModule.HasFiniteStalkGenerators F x := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    schemeModuleStalkModule F x
  letI : Module.Finite (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) := hF x
  obtain ⟨ι : Type u, hι, g, hg⟩ :=
    (Submodule.fg_iff_exists_finite_generating_family
      (A := X.presheaf.stalk x)
      (M := (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u))).mp
      Module.Finite.fg_top
  letI : Fintype ι := Fintype.ofFinite ι
  exact ⟨ι, inferInstance, g, hg⟩

/-- The explicit finite-generator and stalkwise-finite formulations agree. -/
theorem schemeModule_isStalkwiseFinite_iff_hasFiniteStalkGenerators
    {X : Scheme.{u}} (F : X.Modules) :
    SchemeModule.IsStalkwiseFinite F ↔
      ∀ x : X, SchemeModule.HasFiniteStalkGenerators F x := by
  constructor
  · intro h x
    exact SchemeModule.HasFiniteStalkGenerators.of_isStalkwiseFinite h x
  · exact SchemeModule.IsStalkwiseFinite.of_hasFiniteStalkGenerators F

/-- At a fixed point, the finite-generator and finite-module formulations of
stalkwise finiteness agree. -/
theorem schemeModule_hasFiniteStalkGenerators_iff_moduleFinite_stalk
    {X : Scheme.{u}} (F : X.Modules) (x : X) :
    SchemeModule.HasFiniteStalkGenerators F x ↔
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
        schemeModuleStalkModule F x
      Module.Finite (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) := by
  constructor
  · intro hgen
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      schemeModuleStalkModule F x
    dsimp [SchemeModule.HasFiniteStalkGenerators] at hgen
    obtain ⟨ι, hι, g, hg⟩ := hgen
    letI : Fintype ι := hι
    exact moduleFinite_of_finite_generating_family g hg
  · intro hfinite
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      schemeModuleStalkModule F x
    letI : Module.Finite (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) := hfinite
    obtain ⟨ι : Type u, hι, g, hg⟩ :=
      (Submodule.fg_iff_exists_finite_generating_family
        (A := X.presheaf.stalk x)
        (M := (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u))).mp
        Module.Finite.fg_top
    letI : Fintype ι := Fintype.ofFinite ι
    exact ⟨ι, inferInstance, g, hg⟩

/-- Stalkwise finiteness is invariant under isomorphism of scheme modules. -/
theorem SchemeModule.IsStalkwiseFinite.of_iso
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [IsIso f]
    (hN : SchemeModule.IsStalkwiseFinite N) :
    SchemeModule.IsStalkwiseFinite M := by
  intro x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    schemeModuleStalkModule N x
  letI hstalk : IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.mapPresheaf) := by
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((Scheme.Modules.toPresheaf X).map f))
    infer_instance
  let e := schemeModuleStalkLinearEquivOfIsIso f x hstalk
  letI : Module.Finite (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) := hN x
  exact Module.Finite.equiv e.symm

/-- Stalkwise finiteness is equivalent across an isomorphism of scheme modules. -/
theorem schemeModule_isStalkwiseFinite_iff_of_iso
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [IsIso f] :
    SchemeModule.IsStalkwiseFinite M ↔ SchemeModule.IsStalkwiseFinite N := by
  constructor
  · intro hM
    exact SchemeModule.IsStalkwiseFinite.of_iso (inv f) hM
  · exact SchemeModule.IsStalkwiseFinite.of_iso f

/-- Stalkwise finiteness descends along a map that is surjective on stalks. -/
theorem SchemeModule.IsStalkwiseFinite.of_surjective_stalks
    {X : Scheme.{u}} {M N : X.Modules}
    (hM : SchemeModule.IsStalkwiseFinite M) (f : M ⟶ N)
    (hsurj : ∀ x : X, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.mapPresheaf)) :
    SchemeModule.IsStalkwiseFinite N := by
  intro x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    schemeModuleStalkModule N x
  letI : Module.Finite (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) := hM x
  exact Module.Finite.of_surjective (schemeModuleStalkLinearMap f x) (hsurj x)

/-- A residue-fibre surjection gives a sheaf epimorphism once the target
stalks are known to be finite.  The finite-stalk hypothesis is explicit: the
general coherent-stalk theorem needed by Milne I.5.11 is not yet available in
Mathlib, while affine tilde modules can supply it through
`moduleFinite_affineModuleSheaf_stalk`. -/
theorem schemeModule_epi_of_surjective_on_residue_fibres
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (hfinite : ∀ x : X,
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
        schemeModuleStalkModule N x
      Module.Finite (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u))
    (hres : ∀ x : X,
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
        schemeModuleStalkModule M x
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
        schemeModuleStalkModule N x
      Function.Surjective
        ((schemeModuleStalkLinearMap f x).lTensor
          (IsLocalRing.ResidueField (X.presheaf.stalk x)))) :
    Epi f := by
  apply schemeModule_epi_of_surjective_on_stalks f
  intro x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    schemeModuleStalkModule N x
  letI : Module.Finite (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    hfinite x
  exact (LinearMap.surjective_lTensor_residueField_iff_surjective
    (schemeModuleStalkLinearMap f x)).mp (hres x)

/-- The residue-fibre epimorphism criterion can consume finite local
generators directly, without a separately supplied stalk-finiteness proof. -/
theorem schemeModule_epi_of_surjective_on_residue_fibres_of_hasFiniteLocalGenerators
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (hgen : ∀ x : X, SchemeModule.HasFiniteLocalGenerators N x)
    (hres : ∀ x : X,
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
        schemeModuleStalkModule M x
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
        schemeModuleStalkModule N x
      Function.Surjective
        ((schemeModuleStalkLinearMap f x).lTensor
          (IsLocalRing.ResidueField (X.presheaf.stalk x)))) :
    Epi f := by
  apply schemeModule_epi_of_surjective_on_residue_fibres f
  · exact SchemeModule.IsStalkwiseFinite.of_hasFiniteLocalGenerators N hgen
  · exact hres

/-- If the source and target stalks are invertible modules, residue-fibre
surjectivity upgrades to an isomorphism.  This is the algebraic and stalkwise
content of the invertible-sheaf conclusion in Milne I.5.11; the hypotheses are
kept at stalk level until Mathlib exposes the corresponding global sheaf
predicate and its stalk instances. -/
theorem schemeModule_isIso_of_surjective_on_residue_fibres_of_invertible_stalks
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (hinv : ∀ x : X,
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
        schemeModuleStalkModule M x
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
        schemeModuleStalkModule N x
      Module.Invertible (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) ∧
        Module.Invertible (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u))
    (hres : ∀ x : X,
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
        schemeModuleStalkModule M x
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
        schemeModuleStalkModule N x
      Function.Surjective
        ((schemeModuleStalkLinearMap f x).lTensor
          (IsLocalRing.ResidueField (X.presheaf.stalk x)))) :
    IsIso f := by
  apply schemeModule_isIso_of_bijective_on_stalks f
  intro x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    schemeModuleStalkModule N x
  let hi := hinv x
  letI : Module.Invertible (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) := hi.1
  letI : Module.Invertible (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) := hi.2
  exact Module.Invertible.bijective_of_surjective
    ((LinearMap.surjective_lTensor_residueField_iff_surjective
      (schemeModuleStalkLinearMap f x)).mp (hres x))

/-- Affine tilde specialization of the residue-fibre epi bridge.  For a
finite target module, the required finite-stalk instances are supplied by
`moduleFinite_affineModuleSheaf_stalk`; only the residue-fibre maps remain as
an input. -/
theorem affineModuleSheaf_epi_of_surjective_on_residue_fibres
    {R : CommRingCat.{u}} {M N : ModuleCat R} [Module.Finite R N]
    (f : M ⟶ N)
    (hres : ∀ x : Spec R,
      letI : Module ((Spec R).presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk
            ((AlgebraicGeometry.tilde.functor R).obj M).val.presheaf x) : Type u) :=
        schemeModuleStalkModule ((AlgebraicGeometry.tilde.functor R).obj M) x
      letI : Module ((Spec R).presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk
            ((AlgebraicGeometry.tilde.functor R).obj N).val.presheaf x) : Type u) :=
        schemeModuleStalkModule ((AlgebraicGeometry.tilde.functor R).obj N) x
      Function.Surjective
        ((schemeModuleStalkLinearMap
          ((AlgebraicGeometry.tilde.functor R).map f) x).lTensor
          (IsLocalRing.ResidueField ((Spec R).presheaf.stalk x)))) :
    Epi ((AlgebraicGeometry.tilde.functor R).map f) := by
  apply schemeModule_epi_of_surjective_on_residue_fibres
    ((AlgebraicGeometry.tilde.functor R).map f)
  · intro x
    exact moduleFinite_affineModuleSheaf_stalk N x
  · exact hres

/-- A finite affine module gives a stalkwise-finite scheme module. -/
theorem affineModuleSheaf_isStalkwiseFinite
    {R : CommRingCat.{u}} (N : ModuleCat R) [Module.Finite R N] :
    SchemeModule.IsStalkwiseFinite
      ((AlgebraicGeometry.tilde.functor R).obj N) := by
  intro x
  exact moduleFinite_affineModuleSheaf_stalk N x

/-- Method-style form of the residue-fibre epimorphism bridge.  This is the
reusable I.5.11 interface: callers provide a stalkwise-finite target and only
the residue-fibre surjectivity remains to be checked. -/
theorem SchemeModule.IsStalkwiseFinite.epi_of_surjective_on_residue_fibres
    {X : Scheme.{u}} {M N : X.Modules} (hfinite : SchemeModule.IsStalkwiseFinite N)
    (f : M ⟶ N)
    (hres : ∀ x : X,
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
        schemeModuleStalkModule M x
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
        schemeModuleStalkModule N x
      Function.Surjective
        ((schemeModuleStalkLinearMap f x).lTensor
          (IsLocalRing.ResidueField (X.presheaf.stalk x)))) :
    Epi f := by
  exact schemeModule_epi_of_surjective_on_residue_fibres f hfinite hres

/-- Residue-fibre surjectivity together with injectivity on every additive
stalk gives an isomorphism.  The injectivity hypothesis is explicit because
finite stalks alone do not make a residue-fibre bijection lift to an
isomorphism for arbitrary (possibly non-Noetherian) local rings. -/
theorem SchemeModule.IsStalkwiseFinite.isIso_of_surjective_on_residue_fibres_of_injective_stalks
    {X : Scheme.{u}} {M N : X.Modules}
    (hfinite : SchemeModule.IsStalkwiseFinite N) (f : M ⟶ N)
    (hinj : ∀ x : X, Function.Injective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.mapPresheaf))
    (hres : ∀ x : X,
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
        schemeModuleStalkModule M x
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
        schemeModuleStalkModule N x
      Function.Surjective
        ((schemeModuleStalkLinearMap f x).lTensor
          (IsLocalRing.ResidueField (X.presheaf.stalk x)))) :
    IsIso f := by
  apply schemeModule_isIso_of_bijective_on_stalks f
  intro x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    schemeModuleStalkModule N x
  letI : Module.Finite (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    hfinite x
  refine ⟨hinj x, ?_⟩
  exact (LinearMap.surjective_lTensor_residueField_iff_surjective
    (schemeModuleStalkLinearMap f x)).mp (hres x)

/-- The counit of the pullback--pushforward adjunction for a scheme morphism. -/
noncomputable def schemeSheafEvaluation {W V : Scheme} (f : W ⟶ V) :
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f) ⟶ 𝟭 W.Modules :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).counit

/-- Evaluation on a particular sheaf of modules. -/
noncomputable def schemeSheafEvaluationAt {W V : Scheme} (f : W ⟶ V)
    (M : W.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj M) ⟶ M :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M

@[simp]
theorem schemeSheafEvaluation_app {W V : Scheme} (f : W ⟶ V) (M : W.Modules) :
    (schemeSheafEvaluation f).app M = schemeSheafEvaluationAt f M := rfl

/-- Evaluation is natural in the sheaf of modules. -/
theorem schemeSheafEvaluationAt_naturality {W V : Scheme} (f : W ⟶ V)
    {M N : W.Modules} (g : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pushforward f).map g) ≫
        schemeSheafEvaluationAt f N =
      schemeSheafEvaluationAt f M ≫ g := by
  exact (schemeSheafEvaluation f).naturality g

/-- The unit of the pullback--pushforward adjunction for a scheme morphism. -/
noncomputable def schemeSheafCoevaluation {W V : Scheme} (f : W ⟶ V) :
    Functor.id V.Modules ⟶
      (Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit

/-- Coevaluation on a particular sheaf of modules. -/
noncomputable def schemeSheafCoevaluationAt {W V : Scheme} (f : W ⟶ V)
    (M : V.Modules) :
    M ⟶ (Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback f).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M

@[simp]
theorem schemeSheafCoevaluation_app {W V : Scheme} (f : W ⟶ V)
    (M : V.Modules) :
    (schemeSheafCoevaluation f).app M = schemeSheafCoevaluationAt f M := rfl

/-- Coevaluation is natural in the sheaf of modules. -/
theorem schemeSheafCoevaluationAt_naturality {W V : Scheme} (f : W ⟶ V)
    {M N : V.Modules} (g : M ⟶ N) :
    g ≫ schemeSheafCoevaluationAt f N =
      schemeSheafCoevaluationAt f M ≫
        (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullback f).map g) := by
  exact (schemeSheafCoevaluation f).naturality g

/-- Pulling back coevaluation and then evaluating is the identity. -/
@[simp]
theorem schemeSheafCoevaluation_evaluation {W V : Scheme} (f : W ⟶ V)
    (M : V.Modules) :
    (Scheme.Modules.pullback f).map (schemeSheafCoevaluationAt f M) ≫
        schemeSheafEvaluationAt f ((Scheme.Modules.pullback f).obj M) =
      𝟙 ((Scheme.Modules.pullback f).obj M) := by
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).left_triangle_components M

/-- Coevaluating a pushforward and then pushing forward evaluation is the identity. -/
@[simp]
theorem schemeSheafEvaluation_coevaluation {W V : Scheme} (f : W ⟶ V)
    (M : W.Modules) :
    schemeSheafCoevaluationAt f ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.pushforward f).map (schemeSheafEvaluationAt f M) =
      𝟙 ((Scheme.Modules.pushforward f).obj M) := by
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).right_triangle_components M

end MilneLib
