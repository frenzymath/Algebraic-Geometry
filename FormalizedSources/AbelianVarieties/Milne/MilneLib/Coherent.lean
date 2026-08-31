/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Finite generation for coherent-module arguments

This file records the algebraic finiteness step used when a stalk is generated
by finitely many sections.  The statements are deliberately independent of
the sheaf implementation: a finite generating family is converted to a
`Module.Finite` instance, and a surjection from a module with a finite basis
transfers finiteness to its target.
-/

open Function
open CategoryTheory TopologicalSpace TopCat.Presheaf Opposite
open AlgebraicGeometry
open scoped TensorProduct

namespace MilneLib

universe u v w

/-- A finite set of generators makes a module finite. -/
theorem moduleFinite_of_finite_generating_set
    {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    {s : Set M} (hs : s.Finite)
    (hspan : Submodule.span R s = ⊤) : Module.Finite R M := by
  apply Module.Finite.of_fg_top
  rw [← hspan]
  exact Submodule.fg_span hs

/-- A finite-indexed family spanning a module makes it finite. -/
theorem moduleFinite_of_finite_generating_family
    {R : Type u} {M : Type v} {ι : Type w}
    [Semiring R] [AddCommMonoid M] [Module R M] [Finite ι]
    (s : ι → M) (hspan : Submodule.span R (Set.range s) = ⊤) :
    Module.Finite R M := by
  apply Module.Finite.of_fg_top
  exact (Submodule.fg_iff_exists_finite_generating_family).2
    ⟨ι, inferInstance, s, hspan⟩

/-- Finiteness descends along a surjective linear map from a finite-basis
module.  The basis may be indexed by any finite type. -/
theorem moduleFinite_of_surjective_of_finite_basis
    {R : Type u} {P : Type v} {M : Type w} {ι : Type*}
    [Semiring R] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M] [Module R M] [Finite ι]
    (b : Module.Basis ι R P) (f : P →ₗ[R] M) (hf : Function.Surjective f) :
    Module.Finite R M := by
  letI : Module.Finite R P := Module.Finite.of_basis b
  exact Module.Finite.of_surjective f hf

/-- A finite module over a local ring has a finite-dimensional residue fibre. -/
theorem moduleFinite_residueFieldTensor
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M) := by
  infer_instance

/-- The residue fibre of a finite scheme-module stalk is finite-dimensional over
the residue field of the local structure ring. -/
theorem moduleFinite_schemeModuleStalk_residueTensor
    {X : Scheme.{u}} (F : X.Modules) (x : X)
    (hfinite :
      letI : Module (X.presheaf.stalk x)
          (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          F.val x
      Module.Finite (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u)) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        F.val x
    Module.Finite (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u)) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      F.val x
  letI : Module.Finite (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    hfinite
  exact moduleFinite_residueFieldTensor

/-- A finite family of sections on an open set generates the stalk whenever
every section near the point is locally a linear combination of its
restrictions.  This is the explicit local-generation step used to turn a
coherent sheaf's finite local generators into stalkwise module finiteness. -/
theorem moduleFinite_stalk_of_local_generators
    {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {x : X} {U : Opens X} (hxU : x ∈ U)
    {ι : Type u} [Fintype ι]
    (s : ι → (M.obj (op U) : Type u))
    (hgen : ∀ (V : Opens X) (hVU : V ≤ U) (_ : x ∈ V)
      (t : (M.obj (op V) : Type u)), ∃ (W : Opens X) (_ : x ∈ W)
      (hWV : W ≤ V) (c : ι → ((R ⋙ forget₂ CommRingCat RingCat).obj (op W) : Type u)),
      (ConcreteCategory.hom (M.map (homOfLE hWV).op)) t =
        ∑ i, c i • (ConcreteCategory.hom
          (M.map (homOfLE (hWV.trans hVU)).op)) (s i)) :
    Module.Finite (R.stalk x)
      (↑(TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) : Type u) := by
  let g : ι → (↑(TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) : Type u) :=
    fun i => (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf U x hxU)) (s i)
  apply Module.Finite.of_fg_top
  apply (Submodule.fg_iff_exists_finite_generating_family).2
  refine ⟨ι, inferInstance, g, ?_⟩
  apply top_unique
  intro t ht
  obtain ⟨V, hxV, tV, htV⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf t
  let V0 : Opens X := V ⊓ U
  let hxV0 : x ∈ V0 := ⟨hxV, hxU⟩
  let iV0V : V0 ⟶ V := homOfLE inf_le_left
  let tV0 : (M.obj (op V0) : Type u) :=
    (ConcreteCategory.hom (M.map iV0V.op)) tV
  obtain ⟨W, hxW, hWV0, c, hc⟩ := hgen V0 inf_le_right hxV0 tV0
  let iWV : W ⟶ V := homOfLE (hWV0.trans inf_le_left)
  let iWU : W ⟶ U := homOfLE (hWV0.trans inf_le_right)
  apply (Submodule.mem_span_range_iff_exists_fun (R.stalk x)).2
  refine ⟨fun i => (ConcreteCategory.hom (R.germ W x hxW)) (c i), ?_⟩
  have hleft :
      (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
          ((ConcreteCategory.hom (M.map (homOfLE hWV0).op)) tV0) = t := by
    have hmap :
        (ConcreteCategory.hom (M.presheaf.map (homOfLE hWV0).op))
            ((ConcreteCategory.hom (M.presheaf.map iV0V.op)) tV) =
          (ConcreteCategory.hom (M.presheaf.map iWV.op)) tV := by
      rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
      rw [show iV0V.op ≫ (homOfLE hWV0).op = iWV.op by apply Subsingleton.elim]
    change (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
      ((ConcreteCategory.hom (M.presheaf.map (homOfLE hWV0).op))
        ((ConcreteCategory.hom (M.presheaf.map iV0V.op)) tV)) = t
    rw [hmap, TopCat.Presheaf.germ_res_apply]
    exact htV
  have hc' := congrArg (fun z => (ConcreteCategory.hom
      (TopCat.Presheaf.germ M.presheaf W x hxW)) z) hc
  have hsum :
      (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
          (∑ i, c i • (ConcreteCategory.hom (M.map iWU.op)) (s i)) =
        ∑ i, (ConcreteCategory.hom (R.germ W x hxW) (c i)) •
          (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
            ((ConcreteCategory.hom (M.map iWU.op)) (s i)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact PresheafOfModules.germ_smul M x W hxW (c i)
      ((ConcreteCategory.hom (M.map iWU.op)) (s i))
  have hgens :
      ∀ i, (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
          ((ConcreteCategory.hom (M.map iWU.op)) (s i)) = g i := by
    intro i
    change (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
      ((ConcreteCategory.hom (M.presheaf.map iWU.op)) (s i)) = _
    dsimp [g, iWU]
    exact (TopCat.Presheaf.germ_res_apply M.presheaf
      (homOfLE (hWV0.trans inf_le_right)) x hxW (s i)).trans rfl
  rw [hleft] at hc'
  calc
    ∑ i, (ConcreteCategory.hom (R.germ W x hxW) (c i)) • g i =
        ∑ i, (ConcreteCategory.hom (R.germ W x hxW) (c i)) •
          (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
            ((ConcreteCategory.hom (M.map iWU.op)) (s i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hgens]
    _ = (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
          (∑ i, c i • (ConcreteCategory.hom (M.map iWU.op)) (s i)) := hsum.symm
    _ = t := hc'.symm

/-- The same local-generation argument for an arbitrary `RingCat`-valued
presheaf of rings.  This is kept separate from the commutative-structure-sheaf
version above because the two stalk rings are canonically isomorphic, but not
definitionally identical. -/
theorem moduleFinite_stalk_of_local_generators_ring
    {X : TopCat.{u}} {R : X.Presheaf RingCat.{u}}
    (M : PresheafOfModules.{u} R)
    {x : X} {U : Opens X} (hxU : x ∈ U)
    {ι : Type u} [Fintype ι]
    (s : ι → (M.obj (op U) : Type u))
    (hgen : ∀ (V : Opens X) (hVU : V ≤ U) (_ : x ∈ V)
      (t : (M.obj (op V) : Type u)), ∃ (W : Opens X) (_ : x ∈ W)
      (hWV : W ≤ V) (c : ι → (R.obj (op W) : Type u)),
      (ConcreteCategory.hom (M.map (homOfLE hWV).op)) t =
        ∑ i, c i • (ConcreteCategory.hom
          (M.map (homOfLE (hWV.trans hVU)).op)) (s i)) :
    Module.Finite (TopCat.Presheaf.stalk (C := RingCat) R x)
      (↑(TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) : Type u) := by
  let g : ι → (↑(TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) : Type u) :=
    fun i => (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf U x hxU)) (s i)
  apply Module.Finite.of_fg_top
  apply (Submodule.fg_iff_exists_finite_generating_family).2
  refine ⟨ι, inferInstance, g, ?_⟩
  apply top_unique
  intro t ht
  obtain ⟨V, hxV, tV, htV⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf t
  let V0 : Opens X := V ⊓ U
  let hxV0 : x ∈ V0 := ⟨hxV, hxU⟩
  let iV0V : V0 ⟶ V := homOfLE inf_le_left
  let tV0 : (M.obj (op V0) : Type u) :=
    (ConcreteCategory.hom (M.map iV0V.op)) tV
  obtain ⟨W, hxW, hWV0, c, hc⟩ := hgen V0 inf_le_right hxV0 tV0
  let iWV : W ⟶ V := homOfLE (hWV0.trans inf_le_left)
  let iWU : W ⟶ U := homOfLE (hWV0.trans inf_le_right)
  apply (Submodule.mem_span_range_iff_exists_fun
    (TopCat.Presheaf.stalk (C := RingCat) R x)).2
  refine ⟨fun i => (ConcreteCategory.hom (TopCat.Presheaf.germ
    R W x hxW)) (c i), ?_⟩
  have hleft :
      (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
          ((ConcreteCategory.hom (M.map (homOfLE hWV0).op)) tV0) = t := by
    have hmap :
        (ConcreteCategory.hom (M.presheaf.map (homOfLE hWV0).op))
            ((ConcreteCategory.hom (M.presheaf.map iV0V.op)) tV) =
          (ConcreteCategory.hom (M.presheaf.map iWV.op)) tV := by
      rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
      rw [show iV0V.op ≫ (homOfLE hWV0).op = iWV.op by apply Subsingleton.elim]
    change (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
      ((ConcreteCategory.hom (M.presheaf.map (homOfLE hWV0).op))
        ((ConcreteCategory.hom (M.presheaf.map iV0V.op)) tV)) = t
    rw [hmap, TopCat.Presheaf.germ_res_apply]
    exact htV
  have hc' := congrArg (fun z => (ConcreteCategory.hom
      (TopCat.Presheaf.germ M.presheaf W x hxW)) z) hc
  have hsum :
      (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
          (∑ i, c i • (ConcreteCategory.hom (M.map iWU.op)) (s i)) =
        ∑ i, (ConcreteCategory.hom (TopCat.Presheaf.germ R W x hxW) (c i)) •
          (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
            ((ConcreteCategory.hom (M.map iWU.op)) (s i)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact PresheafOfModules.germ_ringCat_smul M x W hxW (c i)
      ((ConcreteCategory.hom (M.map iWU.op)) (s i))
  have hgens :
      ∀ i, (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
          ((ConcreteCategory.hom (M.map iWU.op)) (s i)) = g i := by
    intro i
    change (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
      ((ConcreteCategory.hom (M.presheaf.map iWU.op)) (s i)) = _
    dsimp [g, iWU]
    exact (TopCat.Presheaf.germ_res_apply M.presheaf
      (homOfLE (hWV0.trans inf_le_right)) x hxW (s i)).trans rfl
  rw [hleft] at hc'
  calc
    ∑ i, (ConcreteCategory.hom (TopCat.Presheaf.germ R W x hxW) (c i)) • g i =
        ∑ i, (ConcreteCategory.hom (TopCat.Presheaf.germ R W x hxW) (c i)) •
          (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
            ((ConcreteCategory.hom (M.map iWU.op)) (s i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hgens]
    _ = (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
          (∑ i, c i • (ConcreteCategory.hom (M.map iWU.op)) (s i)) := hsum.symm
    _ = t := hc'.symm

section FiniteIndex

variable {ι : Type u} [Finite ι]

noncomputable local instance fintypeOfFinite : Fintype ι := Fintype.ofFinite ι

/- A finite (rather than fintype) index is the form supplied by
`SheafOfModules.GeneratingSections.IsFiniteType`. -/
theorem moduleFinite_stalk_of_local_generators_ring_of_finite
    {X : TopCat.{u}} {R : X.Presheaf RingCat.{u}}
    (M : PresheafOfModules.{u} R)
    {x : X} {U : Opens X} (hxU : x ∈ U)
    (s : ι → (M.obj (op U) : Type u))
    (hgen : ∀ (V : Opens X) (hVU : V ≤ U) (_ : x ∈ V)
      (t : (M.obj (op V) : Type u)), ∃ (W : Opens X) (_ : x ∈ W)
      (hWV : W ≤ V) (c : ι → (R.obj (op W) : Type u)),
      (ConcreteCategory.hom (M.map (homOfLE hWV).op)) t =
        ∑ i, c i • (ConcreteCategory.hom
          (M.map (homOfLE (hWV.trans hVU)).op)) (s i)) :
    Module.Finite (TopCat.Presheaf.stalk (C := RingCat) R x)
      (↑(TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) : Type u) := by
  exact moduleFinite_stalk_of_local_generators_ring M hxU s hgen

end FiniteIndex

end MilneLib
