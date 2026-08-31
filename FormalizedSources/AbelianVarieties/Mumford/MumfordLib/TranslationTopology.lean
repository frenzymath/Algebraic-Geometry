/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.Uniformization
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Topological translations

Mumford's translation lemma says that translation by any point of an abelian
variety is an automorphism.  This file records the corresponding elementary
topological additive-group API.  It is useful for the torus models in the
uniformization layer, while making no claim about existence of a
uniformization witness.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

/- A left translation is the canonical homeomorphism supplied by the
   topological-group structure. -/
def addTranslationHomeomorph
    {G : Type*} [AddGroup G] [TopologicalSpace G] [SeparatelyContinuousAdd G]
    (a : G) : G ≃ₜ G :=
  Homeomorph.addLeft a

@[simp]
theorem addTranslationHomeomorph_apply
    {G : Type*} [AddGroup G] [TopologicalSpace G] [SeparatelyContinuousAdd G]
    (a x : G) : addTranslationHomeomorph a x = a + x :=
  rfl

@[simp]
theorem addTranslationHomeomorph_symm
    {G : Type*} [AddGroup G] [TopologicalSpace G] [SeparatelyContinuousAdd G]
    (a : G) : (addTranslationHomeomorph a).symm = addTranslationHomeomorph (-a) := by
  exact Homeomorph.addLeft_symm a

@[simp]
theorem addTranslationHomeomorph_trans
    {G : Type*} [AddGroup G] [TopologicalSpace G] [SeparatelyContinuousAdd G]
    (a b : G) :
    (addTranslationHomeomorph a).trans (addTranslationHomeomorph b) =
      addTranslationHomeomorph (b + a) := by
  apply Homeomorph.ext
  intro x
  simp only [Homeomorph.trans_apply, addTranslationHomeomorph_apply]
  rw [add_assoc]

theorem addTranslationHomeomorph_isCompact_image_iff
    {G : Type*} [AddGroup G] [TopologicalSpace G] [SeparatelyContinuousAdd G]
    (a : G) (s : Set G) :
    IsCompact ((fun x : G => a + x) '' s) ↔ IsCompact s := by
  simpa only [addTranslationHomeomorph_apply] using
    (addTranslationHomeomorph a).isCompact_image (s := s)

/-- Left translation is smooth at every differentiability order on a Lie
    additive group. -/
theorem addTranslation_contMDiff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    {G : Type*} [AddGroup G] [TopologicalSpace G] [ChartedSpace H G]
    [LieAddGroup I n G] (a : G) :
    ContMDiff I I n (fun x : G => a + x) := by
  change ContMDiff I I n ((fun _ : G => a) + id)
  exact contMDiff_const.add contMDiff_id

/-- The smooth translation equivalence, including its smooth inverse. -/
noncomputable def addTranslationDiffeomorph
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    {G : Type*} [AddGroup G] [TopologicalSpace G] [ChartedSpace H G]
    [LieAddGroup I n G] (a : G) : Diffeomorph I I G G n := by
  letI : IsTopologicalAddGroup G := topologicalAddGroup_of_lieAddGroup I n
  exact
    { toEquiv := (addTranslationHomeomorph a).toEquiv
      contMDiff_toFun := addTranslation_contMDiff I n a
      contMDiff_invFun := by
        change ContMDiff I I n (fun x : G => -a + x)
        exact addTranslation_contMDiff I n (-a) }

end Uniformization
end Mumford
