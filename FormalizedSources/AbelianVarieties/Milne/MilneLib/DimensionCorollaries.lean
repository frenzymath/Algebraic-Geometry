/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import MilneLib.Dimension
import MilneLib.BasicLemmas

/-!
# Dimension corollaries

Small consequences of the dimension infrastructure used by the isogeny
specializations.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

namespace MilneLib

universe u

/-- A finite surjective scheme over a field is zero-dimensional. -/
theorem topologicalKrullDim_eq_zero_of_isFinite_surjective_to_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Surjective f] :
    topologicalKrullDim X = 0 := by
  rw [topologicalKrullDim_eq_of_isFinite_surjective f]
  exact topologicalKrullDim_spec_of_field K

namespace GroupVariety

/-- Translation by two sections preserves the cotangent-space finrank at their
section-valued points. -/
theorem finrank_cotangentSpace_eq_of_sectionTranslation
    {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsLocallyNoetherian G.left]
    (x y : 𝟙_ (Over S) ⟶ G) (s : S) :
    Module.finrank
        (IsLocalRing.ResidueField (G.left.presheaf.stalk (y.left s)))
        (IsLocalRing.CotangentSpace (G.left.presheaf.stalk (y.left s))) =
      Module.finrank
        (IsLocalRing.ResidueField (G.left.presheaf.stalk (x.left s)))
        (IsLocalRing.CotangentSpace (G.left.presheaf.stalk (x.left s))) := by
  have h := finrank_cotangentSpace_eq_of_pointTranslation G x y (x.left s)
  rw [pointTranslationIso_hom_apply G x y s] at h
  exact h

/-- Regularity of the local ring at a section-valued point is invariant under
translation between sections. -/
theorem isRegularLocalRing_stalk_iff_of_sectionTranslation
    {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsLocallyNoetherian G.left]
    (x y : 𝟙_ (Over S) ⟶ G) (s : S) :
    IsRegularLocalRing (G.left.presheaf.stalk (y.left s)) ↔
      IsRegularLocalRing (G.left.presheaf.stalk (x.left s)) := by
  have h := isRegularLocalRing_stalk_iff_of_pointTranslation G x y (x.left s)
  rw [pointTranslationIso_hom_apply G x y s] at h
  exact h

end GroupVariety

end MilneLib
