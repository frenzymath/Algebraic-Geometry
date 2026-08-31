/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2Sheaves

/-!
# Pushforward identities for sheaves

The direct-image constructions in Chapter II are precomposition with the map
on opens.  These wrappers expose the resulting sectionwise and stalkwise
identities in the source-facing Hartshorne namespace.
-/

set_option autoImplicit false

namespace Hartshorne

noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u v w

@[simp]
theorem presheafDirectImage_map_app {X Y : TopCat.{w}} (f : X ⟶ Y)
    {F G : Presheaf CommRingCat X} (α : F ⟶ G) {U : (Opens Y)ᵒᵖ} :
    ((presheafDirectImage f).map α).app U =
      α.app (op ((Opens.map f).obj U.unop)) := by
  exact TopCat.Presheaf.pushforward_map_app' CommRingCat f α

@[simp]
theorem directImage_map_app {X Y : TopCat.{w}} (f : X ⟶ Y)
    {F G : Sheaf CommRingCat X} (α : F ⟶ G) {U : (Opens Y)ᵒᵖ} :
    ((directImage f).map α).hom.app U =
      α.hom.app (op ((Opens.map f).obj U.unop)) := by
  rfl

@[reassoc (attr := simp)]
theorem presheafDirectImage_stalkPushforward_germ
    {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Presheaf CommRingCat X)
    (U : Opens Y) (x : X) (hx : f x ∈ U) :
    germ ((presheafDirectImage f).obj F) U (f x) hx ≫
        TopCat.Presheaf.stalkPushforward CommRingCat f F x =
      germ F ((Opens.map f).obj U) x hx := by
  exact TopCat.Presheaf.stalkPushforward_germ CommRingCat f F U x hx

end

end Hartshorne
