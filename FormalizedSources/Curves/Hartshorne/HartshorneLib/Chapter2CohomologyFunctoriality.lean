/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2Chi

/-!
# Functoriality of cohomology transport

The cohomology carrier `HModule` is functorial in its sheaf argument.  This
file packages the identity and composition laws for the linear equivalences
induced by sheaf isomorphisms, so that chains of coefficient-sheaf
identifications can be composed without unfolding `Ext`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Type u} [CommRing R] [HasSheafify J (ModuleCat.{u} R)]
  {F G H : Sheaf J (ModuleCat.{u} R)}

namespace HModule

@[simp]
theorem mapEquiv_refl (n : ℕ) :
    mapEquiv (Iso.refl F) n = LinearEquiv.refl R _ := by
  ext x
  exact map_id_apply x

theorem mapEquiv_trans (e : F ≅ G) (e' : G ≅ H) (n : ℕ) :
    mapEquiv (e ≪≫ e') n = (mapEquiv e n).trans (mapEquiv e' n) := by
  ext x
  exact map_comp_apply e.hom e'.hom x

end HModule

end CategoryTheory.Sheaf
