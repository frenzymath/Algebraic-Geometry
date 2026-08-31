/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2Chi

/-!
# Skyscraper sheaves on the curve

This file seals Mathlib's skyscraper sheaf behind the API used by the divisor
dévissage.  It records its sectionwise behavior and computes degree-zero
cohomology.  The independent `H¹`-vanishing argument is intentionally left to
the later affine/flasque frontier.
-/

set_option autoImplicit false
set_option linter.style.openClassical false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

noncomputable section
open scoped Classical

variable {k : Type u} [CommRing k]
variable {X : Over (Spec (CommRingCat.of k))}

def skyModule (x : X.left) (M : ModuleCat.{u} k) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology (X.left : TopCat))
      (ModuleCat.{u} k) :=
  skyscraperSheaf x M

lemma skyModule_obj (x : X.left) (M : ModuleCat.{u} k) (U : X.left.Opens) :
    (skyModule (X := X) x M).obj.obj (op U) =
      if x ∈ U then M else terminal (ModuleCat.{u} k) := rfl

@[simp] lemma skyModule_obj_of_mem (x : X.left) (M : ModuleCat.{u} k)
    {U : X.left.Opens} (h : x ∈ U) :
    (skyModule (X := X) x M).obj.obj (op U) = M := by
  rw [skyModule_obj, if_pos h]

@[simp] lemma skyModule_obj_of_not_mem (x : X.left) (M : ModuleCat.{u} k)
    {U : X.left.Opens} (h : x ∉ U) :
    (skyModule (X := X) x M).obj.obj (op U) = terminal (ModuleCat.{u} k) := by
  rw [skyModule_obj, if_neg h]

noncomputable def skyModuleGammaEquiv (x : X.left) (M : ModuleCat.{u} k) :
    CategoryTheory.Sheaf.HModule
      (Opens.grothendieckTopology (X.left : TopCat)) k
      (skyModule (X := X) x M) 0 ≃ₗ[k] M :=
  (CategoryTheory.Sheaf.HModule.linearEquiv₀
      (isTerminalTop : IsTerminal (⊤ : X.left.Opens))
      (skyModule (X := X) x M)).trans
    (eqToIso (skyModule_obj_of_mem (X := X) x M (Opens.mem_top x))).toLinearEquiv

theorem h0_skyModule (x : X.left) (M : ModuleCat.{u} k) :
    CategoryTheory.Sheaf.h0 (skyModule (X := X) x M) = Module.finrank k M :=
  (skyModuleGammaEquiv (X := X) x M).finrank_eq

end
end Hartshorne
