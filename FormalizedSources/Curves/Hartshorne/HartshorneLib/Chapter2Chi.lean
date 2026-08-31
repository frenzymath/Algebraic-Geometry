/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2Cohomology

/-!
# The truncated Euler-characteristic ledger

This file introduces the dimensions `h0`, `h1`, and the integer-valued
truncation `chi = h0 - h1` for sheaves of modules.  The definitions are
deliberately independent of schemes; later curve files supply finiteness and
short-exact-sequence inputs.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Type u} [CommRing R] [HasSheafify J (ModuleCat.{u} R)]

namespace HModule

variable {F G : Sheaf J (ModuleCat.{u} R)}

/-- Transport cohomology along a sheaf isomorphism. -/
noncomputable def mapEquiv (e : F ≅ G) (n : ℕ) :
    HModule J R F n ≃ₗ[R] HModule J R G n :=
  { HModule.map e.hom n with
    invFun := HModule.map e.inv n
    left_inv := fun x => by
      change HModule.map e.inv n (HModule.map e.hom n x) = x
      rw [← HModule.map_comp_apply, e.hom_inv_id, HModule.map_id_apply]
    right_inv := fun x => by
      change HModule.map e.hom n (HModule.map e.inv n x) = x
      rw [← HModule.map_comp_apply, e.inv_hom_id, HModule.map_id_apply] }

@[simp] lemma mapEquiv_apply (e : F ≅ G) {n : ℕ} (x : HModule J R F n) :
    mapEquiv e n x = HModule.map e.hom n x := rfl

@[simp] lemma mapEquiv_symm_apply (e : F ≅ G) {n : ℕ} (y : HModule J R G n) :
    (mapEquiv e n).symm y = HModule.map e.inv n y := rfl

end HModule

/-- The dimension of degree-zero cohomology. -/
noncomputable def h0 (F : Sheaf J (ModuleCat.{u} R)) : ℕ :=
  Module.finrank R (HModule J R F 0)

/-- The dimension of degree-one cohomology. -/
noncomputable def h1 (F : Sheaf J (ModuleCat.{u} R)) : ℕ :=
  Module.finrank R (HModule J R F 1)

/-- The truncated Euler characteristic `h0 - h1`, valued in the integers. -/
noncomputable def chi (F : Sheaf J (ModuleCat.{u} R)) : ℤ :=
  (h0 F : ℤ) - (h1 F : ℤ)

variable {F G : Sheaf J (ModuleCat.{u} R)}

theorem h0_congr (e : F ≅ G) : h0 F = h0 G :=
  (HModule.mapEquiv e 0).finrank_eq

theorem h1_congr (e : F ≅ G) : h1 F = h1 G :=
  (HModule.mapEquiv e 1).finrank_eq

theorem chi_congr (e : F ≅ G) : chi F = chi G := by
  rw [chi, chi, h0_congr e, h1_congr e]

theorem h1_eq_zero [Nontrivial R] (h : Subsingleton (HModule J R F 1)) : h1 F = 0 := by
  letI := h
  exact Module.finrank_zero_of_subsingleton

theorem chi_eq_h0 [Nontrivial R] (h : Subsingleton (HModule J R F 1)) : chi F = h0 F := by
  rw [chi, h1_eq_zero h, Nat.cast_zero, sub_zero]

end Sheaf
end CategoryTheory
