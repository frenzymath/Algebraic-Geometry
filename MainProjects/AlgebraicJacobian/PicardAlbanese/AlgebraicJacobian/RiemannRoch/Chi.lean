/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.ModuleKSheaf

/-!
# The cohomological ledger: `h⁰`, `h¹`, and the Euler characteristic `χ`

For a sheaf `F` of `R`-modules on a small site, this file introduces the two numeric
invariants `h⁰ F = finrank R H⁰(F)` and `h¹ F = finrank R H¹(F)` (with `Hⁱ` the `Ext`-based
cohomology carrier `CategoryTheory.Sheaf.HModule`) and the truncated Euler characteristic

    χ F = h⁰ F − h¹ F  (in ℤ).

Nothing here is scheme-specific: the definitions and their transport along sheaf
isomorphisms live at the level of an arbitrary small site with `R`-module coefficients.
The Riemann–Roch lane instantiates them at the small Zariski site of a curve, where all
higher cohomology vanishes and the truncation is the honest Euler characteristic.

## Main declarations

* `CategoryTheory.Sheaf.HModule.mapEquiv`: the `R`-linear equivalence `Hⁿ(F) ≃ₗ[R] Hⁿ(G)`
  induced by a sheaf isomorphism `F ≅ G` (functoriality `HModule.map` applied to the two
  legs of the isomorphism).
* `CategoryTheory.Sheaf.h0`, `CategoryTheory.Sheaf.h1`, `CategoryTheory.Sheaf.chi`: the
  ledger invariants.
* `CategoryTheory.Sheaf.h0_congr` / `h1_congr` / `chi_congr`: invariance under sheaf
  isomorphism.
* `CategoryTheory.Sheaf.h1_eq_zero` / `chi_eq_h0`: degenerate forms when `H¹(F)`
  vanishes (e.g. skyscrapers, affine schemes).

The dimension counts are only meaningful when the cohomology modules are finite; no
finiteness hypothesis is imposed here (`finrank` silently reads `0` on infinite-dimensional
spaces), and the finiteness bookkeeping is done downstream where it can be discharged.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Type u} [CommRing R] [HasSheafify J (ModuleCat.{u} R)]

namespace HModule

variable {F G : Sheaf J (ModuleCat.{u} R)}

/-- **Transport of cohomology along a sheaf isomorphism.** A sheaf isomorphism `e : F ≅ G`
induces an `R`-linear equivalence `Hⁿ(F) ≃ₗ[R] Hⁿ(G)` in every degree, with forward and
inverse maps the functorial `HModule.map` of the two legs of `e`. -/
noncomputable def mapEquiv (e : F ≅ G) (n : ℕ) : HModule F n ≃ₗ[R] HModule G n :=
  { HModule.map e.hom n with
    invFun := HModule.map e.inv n
    left_inv := fun x => by
      change HModule.map e.inv n (HModule.map e.hom n x) = x
      rw [← HModule.map_comp_apply, e.hom_inv_id, HModule.map_id_apply]
    right_inv := fun x => by
      change HModule.map e.hom n (HModule.map e.inv n x) = x
      rw [← HModule.map_comp_apply, e.inv_hom_id, HModule.map_id_apply] }

@[simp]
lemma mapEquiv_apply (e : F ≅ G) {n : ℕ} (x : HModule F n) :
    mapEquiv e n x = HModule.map e.hom n x :=
  rfl

@[simp]
lemma mapEquiv_symm_apply (e : F ≅ G) {n : ℕ} (y : HModule G n) :
    (mapEquiv e n).symm y = HModule.map e.inv n y :=
  rfl

end HModule

/-- `h⁰ F`: the `R`-dimension of the degree-zero cohomology of the sheaf `F` of
`R`-modules (`0` when `H⁰(F)` is not finite-dimensional). -/
noncomputable def h0 (F : Sheaf J (ModuleCat.{u} R)) : ℕ :=
  Module.finrank R (HModule F 0)

/-- `h¹ F`: the `R`-dimension of the degree-one cohomology of the sheaf `F` of
`R`-modules (`0` when `H¹(F)` is not finite-dimensional). -/
noncomputable def h1 (F : Sheaf J (ModuleCat.{u} R)) : ℕ :=
  Module.finrank R (HModule F 1)

/-- **The (truncated) Euler characteristic** `χ F = h⁰ F − h¹ F`, in `ℤ`. On a curve all
higher cohomology vanishes and this is the honest Euler characteristic; in general it is
the degree-`≤ 1` truncation. -/
noncomputable def chi (F : Sheaf J (ModuleCat.{u} R)) : ℤ :=
  (h0 F : ℤ) - (h1 F : ℤ)

variable {F G : Sheaf J (ModuleCat.{u} R)}

/-- `h⁰` is invariant under sheaf isomorphism. -/
theorem h0_congr (e : F ≅ G) : h0 F = h0 G :=
  (HModule.mapEquiv e 0).finrank_eq

/-- `h¹` is invariant under sheaf isomorphism. -/
theorem h1_congr (e : F ≅ G) : h1 F = h1 G :=
  (HModule.mapEquiv e 1).finrank_eq

/-- `χ` is invariant under sheaf isomorphism. -/
theorem chi_congr (e : F ≅ G) : chi F = chi G := by
  rw [chi, chi, h0_congr e, h1_congr e]

/-- `h¹ F = 0` when the degree-one cohomology vanishes. -/
theorem h1_eq_zero [Nontrivial R] (h : Subsingleton (HModule F 1)) : h1 F = 0 :=
  haveI := h
  Module.finrank_zero_of_subsingleton

/-- `χ F = h⁰ F` when the degree-one cohomology vanishes. -/
theorem chi_eq_h0 [Nontrivial R] (h : Subsingleton (HModule F 1)) : chi F = h0 F := by
  rw [chi, h1_eq_zero h, Nat.cast_zero, sub_zero]

end CategoryTheory.Sheaf
