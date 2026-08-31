/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityMoving

/-!
# Trivializing a Picard class near a finite set

An invertible module over an affine open becomes free after inverting one element
avoiding any prescribed finite family of primes.  Applied to the germ primes of a
finite set of points, this gives a smaller affine open containing the whole set on
which a prescribed Cech Picard class is trivial.

This is the coordinate-free principalization input for divisor-family
representability: first put a finite residue-fibre support in an affine open, then
trivialize the divisor line bundle near every point of that fibre at once.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry
namespace Scheme

variable {X : Scheme.{u}}

/-- A Cech Picard class is trivial on an affine subneighbourhood of any finite set
contained in an affine open. -/
theorem exists_affineOpen_finset_subset_cechPicMap_ι_eq_one
    (L : X.CechPic) {F : Set X} (hF : F.Finite)
    {W : X.Opens} (hW : IsAffineOpen W) (hFW : F ⊆ (W : Set X)) :
    ∃ V : X.Opens, IsAffineOpen V ∧ F ⊆ (V : Set X) ∧ V ≤ W ∧
      CechPic.map V.ι L = 1 := by
  classical
  let q : F → Ideal Γ(X, W) := fun z =>
    Ideal.comap ((X.presheaf.germ W z.1 (hFW z.2)).hom)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk z.1))
  letI : Finite F := hF.to_subtype
  letI : ∀ z : F, (q z).IsPrime := fun z => Ideal.IsPrime.comap _
  obtain ⟨f, hf, hfree⟩ := Module.Invertible.exists_notMem_isUnit_free
    (W.cechPicClass hW L).AsModule q
  refine ⟨X.basicOpen f, hW.basicOpen f, ?_, X.basicOpen_le f, ?_⟩
  · intro x hx
    apply (Scheme.mem_basicOpen X f x (hFW hx)).2
    by_contra hnu
    exact hf ⟨x, hx⟩ (by
      change ((X.presheaf.germ W x (hFW hx)).hom f) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x)
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
  · exact Opens.cechPicMap_ι_eq_one_of_cechPicClass_eq_one (hW.basicOpen f)
      (Opens.cechPicClass_basicOpen_eq_one_of_free hW L f hfree)

end Scheme
end AlgebraicGeometry
