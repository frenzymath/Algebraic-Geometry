/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.AbelianVariety.Rigidity
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Corollaries of the rigidity lemma

This file proves the engine application of the rigidity lemma (Milne, *Abelian Varieties*,
I Cor 1.2; Mumford, *Abelian Varieties*, §II.4 p. 44, Corollary 1): a **pointed** morphism of
group schemes whose source is proper and geometrically integral over an algebraically closed
field is a **homomorphism** of group objects.

## Main result

* `AlgebraicGeometry.isMonHom_of_isProper_of_geometricallyIntegral`: let `K` be an
  algebraically closed field, `A` a monoid object of `Over (Spec K)` that is proper and
  geometrically integral, and `B` a group object that is separated and locally of finite type.
  Any morphism `g : A ⟶ B` with `η[A] ≫ g = η[B]` satisfies `IsMonHom g`, i.e. commutes with
  the multiplications.

  Since a monoid homomorphism of group objects automatically commutes with inversion
  (`CategoryTheory.inv_hom` in mathlib), for `A` a group object this is the full statement
  "a pointed morphism of group schemes is a homomorphism of group schemes".

## Proof sketch

Following Milne (I Cor 1.2), consider the "defect" morphism

`φ := (μ[A] ≫ g) / ((fst A A ≫ g) * (snd A A ≫ g)) : A ⊗ A ⟶ B`,

written in the group `Hom(A ⊗ A, B)` (mathlib's `MonObj.Hom.group`); pointwise it is
`φ(x, y) = g(x·y) · (g(x)·g(y))⁻¹`. Both slice restrictions `φ(·, e)` and `φ(e, ·)`
collapse to the unit point of `B` (using `g(e) = e`), so the rigidity lemma
(`exists_unique_eq_snd_comp_of_isProper_of_geometricallyIntegral`, with `X = Y = A`,
`y₀ = η[A]`, `z₀ = η[B]`) factors `φ` as `snd A A ≫ ψ`; restricting along the *other*
slice `{e} × A` identifies `ψ = 1`, so `φ = 1`, which is exactly `IsMonHom.mul_hom`.

Compared to Milne's statement the hypothesis set is honest and slightly weaker: `A` only
needs a monoid structure (no inverses, no smoothness), and `B` can be any separated, locally
of finite type group scheme over `K` (no properness, connectedness or commutativity).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **A pointed morphism of group schemes is a homomorphism** (Milne, *Abelian Varieties*,
I Cor 1.2; Mumford, *Abelian Varieties*, §II.4 p. 44, Corollary 1). Let `K` be an
algebraically closed field, `A` a monoid object of `Over (Spec K)` whose underlying scheme is
proper and geometrically integral over `K`, and `B` a group object whose underlying scheme is
separated and locally of finite type over `K`. If `g : A ⟶ B` is pointed (`η[A] ≫ g = η[B]`),
then `g` is a homomorphism of monoid objects.

For `A` a group object this makes `g` a homomorphism of group objects: a monoid homomorphism
automatically commutes with inversion (`CategoryTheory.inv_hom`). 






 * Provenance: ADAPTED.
 * TO CHECK: the cited Mumford and Milne statements assume abelian-variety
   source and target, while this result weakens them to a proper geometrically
   integral monoid source and a separated locally finite-type group target;
   verify the hypothesis weakening.
-/
theorem isMonHom_of_isProper_of_geometricallyIntegral
    {A B : Over (Spec (CommRingCat.of K))} [MonObj A] [GrpObj B]
    [IsProper A.hom] [GeometricallyIntegral A.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (g : A ⟶ B) (hg : η[A] ≫ g = η[B]) : IsMonHom g := by
  -- the defect morphism `φ(x, y) = g(x·y) · (g(x)·g(y))⁻¹` in the group `Hom(A ⊗ A, B)`
  set φ : A ⊗ A ⟶ B := (μ[A] ≫ g) / ((fst A A ≫ g) * (snd A A ≫ g)) with hφdef
  -- `φ` contracts the slice `A × {e}` to the unit point of `B`
  have e1 : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ μ[A] ≫ g = g := by
    rw [← Category.assoc, MonObj.lift_comp_one_right, Category.id_comp]
  have e2 : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ fst A A ≫ g = g := by
    rw [lift_fst_assoc, Category.id_comp]
  have e3 : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ snd A A ≫ g = 1 := by
    rw [lift_snd_assoc, Category.assoc, hg, ← Hom.one_def]
  have hslice : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ φ = toUnit A ≫ η[B] := by
    rw [hφdef, GrpObj.comp_div, MonObj.comp_mul, e1, e2, e3, _root_.mul_one, div_self',
      Hom.one_def]
  -- rigidity: `φ` factors through the second projection
  obtain ⟨ψ, hψ, -⟩ := exists_unique_eq_snd_comp_of_isProper_of_geometricallyIntegral
    φ η[A] η[B] hslice
  -- restricting along the slice `{e} × A` identifies the factor with the unit
  have hψ1 : ψ = (1 : A ⟶ B) := by
    have h1 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ φ = ψ := by
      rw [hψ, lift_snd_assoc, Category.id_comp]
    have f1 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ μ[A] ≫ g = g := by
      rw [← Category.assoc, MonObj.lift_comp_one_left, Category.id_comp]
    have f2 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ fst A A ≫ g = 1 := by
      rw [lift_fst_assoc, Category.assoc, hg, ← Hom.one_def]
    have f3 : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ snd A A ≫ g = g := by
      rw [lift_snd_assoc, Category.id_comp]
    rw [← h1, hφdef, GrpObj.comp_div, MonObj.comp_mul, f1, f2, f3, _root_.one_mul, div_self']
  -- hence the defect vanishes identically
  have hφ1 : φ = (1 : A ⊗ A ⟶ B) := by rw [hψ, hψ1, MonObj.comp_one]
  rw [hφdef, div_eq_one] at hφ1
  -- and `μ[A] ≫ g = (g ⊗ₘ g) ≫ μ[B]`
  have h2 : (g ⊗ₘ g) ≫ μ[B] = (fst A A ≫ g) * (snd A A ≫ g) := by
    rw [MonObj.mul_eq_mul B, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
  exact { one_hom := hg, mul_hom := by rw [hφ1, h2] }

end AlgebraicGeometry
