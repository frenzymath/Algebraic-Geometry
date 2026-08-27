/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.Thm32RationalMapExtension

/-!
# Descent of a morphism from a dense open into an abelian variety

Milne's proof of the Albanese universal property (*Abelian Varieties* III.6
Proposition 6.1) reaches the point "it therefore defines a rational map
`ψ : J ⇢ A`, which (I 3.2) shows to be a regular map". This file supplies that
sentence in the form the Albanese descent actually needs.

## The statement

`extend_to_av` (Milne Theorem 3.2, `Albanese/Thm32RationalMapExtension.lean`)
extends a `Scheme.RationalMap` into an abelian variety to a unique morphism.
But a `RationalMap` is a *quotient* of partial maps, so applying it and then
identifying the result requires unfolding that quotient at every call site.

`exists_unique_hom_restrict_eq_of_dense_open` states the same content in
elementary terms:

> given a **dense open** `V ⊆ X` and *any* morphism `h : V ⟶ A` into an abelian
> variety which is compatible with the structure maps over `k̄`, there is a
> **unique** morphism `g : X ⟶ A` with `V.ι ≫ g = h`.

No rational maps appear in the statement. That is the form a descent step wants:
one produces a morphism on the locus where things are defined, and reads back a
morphism on all of `X` together with the equation identifying it there.

## Why this is the right shape for the Albanese descent

Milne's `ψ` is built by inverting the birational `f^{(g)} : Sym^g C ⟶ Pic⁰` on
the dense open where it is an isomorphism, and composing with `Sym^g φ`.
Mathlib at this pin has **no** API for inverting a birational morphism (see
`Mathlib/AlgebraicGeometry/Birational/{RationalMap,Dominant}.lean`: there is
`IsDominant` machinery but no inverse-on-a-dense-open construction). So the
`Pic⁰ ⇢ A` rational map cannot yet be produced.

What this file establishes is that *producing it is the only remaining gap*: the
moment one has a dense open `V ⊆ Pic⁰` and a morphism `V ⟶ A` (e.g. a
section of `f^{(g)}` over `V` followed by `Sym^g φ`), the unique global `ψ` and
its defining equation follow with no further geometric input. The extension half
of `descentThroughBirationalSigma` is therefore closed; the birationality half
is what remains.

## Main results

* `Scheme.RationalMap.hom_toRationalMap_eq_partialMap_iff` — for a morphism
  `g : X ⟶ A` into an abelian variety and a dense open `V`, the rational-map
  identity `g.toRationalMap = (PartialMap.mk V hV h).toRationalMap` is equivalent
  to the elementary equation `V.ι ≫ g = h`. The bridge that removes the quotient.
* `Scheme.RationalMap.exists_unique_hom_restrict_eq_of_dense_open` — the descent
  statement above.

## References

Milne, *Abelian Varieties*, §I.3 Theorem 3.2 and §III.6 Proposition 6.1, p. 104;
blueprint `lem:descent_through_birational_sigma` in
`blueprint/src/chapters/Albanese_AlbaneseUP.tex`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.RationalMap

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]

/-- **Scheme-level separatedness of an abelian variety.** `A.hom` is separated
(being proper), and `Spec k̄` is affine hence separated over the terminal scheme,
so the composite makes `A.left` separated. Extracted because both results below
need it as an instance. -/
theorem isSeparated_left_of_isProper {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [IsProper A.hom] :
    A.left.IsSeparated := by
  haveI : IsSeparated A.hom := inferInstance
  rw [Scheme.isSeparated_iff]
  have heq : terminal.from A.left = A.hom ≫ terminal.from _ := Subsingleton.elim _ _
  rw [heq]; infer_instance

/-- **Removing the rational-map quotient.** For a morphism `g : X ⟶ A` into an
abelian variety and a dense open `V ⊆ X` carrying `h : V ⟶ A`, the identity of
rational maps `g.toRationalMap = ⟦(V, h)⟧` is *equivalent* to the elementary
equation `V.ι ≫ g = h`.

Both directions are the reduced-and-separated agreement principle
(`PartialMap.equiv_iff_of_isSeparated_of_le` with the common dense open `V`):
two partial maps from a reduced scheme to a separated one are equivalent exactly
when their restrictions to a common dense open agree, and here one of them is
already defined on all of `X`. -/
theorem hom_toRationalMap_eq_partialMap_iff {k : Type u} [Field k]
    {X : Over (Spec (.of k))} [IsReduced X.left]
    {A : Over (Spec (.of k))} [IsProper A.hom]
    (V : X.left.Opens) (hV : Dense (V : Set X.left)) (h : (V : Scheme) ⟶ A.left)
    (g : X.left ⟶ A.left) :
    g.toRationalMap = (PartialMap.mk V hV h).toRationalMap ↔ V.ι ≫ g = h := by
  haveI : A.left.IsSeparated := isSeparated_left_of_isProper A
  rw [Scheme.Hom.toRationalMap, PartialMap.toRationalMap_eq_iff,
    PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme) hV le_top le_rfl]
  simp [Scheme.Hom.toPartialMap, PartialMap.restrict]

/-- **Descent from a dense open into an abelian variety.**

Let `X` be a nonsingular variety over an algebraically closed field `k̄`, let `A`
be an abelian variety over `k̄`, let `V ⊆ X` be a **dense open**, and let
`h : V ⟶ A` be *any* morphism whose associated partial map is compatible with the
structure morphisms over `k̄`. Then there is a **unique** morphism `g : X ⟶ A`
restricting to `h` on `V`:

`∃! g : X ⟶ A, V.ι ≫ g = h`.

Existence is Milne Theorem 3.2 (`extend_to_av`), whose indeterminacy-locus input
— Milne Lemma 3.3 — is proved in `Albanese/Milne33.lean`, so this is
unconditional. Uniqueness is the agreement principle: two morphisms to a
separated scheme agreeing on a dense open of a reduced scheme are equal.

This is the extension half of `lem:descent_through_birational_sigma`. Note what
it does *not* require: no birationality, no properness of `V`, and nothing about
where `h` came from. Consequently the remaining gap in the Albanese descent is
purely the construction of the dense open and the morphism on it (i.e. inverting
`f^{(g)}` where it is an isomorphism), not the extension. -/
theorem exists_unique_hom_restrict_eq_of_dense_open
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [IsIntegral X.left] [IsReduced X.left]
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (V : X.left.Opens) (hV : Dense (V : Set X.left)) (h : (V : Scheme) ⟶ A.left)
    (hover : (PartialMap.mk V hV h).toRationalMap.compHom A.hom
      = X.hom.toRationalMap) :
    ∃! g : X.left ⟶ A.left, V.ι ≫ g = h := by
  obtain ⟨g, hg, huniq⟩ := extend_to_av (PartialMap.mk V hV h).toRationalMap hover
  exact ⟨g, (hom_toRationalMap_eq_partialMap_iff V hV h g).mp hg,
    fun g' hg' => huniq g' ((hom_toRationalMap_eq_partialMap_iff V hV h g').mpr hg')⟩

end Scheme.RationalMap

end AlgebraicGeometry
