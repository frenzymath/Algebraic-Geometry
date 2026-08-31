/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.CodimOneExtension
import AlgebraicJacobian.Albanese.Milne33

/-!
# Rational maps to an abelian variety extend

Over an algebraically closed field `k̄`, a rational map from a nonsingular
variety to an abelian variety extends, uniquely, to a regular morphism
(Milne, *Abelian Varieties*, §I.3, Theorem 3.2). The argument combines two
results of `Albanese/CodimOneExtension.lean`: the indeterminacy locus of a
rational map from a nonsingular variety to a complete variety has codimension
`≥ 2` (Theorem 3.1), while the indeterminacy locus of a rational map into a
group variety is empty or of pure codimension `1` (Lemma 3.3). The two
conditions are incompatible unless the locus is empty, so `f` is everywhere
defined; uniqueness is the agreement principle for morphisms out of a reduced
scheme into a separated scheme.

The extension theorem is what the Albanese universal property
(`Albanese/AlbaneseUP.lean`) uses to promote the symmetric-product rational
map `C^{(g)} ⇢ A` to a regular morphism `J → A`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.extend_to_av` — for `X` a nonsingular
  variety over `k̄` and `A` an abelian variety over `k̄`, every rational map
  `f : X ⇢ A` equals `g.toRationalMap` for a unique morphism `g : X ⟶ A`.

The pure-codimension-one input, Milne Lemma 3.3
(`indeterminacy_pure_codim_one_into_grpScheme` in `Albanese/Milne33.lean`), is
**proved** as of run 0069, so `extend_to_av` is unconditional and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only).

## Conventions

An **abelian variety over `k̄`** is an object `A : Over (Spec (.of k̄))`
carrying:

- `[GrpObj A]` (group-object structure on the over-category),
- `[IsProper A.hom]` (complete),
- `[Smooth A.hom]` (nonsingular),
- `[GeometricallyIrreducible A.hom]`.

A **nonsingular variety over `k̄`** is an object `X : Over (Spec (.of k̄))`
carrying:

- `[Smooth X.hom]`,
- `[GeometricallyIrreducible X.hom]`,
- `[IsSeparated X.hom]`,
- `[LocallyOfFiniteType X.hom]`,
- `[IsIntegral X.left]`,
- `[IsReduced X.left]`.

## References

* Milne, *Abelian Varieties*, §I.3, Theorem 3.2, p. 17.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

/-! ## Rational maps to an abelian variety extend

Let `k̄` be an algebraically closed field, `X` a nonsingular variety over `k̄`
(smooth, geometrically irreducible, separated, locally of finite type,
integral, reduced) and `A` an abelian variety over `k̄` (a group object that is
proper, smooth and geometrically irreducible). For every rational map
`f : X ⇢ A` there is a unique regular morphism `g : X ⟶ A` whose induced
rational map is `f`.

Milne's argument: let `U ⊆ X` be a maximal open of definition of `f` and
`Z := X ∖ U`. The codimension-`≥ 2` indeterminacy theorem for rational maps
into a complete variety gives `codim Z ≥ 2`; the pure-codimension-`1`
indeterminacy lemma for maps into a group variety says `Z` is empty or of pure
codimension `1`. Both together force `Z = ∅`, so `U = X` and `f` has a regular
representative on all of `X`. Uniqueness is the agreement principle
`AlgebraicGeometry.ext_of_isDominant`: two morphisms `X ⟶ A` out of a reduced
scheme into a separated scheme that agree on a dense open agree everywhere. -/

/-- **A scheme smooth over an algebraically closed field is reduced**
(Stacks `056S`/`033B` over `k̄`). Used to derive `IsReduced A.left` in
`av_isIntegral_of_smooth_geomIrred` below.

The proof is `isReduced_of_smooth_of_isAlgClosed` in
`Albanese/CodimOneExtension.lean`: the stalks are localisations of
standard-smooth `k̄`-algebras, whose localisations at maximal ideals are
regular local hence domains, and reducedness is checked at those maximal
localisations and then transported to the stalks. Algebraic closure of `k̄` is
genuinely used. -/
private theorem isReduced_of_smooth_over_field
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (A : Over (Spec (.of kbar)))
    [Smooth A.hom] :
    IsReduced A.left :=
  isReduced_of_smooth_of_isAlgClosed A

/-- **An abelian variety has integral underlying scheme.** For an abelian
variety `A` over an algebraically closed field `k̄` — an object
`A : Over (Spec (.of k̄))` carrying
`[GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]` —
the scheme `A.left` is integral.

Three steps:

1. `Spec k̄` is a one-point scheme.
2. Geometric irreducibility of `A.hom` over a one-point base gives
   `IrreducibleSpace A.left`
   (`GeometricallyIrreducible.irreducibleSpace_of_subsingleton`).
3. Smoothness over the algebraically closed field gives `IsReduced A.left`
   (`isReduced_of_smooth_over_field`), and irreducible plus reduced is
   integral (`isIntegral_of_irreducibleSpace_of_isReduced`). -/
private theorem av_isIntegral_of_smooth_geomIrred
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (A : Over (Spec (.of kbar)))
    [GrpObj A] [IsProper A.hom] [Smooth A.hom]
    [GeometricallyIrreducible A.hom] :
    IsIntegral A.left := by
  -- Step 1: `Spec k̄` has a unique point (Mathlib instance
  -- `Scheme.instUniqueCarrierCarrierCommRingCatSpecOf`); both
  -- `Subsingleton` and `Nonempty` follow.
  haveI : Subsingleton (Spec (.of kbar) : Scheme.{u}) := inferInstance
  haveI : Nonempty (Spec (.of kbar) : Scheme.{u}) := inferInstance
  -- Step 2: geometric irreducibility over a singleton base gives `IrreducibleSpace`.
  haveI : IrreducibleSpace A.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.hom
  -- Step 3: smoothness over the algebraically closed base field forces
  -- reducedness of the source (`isReduced_of_smooth_over_field`).
  haveI : IsReduced A.left := isReduced_of_smooth_over_field A
  exact isIntegral_of_irreducibleSpace_of_isReduced A.left

/-- **The indeterminacy locus of a rational map to an abelian variety is
empty.** For a rational map `f : X ⇢ A` of `k̄`-varieties from a nonsingular
variety `X` to an abelian variety `A` over an algebraically closed field `k̄`,
`indeterminacyLocus f = ∅`.

Two inputs combine (Milne, proof of Theorem 3.2):

1. `indeterminacy_pure_codim_one_into_grpScheme` (Milne Lemma 3.3): for a
   rational map from a smooth integral variety into a *group* variety, the
   indeterminacy locus is empty or of pure codimension `1` — every point of
   `Z(f)` specialises from a coheight-`1` point *of `Z(f)`*.
2. `indeterminacy_codimGe2_of_smooth_of_complete` (Milne Theorem 3.1): for a
   rational map from a nonsingular variety into a complete variety, every
   point of the indeterminacy locus has coheight `≥ 2`.

If `Z(f)` were non-empty, the second disjunct of (1) would produce a point
`z ∈ Z(f)` with `coheight z = 1`, contradicting (2). Hence `Z(f) = ∅`.

Both inputs need `f` to be a rational map *over `k̄`* (the hypothesis `hover`,
Milne's ambient assumption). Note that Milne 3.1 alone is not enough: for a
general complete target, codimension-`≥ 2` indeterminacy does not imply an
extension (see `existsUnique_hom_of_indeterminacyLocus_eq_empty`); the
group-variety input (1) is what forces `Z(f) = ∅`.

Both inputs are proved (input (1) in `Albanese/Milne33.lean` as of run 0069),
so this lemma is unconditional. -/
private theorem av_indeterminacyLocus_eq_empty
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom]
    [GeometricallyIrreducible A.hom]
    (f : X.left.RationalMap A.left)
    (hover : f.compHom A.hom = X.hom.toRationalMap) :
    indeterminacyLocus f = ∅ := by
  -- Materialise the variety-package instances on `A.left` needed by Milne
  -- Lemma 3.3 and Theorem 3.1: `IsIntegral` from
  -- `av_isIntegral_of_smooth_geomIrred`; `IsReduced` from
  -- `isReduced_of_isIntegral`; `IsSeparated` from `IsProper`;
  -- `LocallyOfFiniteType` from `Smooth`.
  haveI : IsIntegral A.left := av_isIntegral_of_smooth_geomIrred A
  haveI : IsReduced A.left := inferInstance
  haveI : IsSeparated A.hom := inferInstance
  haveI : LocallyOfFiniteType A.hom := inferInstance
  -- Milne Lemma 3.3: the locus is empty, or every point of it specialises
  -- from a coheight-1 point of the locus.
  rcases indeterminacy_pure_codim_one_into_grpScheme f hover with hempty | hpure
  · exact hempty
  · -- Milne 3.1 (codim-≥2) contradicts any coheight-1 point of the locus.
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨z, hzZ, hz1, -⟩ := hpure x hx
    have h2 := indeterminacy_codimGe2_of_smooth_of_complete f hover z hzZ
    rw [hz1] at h2
    norm_num at h2

/-- **Milne Theorem 3.2 — a rational map from a nonsingular variety to an
abelian variety extends, uniquely, to a regular morphism.**

For `X` a nonsingular variety over an algebraically closed field `k̄` and `A`
an abelian variety over `k̄`, every rational map `f : X ⇢ A` has a unique
regular extension `g : X ⟶ A`, i.e. `g.toRationalMap = f`.

This is the input the Albanese universal property
(`Albanese/AlbaneseUP.lean`) consumes when promoting the symmetric-product
rational map `C^{(g)} ⇢ A` to a regular morphism `J → A`.

The proof is Milne's two-line argument, routed through the intermediate
statement `Z(f) = ∅`:

1. `av_indeterminacyLocus_eq_empty` combines Milne Lemma 3.3
   (`indeterminacy_pure_codim_one_into_grpScheme`) with the codimension-`≥ 2`
   conclusion of Milne 3.1 (`indeterminacy_codimGe2_of_smooth_of_complete`) to
   force `indeterminacyLocus f = ∅`.
2. `existsUnique_hom_of_indeterminacyLocus_eq_empty`: a rational map from a
   reduced scheme to a separated scheme with empty indeterminacy locus is
   uniquely represented by a regular morphism. The scheme-level separatedness
   `A.left.IsSeparated` comes from `IsSeparated A.hom` (itself from
   `IsProper A.hom`) composed with the affine `Spec k̄ ⟶ ⊤_ Scheme`.

Step 1's Milne Lemma 3.3 input is proved in `Albanese/Milne33.lean` (run
0069), so nothing behind this theorem is missing: it is `sorry`-free and
axiom-clean. -/
theorem extend_to_av
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom]
    [GeometricallyIrreducible A.hom]
    (f : X.left.RationalMap A.left)
    (hover : f.compHom A.hom = X.hom.toRationalMap) :
    ∃! (g : X.left ⟶ A.left), g.toRationalMap = f := by
  -- Scheme-level separatedness of the target (`A.hom` is separated since
  -- proper, and `Spec k̄` is affine hence separated over the terminal).
  haveI : IsSeparated A.hom := inferInstance
  haveI : A.left.IsSeparated := by
    rw [Scheme.isSeparated_iff]
    have heq : terminal.from A.left = A.hom ≫ terminal.from _ :=
      Subsingleton.elim _ _
    rw [heq]; infer_instance
  -- Milne's argument: the indeterminacy locus is empty, then extend.
  exact existsUnique_hom_of_indeterminacyLocus_eq_empty f
    (av_indeterminacyLocus_eq_empty f hover)

end RationalMap

end Scheme

end AlgebraicGeometry
