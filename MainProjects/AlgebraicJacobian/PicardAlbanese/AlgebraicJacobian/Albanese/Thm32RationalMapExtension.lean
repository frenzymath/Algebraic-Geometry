/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.CodimOneSmoothReduced
import AlgebraicJacobian.Albanese.CodimOneMilne31
import AlgebraicJacobian.Albanese.CodimOneExtensionUnique

/-!
# Milne Theorem 3.2: a rational map from a nonsingular variety to an abelian
variety extends

Ported from `Albanese/Thm32RationalMapExtension.lean` of the previous
Algebraic-Jacobian tree (identical toolchain and mathlib pin),
re-kernel-verified here — with **one deliberate signature change**: the
Milne-Lemma-3.3 input, which was a sorried theorem in the source tree, is
threaded as the explicit hypothesis `Milne33Indeterminacy f`
(`Albanese/CodimOneIndeterminacy.lean`), keeping this tree zero-sorry. See
the hypothesis-threading note below.

This file packages the single theorem of Milne's *Abelian Varieties* §I.3,
Theorem 3.2: **a rational map from a nonsingular variety to an abelian
variety extends, uniquely, to a regular morphism**. This is the input that
the Albanese universal-property build consumes when promoting the
symmetric-product rational map `C^{(g)} ⇢ A` to a regular morphism `J → A`.

Milne's proof is two lines: combine Theorem 3.1 (the codim-≥2 indeterminacy
result for rational maps from a nonsingular variety to a complete variety —
`indeterminacy_codimGe2_of_smooth_of_complete`,
`Albanese/CodimOneMilne31.lean`) with Lemma 3.3 (the pure-codim-1
indeterminacy structure for rational maps into a group variety — here the
hypothesis `Milne33Indeterminacy f`). The combination forces the
indeterminacy locus of `f` to be simultaneously of codimension `≥ 2` and
(empty or) pure codimension `1`, hence empty, so `f` is everywhere defined
(`existsUnique_hom_of_indeterminacyLocus_eq_empty`,
`Albanese/CodimOneExtensionUnique.lean`).

## The Milne-3.3 hypothesis threading

`extend_to_av` takes `(h33 : Milne33Indeterminacy f)` explicitly. Modulo that
hypothesis the theorem is **fully proved and axiom-clean** — no `sorry`
anywhere in this tree. The dedicated Milne-3.3 lane proves
`Milne33Indeterminacy f` for every rational map over `k̄` from a nonsingular
`k̄`-variety to a group `k̄`-variety (the statement shape, its proof-substep
inventory, and the landed substeps are documented at the def in
`Albanese/CodimOneIndeterminacy.lean`); discharging is then a matter of
supplying that theorem at each call site.

## Abelian-variety conventions

Throughout the project, an **abelian variety over `k̄`** is encoded as an
object `A : Over (Spec (.of k̄))` carrying the four instances:

- `[GrpObj A]` (group-object structure on the over-category),
- `[IsProper A.hom]` (complete),
- `[Smooth A.hom]` (nonsingular),
- `[GeometricallyIrreducible A.hom]` (geometrically irreducible).

A **nonsingular variety over `k̄`** is an object `X : Over (Spec (.of k̄))`
carrying:

- `[Smooth X.hom]`,
- `[GeometricallyIrreducible X.hom]`,
- `[IsSeparated X.hom]`,
- `[LocallyOfFiniteType X.hom]`,
- `[IsIntegral X.left]`,
- `[IsReduced X.left]`.

These four-plus-two instances will normally be supplied by `inferInstance`
at the call site.

## References

Source: Milne, *Abelian Varieties*, §I.3, Theorem 3.2, p. 17.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

/-! ## Milne Theorem 3.2 — rational maps to an abelian variety extend

Let `k̄` be an algebraically closed field. Let `X` be a nonsingular variety
over `k̄` (smooth, geometrically irreducible, separated, locally of finite
type, integral, reduced). Let `A` be an abelian variety over `k̄`
(a group object that is proper, smooth, and geometrically irreducible). For
every rational map `f : X ⇢ A` over `k̄` satisfying the Milne-3.3
disjunction, there is a *unique* regular morphism `g : X ⟶ A` whose induced
rational map equals `f`.

Milne's argument (Theorem 3.2): let `U ⊆ X` be a maximal open of definition
of `f` and `Z := X ∖ U`. By the codim-≥2 indeterminacy theorem (Theorem 3.1)
the closed subset `Z` has codimension `≥ 2`. By the pure-codim-1
indeterminacy lemma for maps into a group variety (Lemma 3.3 — here the
hypothesis `Milne33Indeterminacy f`), `Z` is either empty or of pure
codimension `1`. Both conditions force `Z = ∅`, so `U = X` and `f` admits a
regular representative on all of `X`. Uniqueness is the standard
reduced-and-separated agreement principle
(`AlgebraicGeometry.ext_of_isDominant`). -/

/-- **A scheme smooth over an algebraically closed field is reduced**
(Stacks `056S`/`033B` over `k̄`). Used to derive `IsReduced A.left` in
`av_isIntegral_of_smooth_geomIrred` below.

Thin wrapper around the project-side `isReduced_of_smooth_of_isAlgClosed`
(`Albanese/CodimOneSmoothReduced.lean`, Step B.e): stalks are localisations
of standard-smooth `k̄`-algebras, whose maximal-ideal localisations are
regular local (Step B.d′) hence domains
(`RingTheory.CohenMacaulay.isDomain_of_regularLocal`, Stacks `00NP` in the
`Algebra/ABRegular*` package), and reducedness is checked at maximal
localisations then transported to stalks and glued. Axiom-clean. -/
private theorem isReduced_of_smooth_over_field
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (A : Over (Spec (.of kbar)))
    [Smooth A.hom] :
    IsReduced A.left :=
  isReduced_of_smooth_of_isAlgClosed A

/-- **Integrality of the abelian variety.**

For an abelian variety `A` over an algebraically closed field `k̄` —
encoded in the project as `A : Over (Spec (.of k̄))` carrying
`[GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]` —
the underlying scheme `A.left` is integral.

**Derivation.** The proof has three steps:

1. `Spec k̄` is a singleton scheme (Mathlib instance
   `Scheme.instUniqueCarrierCarrierCommRingCatSpecOf` provides `Unique`,
   which yields both `Subsingleton` and `Nonempty`).
2. `GeometricallyIrreducible A.hom + Spec k̄ a single point ⟹ IrreducibleSpace A.left`
   via Mathlib's `GeometricallyIrreducible.irreducibleSpace_of_subsingleton`.
3. `IrreducibleSpace + IsReduced ⟹ IsIntegral` via Mathlib's
   `isIntegral_of_irreducibleSpace_of_isReduced`.

The implication `Smooth A.hom ⟹ IsReduced A.left` is supplied project-side
by `isReduced_of_smooth_over_field` (backed by
`isReduced_of_smooth_of_isAlgClosed` in
`Albanese/CodimOneSmoothReduced.lean`). Axiom-clean. -/
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

/-- **Milne 3.2, emptiness step: the indeterminacy locus of a rational map
to an abelian variety is empty.**

For a rational map `f : X ⇢ A` of `k̄`-varieties from a nonsingular variety
`X` to an abelian variety `A` over an algebraically closed field `k̄`,
satisfying the Milne-3.3 disjunction `Milne33Indeterminacy f`,
`indeterminacyLocus f = ∅`.

**Derivation (Milne, *Abelian Varieties*, proof of Theorem 3.2, §I.3,
p. 17).** Two inputs combine:

1. `h33 : Milne33Indeterminacy f` (Milne Lemma 3.3, threaded as an explicit
   hypothesis — see `Albanese/CodimOneIndeterminacy.lean`): the
   indeterminacy locus is either empty or pure codim 1 — every point of
   `Z(f)` specialises from a coheight-1 point *of `Z(f)`*.
2. `indeterminacy_codimGe2_of_smooth_of_complete` (Milne Theorem 3.1 in
   `Albanese/CodimOneMilne31.lean`, proved axiom-clean): for a rational
   map from a nonsingular variety to a complete variety, every point of the
   indeterminacy locus has coheight `≥ 2`.

If `Z(f)` were non-empty, (1)'s second disjunct would produce a point
`z ∈ Z(f)` with `coheight z = 1`, contradicting (2). Hence `Z(f) = ∅`.

Input (2) requires `f` to be a rational map *over `k̄`* (hypothesis
`hover`, Milne's ambient assumption), which the consumer threads through.

**Refactor note (inherited from the source tree).** This replaces former
`CodimOneFree`-valued helpers: `CodimOneFree f` alone does NOT imply an
extension for a complete target (see the historical-trap note in
`Albanese/CodimOneExtensionUnique.lean`), so the Thm-3.2 chain runs through
the honest `Z(f) = ∅` intermediate. -/
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
    (hover : f.compHom A.hom = X.hom.toRationalMap)
    (h33 : Milne33Indeterminacy f) :
    indeterminacyLocus f = ∅ := by
  -- Materialise the variety-package instances on `A.left` needed by Milne
  -- Theorem 3.1: `IsIntegral` from the split helper
  -- `av_isIntegral_of_smooth_geomIrred`; `IsReduced` from
  -- `isReduced_of_isIntegral`; `IsSeparated` from `IsProper`;
  -- `LocallyOfFiniteType` from `Smooth`.
  haveI : IsIntegral A.left := av_isIntegral_of_smooth_geomIrred A
  haveI : IsReduced A.left := inferInstance
  haveI : IsSeparated A.hom := inferInstance
  haveI : LocallyOfFiniteType A.hom := inferInstance
  -- Milne Lemma 3.3 (the threaded hypothesis): the locus is empty, or every
  -- point of it specialises from a coheight-1 point of the locus.
  rcases h33 with hempty | hpure
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

For `X` a nonsingular variety over an algebraically closed field `k̄`, and
`A` an abelian variety over `k̄`, every rational map `f : X ⇢ A` over `k̄`
satisfying the Milne-3.3 disjunction `Milne33Indeterminacy f` has a *unique*
regular extension `g : X ⟶ A` (i.e. `g.toRationalMap = f`).

This is the input the Albanese universal-property build consumes when
promoting the symmetric-product rational map `C^{(g)} ⇢ A` to a regular
morphism `J → A`.

**Hypothesis-threading note.** `h33 : Milne33Indeterminacy f` is Milne
Lemma 3.3 for `f`, taken as an explicit hypothesis so this tree stays
zero-sorry; the dedicated Milne-3.3 lane proves it from the variety and
group-variety packages (see `Albanese/CodimOneIndeterminacy.lean`). Modulo
`h33`, the proof is Milne's two-line argument, run through the honest
`Z(f) = ∅` intermediate:

1. `av_indeterminacyLocus_eq_empty` (above) combines `h33` with the
   codim-≥2 conclusion of Milne 3.1
   (`indeterminacy_codimGe2_of_smooth_of_complete`, proved axiom-clean) to
   force `indeterminacyLocus f = ∅`.

2. `existsUnique_hom_of_indeterminacyLocus_eq_empty` (proved axiom-clean in
   `Albanese/CodimOneExtensionUnique.lean`): a rational map from a reduced
   scheme to a separated scheme with empty indeterminacy locus is uniquely
   represented by a regular morphism. The scheme-level separatedness
   `A.left.IsSeparated` is derived from `IsSeparated A.hom` (from
   `IsProper A.hom`) composed with the affine `Spec k̄ ⟶ ⊤_ Scheme`. -/
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
    (hover : f.compHom A.hom = X.hom.toRationalMap)
    (h33 : Milne33Indeterminacy f) :
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
    (av_indeterminacyLocus_eq_empty f hover h33)

end RationalMap

end Scheme

end AlgebraicGeometry
