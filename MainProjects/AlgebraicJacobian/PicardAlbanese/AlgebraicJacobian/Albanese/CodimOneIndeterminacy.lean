/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Indeterminacy locus of a rational map, and the Milne Lemma 3.3 statement shape

Ported from §1/§5/§6 of `Albanese/CodimOneExtension.lean` of the previous
Algebraic-Jacobian tree (identical toolchain and mathlib pin),
re-kernel-verified here. First file of the codim-one extension layer
(Milne, *Abelian Varieties*, §I.3, pp. 16–17).

* `Scheme.RationalMap.indeterminacyLocus` — the closed complement
  `Z(f) := X ∖ Dom(f)` of the domain of definition, as a `Set X`.
* `Scheme.RationalMap.CodimOneFree` — predicate: every point `η : X` with
  `Order.coheight η = 1` lies in `f.domain`.
* `Scheme.RationalMap.Milne33Indeterminacy` — the **statement shape** of
  Milne Lemma 3.3 ("`Z(f)` is empty or of pure codimension one"), as a
  named `Prop`-valued def.

## The Milne-3.3 hypothesis-threading discipline (zero-sorry port)

In the previous tree, Milne Lemma 3.3
(`indeterminacy_pure_codim_one_into_grpScheme`) was the single `sorry` of the
codim-one extension chapter. This tree keeps a **zero-sorry** invariant, so
the lemma is NOT ported as a sorried theorem. Instead its conclusion — the
disjunction below — is stated once as the `Prop`-valued def
`Milne33Indeterminacy f`, and every downstream consumer (in particular
`extend_to_av`, Milne Theorem 3.2, in
`Albanese/Thm32RationalMapExtension.lean`) takes `Milne33Indeterminacy f` as
an **explicit hypothesis**. The dedicated Milne-3.3 lane proves, for `X` a
nonsingular variety and `G` a group variety over `k̄` and `f : X ⇢ G` a
rational map over `k̄` (`f.compHom G.hom = X.hom.toRationalMap`), the theorem

`indeterminacy_pure_codim_one_into_grpScheme : Milne33Indeterminacy f`,

after which the hypothesis is discharged at every call site. Substantial
substeps of that proof are already landed:

* Substep 1 (difference map `Φ : X × X ⇢ G`, `(x, y) ↦ f(x)·f(y)⁻¹`):
  `Albanese/DifferenceMap.lean` (`differenceRationalMap`,
  `le_domain_differenceRationalMap`, `le_domain_precomp_fst_of_difference`,
  `reconstruct_precomp_fst`).
* Substep 2, topological existence half: `Albanese/Milne33Substeps.lean`
  (`exists_snd_mem_of_fst_eq_of_mem`,
  `exists_mem_domain_precomp_fst_of_differenceRationalMap`).
* Substep 4a (pole-divisor purity): `Albanese/PolePurity.lean`
  (`Scheme.exists_specializes_coheight_eq_one_of_notMem_stalk_range`).
* Substep 4b, Hauptidealsatz transport: `Albanese/Milne33Substeps.lean`
  (`Ideal.exists_height_one_prime_mem_le`,
  `Scheme.exists_specializes_coheight_eq_one_of_mem_maximalIdeal`).

Still open there: Substep 2 (hard direction assembly), Substep 3 (pullback of
`𝒪_{G,e}` along `Φ`), and the final assembly.

## Deferred: the substantive Weil-divisor obstruction

The blueprint pin `thm:weil_divisor_obstruction` (Hartshorne II.6,
pp. 130–131) calls for the genuinely substantive statement

> `f` is defined at the generic point `η_W` of a prime divisor `W` iff every
> regular function on every affine open `V ⊆ Y` around `f(η_W)` pulls back to
> an element of `𝒪_{X,η_W} ⊆ K(X)` of order-value `≥ 0` along `W`,

which requires pullback machinery `Scheme.RationalMap → K(Y) → K(X)` plus an
order/valuation apparatus at codim-one points, neither of which is shipped by
Mathlib at this pin nor rebuilt in this tree yet. Only the truthful
definitional content survives from that pin: definedness at a point is
`Scheme.RationalMap.mem_domain` (a Mathlib lemma). The substantive
reformulation is deferred to a future lemma (working title:
`extend_iff_pullback_order_nonneg`) once the pullback machinery lands.
-/

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

/-! ## §1. The indeterminacy locus of a rational map

The indeterminacy locus `Z(f) ⊆ X` of a rational map `f : X ⇢ Y` is the closed
complement of its domain of definition `Dom(f) := f.domain` (a Mathlib-shipped
open subset of `X`).

Blueprint pin: `def:indeterminacy_locus` (Milne §I.3 p. 16). -/

/-- **Indeterminacy locus of a rational map.** The closed complement of the
domain of definition `f.domain` (an `X.Opens`, exposed by Mathlib at
`Mathlib.AlgebraicGeometry.Birational.RationalMap`):

`Z(f) := X ∖ Dom(f) ⊆ X`.

`f` is everywhere defined (i.e. extends to a regular morphism) iff
`indeterminacyLocus f = ∅`.

Blueprint reference: `def:indeterminacy_locus` (Milne, *Abelian Varieties*,
§I.3, p. 16). -/
def indeterminacyLocus {X Y : Scheme.{u}} (f : X.RationalMap Y) : Set X :=
  (f.domain : Set X)ᶜ

/-- **Codim-1-indeterminacy-free rational map.** A rational map
`f : X ⇢ Y` is codim-1-indeterminacy-free if every codimension-one point
of `X` lies in its domain of definition. Equivalently: no prime divisor of
`X` (i.e. closure of a codim-1 generic point) is contained in
`indeterminacyLocus f`.

The codim-1 condition is encoded via `Order.coheight η = 1` on the
specialisation preorder of `X.carrier`, the project's standing convention
for codimension-one points (cf. `Algebra/CoheightBridge.lean`, which
identifies `Order.coheight` with the stalk's Krull dimension).

Blueprint reference: `def:codim_one_indeterminacy` (Milne, *Abelian
Varieties*, Theorem 3.1, §I.3, p. 16). -/
def CodimOneFree {X Y : Scheme.{u}} (f : X.RationalMap Y) : Prop :=
  ∀ (x : X), Order.coheight x = 1 → x ∈ f.domain

/-! ## §5. Milne Lemma 3.3 — the statement shape

A rational map from a nonsingular variety to a group variety has its
indeterminacy locus either empty or of pure codimension `1`. Combined with
`thm:indeterminacy_codimGe2`'s codim-≥2 conclusion (Milne 3.1,
`Albanese/CodimOneMilne31.lean`), this forces the locus to be empty when the
target is an abelian variety, at which point
`existsUnique_hom_of_indeterminacyLocus_eq_empty`
(`Albanese/CodimOneExtensionUnique.lean`) extends.

Blueprint pin: `lem:milne_codim1_indeterminacy` (Milne §I.3 Lemma 3.3 p. 17). -/

/-- **Milne Lemma 3.3, statement shape — indeterminacy is empty or pure
codim 1.**

`Milne33Indeterminacy f` states: the indeterminacy locus
`Z(f) := indeterminacyLocus f` is either empty (`f` is defined on all of
`X`) or of *pure codimension 1*, encoded as: every point of `Z(f)` lies in
the closure of a codim-1 point *of `Z(f)` itself*. (The
`z ∈ indeterminacyLocus f` conjunct is essential: without it the disjunct is
nearly vacuous — on a variety every non-generic point specialises from *some*
codim-1 point — and, in particular, too weak to combine with the codim-≥2
conclusion of Milne 3.1 to force `Z(f) = ∅` in Theorem 3.2.)

This is a **statement shape**, not a theorem: it is the exact conclusion of
Milne's Lemma 3.3 (*Abelian Varieties*, §I.3, p. 17), which asserts
`Milne33Indeterminacy f` for every rational map `f : X ⇢ G` over `k̄` from a
nonsingular `k̄`-variety to a group `k̄`-variety. Pending that proof (the
dedicated Milne-3.3 lane; see the module docstring for the landed substeps),
every consumer threads `Milne33Indeterminacy f` as an explicit hypothesis —
see `extend_to_av` in `Albanese/Thm32RationalMapExtension.lean`.

The def is stated for arbitrary schemes: all the geometric hypotheses of
Lemma 3.3 (smoothness, properness of the group law, over-`k̄`-ness) belong to
the *proof*, not to the statement shape.

Milne's proof sketch: consider the difference map `Φ : X × X ⇢ G`,
`(x, y) ↦ f(x) · f(y)⁻¹`. Then `Φ` is defined at `(x, x)` iff `f` is defined
at `x`. Pulling back the maximal ideal of `𝒪_{G,e}` gives a finite set of
rational functions on `X × X` whose pole divisors are pure codim-1; their
intersection with the diagonal exhibits the indeterminacy locus of `f` as
pure codim-1.

Blueprint reference: `lem:milne_codim1_indeterminacy` (Milne, *Abelian
Varieties*, Lemma 3.3, §I.3, p. 17). -/
def Milne33Indeterminacy {X G : Scheme.{u}} (f : X.RationalMap G) : Prop :=
  indeterminacyLocus f = ∅ ∨
    ∀ x ∈ indeterminacyLocus f,
      ∃ z ∈ indeterminacyLocus f,
        Order.coheight z = 1 ∧ x ∈ closure ({z} : Set X)

end RationalMap

end Scheme

end AlgebraicGeometry
