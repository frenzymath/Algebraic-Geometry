/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SchemeKrullDimStalk

/-!
# Krull dimension is at most embedding dimension — the `≤` half in cotangent currency

## What this changes, and the measurement it corrects

`Picard/Pic0Dimension.lean` states `dim Pic⁰_{C/k} = g` against a hypothesis

```
hle : ∀ z, ringKrullDim (stalk z) ≤ (genus C : WithBot ℕ∞)
```

and its docstring records that direction as **genuinely absent**, having measured
`Albanese/StandardSmoothDimension.lean` and found "only *lower* bounds, and only
at *maximal* ideals". That measurement was of the wrong quantity. It looked for a
bound on `ringKrullDim` in terms of a presentation; what the tangent-space leg of
this chapter actually produces is a **cotangent** dimension, and the passage from
one to the other is unconditional:

```
ringKrullDim R ≤ dim_{κ} (m/m²)      for every Noetherian local ring R
```

with **no regularity hypothesis and no condition on the residue field**. Both
halves are already in the pinned mathlib and neither was used in this project
(`spanFinrank` appears in exactly one AJC file, for an unrelated purpose):

* `ringKrullDim_le_spanFinrank_maximalIdeal` — Krull's height theorem, in the form
  `dim R ≤ (minimal number of generators of m)`;
* `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` — Nakayama,
  identifying that generator count with `dim_{κ(R)} (m/m²)`.

Equality is the regular case (`IsRegularLocalRing.iff_finrank_cotangentSpace`), and
that is the *only* form the project had. The inequality is what a dimension **upper**
bound needs, and it holds everywhere.

**How close this already was, which is the sharper version of the correction.** The
ingredient was not merely available in mathlib — it was already *in use* in this
project. `Albanese/AuslanderBuchsbaum.lean:2239` applies
`ringKrullDim_le_spanFinrank_maximalIdeal` inline to bound a quotient's dimension, and
`Albanese/StandardSmoothDimension.lean:211` — the very file whose absence of an upper
bound was measured and recorded — states the fact in prose in its own docstring: "the
reverse inequality `dim ≤ dim_κ m/m²` holds in any Noetherian local ring, via
`ringKrullDim_le_spanFinrank_maximalIdeal`". So what was missing was never the
mathematics or even the mathlib lemma: it was a *named, reusable statement at the
scheme level*, and the search that concluded "genuinely absent" was looking for an
upper bound on `ringKrullDim` in a file that only ever needed lower bounds, while the
upper bound sat in its own prose. A fact used inside one proof body and mentioned in
one docstring is invisible to every search that looks for a declaration.

## Why this matters for the `PerfectField` binder

`Pic0.genus_le_topologicalKrullDim_of_smooth` and
`Pic0.topologicalKrullDim_eq_genus_of_forall_ringKrullDim_stalk_le` both carry
`[PerfectField k]`, inherited from
`Scheme.isRegularLocalRing_stalk_of_smooth_of_perfectField` — the only route this
tree has from smoothness to a regular stalk, and its upstream input
`isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField`
carries `[PerfectField k]` in its own signature, so the binder is not removable
there. Under the standing owner decision (inbox I-0491) the Jacobian headline is
stated over an **arbitrary** field, so any `PerfectField` on this leg is a real
gap and not a stylistic one.

The results below do **not** close that gap for the `≥` direction, and this file
claims nothing about it: `≥` genuinely needs regularity at the identity, because it
turns an embedding dimension into a *lower* bound on the Krull dimension and that
implication is false in general (a cusp has embedding dimension `2` and dimension
`1`). What they do is make the `≤` direction free of both `PerfectField` and
regularity — so of the two directions of `dim Pic⁰ = g`, the one previously called
"genuinely absent" is now the one with no side conditions at all.

## Main results

* `ringKrullDim_le_finrank_cotangentSpace` — the ring-level inequality.
* `Scheme.ringKrullDim_stalk_le_finrank_cotangentSpace` — at a scheme point.
* `Scheme.topologicalKrullDim_le_of_forall_finrank_cotangentSpace_le` — the `≤`
  half of a dimension computation, in cotangent currency, for any locally
  Noetherian scheme.
* `Scheme.topologicalKrullDim_eq_of_forall_finrank_cotangentSpace_le_of_regular` —
  the two halves combined: a uniform cotangent bound at every point plus a
  regular point where the cotangent dimension is exactly `d`.

## What is still owed, located precisely (run 0067 r6)

> **SUPERSEDED IN ITS HEADLINE CLAIM (run 0067 r7), and this was the third framing of
> this leg to be wrong.** The section below says the remaining input for `dim Pic⁰ ≤ g`
> is the uniform bound `∀ z, dim_κ (m_z/m_z²) ≤ g`, and then prices it as a standard-smooth
> presentation problem. It is **not** a separate piece of mathematics here: `Pic⁰` is a
> **group** scheme, so translations are automorphisms of the underlying scheme and the
> embedding dimension is constant along a translate orbit.
> `Pic0.forall_finrank_cotangentSpace_le_of_homogeneous`
> (`Picard/GroupSchemeHomogeneity.lean`) derives the uniform bound from the value at *one*
> point plus an orbit condition, and since that value is an *equality*, one point serves
> both directions — `Pic0.topologicalKrullDim_eq_genus_of_homogeneous` is the resulting
> form, axiom-clean. The predecessors of this framing were "`topologicalKrullDim` has no
> mathlib API" (refuted by unfolding the definition) and "no `ringKrullDim` upper bound
> exists" (refuted: the wrong quantity had been searched for).
>
> **AND THAT SUPERSESSION IS ITSELF RETRACTED (run 0067 r8) — the FOURTH wrong framing.
> The uniform bound below IS still the remaining input; the r7 "one point suffices" reading
> was vacuous.** `Pic0.topologicalKrullDim_eq_zero_of_homogeneous`
> (`Picard/HomogeneityOrbitCollapse.lean`) proves that the orbit condition alone forces
> `topologicalKrullDim Pic⁰ = 0`, hence `genus C = 0`: translations are homeomorphisms and
> the identity point is closed, so "every point is a translate of the identity" makes every
> point closed (`T1`), and a nonempty sober `T1` space has dimension `0`. So the section
> below is reinstated as an accurate statement of what is owed — with the correction that
> what the bound needs is a transport reaching **non-closed** points, which is why the
> `k`-rational orbit could never have supplied it.
>
> **What survives below, and is still worth reading:** the *general* theorems of this file
> are untouched and remain the right bricks — they take the uniform bound as a hypothesis,
> which is correct at the generality of an arbitrary scheme, where no group structure is
> available. Only the "this is what `Pic⁰` still owes" reading is retracted. The
> standard-smooth analysis is also still accurate as a statement about presentations, and
> records why `SmoothOfRelativeDimension` is *not* the cheap source it looks like.

The remaining input for `dim Pic⁰ ≤ g` is the *uniform* bound
`∀ z, dim_κ (m_z/m_z²) ≤ g`. The natural source is
`SmoothOfRelativeDimension (genus C) (Pic0Scheme C).hom`, whose field gives a
standard-smooth chart of relative dimension `n` at every point. That does **not**
immediately give the bound, and it is worth recording exactly where it stops, because
the gap is easy to miss:

`Algebra.IsStandardSmoothOfRelativeDimension n k S` unfolds to a presentation with
generator set `ι` and relation set `σ` satisfying `#ι - #σ = n`. Surjecting from the
polynomial ring bounds the dimension by
`ringKrullDim (MvPolynomial ι k) = #ι = n + #σ`
(`ringKrullDim_le_of_surjective` with
`MvPolynomial.ringKrullDim_of_isNoetherianRing`; verified to elaborate). That is the
**weak** bound: it is `n` only when `#σ = 0`. Getting `n` requires the `#σ` relations
to cut dimension by exactly `#σ`, i.e. that they form a regular sequence — which is
true for a standard-smooth presentation (the Jacobian is invertible) but is a real
theorem, not a rearrangement, and mathlib at this pin has no
`ringKrullDim`-of-a-standard-smooth-algebra lemma. `Albanese/StandardSmoothDimension.lean`
proves the matching *lower* bound `n ≤ height m` at maximal ideals by exactly this kind
of argument (Krull's height theorem plus the cardinality bookkeeping `n + #σ = #ι`), so
that file is the model for the missing upper half rather than a source of it.
-/

universe u

open AlgebraicGeometry Order IsLocalRing CategoryTheory

/-- **The Krull dimension of a Noetherian local ring is at most its embedding
dimension** — `dim R ≤ dim_{κ(R)} (m/m²)`, with no regularity hypothesis and no
condition on the residue field.

Two mathlib facts, composed:

* `ringKrullDim_le_spanFinrank_maximalIdeal` (Krull's height theorem) bounds the
  dimension by the minimal number of generators of the maximal ideal;
* `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` (Nakayama)
  identifies that count with the `κ(R)`-dimension of the cotangent space.

Regularity is exactly the case of *equality*
(`IsRegularLocalRing.iff_finrank_cotangentSpace`), which is the only form this
project had; the inequality holds always, and it is the direction an upper bound on
dimension needs. The converse inequality is **false** without regularity — a cusp
`k[x,y]/(y²-x³)` localised at the origin has embedding dimension `2` and dimension
`1` — which is why the `≥` half of a dimension computation still needs a regular
point and this one does not. -/
theorem ringKrullDim_le_finrank_cotangentSpace
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ ((Module.finrank (ResidueField R) (CotangentSpace R) : ℕ) : WithBot ℕ∞) := by
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R

/-- **The weak dimension bound from a standard-smooth presentation** — proved, and
stated to mark exactly how far the presentation alone gets.

For `S` standard-smooth of relative dimension `n` over a field `k`, the presentation
has generators `ι` and relations `σ` with `#ι - #σ = n`, and surjecting from
`MvPolynomial ι k` gives `dim S ≤ #ι = n + #σ`. This is *weaker* than `dim S ≤ n`
whenever there is at least one relation.

It is stated existentially, in the form the proof actually delivers, rather than as
`dim S ≤ n + #σ`: the presentation's `ι` and `σ` are bound inside the class field, so
naming them in the conclusion would require choosing a presentation first. What the
statement records is the honest content — *some* bound follows from the presentation
for free — while making clear that the sharp value does not.

**Why the sharp bound `dim S ≤ n` is a real theorem and not available here.** It needs
the `#σ` relations to cut the dimension by exactly `#σ`, i.e. to form a regular
sequence. That holds for a standard-smooth presentation, because the Jacobian is
invertible, but it is genuine commutative algebra and mathlib at this pin carries no
`ringKrullDim`-of-a-standard-smooth-algebra lemma. Compare
`Albanese/StandardSmoothDimension.lean`, which proves the matching **lower** bound
`n ≤ height m` at maximal ideals by Krull's height theorem plus the same cardinality
bookkeeping `n + #σ = #ι`; it is the model for the missing upper half, not a source
of it. -/
theorem Algebra.IsStandardSmoothOfRelativeDimension.exists_ringKrullDim_le
    {k : Type u} [Field k] {S : Type u} [CommRing S] [Nontrivial S] [Algebra k S]
    (n : ℕ) [H : Algebra.IsStandardSmoothOfRelativeDimension n k S] :
    ∃ m : ℕ, ringKrullDim S ≤ (m : WithBot ℕ∞) := by
  obtain ⟨ι, σ, hσ, hι, P, hPdim⟩ := H.out
  refine ⟨Nat.card ι, ?_⟩
  refine le_trans (ringKrullDim_le_of_surjective _ P.algebraMap_surjective) ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing (R := k) (ι := ι),
    ringKrullDim_eq_zero_of_field k, zero_add]

namespace AlgebraicGeometry.Scheme

/-- **At a point of a locally Noetherian scheme, the stalk's Krull dimension is at
most its embedding dimension.** The scheme-level form of
`ringKrullDim_le_finrank_cotangentSpace`; the stalk of a locally Noetherian scheme
is a Noetherian local ring, which is the only instance input. -/
theorem ringKrullDim_stalk_le_finrank_cotangentSpace
    (X : Scheme.{u}) [IsLocallyNoetherian X] (z : X) :
    ringKrullDim (X.presheaf.stalk z)
      ≤ ((Module.finrank (ResidueField (X.presheaf.stalk z))
            (CotangentSpace (X.presheaf.stalk z)) : ℕ) : WithBot ℕ∞) :=
  ringKrullDim_le_finrank_cotangentSpace _

/-- **The `≤` half of a dimension computation, in cotangent currency.** If the
cotangent space at every point of a locally Noetherian scheme has dimension at most
`d`, then `dim X ≤ d`.

This is the statement `Pic0.topologicalKrullDim_eq_genus_of_forall_ringKrullDim_stalk_le`
wanted and could not get from a presentation: it asks for a bound on the *same*
invariant the tangent-space leg computes, rather than on `ringKrullDim` directly, and
it needs no regularity anywhere. -/
theorem topologicalKrullDim_le_of_forall_finrank_cotangentSpace_le
    (X : Scheme.{u}) [IsLocallyNoetherian X] (d : ℕ)
    (h : ∀ z : X, Module.finrank (ResidueField (X.presheaf.stalk z))
      (CotangentSpace (X.presheaf.stalk z)) ≤ d) :
    topologicalKrullDim X ≤ (d : WithBot ℕ∞) :=
  topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le X _ fun z =>
    le_trans (ringKrullDim_stalk_le_finrank_cotangentSpace X z)
      (by exact_mod_cast Nat.cast_le.mpr (h z))

/-- **A dimension computation entirely in cotangent currency.** A uniform bound
`dim_κ (m_z/m_z²) ≤ d` at every point, together with **one** point `z₀` that is
regular and has cotangent dimension exactly `d`, gives `dim X = d`.

The asymmetry between the two hypotheses is the mathematics, not an artefact:

* the `≤` half is unconditional (`ringKrullDim_le_finrank_cotangentSpace`);
* the `≥` half needs `z₀` **regular**, since it converts an embedding dimension into
  a lower bound on the Krull dimension, and without regularity that is false — at a
  cusp the embedding dimension exceeds the dimension.

For `Pic⁰_{C/k}` the distinguished point is the identity, where the tangent-space
identity of this chapter supplies `d = g(C)`. -/
theorem topologicalKrullDim_eq_of_forall_finrank_cotangentSpace_le_of_regular
    (X : Scheme.{u}) [IsLocallyNoetherian X] (d : ℕ)
    (h : ∀ z : X, Module.finrank (ResidueField (X.presheaf.stalk z))
      (CotangentSpace (X.presheaf.stalk z)) ≤ d)
    (z₀ : X) (hreg : IsRegularLocalRing (X.presheaf.stalk z₀))
    (hz₀ : Module.finrank (ResidueField (X.presheaf.stalk z₀))
      (CotangentSpace (X.presheaf.stalk z₀)) = d) :
    topologicalKrullDim X = (d : WithBot ℕ∞) :=
  le_antisymm (topologicalKrullDim_le_of_forall_finrank_cotangentSpace_le X d h)
    (le_topologicalKrullDim_of_finrank_cotangentSpace X d z₀ hreg hz₀)

end AlgebraicGeometry.Scheme
