/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Albanese.CoheightBridge
import Mathlib

/-!
# Topological Krull dimension of a scheme from its stalks

This file supplies the bridge that the dimension leg of the Jacobian A.3 story
was recorded as *missing*: a way to compute `topologicalKrullDim X` for a scheme
`X` out of local data at the points of `X`.

The recorded price (see `Picard/IdentityComponent.lean`, `finrank_eq_genus`, and
the same analysis at `Jacobian.lean`) was that mathlib v4.31 has essentially no
API for `topologicalKrullDim` — only `IsHomeomorph.topologicalKrullDim_eq`,
`IsInducing.topologicalKrullDim_le`, `topologicalKrullDim_subspace_le`,
`topologicalKrullDim_zero_of_discreteTopology` and
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, none of which connects the
invariant to a tangent-space dimension; the suggested route ran through
`Algebra.IsStandardSmoothOfRelativeDimension` and an affine-local presentation.

That analysis measured the wrong side of the problem. `topologicalKrullDim` is
*by definition* the order-theoretic `krullDim` of the poset of irreducible closed
subsets, and for a scheme that poset is order-isomorphic to the space itself
(`irreducibleSetEquivPoints`, since a scheme is sober and `T0`). Under that
isomorphism mathlib's `Order.krullDim_eq_iSup_coheight` turns the dimension into
a supremum of coheights, and this project already owns
`Scheme.ringKrullDim_stalk_eq_coheight` (`Albanese/CoheightBridge.lean`) which
identifies each coheight with the Krull dimension of a stalk. So the dimension of
a scheme is the supremum of the Krull dimensions of its stalks — and no
standard-smooth presentation is required.

## Main results

* `Scheme.topologicalKrullDim_eq_iSup_ringKrullDim_stalk` — the general identity
  `dim X = ⨆ z, dim 𝒪_{X,z}`, for **any** scheme.
* `Scheme.topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le` and
  `Scheme.ringKrullDim_stalk_le_topologicalKrullDim` — the two halves, combined in
  `Scheme.topologicalKrullDim_eq_of_le_of_exists_ge`.
* `Scheme.le_topologicalKrullDim_of_finrank_cotangentSpace` — the ≥ half in
  cotangent form, from data at a **single** regular point. This is the shape the
  tangent-space computation `dim_k T₀ = g` feeds.

## A scope warning that shaped the statements

Stalks of a scheme do **not** all have the same dimension: at a generic point the
stalk is a localisation at a minimal prime, of dimension `0`. So a
"constant stalk dimension" hypothesis is nearly vacuous, and the
homogeneity of a group scheme does not repair it — translation acts transitively
on *closed* points over an algebraically closed field, not on all points. The
constant forms are retained (`…_eq_of_forall_ringKrullDim_stalk_eq`,
`…_eq_of_forall_finrank_cotangentSpace_eq`) with that warning attached; a real
dimension computation pairs a uniform ≤ bound with a ≥ witness at one point.
-/

universe u

open AlgebraicGeometry Order TopologicalSpace CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **The topological Krull dimension of a scheme is the supremum of the Krull
dimensions of its stalks.**

Proof in three moves, none of them geometric:

* `topologicalKrullDim X` is `krullDim (IrreducibleCloseds X)` by definition;
* a scheme is sober and `T0`, so `irreducibleSetEquivPoints` is an order
  isomorphism `IrreducibleCloseds X ≃o X` (for the specialisation order), and
  `Order.krullDim_eq_of_orderIso` transports the dimension to the carrier;
* `Order.krullDim_eq_iSup_coheight` writes that as `⨆ z, coheight z`, and the
  project's `Scheme.ringKrullDim_stalk_eq_coheight` replaces each coheight by
  `ringKrullDim (X.presheaf.stalk z)`.

This is the missing bridge referred to at `Picard/IdentityComponent.lean`'s
`finrank_eq_genus`: it connects `topologicalKrullDim` to *local* data, which is
what any tangent-space computation produces. -/
theorem topologicalKrullDim_eq_iSup_ringKrullDim_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ (z : X), ringKrullDim (X.presheaf.stalk z) := by
  have h : topologicalKrullDim X = ⨆ (z : X), (Order.coheight z : WithBot ℕ∞) := by
    unfold topologicalKrullDim
    rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact Order.krullDim_eq_iSup_coheight
  rw [h]
  exact iSup_congr fun z => (ringKrullDim_stalk_eq_coheight X z).symm

/-- **A scheme all of whose stalks have Krull dimension `d` has dimension `d`.**

The specialisation of `topologicalKrullDim_eq_iSup_ringKrullDim_stalk` to a
*constant* stalk dimension. `Nonempty X` is genuinely needed: over an empty
scheme the supremum is `⊥`, not `d`.

**READ THE SCOPE WARNING BEFORE REACHING FOR THIS.** It is nearly vacuous, and
saying so is the point of stating the two bounds below instead. Stalks of a
scheme are *not* all of the same dimension: the stalk at a generic point of an
irreducible component is a localisation at a minimal prime, so it has dimension
`0`, while the stalk at a closed point of a `d`-dimensional variety has dimension
`d`. So the hypothesis `∀ z, ringKrullDim (stalk z) = d` forces `d = 0` on any
nonempty scheme with a generic point — in particular this lemma says nothing
about `Pic⁰` beyond `d = 0`, and the "translation makes all stalks isomorphic"
reading of homogeneity is **false**: translation is transitive on *closed* points
of a group scheme over an algebraically closed field, not on all points.

The useful forms are `topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le`
(the ≤ half, quantified over all points) and
`ringKrullDim_stalk_le_topologicalKrullDim` (the ≥ half, at one point), combined
in `topologicalKrullDim_eq_of_le_of_exists_ge`. -/
theorem topologicalKrullDim_eq_of_forall_ringKrullDim_stalk_eq
    (X : Scheme.{u}) [Nonempty X] (d : WithBot ℕ∞)
    (h : ∀ z : X, ringKrullDim (X.presheaf.stalk z) = d) :
    topologicalKrullDim X = d := by
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X]
  simp [h]

/-- **The ≤ half: a bound at every point bounds the dimension.** Unlike the
constant form above this is not vacuous — a bound holding at all points is
exactly what "every local ring has dimension at most `d`" says, and it is the
half a *smooth* scheme of relative dimension `d` supplies. -/
theorem topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le
    (X : Scheme.{u}) (d : WithBot ℕ∞)
    (h : ∀ z : X, ringKrullDim (X.presheaf.stalk z) ≤ d) :
    topologicalKrullDim X ≤ d := by
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X]
  exact iSup_le h

/-- **The ≥ half: one point's stalk dimension bounds the dimension from below.**
The witness may be taken at any single point — for a group scheme, the identity. -/
theorem ringKrullDim_stalk_le_topologicalKrullDim
    (X : Scheme.{u}) (z : X) :
    ringKrullDim (X.presheaf.stalk z) ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X]
  exact le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) z

/-- **The honest constant-dimension criterion**: a uniform upper bound at *every*
point plus a matching lower bound at *one* point. This is the shape a dimension
computation on a variety actually has — the bound comes from smoothness (or a
presentation) globally, and the witness from a distinguished closed point, which
for `Pic⁰_{C/k}` is the identity. -/
theorem topologicalKrullDim_eq_of_le_of_exists_ge
    (X : Scheme.{u}) (d : WithBot ℕ∞)
    (hle : ∀ z : X, ringKrullDim (X.presheaf.stalk z) ≤ d)
    (z₀ : X) (hz₀ : d ≤ ringKrullDim (X.presheaf.stalk z₀)) :
    topologicalKrullDim X = d :=
  le_antisymm (topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le X d hle)
    (hz₀.trans (ringKrullDim_stalk_le_topologicalKrullDim X z₀))

/-- **The ≥ half in cotangent form: the embedding dimension at ONE regular point
bounds the scheme's dimension from below.**

At a regular point, `IsRegularLocalRing.iff_finrank_cotangentSpace` identifies
`dim_{κ(z)} m_z/m_z²` with `dim 𝒪_{X,z}`, and that is at most `dim X` by
`ringKrullDim_stalk_le_topologicalKrullDim`.

No Noetherian hypothesis is needed, and an earlier version of this docstring got
that backwards: it carried `[IsLocallyNoetherian X]` and explained it as "what
makes the stalk Noetherian, which is what
`IsRegularLocalRing.iff_finrank_cotangentSpace` consumes". But
`class IsRegularLocalRing R extends IsLocalRing R, IsNoetherianRing R`, so the
`hreg` hypothesis already *supplies* that instance. The binder was dead, and it
had pulled a helper (`Pic0.isLocallyNoetherian`) into existence downstream purely
to discharge it. Before adding a side instance to feed a consumer of a regularity
hypothesis, read the class's `extends` clause.

**This is the direction the tangent-space identity `dim_k T₀ Pic⁰ = g` feeds**,
and it needs data at the identity only — no quantifier over the points of
`Pic⁰`, which is why it is stated separately from the ≤ half. The cotangent space
is the linear dual of the tangent space, and `Subspace.dual_finrank_eq` makes
that a dimension-preserving step. -/
theorem le_topologicalKrullDim_of_finrank_cotangentSpace
    (X : Scheme.{u}) (d : ℕ) (z : X)
    (hreg : IsRegularLocalRing (X.presheaf.stalk z))
    (h : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk z))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk z)) = d) :
    (d : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  haveI := hreg
  have hdim : ringKrullDim (X.presheaf.stalk z) = (d : WithBot ℕ∞) := by
    rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace (R := X.presheaf.stalk z)).mp hreg, h]
  rw [← hdim]
  exact ringKrullDim_stalk_le_topologicalKrullDim X z

/-- **Dimension from the cotangent spaces, at regular points** — the constant
form, inheriting the vacuity warning of
`topologicalKrullDim_eq_of_forall_ringKrullDim_stalk_eq`: asking the embedding
dimension to be `d` at *every* point (including generic points, where it is `0`)
forces `d = 0`. Kept because it is the direct cotangent translation, but a
dimension computation should use
`le_topologicalKrullDim_of_finrank_cotangentSpace` for the ≥ half together with
`topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le` for the ≤ half. -/
theorem topologicalKrullDim_eq_of_forall_finrank_cotangentSpace_eq
    (X : Scheme.{u}) [Nonempty X] (d : ℕ)
    (hreg : ∀ z : X, IsRegularLocalRing (X.presheaf.stalk z))
    (h : ∀ z : X, Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk z))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk z)) = d) :
    topologicalKrullDim X = (d : WithBot ℕ∞) := by
  refine topologicalKrullDim_eq_of_forall_ringKrullDim_stalk_eq X _ fun z => ?_
  haveI := hreg z
  rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace (R := X.presheaf.stalk z)).mp (hreg z),
    h z]

end AlgebraicGeometry.Scheme
