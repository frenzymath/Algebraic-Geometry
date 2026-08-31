/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.AbelianVariety.Translation

/-!
# The S3 criterion: relative dimension is a COVERING condition, not a pointwise one (W5-S3)

`informal/w5-s-worksheet.md` §3 froze the shape of brick S3
(`SmoothOfRelativeDimension (genus C) d.J.hom`) and ended with a named caveat and an instruction:

> step 3 transports a property *at a point*, and the mathlib class quantifies over points of the
> source `X` — for a group scheme over a field with a rational identity, translations by `k`-points
> may not reach every *scheme* point of `d.J` (only the rational ones). … Probe this before writing
> S3's Lean.

This file is the outcome of that probe (worksheet §3.1). The caveat is **dissolved**, and what
replaces it is small enough to state as two lemmas.

## The finding: the class is Zariski-local at source

`SmoothOfRelativeDimension n` is `IsLocalAtSource … Scheme.zariskiPrecoverage` — an instance
mathlib already provides, found by `inferInstance` (verified with `Smooth` as a control). So
mathlib's `IsLocalAtSource.of_zeroHypercover` applies, and the obligation is not *"exhibit a chart
at every point"* but *"cover the source by opens on each of which the composite has relative
dimension `n`"*.

That is a strictly weaker demand than the caveat feared, and it is the one a group scheme can meet:
the `k`-rational translates of a chart around the identity have only to **cover** `d.J.left`, not
to account for every scheme point of it. Whether they do cover is a separate, honest obligation —
carried here as the hypothesis `hcov` and **not** proved (see "What this does not do").

## Why the transport needs a name

`RespectsIso` holds for the class, so translating a chart is legal. But `infer_instance` does
**not** discharge `SmoothOfRelativeDimension n (e.hom ≫ f)` from the same for `f` plus an iso
`e`: the instance sits on the *property* (`MorphismProperty.RespectsIso`), not on the composite, so
the producer has to be named (`MorphismProperty.RespectsIso.precomp`). A failed `infer_instance`
here reads as absence and is not — the same shape as inbox `I-0567`/`I-0634`, and the reason
`smoothOfRelativeDimension_comp_iso` below exists at all.

## What this does NOT do

It does not prove S3. Two things are still owed, and neither is hidden:

1. **The numeral.** `n = genus C` at the identity is T5, which is itself conditional on the T3/T4
   `ε`-kernel count (`Tangent/Pic0TangentSpace.lean`,
   `JacobianData.finrank_cotangentSpaceDual_eq_genus` takes the count as a hypothesis).
2. **The cover.** That translated identity charts cover `d.J.left`. Stated as `hcov` in
   `smoothOfRelativeDimension_of_translation_cover`; if it fails, worksheet §3's `k̄` route plus the
   t4-§5 codescent brick is the documented contingency, which this file does **not** retire.

So this is the *criterion*, reduced to its two real inputs, with the third (pointwise
reachability) removed. Recorded per the standing rule that a reduction must name what it leaves
open.

## Main declarations

* `AlgebraicGeometry.smoothOfRelativeDimension_comp_iso` — the source-iso transport, by name.
* `AlgebraicGeometry.smoothOfRelativeDimension_of_zeroHypercover` — the covering criterion at this
  property, a direct instantiation of `IsLocalAtSource.of_zeroHypercover`.
* `AlgebraicGeometry.JacobianData.smoothOfRelativeDimension_of_translation_cover` — the S3 shape:
  translated charts that cover, each of relative dimension `n`, give the class on `d.J.hom`.

Reference: `informal/w5-s-worksheet.md` §§3, 3.1; Kleiman, "The Picard scheme", §5.
-/

set_option autoImplicit false

universe u

open CategoryTheory MorphismProperty MonoidalCategory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)

/-! ## The two general facts -/

/-- **The source-iso transport, named.** `SmoothOfRelativeDimension n` respects isomorphisms, so
precomposing with an iso preserves it — but `infer_instance` will not find this (the instance is on
the property, not on the composite), which is why translation transport needs a lemma. -/
theorem smoothOfRelativeDimension_comp_iso [SmoothOfRelativeDimension n f]
    {X' : Scheme.{u}} (e : X' ≅ X) :
    SmoothOfRelativeDimension n (e.hom ≫ f) :=
  (MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension n) e.hom f) ‹_›

/-- **The covering criterion.** `SmoothOfRelativeDimension n` is Zariski-local at source, so it
suffices to check it on the legs of any Zariski cover of the *source*.

This is what replaces worksheet §3's pointwise caveat: one does not have to reach every scheme
point, only to cover. -/
theorem smoothOfRelativeDimension_of_zeroHypercover
    (𝒰 : Precoverage.ZeroHypercover.{u} Scheme.zariskiPrecoverage X)
    (h : ∀ i, SmoothOfRelativeDimension n (𝒰.f i ≫ f)) :
    SmoothOfRelativeDimension n f :=
  MorphismProperty.IsLocalAtSource.of_zeroHypercover (K := Scheme.zariskiPrecoverage) 𝒰 h

/-- The criterion in `iff` form, for a consumer that wants to *use* the class on a cover. -/
theorem smoothOfRelativeDimension_iff_zeroHypercover
    (𝒰 : Precoverage.ZeroHypercover.{u} Scheme.zariskiPrecoverage X) :
    SmoothOfRelativeDimension n f ↔ ∀ i, SmoothOfRelativeDimension n (𝒰.f i ≫ f) :=
  MorphismProperty.IsLocalAtSource.iff_of_zeroHypercover (K := Scheme.zariskiPrecoverage) 𝒰

/-! ## The S3 shape at the Jacobian -/

namespace JacobianData

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **The S3 assembly, reduced to its two real inputs.** If the legs of a Zariski cover of
`d.J.left` each have relative dimension `n` over the base, then so does `d.J.hom`.

The intended instantiation is worksheet §3's chain: `Smooth d.J.hom` (S2) gives a standard-smooth
chart at the identity, T5 pins its relative dimension to `genus C`, and the `k`-rational
translations of X2 (`d.pointTranslationIso`) move that chart around — the legs of the cover being
the translated charts, each of which has the identity's relative dimension by
`smoothOfRelativeDimension_comp_iso`.

**What is a hypothesis here and why.** `𝒰` is exactly the covering claim §3.1 says remains owed:
that the translated charts cover. It is not proved in this file, and a consumer must supply it. The
value of the reduction is that the *pointwise* obligation — reach every scheme point, which
`k`-rational translations may not do — is gone. -/
theorem smoothOfRelativeDimension_of_translation_cover (d : JacobianData C) (n : ℕ)
    (𝒰 : Precoverage.ZeroHypercover.{u} Scheme.zariskiPrecoverage d.J.left)
    (hcov : ∀ i, SmoothOfRelativeDimension n (𝒰.f i ≫ d.J.hom)) :
    SmoothOfRelativeDimension n d.J.hom :=
  smoothOfRelativeDimension_of_zeroHypercover d.J.hom n 𝒰 hcov

/-- **A translated chart inherits the relative dimension of the chart it came from.** The X2
transport, at the level the S3 criterion consumes: if `d.J.hom` has relative dimension `n`, so does
its precomposition with any point translation.

Stated as the bridge between X2 (`AbelianVariety/Translation.lean`) and the covering criterion
above, so that the S3 prover does not have to rediscover that `infer_instance` fails here. -/
theorem smoothOfRelativeDimension_pointTranslationIso (d : JacobianData C) (n : ℕ)
    [SmoothOfRelativeDimension n d.J.hom]
    (x y : 𝟙_ (Over (Spec (.of k))) ⟶ d.J) :
    SmoothOfRelativeDimension n ((d.pointTranslationIso x y).hom ≫ d.J.hom) :=
  smoothOfRelativeDimension_comp_iso d.J.hom n (d.pointTranslationIso x y)

end JacobianData

end AlgebraicGeometry
