/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.ChiUnconditional
import AlgebraicJacobian.RiemannRoch.Adelic.ResidueField

/-!
# Extension uniformity, reduced to a chart count uniform in the extension

`ResidueField.UniformlyBoundedVanishing` writes down cluster P's gap (2) — a **single**
vanishing threshold `b`, chosen before the field extension `κ/k` — and proves it at no
curve.  The two inputs its docstring records as genuinely missing are flat base change for
the section spaces and a `WeilDivisor` pullback along `C_κ ⟶ C`.

This file does **not** supply either.  What it does is remove the *cohomological* half of the
obstruction, using the ungated Čech formula of `ChiUnconditional.lean`:

`h1dim_eq_zero_iff_charts` says `Ȟ¹(D) = 0` iff the three chart dimensions satisfy a
numerical identity.  That criterion mentions **no** connecting homomorphism, no exactness
datum, and nothing about `κ` beyond the chart dimensions themselves.  So extension
uniformity follows from a chart count that is uniform in `κ` — and the residual gap becomes a
statement about **dimensions of section spaces under base change**, which is exactly the flat
base change already identified as missing, and nothing more.

That is the honest gain: the gap does not shrink logically, but it stops being three
different things (vanishing + exactness + base change) and becomes one (base change).

## The three gaps, kept apart as the task requires

* **Single-field vanishing** — `ChiUnconditional.h1dim_eq_zero_iff_charts` is an ungated
  *criterion*; whether its right-hand side holds at a given curve is not proved here or
  anywhere in AJC.  Still open, now purely a counting question.
* **Extension uniformity** — `uniformlyBoundedVanishing_of_uniformChartCount` below reduces
  it to `UniformChartCount`, a κ-uniform chart identity.  `UniformChartCount` is **not
  proved at any curve**; it is a hypothesis, and it is strictly stronger than the
  single-field count. Still open.
* **Global generation** — untouched here; see `GlobalGeneration.lean`.  It is proved from
  the ledger inputs and is *not* implied by anything in this file.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits IsDedekindDomain
open scoped WithZero AlgebraicGeometry.Scheme

namespace AlgebraicGeometry
namespace Adelic

section UniformCharts

variable {k : Type u} [Field k]

/-- **The κ-uniform chart count.**  A single threshold `b`, chosen before the extension `κ`,
above which the Čech inclusion–exclusion count computes `ℓ` on the base-changed curve.

This is the base-change-side hypothesis, isolated.  Compare
`ChiUnconditional.h1dim_eq_zero_iff_charts`, whose right-hand side is this identity at one
fixed field: `UniformChartCount` is that identity with `b` pulled outside the `∀ κ`, which is
precisely the uniformity the predicate `UniformlyBoundedVanishing` demands.

It is stated with the finiteness of the three base-changed chart section spaces as explicit
hypotheses in the body rather than as instance binders, because on the base-changed curve
those instances are exactly what a base-change theorem would produce, and demanding them as
binders here would quietly assume the missing input. -/
def UniformChartCount (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (S : C.left.AffineCoverMVSquare) : Prop :=
  ∃ b : ℤ, ∀ (κ : Type u) [Field κ] [Algebra k κ],
    ∀ D : (Scheme.baseChangeField C κ).left.WeilDivisor, b ≤ degK κ D →
      sectionSub κ ((S.baseChangeField κ).U₁ ⊓ (S.baseChangeField κ).U₂) D ≤
        coboundarySub κ (S.baseChangeField κ).U₁ (S.baseChangeField κ).U₂ D

/-- **Extension-uniform vanishing from the κ-uniform chart count.**

The threshold transfers verbatim: `UniformChartCount`'s `b` is `UniformlyBoundedVanishing`'s
`b`, and at each `κ` and `D` the conclusion is `BoundedVanishing.subsingleton_h1Mod_iff`
applied to the chart inclusion.  No exactness hypothesis, no approximation input, no ledger.

**What this is and is not.**  It is a genuine reduction of *cluster P's gap (2)* to a
statement about base-changed section spaces — the cohomological content is discharged.  It is
**not** a proof of extension uniformity: `UniformChartCount` is unproved at every curve, and
it is strictly stronger than the single-field count because `b` is quantified before `κ`.
Anyone reading this as "extension uniformity is closed" has misread it; a janitor made
exactly that conflation once already (retracted at inbox `I-0412`).

**Relation to `ChiUnconditional` §5–§6, stated carefully.**  Those sections refute the closed
ledger `hledger` on a cover with a prime divisor off a chart, because `hledger` equates χ with the
*unbounded* `deg_k D` while the chart-finiteness binders force χ — and indeed `ℓ`
(`ell_le_finrank_chart_along_tower`) — to be *bounded* along a tower.

`UniformChartCount` is **not** refuted that way: it demands a subspace *inclusion*
`𝒜(D) ⊆ B(D)`, i.e. vanishing, not growth.  Vanishing content survives the tower argument; the
ledger's growth claim does not.  So this reduction is not vacuous for that reason.

What remains true, and is the honest limit: `UniformChartCount` is proved at **no** curve, it is
strictly stronger than the single-field count (the threshold precedes `κ`), and it quantifies over
all divisors above `b` on every base-changed curve.  This is the sharpest honest statement of gap
(2) available in AJC today, and "sharpest honest" is not the same as "usable". -/
theorem uniformlyBoundedVanishing_of_uniformChartCount
    (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [GeometricallyIntegral C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (S : C.left.AffineCoverMVSquare)
    (hcount : UniformChartCount C S) :
    UniformlyBoundedVanishing C S := by
  obtain ⟨b, hb⟩ := hcount
  refine ⟨b, fun κ _ _ D hD => ?_⟩
  exact (subsingleton_h1Mod_iff κ (S.baseChangeField κ).U₁ (S.baseChangeField κ).U₂ D).mpr
    (hb κ D hD)

end UniformCharts

end Adelic
end AlgebraicGeometry
