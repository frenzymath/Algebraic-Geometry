/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.TwoCover
import AlgebraicJacobian.Tangent.TwoChartHonest

/-!
# A degenerate two-chart cover has vanishing `H¹` (W5-T4: the last input, via genus not dimension)

`Tangent/TwoChartHonest.lean` reduces both chart-side inputs of the tangent computation to the
single hypothesis `¬ IsAffine C.left`. Measured (inbox `I-0729`): mathlib has no path to that from
`SmoothOfRelativeDimension 1` — the definition bottoms out at a *submersive presentation's*
combinatorial `P.dimension`, so relating it to quasi-finiteness or to fibre dimension is genuine
dimension theory nobody has developed for `n ≠ 0`.

**This file takes the other route, and it needs no dimension theory and no affine-vanishing
theorem.** If a chart is everything, the Čech `H¹` of the two-chart cover is **zero**:

```
U₀ = ⊤  ⟹  ∀ c : H1Cok k X U₀ U₁, c = 0        (h1Cok_eq_zero_of_left_eq_top)
U₁ = ⊤  ⟹  ∀ c : H1Cok k X U₀ U₁, c = 0        (h1Cok_eq_zero_of_right_eq_top)
```

So a cover with `h¹ ≠ 0` is automatically honest (`ne_top_of_h1Cok_ne_zero`), and since the tree
computes `h¹(𝒪_C) = g`, **`g ≠ 0` discharges what `¬ IsAffine C.left` was wanted for** — without
ever proving the curve non-affine.

## Why this is cheaper than it looks, and it is NOT Serre vanishing

The tempting route is *"an affine scheme has `H¹ = 0`"* — `affine_serre_vanishing` exists in the
sibling project and would need the whole quasi-coherent machinery plus `EnoughInjectives`. That is
not what happens here. The argument is purely about the **cover**: if `U₀ = ⊤` then the overlap
`U₀ ⊓ U₁` *is* `U₁`, so every section of the overlap already extends to `U₁`, and
`TwoCover.h1Cok_mk_resHom_right` kills its class. Two `resHom` lemmas (`resHom_resHom`,
`resHom_refl`) and no cohomology.

> **The lesson, and it is the session's own recurring one.** The obligation was priced as
> dimension theory because it was *stated* as `¬ IsAffine`. Asked instead "what is `¬ IsAffine`
> being used FOR", the answer is: to rule out a degenerate cover — and degeneracy of the cover is
> visible in `H¹` directly. `¬ IsAffine` was a sufficient condition someone had chosen, not the
> content. Cf. §6.28: search for what the hypothesis is a symptom of.

## What this does and does not give

It gives: an implication from a **cohomological** non-degeneracy (`H1Cok ≠ 0`, hence `g ≠ 0` once
the tree's `h¹ = g` identification is applied at the curve's own cover) to
`Scheme.AffineTwoCover.surjective_selector_of_not_isAffine`'s hypothesis being *unnecessary* — a
consumer holding `g ≠ 0` no longer needs `¬ IsAffine`.

It does **not** prove `¬ IsAffine C.left`, and does not claim to. The statement of
`ne_top_of_h1Cok_ne_zero` is about a chart being `⊤`, which is exactly the pair of conditions
`surjective_selector_iff` asks for; wiring it to `AffineTwoCover.selector` needs the cover's own
`H1Cok` instantiated at `U₀ = D.V₀`, `U₁ = D.V₁`, which a consumer does at its own carriers.

`I-0729` remains the record of the `¬ IsAffine` route and its price; this file is an alternative to
it, not a discharge of it.

## Main declarations

* `AlgebraicGeometry.TwoCover.h1Cok_eq_zero_of_left_eq_top` — `U₀ = ⊤ ⟹ H¹ = 0`.
* `AlgebraicGeometry.TwoCover.h1Cok_eq_zero_of_right_eq_top` — the mirror.
* `AlgebraicGeometry.TwoCover.ne_top_of_h1Cok_ne_zero` — a nonzero class makes both charts proper.

Reference: `informal/w5-t4-worksheet.md` §§6.27–6.28; inbox `I-0729`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace TwoCover

attribute [local instance] Scheme.overModule

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
variable (U₀ U₁ : X.Opens)

/-- **If the first chart is everything, the two-chart `H¹` vanishes.**

The overlap `⊤ ⊓ U₁` *is* `U₁`, so any section of the overlap is the restriction of itself viewed
on `U₁`, and `h1Cok_mk_resHom_right` kills its class. No affine hypothesis, no quasi-coherence, no
Serre vanishing — the content is that a degenerate cover has no interesting overlap. -/
theorem h1Cok_eq_zero_of_left_eq_top (h : U₀ = ⊤) (c : H1Cok k X U₀ U₁) : c = 0 := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  subst h
  have hle : U₁ ≤ (⊤ : X.Opens) ⊓ U₁ := le_inf le_top le_rfl
  have hkey : X.resHom (inf_le_right : (⊤ : X.Opens) ⊓ U₁ ≤ U₁) (X.resHom hle s) = s := by
    rw [Scheme.resHom_resHom]
    exact Scheme.resHom_refl _
  rw [← hkey]
  exact h1Cok_mk_resHom_right k X ⊤ U₁ _

/-- **The mirror**: if the *second* chart is everything the `H¹` also vanishes, via
`h1Cok_mk_resHom_left`. -/
theorem h1Cok_eq_zero_of_right_eq_top (h : U₁ = ⊤) (c : H1Cok k X U₀ U₁) : c = 0 := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  subst h
  have hle : U₀ ≤ U₀ ⊓ (⊤ : X.Opens) := le_inf le_rfl le_top
  have hkey : X.resHom (inf_le_left : U₀ ⊓ (⊤ : X.Opens) ≤ U₀) (X.resHom hle s) = s := by
    rw [Scheme.resHom_resHom]
    exact Scheme.resHom_refl _
  rw [← hkey]
  exact h1Cok_mk_resHom_left k X U₀ ⊤ _

/-- **A nonzero `H¹` class forces BOTH charts to be proper** — the conclusion
`Scheme.AffineTwoCover.surjective_selector_iff` asks for, obtained from cohomology rather than
from `¬ IsAffine`.

At the Wave-5 curve the tree identifies `H¹(𝒪_C)` with the genus, so a consumer holding `g ≠ 0`
gets both conditions with no appeal to non-affineness — which is what makes this an alternative to
the (expensive, see `I-0729`) dimension-theoretic route. -/
theorem ne_top_of_h1Cok_ne_zero {c : H1Cok k X U₀ U₁} (hc : c ≠ 0) :
    U₀ ≠ ⊤ ∧ U₁ ≠ ⊤ :=
  ⟨fun h => hc (h1Cok_eq_zero_of_left_eq_top k X U₀ U₁ h c),
    fun h => hc (h1Cok_eq_zero_of_right_eq_top k X U₀ U₁ h c)⟩

end TwoCover

end AlgebraicGeometry
