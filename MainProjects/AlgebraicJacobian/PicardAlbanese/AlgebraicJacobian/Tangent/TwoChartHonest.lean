/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TwoChartSelector

/-!
# A two-chart cover of a NON-AFFINE scheme is honestly two-chart (W5-T4's other consumer input)

`Scheme.AffineTwoCover.surjective_selector_iff` (`Tangent/TwoChartSelector.lean`) reduces the
selector's surjectivity — the `hsel` binder of `Scheme.map_twoChartClass` — to
**`V₀ ≠ ⊥ ∧ V₀ ≠ ⊤`**. Its docstring records that neither conjunct is proved anywhere, that both
hold for the Wave-5 curve *by an argument* ("a curve is non-empty; a proper positive-dimensional
scheme over a field is not affine"), and that a consumer "must still produce those two facts".

This file produces them, from **one** hypothesis and not two:

```
¬ IsAffine Y  ⟹  Function.Surjective D.selector
```

(`surjective_selector_of_not_isAffine`).

## Both conjuncts are the SAME statement about the ambient scheme

The reason the residue was two facts is that it was read off the *characterization* rather than
traced to its cause. Both degeneracies make `Y` affine:

* `V₀ = ⊤` — then `⊤` is an affine open, and `Y ≅ ↑⊤` (`Scheme.topIso`), so `Y` is affine.
* `V₀ = ⊥` — then `sup_eq_top` forces `V₁ = ⊤`, and the same argument applies to the *other* chart.

So a cover of a non-affine scheme is automatically honest, with no reference to curves, fields,
dimension, or non-emptiness. Note in particular that **non-emptiness of the curve is not needed**:
the empty scheme *is* affine (`Spec 0`), so `¬ IsAffine Y` already excludes it. The predicted
proof named non-emptiness as one of two geometric inputs; it is a consequence of the one input, not
a second one.

> **A hypothesis pair read off a characterization is not necessarily two obligations.**
> `surjective_selector_iff` is an honest `↔`, and the two conjuncts on its right are genuinely
> different *conditions on `V₀`*. But they have a common cause one level up, and the consumer's real
> input is that cause. Before shipping "the consumer owes A and B", ask what A and B are both
> symptoms of — here the answer removed one of the two and made the survivor a single instance
> lookup. Cf. `I-0679` on satisfiable-but-unwitnessed hypotheses: the fix was not to witness each,
> it was to find what witnesses both.

## What this leaves for the Wave-5 instance

Exactly one thing: **`¬ IsAffine C.left`** for the smooth proper positive-dimensional curve. That is
a real geometric statement and it is NOT proved here — a search of this project, the sibling and
mathlib finds nothing concluding it (mathlib has `IsAffine`-of-affine-hom instances and the
`Proper` API, but no "proper positive-dimensional over a field ⟹ not affine"). It is one statement
rather than the previous two, and it is the honest form: the two-chart machinery needs the curve to
*not* be coverable by one chart, which is what "not affine" says.

## Main declarations

* `AlgebraicGeometry.Scheme.AffineTwoCover.isAffine_of_V₀_eq_top` — `V₀ = ⊤` ⟹ `Y` affine.
* `AlgebraicGeometry.Scheme.AffineTwoCover.isAffine_of_V₀_eq_bot` — `V₀ = ⊥` ⟹ `Y` affine.
* `AlgebraicGeometry.Scheme.AffineTwoCover.surjective_selector_of_not_isAffine` — hence the
  selector is surjective as soon as `Y` is not affine.

Reference: `informal/w5-t4-worksheet.md` §§6.20(3a), 6.25, 6.27.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

namespace AffineTwoCover

variable {Y : Scheme.{u}} (D : Y.AffineTwoCover)

/-- **If the first chart is everything, the scheme is affine.** `IsAffineOpen ⊤` means the open
subscheme `↑⊤` is affine, and `Scheme.topIso : ↑⊤ ≅ Y` transports that to `Y` along
`IsAffine.of_isIso`. -/
theorem isAffine_of_V₀_eq_top (h : D.V₀ = ⊤) : IsAffine Y := by
  have h2 := D.isAffineOpen₀
  rw [h] at h2
  haveI : IsAffine (↑(⊤ : Y.Opens)) := h2
  exact IsAffine.of_isIso Y.topIso.inv

/-- **If the first chart is empty, the scheme is affine** — because then `sup_eq_top` makes the
*second* chart everything, and `isAffineOpen₁` plays the role `isAffineOpen₀` played above. -/
theorem isAffine_of_V₀_eq_bot (h : D.V₀ = ⊥) : IsAffine Y := by
  have hv1 : D.V₁ = ⊤ := by
    have hs := D.sup_eq_top
    rw [h, bot_sup_eq] at hs
    exact hs
  have h2 := D.isAffineOpen₁
  rw [hv1] at h2
  haveI : IsAffine (↑(⊤ : Y.Opens)) := h2
  exact IsAffine.of_isIso Y.topIso.inv

/-- **The selector of a two-chart cover of a NON-AFFINE scheme is surjective** — the `hsel` binder
of `Scheme.map_twoChartClass`, from one hypothesis about the ambient scheme rather than two about
the first chart.

`surjective_selector_iff` asks for `V₀ ≠ ⊥ ∧ V₀ ≠ ⊤`; both degeneracies make `Y` affine
(`isAffine_of_V₀_eq_bot`, `isAffine_of_V₀_eq_top`), so `¬ IsAffine Y` supplies both at once. No
non-emptiness hypothesis is needed: the empty scheme is affine, hence already excluded. -/
theorem surjective_selector_of_not_isAffine (h : ¬ IsAffine Y) :
    Function.Surjective D.selector :=
  (D.surjective_selector_iff).mpr
    ⟨fun hbot => h (D.isAffine_of_V₀_eq_bot hbot), fun htop => h (D.isAffine_of_V₀_eq_top htop)⟩

end AffineTwoCover

end Scheme

end AlgebraicGeometry
