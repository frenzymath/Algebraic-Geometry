/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.DualNumberFstKernel
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# `Spec` of `ε ↦ 0` is a homeomorphism on points (W5-T4, one of the two named consumer inputs)

`Tangent/TwoChartSelector.lean` closes `Scheme.map_twoChartClass`'s second surjectivity binder
`hsel'` by `surjective_selector_comp`, which relocates the obligation to
**`Function.Surjective f.base` at the `ε ↦ 0` morphism**. Its docstring then names that last step as
what the consumer must supply, and inbox `I-0688`'s review recorded it as *satisfiable and
unwitnessed*. This file witnesses it.

`specMap_fstRingHom_base_surjective` is the binder as a consumer needs it; the sharper
`isHomeomorph_comap_fstRingHom` is free on the way and worth having, since it says the two spaces
have the *same* points and not merely that one surjects onto the other.

## Why this is not the one-point-space argument the worksheet predicted

The prior sizing of this item (worksheet §6.25, and `TwoChartSelector`'s own docstring) was *"a
bijection of one-point spaces, `Spec k → Spec k[ε]`"*. That argument is correct **over a field** and
is not what got proved: the statement here is over an **arbitrary commutative ring** `A`, where
`Spec A[ε]` has as many points as `Spec A` and neither is a point.

The general fact is `PrimeSpectrum.isHomeomorph_comap` (mathlib): `comap f` is a homeomorphism as
soon as every element of the target has a power in the range of `f` and `ker f` lies in the
nilradical. For `fst : A[ε] → A` both are immediate — `fst` is *surjective* (`n = 1`), and
`ker fst = (ε)` with `ε² = 0`, so `ker_fstRingHom_le_nilradical` is one `rw` and `⟨2, by simp⟩`.

> **The one-point argument was true and would have been the wrong proof.** It would have produced a
> lemma pinned to a field, needing a base-change or a re-derivation the moment the tangent
> computation is instantiated at a chart's section ring rather than at `k`. Searching for the
> *mechanism* (nilpotent kernel ⟹ same spectrum) instead of formalising the *available picture*
> (both sides are points) gives the ring-general statement for less work. Cf. `I-0679`'s family:
> when an obligation is recorded as "easy for our case", check whether the general case is easier.

## What this does NOT close

The other named consumer input of T4 — `V₀ ≠ ⊥ ∧ V₀ ≠ ⊤` for the Wave-5 curve's two-chart cover
(`Scheme.AffineTwoCover.surjective_selector_iff`) — is untouched and remains unwitnessed. It is a
genuinely geometric statement (the curve is non-empty and not affine), not a spectrum computation.

Nothing here is stated at the *scheme morphism* `overDualNumberZero` of the Wave-5 test object; the
bridge from `Spec.map (ofHom fstRingHom)` to that morphism is
`Tangent/TwoChartSelector.lean`'s `overSpecMap_eps_eq_overDualNumberZero` plus
`Tangent/DualNumberUnitTransport.lean`, and composing them is the consumer's step.

## Main declarations

* `TruncExpCech.ker_fstRingHom_le_nilradical` — `ker (ε ↦ 0) ≤ nilradical A[ε]`.
* `TruncExpCech.isHomeomorph_comap_fstRingHom` — `comap fst` is a homeomorphism.
* `TruncExpCech.specMap_fstRingHom_base_surjective` — hence `Spec.map (ε ↦ 0)` is surjective on
  points, which is the binder.

Reference: `informal/w5-t4-worksheet.md` §§6.25, 6.27.
-/

set_option autoImplicit false

universe u

open CategoryTheory TrivSqZeroExt DualNumber

namespace TruncExpCech

variable {A : Type u} [CommRing A]

/-- **The kernel of `ε ↦ 0` consists of nilpotents.** `ker fstRingHom = (ε)` (`ker_fstRingHom`) and
`ε² = 0`, so the generator is nilpotent of order 2 and `Ideal.span_le` finishes. -/
theorem ker_fstRingHom_le_nilradical :
    RingHom.ker (fstRingHom (R := A)) ≤ nilradical (DualNumber A) := by
  rw [ker_fstRingHom, Ideal.span_le, Set.singleton_subset_iff]
  exact ⟨2, by simp⟩

/-- **`Spec` of `ε ↦ 0` is a homeomorphism** — the thickened affine line has exactly the points of
the line it thickens.

`PrimeSpectrum.isHomeomorph_comap` needs two inputs: every element of the source ring has a power in
the range (here `n = 1`, since `fst` is surjective) and the kernel is contained in the nilradical
(`ker_fstRingHom_le_nilradical`). Both are cheap because `ε` is nilpotent, and neither needs `A` to
be a field. -/
theorem isHomeomorph_comap_fstRingHom :
    IsHomeomorph (PrimeSpectrum.comap (fstRingHom (R := A))) :=
  PrimeSpectrum.isHomeomorph_comap _
    (fun x => ⟨1, by simpa using fstRingHom_surjective x⟩) ker_fstRingHom_le_nilradical

/-- **The binder `Tangent/TwoChartSelector.lean` names**: `Spec.map (ε ↦ 0)` is surjective on
points, so `Scheme.surjective_selector_comp` applies at the `ε ↦ 0` morphism and
`Scheme.map_twoChartClass`'s second surjectivity hypothesis `hsel'` has a producer.

`Spec.map`'s underlying map **is** `PrimeSpectrum.comap` definitionally, so this is
`isHomeomorph_comap_fstRingHom.surjective` by `exact` — `simpa` actually *fails* here, having
rewritten the goal into a shape where the two carriers no longer match. (One more instance of
`I-0685`: when a term should apply directly, try it before normalising.) -/
theorem specMap_fstRingHom_base_surjective :
    Function.Surjective
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (fstRingHom (R := A)))).base :=
  isHomeomorph_comap_fstRingHom.surjective

end TruncExpCech
