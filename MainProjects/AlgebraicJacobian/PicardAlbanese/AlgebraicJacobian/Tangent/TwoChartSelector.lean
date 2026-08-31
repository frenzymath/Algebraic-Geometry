/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TwoChartQuotientNaturality
import AlgebraicJacobian.Tangent.DualNumberCarrierReduction
import AlgebraicJacobian.Tangent.DualNumberTestObject
import AlgebraicJacobian.Picard.AffineTwoCover

/-!
# The `Bool`-indexed family and selector of an affine two-chart cover (W5-T4, item (3a))

Everything in `Tangent/TwoChartCechPic.lean` and its successors is stated for a family
`V : Bool → X.Opens` together with a selector `sel : X → Bool` satisfying `x ∈ V (sel x)`, and the
quotient-level results additionally need `Function.Surjective sel`. The Wave-5 consumer, by
contrast, holds a `Scheme.AffineTwoCover` (two named affine opens with affine overlap), which is
what `Cohomology/RelativeTwoCover.lean`'s `relCover` produces. This file is the bridge.

## The finding: `hsel` is a real side condition, and it is exactly non-triviality

`informal/w5-t4-worksheet.md` §6.20(3a) flagged that selector surjectivity "is a real side
condition, not bookkeeping". Measured here, it is sharper than that: for the canonical selector
`sel x = if x ∈ V₀ then false else true`,

```
Function.Surjective sel  ↔  V₀ ≠ ⊥ ∧ V₀ ≠ ⊤
```

(`Scheme.AffineTwoCover.surjective_selector_iff`). Both directions are *genuine* content rather than
an artefact of this particular selector:

* `V₀ = ⊥` makes `sel` constantly `true` — and then the "two-chart" cover is the one-chart cover
  `V₁ = ⊤`, whose Čech `Ȟ¹` is trivial for a different reason;
* `V₀ = ⊤` makes `sel` constantly `false`, i.e. `X` is covered by one *affine* chart, so `X` is
  affine.

So a two-chart argument that needs `hsel` is asking for the cover to be **honestly two-chart**, and
that is the right hypothesis to carry rather than to hide. For the Wave-5 curve both conditions hold
— a curve is non-empty, and a proper positive-dimensional scheme over a field is not affine — but
neither is free, and neither is proved here: they are supplied by the consumer as
`h0 : V₀ ≠ ⊥` and `h1 : V₀ ≠ ⊤`.

## Implementation notes

The selector is defined by `Classical.dec`-backed `if x ∈ V₀`, so `hmem` is a two-case `split_ifs`
using `sup_eq_top` for the `x ∉ V₀` branch: a point of `⊤ = V₀ ⊔ V₁` outside `V₀` lies in `V₁`
(`TopologicalSpace.Opens.mem_sup`).

The family is `boolFamily D := fun s ↦ bif s then D.V₁ else D.V₀`, chosen over a `match` so that
`boolFamily D false` and `boolFamily D true` reduce by `rfl` and the `⊓` of the two is
*syntactically* `D.V₀ ⊓ D.V₁` — which is what lets the landed affineness field `isAffineOpen_inf`
be used at the overlap with no transport. That reduction is the whole reason this file is short.

## Main declarations

* `AlgebraicGeometry.Scheme.AffineTwoCover.boolFamily` — the `Bool`-indexed family, with
  `boolFamily_false`, `boolFamily_true` and `boolFamily_inf` (all `rfl`).
* `AlgebraicGeometry.Scheme.AffineTwoCover.selector` — the canonical selector, with
  `selector_mem` (the `hmem` clause).
* `AlgebraicGeometry.Scheme.AffineTwoCover.surjective_selector_iff` — **the side condition,
  characterized**: surjectivity is `V₀ ≠ ⊥ ∧ V₀ ≠ ⊤`.
* `AlgebraicGeometry.Scheme.AffineTwoCover.isAffineOpen_boolFamily` — each chart of the family is
  affine, and `isAffineOpen_boolFamily_inf` for the overlap.
* `AlgebraicGeometry.Scheme.surjective_selector_comp` — **the producer for the second surjectivity
  binder** `hsel'` of `Scheme.map_twoChartClass`, which inbox `I-0688` found had none: selector
  surjectivity at the pulled-back end follows from surjectivity at the base end plus surjectivity of
  `f.base`.
* `AlgebraicGeometry.overSpecMap_eps_eq_overDualNumberZero` — **(3b)**: the `ε ↦ 0` test-object
  morphism and the coefficient comparison `overSpecMap k[ε] k` have the *same underlying scheme
  morphism*, by `rfl` under the `scoped` `epsAlgebra`. It says **nothing** about the source objects
  — see its docstring for the withdrawn claim that it did.
* `AlgebraicGeometry.ofHom_algebraMap_self_eq_id` / `specMap_algebraMap_self_eq_id` — the (3c)
  measurement: the first is `rfl`, the second is **not** (it needs `Spec.map_id`), which is why
  (3c) is a genuine object transport and not free. See that docstring for the retraction it forces.

## What this file does not contain — and where it now lives (updated)

An identification of `relCurveMap C k[ε] k` with `(C ◁ overDualNumberZero k).left`. Those two have
**different types** — a kernel check refuted the naive attempt — because their sources are the
monoidal unit and `overSpec k k` respectively, which are equal objects but not definitionally equal.

**That transport, (3c), is now BUILT**: `Tangent/DualNumberUnitTransport.lean`
(`overDualNumberZero_eq`, `whiskerLeft_overDualNumberZero_left`, `isIso_transportLeft`). The seam
turned out to be an **isomorphism** `Over.mk (𝟙 (Spec k)) ≅ overSpec k k` rather than an `eqToHom`,
so it travels in both directions; see `informal/w5-t4-worksheet.md` §6.26. The measurements below
(`ofHom_algebraMap_self_eq_id`, `specMap_algebraMap_self_eq_id`) are what that file consumes, and
they remain the honest record of why (3c) was not free.

Reference: `informal/w5-t4-worksheet.md` §§6.20(3a), 6.23, 6.26.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

namespace Scheme

namespace AffineTwoCover

variable {Y : Scheme.{u}} (D : Y.AffineTwoCover)

/-! ## The `Bool`-indexed family -/

/-- **The two charts as a `Bool`-indexed family.** Spelled with `cond` so that both values, and
their `⊓`, reduce by `rfl` — see the module docstring. -/
def boolFamily : Bool → Y.Opens := fun s ↦ bif s then D.V₁ else D.V₀

@[simp] theorem boolFamily_false : D.boolFamily false = D.V₀ := rfl

@[simp] theorem boolFamily_true : D.boolFamily true = D.V₁ := rfl

/-- The overlap of the family **is** the overlap of the cover, syntactically. -/
@[simp] theorem boolFamily_inf : D.boolFamily false ⊓ D.boolFamily true = D.V₀ ⊓ D.V₁ := rfl

/-- Each chart of the family is affine. -/
theorem isAffineOpen_boolFamily (s : Bool) : IsAffineOpen (D.boolFamily s) := by
  cases s
  · exact D.isAffineOpen₀
  · exact D.isAffineOpen₁

/-- The overlap of the family is affine. -/
theorem isAffineOpen_boolFamily_inf :
    IsAffineOpen (D.boolFamily false ⊓ D.boolFamily true) :=
  D.isAffineOpen_inf

/-! ## The selector -/

open Classical in
/-- **The canonical chart selector**: send `x` to the first chart if it lies there, else to the
second. -/
noncomputable def selector : Y → Bool := fun x ↦ if x ∈ D.V₀ then false else true

/-- The selector selects a chart containing the point — the `hmem` clause every two-chart
declaration takes. The `x ∉ V₀` branch is where `sup_eq_top` is spent. -/
theorem selector_mem (x : Y) : x ∈ D.boolFamily (D.selector x) := by
  classical
  rw [selector]
  split_ifs with h
  · exact h
  · have hx : x ∈ (⊤ : Y.Opens) := trivial
    rw [← D.sup_eq_top] at hx
    exact (TopologicalSpace.Opens.mem_sup.mp hx).resolve_left h

/-! ## The side condition, characterized -/

/-- **The selector is surjective exactly when the first chart is neither empty nor everything.**

This is the measurement `informal/w5-t4-worksheet.md` §6.20(3a) called for, and it sharpens the flag
raised there: `hsel` is not bookkeeping, it is the statement that the cover is *honestly*
two-chart. `V₀ = ⊥` degenerates to the one-chart cover `V₁ = ⊤`; `V₀ = ⊤` says `X` is covered by a
single affine chart, hence affine.

Neither condition is proved here — for the Wave-5 curve both hold (a curve is non-empty; a proper
positive-dimensional scheme over a field is not affine) but each is a real geometric input, and the
consumer supplies them.

**And "both hold for the curve" is at present an argument, not a witness in this project** — the
distinction inbox `I-0679` names (a hypothesis can be satisfiable and yet witnessed nowhere, which
every ordinary check reports as healthy). Measured: `Scheme.AffineTwoCover.nonempty_of_curve`
supplies a cover of the curve but says nothing about either chart being proper or non-empty, and a
search of both projects and mathlib finds no declaration concluding `V₀ ≠ ⊥` or `V₀ ≠ ⊤` for it. So a
consumer instantiating this lemma at the Wave-5 curve **must still produce those two facts**, and
should not expect to find them lying about. Recorded rather than papered over. -/
theorem surjective_selector_iff :
    Function.Surjective D.selector ↔ D.V₀ ≠ ⊥ ∧ D.V₀ ≠ ⊤ := by
  classical
  constructor
  · intro hs
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hs false
      rw [selector] at hx
      have hxV : x ∈ D.V₀ := by by_contra h; simp [h] at hx
      intro hbot
      rw [hbot] at hxV
      exact hxV
    · obtain ⟨x, hx⟩ := hs true
      rw [selector] at hx
      have hxV : x ∉ D.V₀ := by by_contra h; simp [h] at hx
      intro htop
      exact hxV (htop ▸ trivial)
  · rintro ⟨h0, h1⟩ s
    cases s
    · obtain ⟨x, hx⟩ : ∃ x, x ∈ D.V₀ := by
        by_contra hc
        simp only [not_exists] at hc
        exact h0 (by ext x; simpa using hc x)
      exact ⟨x, by rw [selector, if_pos hx]⟩
    · obtain ⟨x, hx⟩ : ∃ x, x ∉ D.V₀ := by
        by_contra hc
        simp only [not_exists, not_not] at hc
        exact h1 (by ext x; simpa using hc x)
      exact ⟨x, by rw [selector, if_neg hx]⟩

end AffineTwoCover

end Scheme

/-! ## The SECOND surjectivity binder, and a producer for it

`Scheme.map_twoChartClass` (`Tangent/TwoChartQuotientNaturality.lean`) takes **two** surjectivity
hypotheses — `hsel` for the selector on `Y` and `hsel'` for `sel ∘ f.base` on `X`. A reviewer
(inbox `I-0688`) found that the second had **no producer anywhere in the project**: grepping `hsel'`
returns only occurrences inside the declaration itself, so every consumer would have had to invent
it. That is an obligation *moved*, not discharged, and a carrier-level "level check" cannot see it
because binders do not appear in carriers.

The lemma below is the producer. It is deliberately stated as the general composition fact rather
than at `f = ε ↦ 0`, because that is where the content is: **surjectivity of the selector at the
pulled-back end follows from surjectivity at the base end together with surjectivity of `f.base`.**
So a consumer owes a topological fact about `f`, not a new combinatorial one about charts.

For the Wave-5 instance `f = ` the `ε ↦ 0` map `C ⟶ C_ε`, `f.base` is surjective — it is a
homeomorphism on points, `Spec k → Spec k[ε]` being a bijection of one-point spaces (the standing
observation of `Tangent/RelPicPointTest.lean`). That last step is **not** proved here; it is named as
what the consumer supplies, in the same spirit as `V₀ ≠ ⊥`/`V₀ ≠ ⊤` above. -/
theorem Scheme.surjective_selector_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (sel : Y → Bool)
    (hsel : Function.Surjective sel) (hf : Function.Surjective f.base) :
    Function.Surjective (fun x ↦ sel (f.base x)) :=
  hsel.comp hf

/-! ## (3b): the `ε ↦ 0` test-object morphism IS the coefficient comparison -/

section EpsilonZero

open TruncExpCech.EpsilonReduction DualNumber

variable (k : Type u) [Field k]

/-- **(3b): `overDualNumberZero` is `overSpecMap k[ε] k`**, hence its whiskering is
`relCurveMap C k[ε] k`.

This is the identification inbox `I-0630`(3) reported as absent: `(b-coeff)`
(`Over.relSectionsMap_dualNumberSections`) is a statement about `relSectionsMap`, which is built
from `relCurveMap`, whereas the test-object side of the tangent computation is phrased with
`overDualNumberZero`. Without this lemma the two are different morphisms that happen to look alike.

**And it is a `rfl`, once the `scoped` instance is open.** `overSpecMap k[ε] k` is
`Over.homMk (Spec.map (ofHom (algebraMap k[ε] k)))`, `overDualNumberZero k` is
`Over.homMk (Spec.map (ofHom (TruncExpCech.fstRingHom)))`, and under `epsAlgebra` the structure map
`algebraMap k[ε] k` **is** `TrivSqZeroExt.fst` definitionally
(`algebraMap_eps_eq_fst`) — so the two `RingHom`s are equal, and `Over.homMk`'s proof field is
irrelevant.

**But this is a statement about the two MORPHISMS ONLY, and their source OBJECTS do not agree
definitionally.** An earlier version of this docstring added *"the source objects agree for the same
reason: `overSpec k k` is `Over.mk (Spec.map (ofHom (algebraMap k k)))` and
`algebraMap k k = RingHom.id k`"*. **That sentence was false and is withdrawn** (reviewer finding,
inbox `I-0687`): the ring-level equation is indeed `rfl`, but `Spec.map` of it is not, so
`Over.mk (Spec.map (ofHom (algebraMap k k)))` and `Over.mk (𝟙 (Spec k))` are equal objects that are
**not** definitionally equal. See `specMap_algebraMap_self_eq_id` immediately below, and
`informal/w5-t4-worksheet.md` §6.23. Do not use this lemma as if it identified the objects.

So the seam that looked like missing infrastructure is, *at the level of the morphisms*, a
**spelling** difference across a deliberately-`scoped` instance — the `I-0567`/`I-0634` family: the
thing exists upstream (here: in the tree), it is just not in ambient scope. The object-level seam is
a separate, genuine obligation. Recorded in `informal/w5-t4-worksheet.md` §§6.22–6.23. -/
theorem overSpecMap_eps_eq_overDualNumberZero :
    (overSpecMap (k := k) (DualNumber k) k).left = (overDualNumberZero k).left :=
  rfl

/-- **(3c) IS NOT FREE, and this is the measurement** — recorded as a theorem about the *source
objects* rather than left as a claim in prose.

`overDualNumberZero k` has source the monoidal unit `Over.mk (𝟙 (Spec k))`, whereas
`overSpecMap k[ε] k` has source `overSpec k k = Over.mk (Spec.map (ofHom (algebraMap k k)))`. The
two structure morphisms agree only *propositionally*:

* `CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k)` **is** `rfl` (this lemma), but
* `Spec.map (ofHom (algebraMap k k)) = 𝟙 (Spec k)` is **NOT** `rfl` — it needs `Spec.map_id`,
  because `Spec.map` is functorial only up to propositional equality.

So `overSpec k k` and the monoidal unit are equal objects but not *definitionally* equal ones, and
consequently `relCurveMap C k[ε] k` and `(C ◁ overDualNumberZero k).left` have **different types**:
`relCurve C k ⟶ relCurve C k[ε]` against
`(C ⊗ Over.mk (𝟙 _)).left ⟶ (C ⊗ overDualNumber k).left`. A kernel check refuted the `congr`-plus-
`rfl` attempt with exactly that type mismatch.

**This retracts `informal/w5-t4-worksheet.md` §6.22's claim that (3c) "is the same `rfl`" and that
item (3) is "two sub-items, not three".** It is three, and the third needs an object transport,
which is not built here but **is** built in `Tangent/DualNumberUnitTransport.lean` — as an
`Over.isoMk` along `Spec.map_id` plus a whiskering congruence, with **no `eqToHom`** (the two source
objects share their underlying scheme, so only the structure-morphism triangle needs `Spec.map_id`);
worksheet §6.26. What is true and useful here is the ring-level half below plus
`overSpecMap_eps_eq_overDualNumberZero` above, which is where the `ε ↦ 0` content actually lives and
which that transport consumes. -/
theorem ofHom_algebraMap_self_eq_id :
    CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) :=
  rfl

/-- The propositional identification of the two structure morphisms, which is what an object
transport for (3c) must be built from: `Spec.map` of the identity algebra map is the identity, by
`Spec.map_id` and **not** by `rfl`. -/
theorem specMap_algebraMap_self_eq_id :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [ofHom_algebraMap_self_eq_id, Spec.map_id]

end EpsilonZero

end AlgebraicGeometry
