/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TwoChartSelector

/-!
# (3c): the monoidal-unit transport at `ε ↦ 0` (W5-T4, intertwining item (3), last sub-item)

`Tangent/TwoChartSelector.lean` closed items (3a) and (3b) of `informal/w5-t4-worksheet.md` §6.20
and then **measured a wall** where a predecessor had claimed a `rfl`: the `ε ↦ 0` test-object
morphism `overDualNumberZero k` has source the **monoidal unit** `Over.mk (𝟙 (Spec k))`, whereas the
coefficient comparison `overSpecMap k[ε] k` has source `overSpec k k`. Those are equal objects that
are **not definitionally equal** — `Spec.map (ofHom (algebraMap k k)) = 𝟙 (Spec k)` is
`Spec.map_id`, a theorem, not `rfl` (`specMap_algebraMap_self_eq_id`). So `relCurveMap C k[ε] k` and
`(C ◁ overDualNumberZero k).left` have **different types**, and no `congr` closes a type mismatch.
Worksheet §6.23 recorded that retraction and named the residue: *an object transport along
`Spec.map_id`, then a whiskering congruence.* This file builds it.

## The finding: the transport is an ISO, not an `eqToHom`, and the factorisation is one `rw`

The predecessor's diagnosis prescribed `eqToHom`/`Over.isoMk` along `Spec.map_id`. Measured, the
`Over.isoMk` half is the whole story and the `eqToHom` half is never needed:

* `unitIso k : Over.mk (𝟙 (Spec k)) ≅ overSpec k k` is `Over.isoMk (Iso.refl _)` — the two objects
  have the *same* underlying scheme `Spec k` (that much **is** `rfl`); only the two structure
  morphisms to `Spec k` differ, and `specMap_algebraMap_self_eq_id` is exactly the triangle.
* `overDualNumberZero k = (unitIso k).hom ≫ overSpecMap k[ε] k` (`overDualNumberZero_eq`) —
  after `Over.OverMorphism.ext` and `Category.id_comp` this is the landed **(3b)** lemma
  `overSpecMap_eps_eq_overDualNumberZero`, reversed.
* Whiskering is functorial, so the same factorisation holds after `C ◁ -` and after `.left`
  (`whiskerLeft_overDualNumberZero`, `whiskerLeft_overDualNumberZero_left`) — and the second factor
  of the `.left` form is `relCurveMap C k[ε] k` **on the nose**, which is the identification
  worksheet §6.24 called "the step that turns two aligned diagrams into one commuting one".

**So (3c) is a transport by an isomorphism**: `transportLeft C` below is an `IsIso`
(`isIso_transportLeft`), whiskering an iso being an iso and `Over.forget` preserving that. A
consumer therefore does not merely *rewrite* along the seam, it may **invert** it — which is what a
kernel comparison needs, since an injectivity/kernel statement must travel in both directions.

## Why this needed a named definition rather than a `rw` at the use site

`(C ◁ (unitIso k).hom).left` and `transportLeft C` are the same term, but the *spelling* decides
whether the composite with `relCurveMap` elaborates: written inline, Lean assigns the composite's
left factor a type ending in `(C ⊗ overSpec k k).left`, and `relCurveMap C k[ε] k` is typed
`relCurve C k ⟶ relCurve C k[ε]`. Those unfold to the same scheme, so the goal *is* type-correct,
but `rw` reports

```
Application type mismatch … but is expected to have type
  (C ⊗ overSpec k k).left ⟶ relCurve C k[ε]
Note: The target expression is not type-correct under the `instances` transparency level
```

which reads like a broken goal and is not one (inbox `I-0685`: *rfl-equal spellings block `rw`*).
Giving the transport a definition whose **declared type** already says `⟶ relCurve C k` fixes the
spelling once, and `whiskerLeft_overDualNumberZero_left` then typechecks as a restatement of the
whiskering form — proof term `whiskerLeft_overDualNumberZero_left'`, no transport, no `eqToHom`.

## Main declarations

* `AlgebraicGeometry.unitIso` — the source-object seam, `Over.mk (𝟙 (Spec k)) ≅ overSpec k k`.
* `AlgebraicGeometry.overDualNumberZero_eq` — **(3c) at the test-object level**: `ε ↦ 0` factors as
  the seam followed by the coefficient comparison.
* `AlgebraicGeometry.whiskerLeft_overDualNumberZero` / `..._left` / `..._left'` — the same after
  `C ◁ -`, and after `.left` in both spellings.
* `AlgebraicGeometry.transportLeft` — the seam on relative curves,
  `(C ⊗ Over.mk (𝟙 (Spec k))).left ⟶ relCurve C k`, with `isIso_transportLeft`.

Reference: `informal/w5-t4-worksheet.md` §§6.20(3), 6.23, 6.24, 6.26.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

open TruncExpCech.EpsilonReduction DualNumber

variable (k : Type u) [Field k]

/-! ## The source-object seam -/

/-- **The monoidal unit of `Over (Spec k)` is `overSpec k k`, as an isomorphism.**

The two objects have the *same* underlying scheme `Spec k` — that is `rfl`, and is why
`Iso.refl` suffices for the left component. What is not `rfl`, and is the entire content of
worksheet §6.23's retraction, is that their structure morphisms agree: `Spec.map` of the identity
algebra map is the identity only *propositionally*
(`specMap_algebraMap_self_eq_id`, i.e. `Spec.map_id`). -/
noncomputable def unitIso : Over.mk (𝟙 (Spec (CommRingCat.of k))) ≅ overSpec k k :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (overSpec k k).hom = (Over.mk (𝟙 (Spec (CommRingCat.of k)))).hom
    rw [Category.id_comp]
    exact specMap_algebraMap_self_eq_id k)

@[simp]
theorem unitIso_hom_left : (unitIso k).hom.left = 𝟙 (Spec (CommRingCat.of k)) := rfl

/-! ## (3c): the factorisation -/

/-- **(3c), at the test-object level.** The `ε ↦ 0` morphism out of the monoidal unit factors as
the source-object seam followed by the coefficient comparison `overSpecMap k[ε] k`.

This is the object transport worksheet §6.23 named as T4's residue after retracting the claim that
it was free. It is *not* free — `unitIso` is where `Spec.map_id` is spent — but it is one lemma, and
once the seam is applied the remaining equation is exactly the landed **(3b)**
`overSpecMap_eps_eq_overDualNumberZero`. -/
theorem overDualNumberZero_eq :
    overDualNumberZero k = (unitIso k).hom ≫ overSpecMap (k := k) (DualNumber k) k := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (TruncExpCech.fstRingHom (R := k)))
      = (unitIso k).hom.left ≫ Spec.map (CommRingCat.ofHom (algebraMap (DualNumber k) k))
  change Spec.map (CommRingCat.ofHom (TruncExpCech.fstRingHom (R := k)))
      = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DualNumber k) k))
  rw [Category.id_comp]
  exact (overSpecMap_eps_eq_overDualNumberZero k).symm

variable (C : Over (Spec (CommRingCat.of k)))

/-- The factorisation after whiskering with the curve — `C ◁ -` is a functor, so this is
`overDualNumberZero_eq` transported by `whiskerLeft_comp`. -/
theorem whiskerLeft_overDualNumberZero :
    (C ◁ overDualNumberZero k)
      = (C ◁ (unitIso k).hom) ≫ (C ◁ overSpecMap (k := k) (DualNumber k) k) := by
  rw [← MonoidalCategory.whiskerLeft_comp, ← overDualNumberZero_eq]
  rfl

/-- The factorisation on the underlying schemes, in the whiskering spelling. -/
theorem whiskerLeft_overDualNumberZero_left' :
    (C ◁ overDualNumberZero k).left
      = (C ◁ (unitIso k).hom).left ≫ (C ◁ overSpecMap (k := k) (DualNumber k) k).left := by
  rw [← Over.comp_left, ← whiskerLeft_overDualNumberZero]

/-! ## The transport on relative curves -/

/-- **The (3c) seam on relative curves.** The same morphism as `(C ◁ (unitIso k).hom).left`, but
with its *declared* type ending in `relCurve C k` — which is what lets a composite with
`relCurveMap` elaborate. See the module docstring: the inline spelling is `rfl`-equal but blocks
`rw` under `instances` transparency. -/
noncomputable def transportLeft :
    (C ⊗ Over.mk (𝟙 (Spec (CommRingCat.of k)))).left ⟶ relCurve C k :=
  (C ◁ (unitIso k).hom).left

/-- **(3c) in the form the tangent computation reads**: the `ε ↦ 0` map of relative curves is the
seam followed by `relCurveMap C k[ε] k`.

This is the identification worksheet §6.24 isolated as the one missing link between the two aligned
diagrams — the engine's arrow (`unitsFst` on the dual-number carrier, reached through
`relCurveMap`) and item (1)'s arrow (`pullbackOverlapQuot` along the `ε ↦ 0` scheme morphism). -/
theorem whiskerLeft_overDualNumberZero_left :
    (C ◁ overDualNumberZero k).left
      = transportLeft k C ≫ relCurveMap C (DualNumber k) k :=
  whiskerLeft_overDualNumberZero_left' k C

/-- **The seam is invertible.** `unitIso` is an isomorphism, `C ◁ -` preserves isomorphisms, and
`Over.forget` carries the result to schemes. So a consumer may transport a kernel or injectivity
statement across the seam in *either* direction — which is what a kernel comparison needs, and what
an `eqToHom`-only diagnosis would not have made obvious. -/
instance isIso_transportLeft : IsIso (transportLeft k C) := by
  have h : IsIso (C ◁ (unitIso k).hom) :=
    inferInstanceAs (IsIso (whiskerLeftIso C (unitIso k)).hom)
  exact inferInstanceAs (IsIso ((Over.forget _).map (C ◁ (unitIso k).hom)))

end AlgebraicGeometry
