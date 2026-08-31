/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TwoChartCechPic

/-!
# Naturality of the two-chart comparison (W5-T4, the reduction square)

For a morphism of schemes `f : X ⟶ Y` and two opens `V : Bool → Y.Opens`, pulling back the
Čech Picard class of an overlap unit is the Čech Picard class of the pulled-back overlap
unit:

```
CechPic.map f (twoChartClassHom V sel hmem u)
  = twoChartClassHom (f ⁻¹ᵁ V ·) (sel ∘ f.base) _ (pullbackOverlapUnit f u)
```

(`Scheme.map_twoChartClassHom`).

## Why this file exists: "groups agreeing" is not "maps agreeing"

The Wave-5 tangent computation compares two things that, before this file, were only known to
agree *at each end*:

* the truncated-exponential engine of `Tangent/TruncExpCech.lean` computes the kernel of
  `TwoCover.unitsReduction` — a map **between** the two Čech unit quotients, at `Γ[ε]` and at
  `Γ`;
* the comparison `twoChartClass` of `Tangent/TwoChartCechPic.lean` maps *each* such quotient
  into its own `Scheme.CechPic`.

Nothing said those two commute, and the consumer computes a **kernel** — for which an
isomorphism at each end is worth nothing (the standing lesson of inbox `I-0571`, and the third
occurrence of that shape in this lane; compare
`AlgebraicGeometry.relPicMulEquivCechPic_relPicMap`, which records the same distinction for the
relative Picard group). This file supplies the missing square.

## Implementation notes

The square is **not** a cohomological statement: the two cocycles are equal *before* passing to
`H¹`, so `map_twoChartCocycle` is an equality of `OneCocycle`s and the class-level statement is
`congrArg` of it. Three facts make that work, all definitional:

* `(twoChartCover V sel hmem).pullback f` **is** `twoChartCover (f ⁻¹ᵁ V ·) (sel ∘ f.base) _`
  (`twoChartCover_pullback`, by `rfl`) — the pulled-back cover is not merely a refinement of
  the preimage-chart cover, it is that cover, so no comparison along a refinement is needed;
* `f ⁻¹ᵁ V false ⊓ f ⁻¹ᵁ V true` **is** `f ⁻¹ᵁ (V false ⊓ V true)`, so
  `pullbackOverlapUnit` is typed on the nose;
* the pair values commute with `unitsAppLE` in all four `Bool` cases by `map_one` / `map_inv`
  and the `unitsAppLE` calculus (`unitsAppLE_twoChartPairUnit`).

**A trap recorded so it is not re-hit** (the same family as the `▸` trap of
`Tangent/TwoChartCechPic.lean` and the `subst` lesson of `Tangent/TwoChartNormalize.lean`): in
`map_twoChartCocycle` the chart indices are the *terms* `sel (f.base x)`, and the type
`Γ(X, V (sel (f.base x)) ⊓ ⋯)ˣ` mentions them, so `cases h : sel (f.base x)` fails with
`generalize failed: result is not type correct`. The four-case split must therefore be factored
out into `unitsAppLE_twoChartPairUnit`, which quantifies over `s t : Bool` as honest variables,
and then applied at the instantiated indices.

## Main declarations

* `AlgebraicGeometry.Scheme.pullbackOverlapUnit` — the overlap unit pulled back along `f`.
* `AlgebraicGeometry.Scheme.twoChartCover_pullback` — the cover identification (`rfl`).
* `AlgebraicGeometry.Scheme.unitsAppLE_twoChartPairUnit` — the four-case core.
* `AlgebraicGeometry.Scheme.map_twoChartCocycle` — naturality at cocycle level (an equality).
* `AlgebraicGeometry.Scheme.map_twoChartClassHom` — **the reduction square**, at the level of
  `CechPic`.
* `AlgebraicGeometry.Scheme.map_twoChartClassHom_eq_one_iff` — the form a kernel computation
  consumes.

Reference: Kleiman, "The Picard scheme", §5, proof of Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §6.12.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}} {V : Bool → Y.Opens}

/-! ## The pulled-back overlap unit -/

/-- **The overlap unit pulled back along `f`.** A unit on `V false ⊓ V true` pulls back to a
unit on the overlap of the two *preimage* charts — typed on the nose, since
`f ⁻¹ᵁ V false ⊓ f ⁻¹ᵁ V true` and `f ⁻¹ᵁ (V false ⊓ V true)` are the same open by
definitional unfolding of preimages. -/
noncomputable def pullbackOverlapUnit (f : X ⟶ Y) (u : Γ(Y, V false ⊓ V true)ˣ) :
    Γ(X, (fun s ↦ f ⁻¹ᵁ V s) false ⊓ (fun s ↦ f ⁻¹ᵁ V s) true)ˣ :=
  f.unitsAppLE (V false ⊓ V true) (f ⁻¹ᵁ V false ⊓ f ⁻¹ᵁ V true) le_rfl u

/-- `pullbackOverlapUnit` is `unitsAppLE` of the first projection, definitionally — the
spelling `Hom.unitsAppLE` lemmas apply to. -/
theorem pullbackOverlapUnit_def (f : X ⟶ Y) (u : Γ(Y, V false ⊓ V true)ˣ) :
    pullbackOverlapUnit f u
      = f.unitsAppLE (V false ⊓ V true) (f ⁻¹ᵁ V false ⊓ f ⁻¹ᵁ V true) le_rfl u :=
  rfl

/-- The pullback of an overlap unit is multiplicative. -/
theorem pullbackOverlapUnit_mul (f : X ⟶ Y) (u v : Γ(Y, V false ⊓ V true)ˣ) :
    pullbackOverlapUnit f (u * v)
      = pullbackOverlapUnit f u * pullbackOverlapUnit f v :=
  map_mul _ u v

@[simp]
theorem pullbackOverlapUnit_one (f : X ⟶ Y) :
    pullbackOverlapUnit (V := V) f 1 = 1 :=
  map_one _

/-! ## The cover identification -/

/-- **The pulled-back two-chart cover is the two-chart cover of the preimages**, and it holds
by `rfl`: both pointed covers send `x` to `f ⁻¹ᵁ V (sel (f.base x))`.

This is what removes every transport from the naturality proof. Were the two covers merely
*mutually refining*, the classes below would live in different `unitsH1` groups and would have
to be compared along a refinement; they do not. -/
theorem twoChartCover_pullback (f : X ⟶ Y) (sel : Y → Bool) (hmem : ∀ y, y ∈ V (sel y)) :
    (twoChartCover V sel hmem).pullback f
      = twoChartCover (fun s ↦ f ⁻¹ᵁ V s) (fun x ↦ sel (f.base x))
          (fun x ↦ hmem (f.base x)) :=
  rfl

/-! ## The four-case core -/

/-- **The pair values commute with pullback.** Restricting the `(s,t)` pair value of `u` to an
open `T` of `X` through `f` is the `(s,t)` pair value of the pulled-back unit, restricted to
`T`.

All four `Bool` cases: the diagonals are `map_one`, the `(0,1)` case is the definition of
`pullbackOverlapUnit`, and the `(1,0)` case is `map_inv` together with the two `unitsAppLE`
commutation lemmas — which absorb the `inf_comm` restriction built into
`twoChartPairUnit`.

Stated with `s t : Bool` as *variables* on purpose: at the call site the indices are the terms
`sel (f.base x)`, which a dependent type mentions, so the case split has to happen here. See
the module docstring. -/
theorem unitsAppLE_twoChartPairUnit (f : X ⟶ Y) (u : Γ(Y, V false ⊓ V true)ˣ) (s t : Bool)
    (T : X.Opens) (e : T ≤ f ⁻¹ᵁ (V s ⊓ V t)) (h : T ≤ f ⁻¹ᵁ V s ⊓ f ⁻¹ᵁ V t) :
    f.unitsAppLE (V s ⊓ V t) T e (twoChartPairUnit u s t)
      = X.unitsRestrict h
          (twoChartPairUnit (V := fun s ↦ f ⁻¹ᵁ V s) (pullbackOverlapUnit f u) s t) := by
  cases s <;> cases t <;>
    simp only [pullbackOverlapUnit, twoChartPairUnit, map_one, map_inv,
      Scheme.Hom.unitsAppLE_map, Scheme.Hom.map_unitsAppLE]

/-! ## Naturality, at cocycle level and at the level of `CechPic` -/

/-- **Naturality of the two-chart cocycle** — an *equality* of unit `1`-cocycles on the
pulled-back cover, not merely a cohomology relation. Everything cohomological in the reduction
square is therefore vacuous. -/
theorem map_twoChartCocycle (f : X ⟶ Y) (sel : Y → Bool) (hmem : ∀ y, y ∈ V (sel y))
    (u : Γ(Y, V false ⊓ V true)ˣ) :
    f.pullbackUnitsCocycle (twoChartCocycle u sel hmem)
      = twoChartCocycle (V := fun s ↦ f ⁻¹ᵁ V s) (pullbackOverlapUnit f u)
          (fun x ↦ sel (f.base x)) (fun x ↦ hmem (f.base x)) := by
  ext x y T a b
  change f.unitsAppLE _ T _ (unitsEvInf (twoChartCocycle u sel hmem) (f.base x) (f.base y))
    = X.unitsRestrict _ (twoChartPairUnit (V := fun s ↦ f ⁻¹ᵁ V s)
        (pullbackOverlapUnit f u) (sel (f.base x)) (sel (f.base y)))
  rw [twoChartCocycle_unitsEvInf]
  exact unitsAppLE_twoChartPairUnit f u (sel (f.base x)) (sel (f.base y)) T _ _

/-- **THE REDUCTION SQUARE.** The comparison `twoChartClassHom` is natural in the scheme:
pulling back the Čech Picard class of an overlap unit gives the class of the pulled-back
overlap unit.

No affineness, no dual numbers, no curve, and no `Function.Surjective sel` — so this holds in
particular at the `ε ↦ 0` map, which is the instance the Wave-5 kernel computation consumes
(`Tangent/TruncExpCech.lean`'s `cechUnitsReduction`), but it is not special to it.

This is what makes the T2 engine and the two-chart comparison compose: without it the two are
known only to agree at each *end* of the reduction, which says nothing about its **kernel** —
and the kernel is the whole computation. See `informal/w5-t4-worksheet.md` §6.12. -/
theorem map_twoChartClassHom (f : X ⟶ Y) (sel : Y → Bool) (hmem : ∀ y, y ∈ V (sel y))
    (u : Γ(Y, V false ⊓ V true)ˣ) :
    Scheme.CechPic.map f (twoChartClassHom V sel hmem u)
      = twoChartClassHom (fun s ↦ f ⁻¹ᵁ V s) (fun x ↦ sel (f.base x))
          (fun x ↦ hmem (f.base x)) (pullbackOverlapUnit f u) := by
  rw [twoChartClassHom_apply, Scheme.CechPic.map_mk, Scheme.Hom.pullbackUnitsH1_class,
    twoChartClassHom_apply, map_twoChartCocycle]
  rfl

/-- **The form a kernel computation consumes**: the class of `u` dies under `CechPic.map f`
exactly when the class of the pulled-back unit is trivial. Immediate from
`map_twoChartClassHom`; recorded separately because the `ε`-kernel statement is phrased this
way. -/
theorem map_twoChartClassHom_eq_one_iff (f : X ⟶ Y) (sel : Y → Bool)
    (hmem : ∀ y, y ∈ V (sel y)) (u : Γ(Y, V false ⊓ V true)ˣ) :
    Scheme.CechPic.map f (twoChartClassHom V sel hmem u) = 1
      ↔ twoChartClassHom (fun s ↦ f ⁻¹ᵁ V s) (fun x ↦ sel (f.base x))
          (fun x ↦ hmem (f.base x)) (pullbackOverlapUnit f u) = 1 := by
  rw [map_twoChartClassHom]

end Scheme

end AlgebraicGeometry
