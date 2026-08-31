/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TwoChartRepresentable
import AlgebraicJacobian.Tangent.TwoChartQuotientNaturality

/-!
# (T3-3): the two-chart Čech kernel IS the `CechPic` kernel (W5-T3)

The last step of the `ε`-kernel chain of `informal/w5-t4-worksheet.md` §7.1. With (T3-2) closed
(`Tangent/EpsArrowIdentification.lean`) and (T3-4) closed
(`Tangent/CechPicIsoTransport.lean`), this is what remained.

For a scheme `Y` with a two-chart cover `V` and a morphism `f : X ⟶ Y`, the comparison
`twoChartClass` restricts to a **bijection**

```
ker( pullbackOverlapQuot f )  ≃  ker( CechPic.map f )
```

— `twoChartKernelEquiv`. So a kernel *computation* upstream, which is what the
truncated-exponential engine of `Tangent/TruncExpCechH1.lean` performs, transports to the geometric
kernel, and it transports as a **bijection** rather than as two surjections: that is what a
dimension count needs and what `I-0571` records as the difference between usable and not.

## The one hypothesis, and why it is a hypothesis rather than a weakening

`hchart : ∀ L, CechPic.map f L = 1 → ∀ s, CechPic.map (V s).ι L = 1` — *classes killed by `f` are
trivial on each chart.* Nothing here derives it, and it is **exactly clause (iii-c2)** of the W5-T4
decomposition: at the Wave-5 instance `f` is `ε ↦ 0` and the statement is that an `ε`-kernel
class is trivial on each thickened affine chart, because an invertible `A[ε]`-module trivial mod
`ε` is free. That is dual-number algebra, it is proved in this directory
(`Opens.cechPicMap_ι_eq_one_of_map_eq_one` + `Tangent/EpsChartSquare.lean`), and it is the *only*
geometric input of the whole chain.

Carrying it as a binder rather than folding it in is deliberate. Per `I-0688`'s rule every explicit
binder needs a producer, and this one has one, in a different file, for a dual-number-specific
reason — so the general statement stays scheme-general and the geometry stays where it was proved.

## What was NOT done, and the shape that was refused

The first draft of this file stated the bijection against the subtype

```
{L : Y.CechPic // (∀ s, L|_{V s} = 1) ∧ ∃ q, twoChartClass … q = L ∧ pullbackOverlapQuot f q = 1}
```

which typechecks and is **vacuous**: the target mentions the source, so the "bijection" says a
set is in bijection with its own image. That is `isolating-a-residue-as-a-class` — a residue
restated until it demands nothing — and the tell was that the `Equiv`'s `toFun` needed a `sorry` for
chart-triviality *of a `twoChartClass` value*, a statement nothing in the tree provides.

Taking `hchart` as a hypothesis removes both problems at once: `toFun` needs no chart-triviality (it
only needs `map_twoChartClass_eq_one_iff`), the target is the honest `f`-kernel, and the missing
statement is not needed at all. **The residue disappeared when the obligation moved to the binder
that the consumer can actually discharge.**

## Implementation notes

`chartSection` names the chosen preimage rather than using `Exists.choose` inline. Measured: with
the `choose` inline, `rw` cannot see through the `Subtype`/`Equiv` field projections and the three
round-trip goals report *"did not find an occurrence of the pattern"* plus a
`presheaf`-coercion type-mismatch note (`I-0685`'s family). With the section named and its defining
equation `twoChartClass_chartSection` available, all three legs are one term each.

## Scope

`X`, `Y` arbitrary schemes, `f` an arbitrary morphism: no affineness, no curve, no field, no dual
numbers. The two surjectivity binders are the ones `Tangent/TwoChartSelector.lean` characterizes and
produces, discharged at the Wave-5 instance by `Tangent/TwoChartHonestGenus.lean` and
`Tangent/EpsZeroSurjective.lean`.

This file does **not** compose the chain: (T3-1)…(T3-4) are four separate statements and the
composite `H¹(C,𝒪) ≃+ ker(CechPic(C_ε) → CechPic(C))` is not written anywhere yet. That composition
is what T3 now is.

## Main declarations

* `AlgebraicGeometry.Scheme.chartSection` / `twoChartClass_chartSection` — the chosen preimage of a
  chart-trivial class, and its defining equation.
* `AlgebraicGeometry.Scheme.map_eq_one_of_pullbackOverlapQuot_eq_one` — the forward leg.
* `AlgebraicGeometry.Scheme.exists_unique_pullbackOverlapQuot_eq_one` — the backward leg with
  uniqueness.
* `AlgebraicGeometry.Scheme.twoChartKernelEquiv` — **(T3-3)**: the bijection of the two kernels.

Reference: Kleiman, "The Picard scheme", §5, proof of Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §§7.1, 7.5.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TruncExpCech

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}} {V : Bool → Y.Opens}

/-- The two-chart Čech `Ȟ¹`-of-units group of `V` on `Y`. A local abbreviation so the statements
below fit on a line; it is `twoChartClass`'s source verbatim. -/
abbrev overlapQuot (Y : Scheme.{u}) (V : Bool → Y.Opens) :=
  Γ(Y, V false ⊓ V true)ˣ ⧸ cechCoboundaryUnits
    (Y.resHom (inf_le_left : V false ⊓ V true ≤ V false))
    (Y.resHom (inf_le_right : V false ⊓ V true ≤ V true))

variable (sel : Y → Bool) (hmem : ∀ y, y ∈ V (sel y)) (hsel : Function.Surjective sel)

/-! ## The chosen preimage of a chart-trivial class -/

/-- **The two-chart representative of a chart-trivial class.** `(iii-c2-Zar)`
(`twoChartClassHom_surjOn_of_chartTrivial`) produces an overlap unit from chart-triviality alone;
this names its class.

Named rather than left as an inline `Exists.choose` because the round-trip proofs of
`twoChartKernelEquiv` need a *rewritable* defining equation — see the module docstring for the exact
failure the inline version gives. -/
noncomputable def chartSection (L : Y.CechPic)
    (h : ∀ s : Bool, CechPic.map (V s).ι L = 1) : overlapQuot Y V :=
  QuotientGroup.mk (twoChartClassHom_surjOn_of_chartTrivial (V := V) sel hmem L h).choose

/-- The defining equation of `chartSection`: it is a `twoChartClass` preimage. -/
theorem twoChartClass_chartSection (L : Y.CechPic)
    (h : ∀ s : Bool, CechPic.map (V s).ι L = 1) :
    twoChartClass V sel hmem hsel (chartSection sel hmem L h) = L := by
  rw [chartSection, twoChartClass_mk]
  exact (twoChartClassHom_surjOn_of_chartTrivial (V := V) sel hmem L h).choose_spec

/-! ## The two legs -/

/-- **Forward: the upstream kernel lands in the `CechPic` kernel.** The landed
`map_twoChartClass_eq_one_iff` in the direction the bijection's `toFun` consumes. -/
theorem map_eq_one_of_pullbackOverlapQuot_eq_one (f : X ⟶ Y)
    (hsel' : Function.Surjective (fun x ↦ sel (f.base x))) (q : overlapQuot Y V)
    (hq : pullbackOverlapQuot f q = 1) :
    CechPic.map f (twoChartClass V sel hmem hsel q) = 1 :=
  (map_twoChartClass_eq_one_iff f sel hmem hsel hsel' q).mpr hq

/-- **Backward, with uniqueness: a chart-trivial class in the `CechPic` kernel comes from the
upstream kernel, and from exactly one element of it.**

Existence is `chartSection`; membership in the upstream kernel is
`map_twoChartClass_eq_one_iff` read backwards; uniqueness is the landed
`twoChartClass_injective` — which is what makes the comparison a bijection rather than a pair of
surjections. -/
theorem exists_unique_pullbackOverlapQuot_eq_one (f : X ⟶ Y)
    (hsel' : Function.Surjective (fun x ↦ sel (f.base x)))
    (L : Y.CechPic) (hchart : ∀ s : Bool, CechPic.map (V s).ι L = 1)
    (hker : CechPic.map f L = 1) :
    ∃! q : overlapQuot Y V,
      twoChartClass V sel hmem hsel q = L ∧ pullbackOverlapQuot f q = 1 := by
  refine ⟨chartSection sel hmem L hchart,
    ⟨twoChartClass_chartSection sel hmem hsel L hchart, ?_⟩, ?_⟩
  · rw [← map_twoChartClass_eq_one_iff f sel hmem hsel hsel',
      twoChartClass_chartSection sel hmem hsel]
    exact hker
  · rintro q' ⟨hq', -⟩
    exact twoChartClass_injective V sel hmem hsel
      (hq'.trans (twoChartClass_chartSection sel hmem hsel L hchart).symm)

/-! ## (T3-3): the bijection of the two kernels -/

/-- **(T3-3): `twoChartClass` is a bijection from the two-chart Čech kernel onto the `CechPic`
kernel.**

`hchart` is clause (iii-c2) — see the module docstring: it is the chain's only geometric input, it
has a producer at the Wave-5 instance, and it is carried as a binder so that this statement stays
scheme-general.

Not a `MulEquiv`, deliberately: the two sides are kernels of monoid homomorphisms and *are* groups,
but the target `{L // CechPic.map f L = 1}` carries no group instance in the tree, and manufacturing
one here would be infrastructure this file does not need. A consumer wanting the group structure
should read `map_eq_one_of_pullbackOverlapQuot_eq_one` (the map is `twoChartClass`, a `MonoidHom`)
together with this bijection. -/
noncomputable def twoChartKernelEquiv (f : X ⟶ Y)
    (hsel' : Function.Surjective (fun x ↦ sel (f.base x)))
    (hchart : ∀ L : Y.CechPic, CechPic.map f L = 1 → ∀ s : Bool, CechPic.map (V s).ι L = 1) :
    {q : overlapQuot Y V // pullbackOverlapQuot f q = 1}
      ≃ {L : Y.CechPic // CechPic.map f L = 1} where
  toFun q := ⟨twoChartClass V sel hmem hsel q.1,
    map_eq_one_of_pullbackOverlapQuot_eq_one sel hmem hsel f hsel' q.1 q.2⟩
  invFun L := ⟨chartSection sel hmem L.1 (hchart L.1 L.2), by
    rw [← map_twoChartClass_eq_one_iff f sel hmem hsel hsel',
      twoChartClass_chartSection sel hmem hsel]
    exact L.2⟩
  left_inv q := Subtype.ext (twoChartClass_injective V sel hmem hsel
    (twoChartClass_chartSection sel hmem hsel (twoChartClass V sel hmem hsel q.1)
      (hchart _ (map_eq_one_of_pullbackOverlapQuot_eq_one sel hmem hsel f hsel' q.1 q.2))))
  right_inv L := Subtype.ext (twoChartClass_chartSection sel hmem hsel L.1 (hchart L.1 L.2))

@[simp]
theorem twoChartKernelEquiv_apply (f : X ⟶ Y)
    (hsel' : Function.Surjective (fun x ↦ sel (f.base x)))
    (hchart : ∀ L : Y.CechPic, CechPic.map f L = 1 → ∀ s : Bool, CechPic.map (V s).ι L = 1)
    (q : {q : overlapQuot Y V // pullbackOverlapQuot f q = 1}) :
    (twoChartKernelEquiv sel hmem hsel f hsel' hchart q : Y.CechPic)
      = twoChartClass V sel hmem hsel q.1 :=
  rfl

end Scheme

end AlgebraicGeometry
