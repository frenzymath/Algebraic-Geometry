/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.CollapseCechH1
import AlgebraicJacobian.Tangent.DualNumberCarrierReduction
import AlgebraicJacobian.Tangent.TwoChartKernelComparison

/-!
# (T3-6a): the section-level core of the composite, and the opens-family transport (W5-T3)

`informal/w5-t4-worksheet.md` §7.8 measured (T3-6) — the composite
`H¹(C,𝒪) ≃+ ker(CechPic(C_ε) → CechPic(C))` — by writing the square and reading the leftover
goal, and quoted its whole content as **one section-level equation**:

```
(relCurve C k).resHom ⋯ ((relCurveMap C k[ε] k).appLE … (dualNumberSections C … u))
  = collapseUnits C (U₀ ⊓ U₁) hci hqi (unitsFst u)
```

This file proves that equation, in both the ring form (`appLE_dualNumberSections`) and the units
form (`unitsAppLE_dualNumberSectionsUnits`), and supplies the **second** ingredient the composite
needs — which §7.8 did not name.

## §7.8's measurement was right about the content and short by one transport

The equation itself came out as §7.8 predicted: spelling, not mathematics. It is
`Over.relSectionsMap_dualNumberSections` (the landed `(b-coeff)`) plus the identification of
`sectionsCollapse` against `Over.sectionsBaseChange`, which §7.8 probed green in two rewrites and a
`rfl`. Both of those are reproduced below inside `appLE_dualNumberSections`'s proof.

**What §7.8 did not name is a cast.** `relSectionsMap C k[ε] k W` is `appLE` at the pair of opens
`(fst_{k[ε]} ⁻¹ᵁ W, fst_k ⁻¹ᵁ W)`; the geometric arrow `pullbackOverlapQuot (relCurveMap …)` lands
at the opens `relCurveMap ⁻¹ᵁ fst_{k[ε]} ⁻¹ᵁ W`. Those two are **not** `rfl`-equal — measured, not
assumed:

```
example (W : C.left.Opens) :
    relCurveMap C k[ε] k ⁻¹ᵁ ((fst C (overSpec k k[ε])).left ⁻¹ᵁ W)
      = (fst C (overSpec k k)).left ⁻¹ᵁ W
  := rfl        -- FAILS: "type mismatch, rfl has type ?m = ?m"
```

`relCurveMap_preimage` relates them **propositionally**, by `rw [← comp_preimage, relCurveMap_fst]`.
So the composite has to move across an equality of opens, and — since the geometric side is indexed
by a *family* `Bool → Opens` — across an equality of **families**. That is `overlapQuotCongr` and
`epsFamilyEq` here.

The honest reading of §7.8's price, then: it named the section equation correctly and reported "[S],
no missing input identified", and there **was** a missing input — not a brick (the transport is
`subst` on a `funext`), but not nothing either, and it is the piece that decides the *shape* of the
composite's statement rather than its difficulty. Writing the equation with an explicit `e`-binder,
as `appLE_dualNumberSections` does, is what keeps the cast out of the mathematics: the consumer
supplies whichever `≤` its own opens satisfy, and the transport happens once, at the family level.

## Scope

The section equation is at an **arbitrary** qcqs open `W` and an arbitrary target open `V'` below
both preimages; no two-chart structure, no cover, no affineness. `overlapQuotCongr` is
scheme-general and says nothing about dual numbers. What is **not** here: the composite, and in
particular
whether it comes out **additive** — every arrow in the chain is a `MulEquiv` and `Additive`-wrapping
happens only on the (T3-1) leg (worksheet §7.8's closing paragraph). That question is untouched by
this file.

## Main declarations

* `AlgebraicGeometry.overlapQuotCongr` — the two-chart Čech `Ȟ¹`-of-units group transported along an
  equality of cover families.
* `AlgebraicGeometry.Over.epsFamilyEq` — the family equality the `ε ↦ 0` comparison needs.
* `AlgebraicGeometry.Over.appLE_dualNumberSections` — **§7.8's equation**, ring form.
* `AlgebraicGeometry.Over.unitsAppLE_dualNumberSectionsUnits` — units form, which is what the Čech
  quotients consume.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §§7.8, 8.0.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open TruncExpCech DualNumber TrivSqZeroExt

namespace AlgebraicGeometry

open scoped TruncExpCech.EpsilonReduction

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

/-! ## The opens-family transport -/

/-- **The two-chart Čech `Ȟ¹`-of-units group transported along an equality of cover families.**

Scheme-general, and `subst` on the family equality — but not omissible: the `ε ↦ 0` comparison
produces the family `fun s ↦ relCurveMap ⁻¹ᵁ fst_{k[ε]} ⁻¹ᵁ U s` while the downstairs engine
consumes `fun s ↦ fst_k ⁻¹ᵁ U s`, and those are equal only propositionally
(`Over.epsFamilyEq`; the `rfl` attempt is quoted in the module docstring). -/
noncomputable def overlapQuotCongr {X : Scheme.{u}} {V V' : Bool → X.Opens} (h : V = V') :
    Scheme.overlapQuot X V ≃* Scheme.overlapQuot X V' :=
  h ▸ MulEquiv.refl _

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))

namespace Over

variable (U : Bool → C.left.Opens)

/-- **The family equality the `ε ↦ 0` comparison crosses.** Pulling the base-changed charts of
`C_{k[ε]}` back along `relCurveMap` gives the base-changed charts of `C_k`, chart by chart. One
`funext` over the landed `relCurveMap_preimage`. -/
theorem epsFamilyEq :
    (fun s ↦ relCurveMap C (DualNumber k) k ⁻¹ᵁ
        (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U s)
      = fun s ↦ (fst C (overSpec k k)).left ⁻¹ᵁ U s :=
  funext fun s ↦ relCurveMap_preimage C (DualNumber k) k (U s)

/-! ## §7.8's equation -/

/-- **§7.8's section equation, ring form**: restricting the `ε ↦ 0` image of a thickened section
gives the collapse of `fst x`.

Stated with the target open `V'` and its `e`-binder **explicit**, rather than at
`fst_k ⁻¹ᵁ W`: that is what keeps the opens cast (module docstring) out of the statement, since a
consumer supplies whichever `≤` its own opens satisfy and this equation never has to mention the
propositional equality of the two preimages.

Two ingredients, both landed and both named by worksheet §6.24 as what the missing link would need:
`Over.relSectionsMap_dualNumberSections` — the `(b-coeff)` reduction — and the identification of
`sectionsCollapse` against `Over.sectionsBaseChange` at `· ⊗ₜ 1`, which is `hbridge` below and cost
two rewrites plus `rfl`. The remaining step is `Scheme.Hom.appLE_map`: `appLE` followed by a
restriction is a single `appLE`, by proof irrelevance of the inclusion witnesses. -/
theorem appLE_dualNumberSections {W : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    {V' : (relCurve C k).Opens}
    (e : V' ≤ relCurveMap C (DualNumber k) k ⁻¹ᵁ
        ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W))
    (hle : V' ≤ (fst C (overSpec k k)).left ⁻¹ᵁ W)
    (x : DualNumber Γ(C.left, W)) :
    ((relCurveMap C (DualNumber k) k).appLE
        ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W) V' e).hom
        (Over.dualNumberSections C hW hW' x)
      = (relCurve C k).resHom hle (collapseRingEquiv C W hW hW' (TrivSqZeroExt.fst x)) := by
  have h0 := Over.relSectionsMap_dualNumberSections C hW hW' x
  have hbridge : Over.sectionsBaseChange C k hW hW' (TrivSqZeroExt.fst x ⊗ₜ (1 : k))
      = collapseRingEquiv C W hW hW' (TrivSqZeroExt.fst x) := by
    rw [Over.sectionsBaseChange_tmul_one]
    change _ = sectionsCollapse C W hW hW' (TrivSqZeroExt.fst x)
    rw [sectionsCollapse_apply]
    rfl
  rw [hbridge] at h0
  rw [← h0, relSectionsMap]
  exact (congr((CommRingCat.Hom.hom $(Scheme.Hom.appLE_map (relCurveMap C (DualNumber k) k)
    (le_of_eq (relCurveMap_preimage C (DualNumber k) k W).symm)
    (homOfLE hle).op)) (Over.dualNumberSections C hW hW' x))).symm

/-- **§7.8's section equation, units form** — the shape the Čech `Ȟ¹` quotients consume, since a
two-chart `Ȟ¹` is a quotient of a group of *units*. `Units.ext` over the ring form; the
`unitsAppLE`/`collapseUnits`/`Units.map` coercions are all `rfl` on the underlying section
(`coe_unitsAppLE`, and `collapseUnits` is `Units.mapEquiv` of `collapseRingEquiv`). -/
theorem unitsAppLE_dualNumberSectionsUnits {W : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    {V' : (relCurve C k).Opens}
    (e : V' ≤ relCurveMap C (DualNumber k) k ⁻¹ᵁ
        ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W))
    (hle : V' ≤ (fst C (overSpec k k)).left ⁻¹ᵁ W)
    (u : (DualNumber Γ(C.left, W))ˣ) :
    (relCurveMap C (DualNumber k) k).unitsAppLE
        ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W) V' e
        (Over.dualNumberSectionsUnits C hW hW' u)
      = Units.map ((relCurve C k).resHom hle).toMonoidHom
          (collapseUnits C W hW hW' (unitsFst u)) := by
  ext
  exact appLE_dualNumberSections C hW hW' e hle (u : DualNumber Γ(C.left, W))

end Over

end AlgebraicGeometry
