/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.DualNumberCarrierCoboundary
import AlgebraicJacobian.Tangent.DualNumberCarrierReduction
import AlgebraicJacobian.Tangent.TwoChartQuotientNaturality

/-!
# (T3-2): the engine's arrow IS the geometric arrow (W5-T3, the §6.24 link)

`informal/w5-t4-worksheet.md` §6.24 ran a carrier-by-carrier level check on the `ε`-kernel chain and
concluded, in its own words:

> *"What is therefore still missing is **exactly one link**, stated sharply. The engine's arrow is
> `unitsFst` on the dual-number carrier; item (1)'s arrow is `pullbackOverlapQuot` along the `ε ↦ 0`
> scheme morphism. Saying these are the same arrow across `dualNumberCechH1Equiv` is precisely
> `(b-coeff)` composed with the (3c) object transport — which is why (3c) is not cosmetic
> bookkeeping: **it is the step that turns two aligned diagrams into one commuting one**."*

This file is that link. `pullbackOverlapQuot_dualNumberCechH1Equiv_mk` says the geometric
pullback of a thickened two-chart Čech `Ȟ¹`-of-units class along `relCurveMap C k[ε] k` is the
algebraic restriction of the corresponding dual-number class — the square §6.24 named, on
generators, which is
all a quotient needs.

## Two findings, and the second retracts a price this worksheet set an hour earlier

**(1) The two coboundary subgroups are the SAME TERM.** `dualNumberCechH1Equiv`'s target is stated
with `resHom (Scheme.Hom.preimage_mono (fst …) inf_le_left)` (restriction between *preimages of
charts*), and `pullbackOverlapQuot`'s source with `resHom inf_le_left` at the family
`fun s => fst ⁻¹ᵁ U s`. Those look like two different spellings needing a transport. Probed:
they are `rfl`-equal as **subgroups**, because preimage distributes over `⊓` definitionally
(`h ⁻¹ᵁ (U ⊓ V) = h ⁻¹ᵁ U ⊓ h ⁻¹ᵁ V` is `rfl`) and `preimage_mono` at `inf_le_left` is then the same
proof term as `inf_le_left`. So the engine's transported carrier *is* the geometric map's source,
with nothing between them.

**(2) The arrow itself is `rfl`.** Given (1), the statement below closes by `rfl` — no `(b-coeff)`,
no `(3c)`, no rewriting. §7.3 of the worksheet priced this item **[M]**, "and it is the real
residue", on the strength of "both ingredients are landed"; §7.4 records the retraction. What
made it `rfl` is **stating the target in the pulled-back opens** rather than in `relCurve C k`'s own
`fst ⁻¹ᵁ (U₀ ⊓ U₁)` spelling: the first attempt asked for
`Units.map (relSectionsMap …)` landing in `Γ(relCurve C k, fst ⁻¹ᵁ (U₀ ⊓ U₁))` and failed to
typecheck, naming exactly the two opens (`relCurveMap ⁻¹ᵁ fst ⁻¹ᵁ U s` versus `fst ⁻¹ᵁ U s`) that
`relCurveMap_preimage` relates *propositionally*.

> **The lesson is the one this directory has recorded twice already, from the other side.**
> `restrict-into-the-type-dont-rewrite-the-type`: the predicted transport cost zero once the
> conclusion was phrased at the opens the consumer actually produces. Here the two prior instances
> were about `≤`-restriction and `inf_idem`; this one is about a base-change preimage, and the tell
> was identical — a type mismatch naming the two opens rather than a failing tactic.

## What this does NOT close

**It does not compute the kernel.** This is the *commuting square*, i.e. the statement that makes a
kernel comparison between the two sides *meaningful* (`I-0571`: an isomorphism of the two ends of a
map says nothing about the map). Combining it with T2's
`h1AddEquivTruncExpCechKernel` and with `map_twoChartClass_eq_one_iff` is (T3-3), still to be
written, and that step consumes `twoChartClass_injective` plus the (iii-c2) surjectivity leg.

**And it says nothing about `relCurve C k` versus `C.left`.** That is (T3-4),
`Tangent/CechPicIsoTransport.lean`, a separate transport across the `(3c)` seam.

## Main declarations

* `AlgebraicGeometry.Over.epsOverlapLe` — the `≤` the pulled-back overlap satisfies, named so the
  statement below does not carry an inline proof term.
* `AlgebraicGeometry.Over.pullbackOverlapQuot_dualNumberCechH1Equiv_mk` — **(T3-2)**, the
  §6.24 link.
* `AlgebraicGeometry.Over.cechCoboundaryUnits_preimage_eq` — finding (1), recorded as a statement so
  that a later session does not re-derive it as a transport.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §§6.20, 6.24, 7.1, 7.4.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open TruncExpCech DualNumber TrivSqZeroExt

namespace AlgebraicGeometry

open scoped TruncExpCech.EpsilonReduction

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
variable (U : Bool → C.left.Opens)

namespace Over

/-! ## Finding (1): the two coboundary subgroups agree on the nose -/

/-- **The thickened-chart coboundary subgroup in the two spellings is one subgroup.**

`Tangent/DualNumberCarrierCoboundary.lean` states it with `preimage_mono` (restriction between the
preimages of the two charts); `Tangent/TwoChartQuotientNaturality.lean` states it with `inf_le_left`
at the family `fun s => fst ⁻¹ᵁ U s`. They are the same term: preimage distributes over `⊓`
definitionally, so the two `≤` proofs are the same proof of the same inequality.

Recorded as a statement rather than left implicit because "these need a transport" is the natural
reading, and it is wrong — the `ε`-kernel chain crosses this seam for free. -/
theorem cechCoboundaryUnits_preimage_eq :
    cechCoboundaryUnits
        ((C ⊗ overSpec k (DualNumber k)).left.resHom
          (Scheme.Hom.preimage_mono (fst C (overSpec k (DualNumber k))).left
            (inf_le_left : U false ⊓ U true ≤ U false)))
        ((C ⊗ overSpec k (DualNumber k)).left.resHom
          (Scheme.Hom.preimage_mono (fst C (overSpec k (DualNumber k))).left
            (inf_le_right : U false ⊓ U true ≤ U true)))
      = cechCoboundaryUnits
        ((C ⊗ overSpec k (DualNumber k)).left.resHom
          (inf_le_left :
            (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U false
              ⊓ (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U true
            ≤ (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U false))
        ((C ⊗ overSpec k (DualNumber k)).left.resHom
          (inf_le_right :
            (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U false
              ⊓ (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U true
            ≤ (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U true)) :=
  rfl

/-! ## The `≤` the pulled-back overlap satisfies -/

/-- **The pulled-back overlap sits inside the preimage of the thickened overlap.** The `e` binder of
`Scheme.Hom.unitsAppLE` at the `ε ↦ 0` map of relative curves, named so that (T3-2)'s statement
carries a lemma rather than an inline `by` block.

Both sides unfold to the same set; the `intro`/`exact` is spelling out that
`relCurveMap ⁻¹ᵁ (A ⊓ B) = relCurveMap ⁻¹ᵁ A ⊓ relCurveMap ⁻¹ᵁ B`, which is `rfl` but not
syntactically the goal. -/
theorem epsOverlapLe :
    (relCurveMap C (DualNumber k) k ⁻¹ᵁ
        (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U false
      ⊓ relCurveMap C (DualNumber k) k ⁻¹ᵁ
        (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U true)
      ≤ relCurveMap C (DualNumber k) k ⁻¹ᵁ
        ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ (U false ⊓ U true)) := by
  intro x hx
  exact ⟨hx.1, hx.2⟩

/-! ## (T3-2): the two arrows are one arrow -/

/-- **(T3-2): THE §6.24 LINK.** The geometric pullback of a thickened two-chart Čech
`Ȟ¹`-of-units class along the `ε ↦ 0` map of relative curves is the algebraic restriction of the
corresponding dual-number class.

Read left to right: take `u : (Γ(C, U₀ ⊓ U₁)[ε])ˣ`, carry it to the thickened curve by the carrier
translation `dualNumberSectionsUnits`, descend to the Čech `Ȟ¹` quotient
(`dualNumberCechH1Equiv`), and pull back along `relCurveMap C k[ε] k` — the result is the class of
`unitsAppLE` applied to the translated unit. That is the square worksheet §6.24 isolated as the one
thing standing between the truncated-exponential engine and the two-chart `CechPic` comparison.

**It is `rfl`**, given `cechCoboundaryUnits_preimage_eq` and the target stated in the *pulled-back*
opens. See the module docstring: an earlier phrasing in `relCurve C k`'s own
`fst ⁻¹ᵁ (U₀ ⊓ U₁)` spelling does not typecheck, and the price the worksheet had set for this item
was based on that phrasing. -/
theorem pullbackOverlapQuot_dualNumberCechH1Equiv_mk
    (hc : ∀ s, IsCompact ((U s : Set C.left))) (hq : ∀ s, IsQuasiSeparated ((U s : Set C.left)))
    (hci : IsCompact (((U false ⊓ U true : C.left.Opens) : Set C.left)))
    (hqi : IsQuasiSeparated (((U false ⊓ U true : C.left.Opens) : Set C.left)))
    (u : (DualNumber Γ(C.left, U false ⊓ U true))ˣ) :
    Scheme.pullbackOverlapQuot (V := fun s => (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U s)
        (relCurveMap C (DualNumber k) k)
        (Over.dualNumberCechH1Equiv C hc hq hci hqi (QuotientGroup.mk u))
      = QuotientGroup.mk
          (Scheme.Hom.unitsAppLE (relCurveMap C (DualNumber k) k)
            ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ (U false ⊓ U true))
            (relCurveMap C (DualNumber k) k ⁻¹ᵁ
                (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U false
              ⊓ relCurveMap C (DualNumber k) k ⁻¹ᵁ
                (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ U true)
            (Over.epsOverlapLe C U)
            (Over.dualNumberSectionsUnits C hci hqi u)) :=
  rfl

end Over

end AlgebraicGeometry
