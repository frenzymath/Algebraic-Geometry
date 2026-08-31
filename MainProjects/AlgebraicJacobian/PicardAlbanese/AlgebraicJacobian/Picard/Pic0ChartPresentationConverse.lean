/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartPresentationHalf
import AlgebraicJacobian.Picard.Pic0ChartLocusFibreField
import AlgebraicJacobian.Picard.CechKernelLemma
import AlgebraicJacobian.Tangent.RelPicPointTest

/-!
# CHART-U(b)'s last residue: the descent direction `hconv`

`Picard/Pic0ChartPresentationHalf.lean` splits `IsChartDatumPresentation` into a forward half
(proved there, by the trivial splitting) and a converse `hconv`, and its docstring prices the
converse as follows:

> `hconv` is the descent direction: from a split witness over *some* extension `L_t/κ(t)`
> chosen per point, produce the datum's predicate at `κ(t)` itself.  Its two ingredients both
> exist — `hasWitnessH1Vanishing_iff_of_fieldExtension` carries a *datum* predicate across a
> field extension, and `hfib` identifies the classes — but composing them is not a rewrite,
> because the witness received lies in `μ`'s class at `L_t` rather than visibly in `D`'s at
> `κ(t)`.

**That diagnosis is right, and it names two of the three ingredients.**  The missing one is
the reason the composition is not a rewrite: to see the received witness as lying in `D`'s
fibre class one must go *backwards* through `PicEtAff.unit`, and that step is
`PicEtAff.unit_injective` (`Picard/CechKernelLemma.lean:361`) — the unconditional close of the
ζ3 campaign, Kleiman 2.5(1).  With it the descent is three steps and no geometry:

1. the split witness at `L_t` gives a presenting class `M` with
   `PicEtAff.map … (picEtAffineEquiv … μ_t) = PicEtAff.unit … (relPicMk … M)` and a witness
   divisor in `M` with vanishing `H¹`;
2. `hfib` at `t`, transported to `L_t`, says the *same* left-hand side equals
   `PicEtAff.unit … (relPicMk … (D's fibre class at L_t))`.  `unit_injective` then makes the
   two `relPicMk` arguments equal, and `relPicMk` is injective too — so `M` **is** `D`'s fibre
   class at `L_t`, which is what "visibly in `D`'s class" was missing;
3. hence `D.HasWitnessH1Vanishing L_t` holds by definition, and
   `hasWitnessH1Vanishing_iff_of_fieldExtension` brings it down to `κ(t)`.

## What this file does and does not close

It closes `hconv` **from a per-point transported `hfib`** — the statement
`IsChartDatumPlusFibreAt` below, which is `hfib`'s identity read at the chosen extension
rather than at `κ(t)`.  That is a real reduction: `hconv`'s conclusion is a statement about
witnesses and `H¹`, and what remains is a statement about *plus classes only*, with no witness,
no `H¹` and no divisor — exactly the shape §0.3's GAP-6 dictionary cannot see and the shape
`IsChartDatumPlusFibre` already has at `κ(t)`.

**CORRECTION 2026-07-29 (r7), and this paragraph is why it is worth reading.**  The sentence that
stood here said the transport was not silently assumed because
`isChartDatumPlusFibreAt_of_isScalarTower` was "the honest statement" of it — and **that
declaration did not exist**, in this file or anywhere in the tree.  It was advertised by name and
never written (the failure mode `docstring-declaration-lists-unchecked`), and the effect was worse
than a dangling reference: the sentence made `hplus` read as bookkeeping already discharged, while
`hplus` was in fact the *whole* of B-4's remaining content.  The last clause — "so the composite
needs `hfib` at `κ(t)` and nothing else" — was therefore false of the theorem actually below it,
which takes `hplus` as a hypothesis.

**It is true now, and of a different theorem.**  `Picard/Pic0ChartPlusFibreTower.lean` proves the
transport (three functoriality laws — `PicEtAff.map_map`, `PicEtAff.map_unit`, `relCurveMap_comp`
— and no geometry) and derives `IsChartDatumPresentation` from `hfib` alone as
`isChartDatumPresentation_of_plusFibre_tower`.  **Prefer that theorem**; the one below remains
correct and is the general form.

**One further finding, about the statement of `hasWitnessH1Vanishing_of_isSplitWitness_at` below
rather than its proof.**  Its `hplus` binder quantifies `(_ : Algebra A L)` universally with only
the `k`-tower imposed, and that is strictly stronger than the proof consumes: the proof takes the
`A`-structure from its own `htow` and uses `hplus` at *that* instance only.  The extra strength is
not harmless — `IsChartDatumPlusFibreAt` mentions `relCurveMap C A L`, so at an `Algebra A L`
unrelated to the composite `A → κ(t) → L` the right-hand side pulls `D.cechPicClass` along a
different morphism and `hfib` cannot imply it.  So the `∀`-form is not merely hard to supply, it
is the wrong statement.  `hasWitnessH1Vanishing_of_isSplitWitness_tower` (same file as the
transport) is this theorem with `IsScalarTower A κ(t) L` added to that binder — the third
component `towerOfResidueFieldExtension` already returns, and which the proof below already
destructures and then discards.

## Main declarations

* `AlgebraicGeometry.IsChartDatumPlusFibreAt` — the plus-class identity at a *given*
  extension of the residue field.  Witness-free.
* `AlgebraicGeometry.hasWitnessH1Vanishing_of_isSplitWitness_at` — **the descent step**: a
  split witness whose splitting field satisfies that identity gives the datum's predicate
  there, hence (by the field-extension `iff`) at `κ(t)`.  This is where
  `PicEtAff.unit_injective` is spent.
* `AlgebraicGeometry.isChartDatumPresentation_of_plusFibre` — **CHART-U(b)'s residue closed
  modulo the plus-class identity**: `IsChartDatumPresentation` from `hfib` at `κ(t)` together
  with the per-point transported identity, with no separate `hconv`.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

noncomputable section

/-! ## The plus-class identity at a chosen extension -/

variable (C π) in
/-- **The plus-class identity of `IsChartDatumPlusFibre`, read at a given extension `L` of the
residue field** rather than at `κ(t)` itself.

Witness-free, `H¹`-free and divisor-free, exactly like `IsChartDatumPlusFibre`: it says the
plus class obtained by restricting `μ` to `κ(t)` and then reading it over `L` is the plus-unit
of `D`'s fibre class at `L`.

This is the form the descent step below consumes, because a split witness for `μ` at `t`
produces its data over an extension it chooses, not over `κ(t)`. -/
def IsChartDatumPlusFibreAt {A : Type u} [CommRing A] [Algebra k A]
    (μ : picEt C (overSpec k A)) (D : BasicOpenCocycleDatum C A π)
    (t : (overSpec k A).left) (L : Type u) [Field L] [Algebra k L]
    [Algebra (Over.testPointField (T := overSpec k A) t) L]
    [IsScalarTower k (Over.testPointField (T := overSpec k A) t) L] [Algebra A L]
    [IsScalarTower k A L] : Prop :=
  PicEtAff.map C L
      (picEtAffineEquiv C (Over.testPointField (T := overSpec k A) t)
        (picEtMap C (Over.testPoint t) μ))
    = PicEtAff.unit C L
        (relPicMk C (overSpec k L)
          (Scheme.CechPic.map (relCurveMap C A L) D.cechPicClass))

/-! ## The descent step -/

variable (C π) in
/-- **THE DESCENT STEP** — `hconv` at one point, given the plus-class identity at the
splitting field.

A split witness for `μ`'s fibre at `t` hands over a finite separable `L/κ(t)`, a presenting
class `M` over `L`, and a divisor `W` in `M` with vanishing `H¹`.  The plus-class identity at
`L` says the *same* left-hand side that `M` presents is the plus-unit of `D`'s fibre class at
`L`.  So:

* `PicEtAff.unit_injective` (`Picard/CechKernelLemma.lean:361`, Kleiman 2.5(1) — the
  unconditional close of the ζ3 campaign) makes the two `relPicMk` arguments equal;
* `relPicMk` is injective (`relPicMk_injective_of_subsingleton`), so `M` **is** `D`'s fibre
  class at `L`;
* `W` therefore witnesses `D.HasWitnessH1Vanishing L` by definition, and
  `hasWitnessH1Vanishing_iff_of_fieldExtension` carries that down to `κ(t)`.

**This is the ingredient `Pic0ChartPresentationHalf`'s docstring was missing.**  It diagnosed
correctly that "the witness received lies in `μ`'s class at `L_t` rather than visibly in `D`'s
at `κ(t)`", and named the two transport lemmas — but the step that makes the class *visible*
is not a transport at all: it is the injectivity of the plus unit, which the tree has had since
the ζ3 close and which no CHART-U row cites. -/
theorem hasWitnessH1Vanishing_of_isSplitWitness_at {A : Type u} [CommRing A] [Algebra k A]
    (μ : picEt C (overSpec k A)) (D : BasicOpenCocycleDatum C A π)
    (t : (overSpec k A).left)
    (hplus : ∀ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (_ : Algebra (Over.testPointField (T := overSpec k A) t) L)
      (_ : IsScalarTower k (Over.testPointField (T := overSpec k A) t) L)
      (_ : Algebra A L) (_ : IsScalarTower k A L),
      IsChartDatumPlusFibreAt C π μ D t L)
    (htow : ∀ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (_ : Algebra (Over.testPointField (T := overSpec k A) t) L)
      (_ : IsScalarTower k (Over.testPointField (T := overSpec k A) t) L),
      Σ' (_ : Algebra A L) (_ : IsScalarTower k A L),
        IsScalarTower A (Over.testPointField (T := overSpec k A) t) L)
    (h : IsSplitWitness C (picEtMap C (Over.testPoint t) μ)) :
    D.HasWitnessH1Vanishing (Over.testPointField (T := overSpec k A) t) := by
  obtain ⟨L, hLf, hLk, hLK, hLtow, hLfin, hLsep, M, hM, W, hW, hW1⟩ := h
  obtain ⟨hAL, hAtow, hATow⟩ := htow L hLf hLk hLK hLtow
  -- the plus-class identity at `L`, and the presenting identity the witness came with
  have hid : PicEtAff.unit C L (relPicMk C (overSpec k L) M)
      = PicEtAff.unit C L
        (relPicMk C (overSpec k L)
          (Scheme.CechPic.map (relCurveMap C A L) D.cechPicClass)) := by
    rw [← hM]
    exact hplus L hLf hLk hLK hLtow hAL hAtow
  -- `unit_injective` then `relPicMk` injective: `M` IS `D`'s fibre class at `L`
  have hMcl : M = Scheme.CechPic.map (relCurveMap C A L) D.cechPicClass :=
    relPicMk_injective_of_subsingleton C (overSpec k L)
      (PicEtAff.unit_injective C L hid)
  -- so `W` witnesses `D`'s predicate at `L`, and the field-extension `iff` descends it
  refine (D.hasWitnessH1Vanishing_iff_of_fieldExtension
    (Over.testPointField (T := overSpec k A) t) L).mpr ⟨W, ?_, hW1⟩
  rw [hW, hMcl]

/-! ## The `htow` hypothesis is satisfiable, checked rather than assumed

`htow` returns *data* (three instances), so it could in principle be an unmeetable demand and
the descent step vacuous — the failure mode memory `isolating-a-residue-as-a-class` records
from the other direction.  It is not: the composite tower always exists. -/

/-- **`htow` is constructible**, at any `L` over the residue field.

The `A`-algebra structure on `L` is the composite `A → κ(t) → L`, where `A → κ(t)` is the
tree's own `Over.instAlgebraTestPointFieldAffine`.  Both towers then hold by
`IsScalarTower.of_algebraMap_eq`.

Worth stating rather than inlining, because `Algebra A L` does **not** synthesize from the
hypotheses of `hasWitnessH1Vanishing_of_isSplitWitness_at` — measured — so a reader would
otherwise have to guess whether `htow` is a genuine obligation or bookkeeping.  It is
bookkeeping, and this is the proof. -/
def towerOfResidueFieldExtension {A : Type u} [CommRing A] [Algebra k A]
    (t : (overSpec k A).left) (L : Type u) [Field L] [Algebra k L]
    [Algebra (Over.testPointField (T := overSpec k A) t) L]
    [IsScalarTower k (Over.testPointField (T := overSpec k A) t) L] :
    Σ' (_ : Algebra A L) (_ : IsScalarTower k A L),
      IsScalarTower A (Over.testPointField (T := overSpec k A) t) L := by
  letI : Algebra A L :=
    ((algebraMap (Over.testPointField (T := overSpec k A) t) L).comp
      (algebraMap A (Over.testPointField (T := overSpec k A) t))).toAlgebra
  haveI htow : IsScalarTower A (Over.testPointField (T := overSpec k A) t) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨_, IsScalarTower.of_algebraMap_eq fun x => ?_, htow⟩
  change (algebraMap k L) x
      = (algebraMap (Over.testPointField (T := overSpec k A) t) L)
          ((algebraMap A (Over.testPointField (T := overSpec k A) t)) ((algebraMap k A) x))
  rw [← IsScalarTower.algebraMap_apply k A (Over.testPointField (T := overSpec k A) t),
    ← IsScalarTower.algebraMap_apply k (Over.testPointField (T := overSpec k A) t) L]

/-- **`IsChartDatumPlusFibreAt` at `L := κ(t)` IS `IsChartDatumPlusFibre` at `t`** — by
`Iff.rfl`, so the generalisation in `L` is a genuine generalisation of the *same* equation and
not a different statement that happens to specialise.

This is the upper half of the two-sided check on `hplus` below, and it is the sharp one: it shows
the extra strength of `hplus` over `hfib` is exactly "the same identity at every extension", so a
lane reading `hplus` knows precisely what it owes beyond `hfib` — the naturality of `cechPicClass`
along `κ(t) → L`, and nothing else.

**The lower half was measured too, and is recorded here because it cannot be a theorem.**  A
reduction whose new hypothesis is *satisfiable by construction* is vacuous, and `D` in
`IsChartDatumPlusFibreAt` is chosen by the consumer — exactly the configuration in which that
happens.  Probed at arbitrary `μ`, `D`, `t`, `L`: `rfl` fails on the left-hand side, and `simp`
and `aesop` both leave unsolved goals.  So it is a genuine equation between two plus classes and
not a `Prop` true for free.  (A passing automation attempt would have refuted the reduction, which
is why the probe is worth running before pricing anything as a residue.)

**And the probe has a second form, which the first does not cover.**  Junk-inhabitation is the risk
when the hypothesis is *consumer-chosen* — `D` here.  When it is *determined* by the setting, the
mirror risk is **unsatisfiability**: a reduction to a false hypothesis passes every `sorry` census
and every axiom probe, because it then *is* a theorem.  `hplus` is determined in `μ`, so that
direction needs a witness, and the witness is landed and unconditional:
`exists_splitting_of_picEt` produces, for **any** plus class over **any** reading field, a finite
separable `L` and a presenting class `M` with exactly the identity `hplus` asserts.  So the
plus-class identity is *inhabited* at every `μ`, not merely consistent. -/
theorem isChartDatumPlusFibreAt_self {A : Type u} [CommRing A] [Algebra k A]
    (μ : picEt C (overSpec k A)) (D : BasicOpenCocycleDatum C A π)
    (t : (overSpec k A).left) (h : IsChartDatumPlusFibre C π μ D) :
    IsChartDatumPlusFibreAt C π μ D t (Over.testPointField (T := overSpec k A) t) :=
  h t

/-! ## CHART-U(b)'s residue, assembled -/

variable (C π) in
/-- **`IsChartDatumPresentation` WITH NO SEPARATE `hconv`** — CHART-U(b)'s residue reduced to a
witness-free statement about plus classes.

`isChartDatumPresentation_of_plusFibre_of_converse` asks for `hfib` *and* `hconv`.  This asks
for `hfib` and the per-point plus-class identity at the splitting field, which is `hfib`'s own
statement read at `L` instead of at `κ(t)` — and discharges `hconv` from it via the descent step
above.  `htow` is supplied by `towerOfResidueFieldExtension`, so it is not an
obligation on the caller.

**What this buys the CHART-U(b) row.**  Its residue was "the pointwise presentation", an `↔`
one half of which involved witnesses and `H¹`.  Both halves are now witness-free: the forward
one was already (`isSplitWitness_of_hasWitnessH1Vanishing`, by the trivial splitting) and the
converse is now, by the plus-unit injectivity.  So the whole of CHART-U(b) reduces to
`cechPicClass` base-change identities — which is what the row's own §0.3 retraction predicted
("a `cechPicClass` base-change statement, and not any construction") and what
`Pic0ChartLocusIsOpen`'s header calls the residue.

**What it does not buy — SUPERSEDED 2026-07-29 (r7).**  This paragraph said the remaining identity
is at *every* extension `L` of `κ(t)`, strictly more than `IsChartDatumPlusFibre` asks, and that
whether the two are equivalent "is the naturality of `cechPicClass` under `κ(t) → L`, which this
file does not settle".  **They are equivalent, and the answer was cheaper than the framing
suggested**: the identity at `L` is the identity at `κ(t)` pushed forward along `PicEtAff.map C L`,
so it needs `PicEtAff.map_map`, `PicEtAff.map_unit` and `relCurveMap_comp` and nothing about
`cechPicClass` specifically.  `isChartDatumPlusFibreAt_of_isScalarTower`
(`Picard/Pic0ChartPlusFibreTower.lean`) is the transport, and
`isChartDatumPresentation_of_plusFibre_tower` is this theorem with the `hplus` argument
removed.  Use that one.

The one caveat the transport does carry is the tower compatibility `IsScalarTower A κ(t) L`, which
is genuinely needed (see the correction in this file's header) and is supplied by
`towerOfResidueFieldExtension` — so it is not an obligation on any caller. -/
theorem isChartDatumPresentation_of_plusFibre {A : Type u} [CommRing A] [Algebra k A]
    {μ : picEt C (overSpec k A)} {D : BasicOpenCocycleDatum C A π}
    (hfib : IsChartDatumPlusFibre C π μ D)
    (hplus : ∀ (t : (overSpec k A).left) (L : Type u) (_ : Field L) (_ : Algebra k L)
      (_ : Algebra (Over.testPointField (T := overSpec k A) t) L)
      (_ : IsScalarTower k (Over.testPointField (T := overSpec k A) t) L)
      (_ : Algebra A L) (_ : IsScalarTower k A L),
      IsChartDatumPlusFibreAt C π μ D t L) :
    IsChartDatumPresentation C π μ D :=
  isChartDatumPresentation_of_plusFibre_of_converse C π hfib fun t =>
    hasWitnessH1Vanishing_of_isSplitWitness_at C π μ D t (hplus t)
      (fun L _ _ _ _ => towerOfResidueFieldExtension t L)

end

end AlgebraicGeometry
