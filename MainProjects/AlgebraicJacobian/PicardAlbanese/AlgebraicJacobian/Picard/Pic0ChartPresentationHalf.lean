/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartTwistSplit
import AlgebraicJacobian.Picard.Pic0ChartLocusIsOpen

/-!
# `IsChartDatumPresentation`: the FORWARD half, from a pointwise plus-class identity

`IsChartDatumPresentation μ D` (`Picard/Pic0ChartLocusIsOpen.lean:161`) is CHART-U(b)'s one
remaining residue: an `↔`, at every point `t` of an affine test, between

* `D.HasWitnessH1Vanishing κ(t)` — the datum's fibre predicate, and
* `IsSplitWitness C (fibre of μ at κ(t))` — the split predicate `chartLocus` is defined by.

That file's header prices it as a *construction* rather than bookkeeping, and is right to: the
splitting field `L` in `IsSplitWitness` is quantified **per point**, so no single datum obviously
matches it everywhere.

**This file discharges the `→` direction from a hypothesis that mentions no witness at all.**

## What makes the forward direction cheap now

The datum side hands you a witness divisor `W` over `κ(t)` in the class
`CechPic.map (relCurveMap C A κ(t)) D.cechPicClass`, with vanishing `H¹`.  To build
`IsSplitWitness` you must exhibit a finite separable extension over which the *fibre of `μ`* is
honest, with a witness in its class.  Take the extension to be `κ(t)` itself — the identity
extension, finite and separable — and the witness to be `W`.

That is exactly `isSplitWitness_of_presenting_witness_self`
(`Picard/Pic0ChartTwistSplit.lean`), the trivial splitting `L := K`.  Memory item I-0564 had
recorded that instance as **unelaborable** and singled it out as "worth wanting"; it is a
one-liner once the existentials are staged rather than bundled, and this file is the first
consumer that needed it.

So the whole forward direction reduces to a statement with **no witness, no `H¹`, no divisor**:
that the datum's fibre class, read as a plus class, *is* the fibre of `μ`.  That is
`IsChartDatumPlusFibre` below — a naturality identity between `PicEtAff.map ∘ picEtAffineEquiv`
and `relPicMk ∘ CechPic.map`, one equation per point.

## What is NOT here, stated so the file is not over-read

The `←` direction.  It is the genuinely harder one and it is where the per-point quantification
of `L` bites: from `IsSplitWitness` you receive *some* extension `L_t/κ(t)`, varying with `t`,
and must produce the datum's predicate at `κ(t)` itself — i.e. descend the witness along
`κ(t) → L_t`.  The tree's fibre-field invariance
(`BasicOpenCocycleDatum.hasWitnessH1Vanishing_iff_of_fieldExtension`) is an `↔` and so does
carry that descent for a *datum* predicate — but the witness one receives lies in `μ`'s class,
not visibly in `D`'s, so closing it still needs the plus-class identity below **plus** the
transport.  Nothing here claims that half.

## Main declarations

* `AlgebraicGeometry.IsChartDatumPlusFibre` — the witness-free hypothesis: the datum presents
  `μ` at every residue field, as plus classes.
* `AlgebraicGeometry.isSplitWitness_of_hasWitnessH1Vanishing` — **the forward half**, pointwise.
* `AlgebraicGeometry.isChartDatumPresentation_of_plusFibre_of_converse` — the `↔` assembled from
  the forward half and the one direction still owed, so that a lane closing CHART-U(b) sees
  exactly what is left.
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
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The witness-free hypothesis -/

variable (C π) in
/-- **The datum presents `μ` at every residue field, as plus classes** — the witness-free
content of `IsChartDatumPresentation`.

No witness divisor, no `H¹`, no degree: this says only that the plus class obtained by
restricting `μ` to the residue field at `t` is the plus-unit of the datum's fibre class there.

Isolated as a definition because it is what the forward direction of
`IsChartDatumPresentation` actually consumes, and because it is a statement about the *naturality
of `cechPicClass` under base change to residue fields* — checkable independently of anything
about witnesses. -/
def IsChartDatumPlusFibre {A : Type u} [CommRing A] [Algebra k A]
    (μ : picEt C (overSpec k A)) (D : BasicOpenCocycleDatum C A π) : Prop :=
  ∀ t : (overSpec k A).left,
    PicEtAff.map C (Over.testPointField (T := overSpec k A) t)
        (picEtAffineEquiv C (Over.testPointField (T := overSpec k A) t)
          (picEtMap C (Over.testPoint t) μ))
      = PicEtAff.unit C (Over.testPointField (T := overSpec k A) t)
          (relPicMk C (overSpec k (Over.testPointField (T := overSpec k A) t))
            (Scheme.CechPic.map
              (relCurveMap C A (Over.testPointField (T := overSpec k A) t))
              D.cechPicClass))

/-! ## The forward half -/

variable (C π) in
/-- **The forward half of `IsChartDatumPresentation`, pointwise.**

If the datum presents `μ` at `κ(t)` as plus classes (`IsChartDatumPlusFibre`, which mentions no
witness), then the datum's fibre predicate at `κ(t)` implies the split predicate for `μ`'s fibre.

The proof is the **trivial splitting**: take `L := κ(t)`, the identity extension.  The witness
divisor the datum predicate hands over already lies in the right class and already has vanishing
`H¹`, so nothing has to be transported.  `isSplitWitness_of_presenting_witness_self` is the
instance of the introduction rule this needs, and it is the instance memory I-0564 recorded as
unelaborable — see its docstring in `Picard/Pic0ChartTwistSplit.lean` for why staging the
existentials makes it a one-liner.

Note what this does *not* need: no separability argument, no common refinement, no descent.  All
of that belongs to the converse. -/
theorem isSplitWitness_of_hasWitnessH1Vanishing {A : Type u} [CommRing A] [Algebra k A]
    {μ : picEt C (overSpec k A)} {D : BasicOpenCocycleDatum C A π}
    (hfib : IsChartDatumPlusFibre C π μ D) (t : (overSpec k A).left)
    (h : D.HasWitnessH1Vanishing (Over.testPointField (T := overSpec k A) t)) :
    IsSplitWitness C (picEtMap C (Over.testPoint t) μ) := by
  obtain ⟨W, hW, hW1⟩ := h
  exact isSplitWitness_of_presenting_witness_self C _ _ (hfib t) W hW hW1

/-! ## The `↔`, with the owed direction named -/

variable (C π) in
/-- **`IsChartDatumPresentation` assembled** — the forward half proved, the converse named.

Stated so that a lane closing CHART-U(b) sees exactly one obligation rather than two: given the
witness-free plus-class identity, the `→` direction is free, and what remains is `hconv`.

`hconv` is the descent direction: from a split witness over *some* extension `L_t/κ(t)` chosen
per point, produce the datum's predicate at `κ(t)` itself.  Its two ingredients both exist —
`hasWitnessH1Vanishing_iff_of_fieldExtension` carries a *datum* predicate across a field
extension, and `hfib` identifies the classes — but composing them is not a rewrite, because the
witness received lies in `μ`'s class at `L_t` rather than visibly in `D`'s at `κ(t)`.

**`hconv` IS DISCHARGED as of 2026-07-29** (`Picard/Pic0ChartPresentationConverse.lean`,
`hasWitnessH1Vanishing_of_isSplitWitness_at`), and the diagnosis above was right about the
obstruction while **naming only two of the three ingredients**.  The step that makes the
received witness *visibly* lie in `D`'s class is not a transport at all: it is
`PicEtAff.unit_injective` (`Picard/CechKernelLemma.lean:361`, Kleiman 2.5(1), the unconditional
close of the ζ3 campaign) followed by `relPicMk_injective_of_subsingleton`, which together force
the presenting class `M` to *equal* `D`'s fibre class at `L_t`.  Then
`hasWitnessH1Vanishing_iff_of_fieldExtension` descends it, exactly as predicted.

What the discharge consumes in place of `hconv` is the same plus-class identity as `hfib` but at
an arbitrary extension of `κ(t)` (`IsChartDatumPlusFibreAt`); at `L := κ(t)` it *is* `hfib` by
`Iff.rfl`.  So use `isChartDatumPresentation_of_plusFibre` rather than supplying `hconv` by
hand — this theorem remains correct and is the general form. -/
theorem isChartDatumPresentation_of_plusFibre_of_converse {A : Type u} [CommRing A]
    [Algebra k A] {μ : picEt C (overSpec k A)} {D : BasicOpenCocycleDatum C A π}
    (hfib : IsChartDatumPlusFibre C π μ D)
    (hconv : ∀ t : (overSpec k A).left,
      IsSplitWitness C (picEtMap C (Over.testPoint t) μ) →
        D.HasWitnessH1Vanishing (Over.testPointField (T := overSpec k A) t)) :
    IsChartDatumPresentation C π μ D :=
  fun t => ⟨isSplitWitness_of_hasWitnessH1Vanishing C π hfib t, hconv t⟩

end

end AlgebraicGeometry
