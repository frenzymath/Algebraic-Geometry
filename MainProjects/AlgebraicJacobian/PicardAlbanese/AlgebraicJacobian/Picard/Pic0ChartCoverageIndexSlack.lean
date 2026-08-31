/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageNoDrop
import AlgebraicJacobian.Picard.Pic0ChartCoverageDegreeStep2

/-!
# B-5 step 3: `b = n` IS FORCED, AND IT IS THE CALIBRATION, NOT A DEFECT (I-0660 adjudicated)

A reviewer (I-0660) measured that `mem_chartLocus_of_vanishing_bound`
(`Picard/Pic0ChartCoverageNoDrop.lean:134`) has a hypothesis pack that **forces `b = g`**, and
concluded that its `hb` "cannot be DAT-0a's threshold" and that step 3 is therefore not
"derived".  **The arithmetic is right; the conclusion is one step too strong, and this file
settles which parts stand.**

## What is confirmed, and it is a real correction to this lane's prose

`ledger_forces_b_eq_n` reproduces the reviewer's derivation and generalises it: at a chart index
legal at parameter `n` — i.e. satisfying the constraint `deg_k Z = m·d₁ − n` that
`chartValueTrans` / `chartValue_mem_pic0Subgroup` (`DivSchemeAbel.lean:382`) require — the
hypothesis `hdeg` of `mem_chartLocus_of_vanishing_bound` **determines `b`**, and `b = n`.  So
`b` is *not* a free parameter that DAT-0a may instantiate: the chart index pins it.

`hb_forces_h0_eq_one` then shows what `hb` at `b = n` amounts to on a genus-`g` curve at `n = g`:
**every** degree-`g` divisor has `h⁰ = 1`.  That is false on any curve with a degree-`g`
effective divisor moving in a positive-dimensional family, and it is strictly stronger than
every threshold theorem in the tree (DAT-0a's bound is `n₁·deg F + 1 − χ = n₁·deg F + g` with
`0 < deg F`, so it exceeds `g` as soon as `n₁ ≥ 1`).  The reviewer's reading of the *strength*
is therefore confirmed, and sharpened: it is not merely "stronger than a threshold result", it
is a statement the χ-ledger converts into an `h⁰` equality for every divisor at once.

## What does NOT follow — and this is the correction to the reviewer

The reviewer's conclusion assumes `n = g`.  **`n` is a free parameter of the entire chart
layer.**  `divFunctor C π n`, `chartValue C π n m Z`, `chartValueTrans C π n m Z hdeg` and
`abelSigmaChart C π n rep m Z hdeg` are all stated for an arbitrary `n : ℕ`; nothing in
`Pic0AtlasFromDivRep.lean` or `DivSchemeAbel.lean` pins it.  `n = g` is where the *divisor
representability lane* instantiates (`divFunctor_representableBy_of_chartClause`,
`DivRepAffPullClause.lean:475`), and where `Pic^0` has the right dimension — but the coverage
theorem does not know that.

So `b = n` is a **calibration equation between two independently chosen numbers**, and reading
it as "an over-constraint" versus "the definition of the chart parameter" depends entirely on
which of `n` and `b` is free.  `index_of_threshold` records the direction that is actually
available: given DAT-0a's threshold `b ≥ 0` at the splitting field, a chart index constraint at
parameter `b.toNat` makes `hdeg` hold **by construction**.  There is no obstruction to
satisfying `hdeg`; the obstruction is that satisfying it *at n = g* requires the sharp
vanishing.

## THE HONEST STATUS OF STEP 3, therefore

Three statements, all now machine-checked, none of which was the one the roadmap carried:

1. `hdeg` is satisfiable, for every threshold `b ≥ 0`, at the chart parameter `n := b.toNat`
   (`index_of_threshold`).  So coverage-at-a-chart-index is not blocked.
2. At the *representability* parameter `n = g`, `hdeg` forces `b = g`, and `hb` at `b = g` is
   the sharp vanishing — **not available, and not expected to be true**
   (`hb_forces_h0_eq_one`).
3. Hence the residue is neither "instantiate DAT-0a" (the roadmap's claim, too optimistic) nor
   "restate with slack" (the reviewer's repair, which as they themselves note runs into the
   `0 ≤ Σ` legality of the index).  It is: **reconcile the chart parameter with the threshold.**

**SHARPENED 2026-07-30 (`Picard/Pic0ChartCoverageThreshold.lean`, inbox `I-1329`): item 3
above reasons about "the threshold" as a per-fibre quantity still to be obtained.  It is not
per-fibre, and it is already available.**  The two halves:

* ~~DAT-0a itself really is *not* instantiable at a splitting field `L`~~ — **this bullet was
  FALSE and is retracted the same day it was written** (audit + author reproduction, inbox
  `I-1349`/`I-1350`).  `exists_isFinite_isDominant_toP1` (`Curve/MapToP1.lean:126`) produces
  the morphism for any bundle meeting the curve hypotheses, and `Curve/BaseChangeInstances.lean`
  supplies those for `baseChangeBundle C L`, so DAT-0a **is** instantiable at `L` in three
  `haveI`s.  The error was grepping for the arrow as a term when the answer was an
  `exists_`-producer quantified over curves.
* But the threshold does not need DAT-0a.  `subsingleton_hModule_one_of_witness`
  (`RiemannRoch/WindowFieldTransport.lean:87`) is the **π-free** peeling — one witness with
  vanishing `H¹` bounds every divisor of degree `≥ deg W₀ + 1 − χ` — and `windowN C L hπ g` is
  such a witness at every `L`.  Since `windowM_choice` and `windowδ` are *base-field* ledger
  constants, the resulting bound `M·δ + g` does not mention `L`: **one threshold for all
  fibres** (`subsingleton_h1_of_ledger_bound`, and
  `exists_uniform_bound_forall_baseChange` for the `∃ b, ∀ L` shape).

Where this account went wrong is worth naming, since the sentence reads as measured: "no
uniform `m₀` exists" (I-0204) is about the per-field ledger *constants* not transporting —
true, and why the window lane transports window *facts*.  It does not follow that the induced
*threshold* is per-field, because the transported witness carries a base-field degree.

**What is not affected.**  Items 1 and 2 stand verbatim; in particular `hb_forces_h0_eq_one`
is untouched, and `M·δ + g` exceeds `g` (as `δ ≥ 1`), so the uniform threshold is *not* a route
to `b = g`.  The residue that replaces item 3 is **parameter matching**: coverage now reaches
the parameter `M·δ + g`, the divRep endpoint supplies `rep` at the parameter its own `hchi`
pins, and `genus_eq_zero_of_ledgerParam_eq_genus` proves those coincide only when `g = 0`.
   The chart family the atlas glues may be indexed by `m`, and `d₁ = classDeg k Θ > 0`, so the
   available move is to let the chart index *at parameter g* carry the slack in `Z` rather than
   in `n` — which is exactly `classDeg_presenting_twist_eq_add`'s `g + e` shape, whose own
   legality (`0 ≤ Σ`) is the open question.

That is a genuinely different residue from the one the roadmap and the reviewer each named, and
it is recorded here rather than in prose only.

## Main declarations

* `AlgebraicGeometry.ledger_forces_b_eq_n` — the reviewer's derivation, at general `n`.
* `AlgebraicGeometry.index_of_threshold` — the converse: every nonneg threshold is realised as
  the ledger value of a legal index at parameter `b.toNat`.
* `AlgebraicGeometry.hb_forces_h0_eq_one` — what `hb` at `b = n` costs: on a curve with
  `χ = 1 − n`, every degree-`n` divisor has `h⁰ = 1`.
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
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The reviewer's derivation, at a general chart parameter -/

variable (C) in
/-- **THE CHART INDEX DETERMINES THE THRESHOLD** (I-0660, confirmed and generalised).

At a chart index legal at parameter `n` — the constraint `deg_k Z = m·d₁ − n` that
`chartValue_mem_pic0Subgroup` requires for the chart value to land in `pic^0` — the hypothesis
`hdeg` of `mem_chartLocus_of_vanishing_bound` is *not* a way of feeding in a threshold: it
**forces** `b = n`.

The reviewer stated this at `n = g` and read it as a defect.  Read at general `n` it is a
calibration: `b` and `n` are two independently chosen naturals and the ledger equates them.
Which one is "over-constrained" depends on which is free — see `index_of_threshold` for the
other direction, and the module docstring for why `n = g` is the case where this bites. -/
theorem ledger_forces_b_eq_n {K : Type u} [Field K] [Algebra k K]
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : overSpec k K ⟶ T)
    (hlam : degAt lam t = 0)
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (M₀ : (C ⊗ overSpec k L).left.CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K (picEtMap C t lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (m n : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hZ : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (b : ℤ)
    (hdeg : classDeg L (M₀ * Scheme.CechPic.map
      ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left) (chartTwistClass C m Z)) = b) :
    b = (n : ℤ) := by
  rw [classDeg_presenting_twist C lam t hlam L M₀ hM₀ m Z, hZ] at hdeg
  omega

variable (C) in
/-- **The converse direction: every nonnegative threshold is realised.**

Given a threshold `b ≥ 0` and a legal chart index at parameter `b.toNat`, the `hdeg` of
`mem_chartLocus_of_vanishing_bound` holds **by construction**.  So `hdeg` is not an
unsatisfiable hypothesis and coverage-at-a-chart-index is not blocked by it — which is the half
of the reviewer's report that needs correcting.

What this does *not* do is put the index at the representability parameter `n = g`.  That is the
whole remaining question, and `hb_forces_h0_eq_one` says what it would cost to answer it by
taking `b = g`. -/
theorem index_of_threshold {K : Type u} [Field K] [Algebra k K]
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : overSpec k K ⟶ T)
    (hlam : degAt lam t = 0)
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (M₀ : (C ⊗ overSpec k L).left.CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K (picEtMap C t lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) (b : ℤ) (hb0 : 0 ≤ b)
    (hZ : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - b) :
    classDeg L (M₀ * Scheme.CechPic.map
        ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left) (chartTwistClass C m Z))
      = ((b.toNat : ℕ) : ℤ) := by
  rw [classDeg_presenting_twist C lam t hlam L M₀ hM₀ m Z, hZ, Int.toNat_of_nonneg hb0]
  ring

/-! ## What the threshold hypothesis costs at `b = n` -/

/-- **`hb` at `b = n` is the SHARP vanishing, and the χ-ledger turns it into an `h⁰` equality.**

If every divisor of degree `≥ n` on the base-changed curve has `H¹ = 0`, then on a curve with
`χ(𝒪) = 1 − n` **every** divisor of degree exactly `n` has `h⁰ = 1`.

This is the sharpened form of the reviewer's strength observation.  Their version — "strictly
stronger than any threshold result" — is a comparison with what the tree has; this is a
comparison with what is *true*: for `n = g ≥ 1` a degree-`g` divisor may well have `h⁰ ≥ 2` (any
`g`-tuple of points imposing dependent conditions), so `hb` at `b = g` is not merely unproved,
it is **false in general**.  Hence there is no route to B-5 that instantiates DAT-0a at `b = g`,
and the residue is the chart-parameter reconciliation described in the module docstring.

One line from the rank anchor `h0_eq_deg_add_chi_of_subsingleton_hModule_one`
(`RiemannRoch/FLVClass.lean:412`) — recorded because the whole argument fits in it and the
conclusion is worth having in Lean rather than in a review comment. -/
theorem hb_forces_h0_eq_one
    {L : Type u} [Field L] [Algebra k L]
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)]
    (n : ℕ) (hχ : Sheaf.chi (((C ⊗ overSpec k L).left).moduleKSheaf L) = 1 - (n : ℤ))
    (hb : ∀ D : ((C ⊗ overSpec k L).left).CurveDivisor,
      (n : ℤ) ≤ Scheme.CurveDivisor.deg L D →
        Subsingleton (Sheaf.HModule ((C ⊗ overSpec k L).left.divisorSheaf L D) 1))
    (D : ((C ⊗ overSpec k L).left).CurveDivisor)
    (hD : Scheme.CurveDivisor.deg L D = (n : ℤ)) :
    (Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L D) : ℤ) = 1 := by
  have h1 := hb D (le_of_eq hD.symm)
  have hanchor := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := L) D h1
  rw [hD, hχ] at hanchor
  omega

end

end AlgebraicGeometry
