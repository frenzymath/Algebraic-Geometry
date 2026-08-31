/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartSplit
import AlgebraicJacobian.Picard.Pic0ChartTwistCollapse

/-!
# COV-1 input 1: the twisted class splits with a COMPUTABLE Čech representative

`Picard/Pic0ChartSplit.lean` says every plus class over a field is `relPicMk` of an honest
Čech class over *some* finite separable extension.  For the coverage theorem (`w4-datb` §1.2)
that is not enough by itself: the class under test is the *twisted* class
`λ_t · θᵐ · Σ⁻¹`, and COV-1 must know what its presenting Čech class IS, because step 2
of the route computes the presenting class's DEGREE and steps 4–5 build a witness divisor
inside that class.  A bare `∃ M` gives the degree of nothing.

## What this file adds

`exists_splitting_chartTwist` splits the twisted class **and identifies the presenting
class** as

  `M₀ · CechPic.map (relCurveMap C k L) (chartTwistClass C m Z)`,

where `M₀` presents the untwisted fibre class over the same `L`.  So the twist survives
the splitting *as an explicit factor*, and its degree is computable by the landed ledger:
`classDeg` of a base-changed class is base-field invariant (E-iv-alg,
`classDeg_cechPicMap_baseFieldTransition`), so the twist contributes exactly
`m·d₁ − deg Z` and nothing else.

Two landed facts make this cheap, and both were established by this lane earlier today:

* `chartTwist_collapse` (`Picard/Pic0ChartTwistCollapse.lean`) — the twist is ONE
  `thetaFamily`, at the single base class `chartTwistClass C m Z`.  There is no product of
  families to split.
* `thetaFamily_overSpec_affineEquiv` (`Picard/ThetaShift.lean:122`) — a θ-family is
  **already honest at every affine test**: its affine collapse is the plus *unit* of the
  base-changed base class, with no cover and no extension.  So the twist factor needs no
  splitting at all; only the `λ`-factor does.

That second point is the content.  A reader who expects "split a product of two plus
classes" would look for a common refinement of two étale covers.  There is none to find:
one factor is honest over every base, so the splitting of the product is the splitting of
the other factor.

## Main declarations

* `AlgebraicGeometry.picEtAffineEquiv_thetaFamily_eq_unit_relPicMk` — a θ-family is honest at
  every affine test: its collapse is the plus *unit* of the base-changed base class.
* `AlgebraicGeometry.relCurveMap_base_comp` — the base comparison factors through any
  intermediate field of the tower.
* `AlgebraicGeometry.picEtAffineEquiv_map_chartTwistFactor_eq_unit` — **the twisted class
  splits with its presenting class NAMED**: `M₀ · (twist class base-changed to L)`.
* `AlgebraicGeometry.isSplitWitness_of_presenting_witness` — the positional introduction rule
  for `IsSplitWitness`, and the retraction below.
* `AlgebraicGeometry.isSplitWitness_of_presenting_witness_self` — its `L := K` case.
* `AlgebraicGeometry.isSplitWitness_of_witness_twistClass` — what COV-1 consumes: a witness
  divisor for the named class certifies `IsSplitWitness` of the twisted class.

## A RETRACTION this file carries

`isSplitWitness_of_presenting_witness` is a positional introduction rule for `IsSplitWitness`,
which this lane had recorded as **impossible** (the closing note of
`Picard/Pic0ChartSplit.lean`, and memory item I-0564: "measured three times, do not retry").
The old measurement tested five ways of handing the twelve components to *one* anonymous
constructor, and all five do time out.  It did not test **staging** them: eight `Exists.intro`s
in sequence cost nothing at the default heartbeat budget, because `L` is fixed at the first
step and the two curve spellings never race as metavariables.  The trivial splitting `L := K`,
named in that record as the variant worth wanting, follows in one line.  See the theorem's
docstring for the diagnosis and the corrected rule.
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

/-! ## The θ-family is honest at every field point -/

variable (C) in
/-- **A θ-family is honest at every affine test**, in the `PicEtAff` spelling the split
predicate uses: its affine collapse is the plus unit of `relPicMk` of the base-changed base
class.

This is `thetaFamily_overSpec_affineEquiv` (`Picard/ThetaShift.lean:122`) plus
`relPicAlgMap_mk`, and it is the reason the twist needs no splitting: `PicEtAff.unit` is
already the honest reading, so no étale cover ever enters for this factor. -/
theorem picEtAffineEquiv_thetaFamily_eq_unit_relPicMk
    (L₀ : (C ⊗ overSpec k k).left.CechPic) (A : Type u) [CommRing A] [Algebra k A] :
    picEtAffineEquiv C A (thetaFamily C L₀ (overSpec k A))
      = PicEtAff.unit C A (relPicMk C (overSpec k A)
          (Scheme.CechPic.map (relCurveMap C k A) L₀)) := by
  rw [thetaFamily_overSpec_affineEquiv C L₀ A, relPicAlgMap_mk]
  rfl

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
variable (C) in
/-- **The base-change comparison composes**: the relative-curve comparison down to the base
factors through any intermediate field of the tower.  Both sides are `C ◁ Spec` of a
`k`-algebra map into `L`, and there is only one such map out of `k`. -/
theorem relCurveMap_base_comp {K : Type u} [Field K] [Algebra k K]
    {L : Type u} [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L] :
    relCurveMap C k L
      = (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K L)).left ≫ relCurveMap C k K := by
  rw [relCurveMap, relCurveMap, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp]
  refine congrArg (fun ψ : overSpec k L ⟶ overSpec k k => (C ◁ ψ).left)
    (Over.OverMorphism.ext ?_)
  change Spec.map (CommRingCat.ofHom (algebraMap k L))
    = Spec.map (CommRingCat.ofHom (algebraMap K L))
      ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))
  rw [← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext ?_)
  exact (IsScalarTower.algebraMap_eq k K L).symm ▸ rfl

/-! ## The twisted class splits, with its presenting class named -/

variable (C) in
/-- **COV-1 input 1: the twisted class splits, and its presenting Čech class is named.**

If the untwisted plus class `μ` over the field `K` is presented over the finite separable
extension `L/K` by the Čech class `M₀`, then the *twisted* class
`μ · thetaFamily (chartTwistClass m Z)` is presented over the SAME `L` by

  `M₀ · CechPic.map (relCurveMap C k L) (chartTwistClass C m Z)`.

No second extension, no common refinement of covers: the twist factor is honest over every
base (`picEtAffineEquiv_thetaFamily_eq_unit_relPicMk`), so it passes through the splitting
of `μ` untouched, as a multiplicative factor of the presenting class.

This is what makes the degree of the presenting class computable, which is what `w4-datb`
§1.2 steps 2–4 spend: `classDeg L` of the second factor is `classDeg k (chartTwistClass)`
by E-iv-alg, hence `m·d₁ − deg Z`.  A bare `∃ M` splitting would leave that unavailable. -/
theorem picEtAffineEquiv_map_chartTwistFactor_eq_unit
    {K : Type u} [Field K] [Algebra k K] {L : Type u} [Field L] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L]
    (μ : picEt C (overSpec k K)) (M₀ : (relCurve C L).CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K μ)
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) :
    PicEtAff.map C L (picEtAffineEquiv C K
        (μ * thetaFamily C (chartTwistClass C m Z) (overSpec k K)))
      = PicEtAff.unit C L (relPicMk C (overSpec k L)
          (M₀ * Scheme.CechPic.map (relCurveMap C k L) (chartTwistClass C m Z))) := by
  -- the twist factor's fibre at `L`: honest over `K`, then transported to `L`
  have hθ : PicEtAff.map C L (picEtAffineEquiv C K
        (thetaFamily C (chartTwistClass C m Z) (overSpec k K)))
      = PicEtAff.unit C L (relPicMk C (overSpec k L)
          (Scheme.CechPic.map (relCurveMap C k L) (chartTwistClass C m Z))) := by
    rw [picEtAffineEquiv_thetaFamily_eq_unit_relPicMk C (chartTwistClass C m Z) K,
      show PicEtAff.map C L
            (PicEtAff.unit C K (relPicMk C (overSpec k K)
              (Scheme.CechPic.map (relCurveMap C k K) (chartTwistClass C m Z))))
          = PicEtAff.unit C L (relPicAlgMap C (IsScalarTower.toAlgHom k K L)
              (relPicMk C (overSpec k K)
                (Scheme.CechPic.map (relCurveMap C k K) (chartTwistClass C m Z))))
        from PicEtAff.map_unit C L _]
    refine congrArg (PicEtAff.unit C L) ?_
    rw [relPicAlgMap_mk]
    refine congrArg (relPicMk C (overSpec k L)) ?_
    -- `relCurveMap C k K ∘ (base change K → L)` and `relCurveMap C k L` are the same
    -- whisker, since both are `C ◁ Spec` of the unique `k`-algebra map to `L`.
    rw [relCurveMap_base_comp C (K := K) (L := L), Scheme.CechPic.map_comp]
    rfl
  rw [map_mul, map_mul, hM₀, hθ, ← map_mul, ← map_mul]

/-! ## The introduction rule COV-1 uses

Read the docstring of `isSplitWitness_of_presenting_witness` before editing anything here: it
retracts a standing negative result of this lane, and the retraction is what makes the
corollaries possible. -/

variable (C) in
/-- **THE `IsSplitWitness` INTRODUCTION RULE — the one this lane recorded as impossible.**

A presenting Čech class over a finite separable `L`, plus a witness divisor inside it, gives
`IsSplitWitness`.  Nothing here mentions `θ`, `Σ` or a twist; the twisted case is the
corollary below.

**This RETRACTS the "no positional introduction rule exists" record** of
`Picard/Pic0ChartSplit.lean`'s closing note and of the memory item filed with it.  That
record was measured, and its measurement was right about what it tested — five variants, all
timing out at 1000000+ heartbeats:

* `exact`/`refine` with all twelve components as ONE anonymous constructor;
* the witness clause pre-bundled as a `have`;
* either curve spelling normalised to the other;
* `(isSplitWitness_iff_exists_splitting_witness …).mpr` applied to the twelve-tuple;
* the trivial splitting `L := K`.

What none of them tested is **staging the existentials**.  Introducing them one at a time —
eight `Exists.intro`s and a four-component tail — costs nothing at the DEFAULT 200000
heartbeat budget.  The diagnosis the old record gives is still correct: the anonymous
constructor makes Lean unify the seven instance slots *while `L` is still a metavariable*,
re-checking `(relCurve C L).CechPic` against `((C ⊗ overSpec k L).left).CurveDivisor` on each
attempted assignment.  Staging fixes `L` at the first step, so every later component is
checked against a closed type and the two spellings never race.

**The transferable rule**, and it is stronger than the one it replaces: for a deep existential
over types-with-instances, `refine Exists.intro x ?_` repeatedly, rather than one tuple.  The
old advice ("restate the definition with one spelling") would have been a large refactor of a
co-signed definition; the actual fix is a tactic-level one.  Measured, not inferred: this
theorem's own body is the evidence, and the twisted corollary below consumes it. -/
theorem isSplitWitness_of_presenting_witness
    {K : Type u} [Field K] [Algebra k K] (ν : picEt C (overSpec k K))
    {L : Type u} [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    (M : (relCurve C L).CechPic)
    (hM : PicEtAff.map C L (picEtAffineEquiv C K ν)
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M))
    (W : ((C ⊗ overSpec k L).left).CurveDivisor)
    (hW : Scheme.CurveDivisor.picClass L W = M)
    (hW1 : Subsingleton (Sheaf.HModule ((C ⊗ overSpec k L).left.divisorSheaf L W) 1)) :
    IsSplitWitness C ν := by
  refine Exists.intro L ?_
  refine Exists.intro ‹Field L› ?_
  refine Exists.intro ‹Algebra k L› ?_
  refine Exists.intro ‹Algebra K L› ?_
  refine Exists.intro ‹IsScalarTower k K L› ?_
  refine Exists.intro ‹Module.Finite K L› ?_
  refine Exists.intro ‹Algebra.IsSeparable K L› ?_
  refine Exists.intro M ?_
  exact ⟨hM, W, hW, hW1⟩

variable (C) in
/-- **The TRIVIAL splitting `L := K`** — the variant the predecessor record singled out as
"worth wanting" and reported as unelaborable.

At a field where the class is *already* honest, no extension is needed: a witness divisor over
`K` itself certifies `IsSplitWitness`.  The record (I-0564) noted specifically that this one
"fails for elaboration reasons, NOT because the mathematics is wrong".  The mathematics was
indeed fine and the elaboration is fine too, once the existentials are staged — this is a
one-line corollary of the theorem above, at `L := K` with the identity instances.

Why it matters beyond closing a record: this is the **reverse half of
`IsChartDatumPresentation`**, the one residue CHART-U(b) still carries.  The forward half needs
a presenting datum's fibre predicate to imply the split predicate; that direction is the one
this supplies, since a datum over the base gives an honest class at the fibre field with no
extension to find. -/
theorem isSplitWitness_of_presenting_witness_self
    {K : Type u} [Field K] [Algebra k K] (ν : picEt C (overSpec k K))
    (M : (relCurve C K).CechPic)
    (hM : PicEtAff.map C K (picEtAffineEquiv C K ν)
      = PicEtAff.unit C K (relPicMk C (overSpec k K) M))
    (W : ((C ⊗ overSpec k K).left).CurveDivisor)
    (hW : Scheme.CurveDivisor.picClass K W = M)
    (hW1 : Subsingleton (Sheaf.HModule ((C ⊗ overSpec k K).left.divisorSheaf K W) 1)) :
    IsSplitWitness C ν :=
  isSplitWitness_of_presenting_witness C ν M hM W hW hW1

variable (C) in
/-- **COV-1's introduction rule for `chartLocus` membership.**

Given, at the fibre field `K = κ(t)`:
* a finite separable `L/K` and a Čech class `M₀` presenting the *untwisted* fibre class `μ`;
* a divisor `W` on `C_L` whose class is `M₀ · (twist class base-changed to L)` and whose
  `H¹` vanishes,

the *twisted* class `μ · θ^m · Σ⁻¹` satisfies `IsSplitWitness`.  Both hypotheses are what
`w4-datb` §1.2 produces: the first at step 1 (`exists_splitting_of_picEt`), the second at
step 5 (the greedy drop of `RiemannRoch/CoverageDrop.lean`) once step 3 has chosen `m`
against the fibre's own vanishing bound.

The twist is written in the `chartTwistClass` (collapsed) spelling, which is where the
degree bookkeeping happens; `chartTwist_eq_mul_thetaFamily_chartTwistClass` converts. -/
theorem isSplitWitness_of_witness_twistClass
    {K : Type u} [Field K] [Algebra k K] (μ : picEt C (overSpec k K))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {L : Type u} [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    (M₀ : (relCurve C L).CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K μ)
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (W : ((C ⊗ overSpec k L).left).CurveDivisor)
    (hW : Scheme.CurveDivisor.picClass L W
      = M₀ * Scheme.CechPic.map (relCurveMap C k L) (chartTwistClass C m Z))
    (hW1 : Subsingleton (Sheaf.HModule ((C ⊗ overSpec k L).left.divisorSheaf L W) 1)) :
    IsSplitWitness C (μ * thetaFamily C (chartTwistClass C m Z) (overSpec k K)) :=
  isSplitWitness_of_presenting_witness C _ _
    (picEtAffineEquiv_map_chartTwistFactor_eq_unit C μ M₀ hM₀ m Z) W hW hW1

end

end AlgebraicGeometry
