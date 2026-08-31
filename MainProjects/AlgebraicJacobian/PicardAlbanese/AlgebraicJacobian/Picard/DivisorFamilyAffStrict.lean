/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffSeedEndpoint
import AlgebraicJacobian.Picard.DivSchemeCertZarVerdict

/-!
# The R2 widening is **strict** — the payoff, as a theorem rather than a docstring

Protection `I-0492` widened the certificate cover from basic opens of a fixed pair of pinned
`P¹` charts to arbitrary affine opens.  Everything about that widening was landed by
predecessor sessions: the widened carrier, its functoriality, the comparison
`divFunctorToAff`, and the endpoint `exists_isCertified_of_swallowing_affineOpen`.

What was **not** landed is the statement that the widening *buys* anything.  Two facts sat in
the project as separate theorems, and the claim that together they make the widening strict
appeared only in prose — `DivisorFamilyAffCompare.lean:249` says "the converse is FALSE, and
that failure is the content of R2", with no declaration a consumer could cite:

* `DivisorAdaptation.not_isCertified_of_isPreconnected_of_witnesses`
  (`DivSchemeCertZarVerdict.lean`) — a chart-typed adaptation of a **connected** divisor meeting
  both `pi⁻¹(0)` and `pi⁻¹(∞)` carries no certificate, in any degree;
* `exists_isCertified_of_swallowing_affineOpen` (`DivisorFamilyAffStraddle.lean`) — the widened
  layer certifies exactly such a divisor, given the Stacks `0B8B` input.

This file composes them.  The `≤`-direction of the comparison
(`isLocallyCertifiedAff_of_isLocallyCertified`) was already a theorem; a `≤` is only a *strict*
widening once something on the far side is exhibited, and per memory
`reduction-needs-its-converse` a restatement without that exhibit is not a reduction.

## What is proved, and what is assumed

The straddling geometric input is **assumed**, exactly as protection `I-0492` clause 2 directs
(USE Stacks `0B8B`, do not re-derive it) — so the theorems below are conditional on the same
one input the whole lane is conditional on, and on nothing else.  What they add is that this
single input suffices to *separate* the two carriers: no second hypothesis appears on the
chart-typed side, because the refutation needs none.

The separation is **field-independent**: no hypothesis on `|P¹(k)|` occurs anywhere in either
half, which is why R2 and not a field-size hypothesis was the human's answer (`I-0492`).

## SCOPE — the joint inhabitation is NOT exhibited in Lean, and that is deliberate

Read this before quoting the separation as "the widening is strict, proved".  The separation
below is a **conditional**: given a divisor satisfying both the straddling witnesses and the
`0B8B` containment, the two carriers disagree.  Whether such a divisor exists *in this Lean
tree* is a different question, and the honest answer is that no witness is constructed here:

* Mathematically the witness exists over **every** field, including `F₂` — `spec-dd-r.md`
  ADDENDUM 4 §4.3 builds it as `(g−1)Q₀ + Q₁` inside the universal divisor on `Sym^g C`, with no
  rational-point and no `k = k̄` hypothesis.
* Formalising it is explicitly **out of scope** by ADDENDUM 4 §4.5: it needs `Sym^g C` (or
  `Hilb^g`) with its universal flat divisor, mathlib has no symmetric products of schemes and no
  Hilbert or Picard schemes, and this tree constructs no curve other than `P¹`.

So per trap (c) of the axiom-probe catalogue (`I-0442`) these theorems are **not** certified
non-vacuous, and the predecessor's `n = 0` witnesses do not help: those inhabit the widened
endpoint's hypotheses at an EMPTY support locus, which directly contradicts `hx`/`hy` here.  A
straddling divisor has nonempty support by definition.  What the conditional does establish is
that the two carriers are separated *by one named geometric input and nothing else* — no second
hypothesis is smuggled in on the chart-typed side, because the refutation needs none.

## WHY THE REFUTATION DOES NOT ALSO KILL THE WIDENED SIDE

The two conjuncts below look close enough that a reader should be suspicious: both carriers get
per-piece swallow-or-miss from the *same* clopen-trace argument, which needs only that the piece
is **open** (`AffAdaptation.subset_or_disjoint_of_isPreconnected_of_supportLeak`, the chart-free
twin of `DivSchemeCertZarConn.lean:98`). So why is only the chart-typed side refuted?

Because the chart-typed verdict is not the per-piece statement — it is an *upgrade* of it, and the
upgrade is where the pinned pair enters. `supportLocus_subset_chart_of_isPreconnected` runs the
dichotomy at `V₀` and then uses **`relCover_sup`, i.e. `V₀ ⊔ V₁ = ⊤`**, to conclude that a support
missing `V₀` lies in `V₁`. That step consumes the fact that there are exactly **two** charts
covering everything, so "misses this one" forces "inside that one".

A widened `AffCoverData` has `m` pieces with `⨆ j, pieces j = ⊤` and no distinguished pair, so
missing one piece forces nothing — the support can sit inside a piece that is neither, which is
exactly what a straddling `W` from Stacks `0B8B` is. The widened layer therefore has swallow-or-miss
and **no** confinement verdict, and that asymmetry is the whole content of R2 rather than an
oversight. Grepping for a widened analogue of `supportLocus_subset_chart_*` returns nothing, and
the paragraph above is why nothing is missing.

## Main declarations

* `AlgebraicGeometry.isCertified_affine_and_not_isCertified_chart` — the separation at one
  divisor: some widened adaptation is certified while **no** chart-typed adaptation is, in any
  degree.
* `AlgebraicGeometry.exists_affAdaptation_isCertified_of_straddling` — the widened half alone,
  packaged so a consumer need not name the cover.
* `AlgebraicGeometry.forall_not_isCertified_of_straddling` — the chart-typed half alone, with
  the quantifier over adaptations *and* degrees made explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

/-! ## The chart-typed side: no adaptation, in no degree

The refutation is already a theorem; what this section adds is the quantifier shape a
separation statement needs.  `not_isCertified_of_isPreconnected_of_witnesses` is stated about
one adaptation `A` and one degree `n`; the widening claim is about *all* of them, and that
strengthening is free because the hypotheses mention neither. -/

/-- **The chart-typed carrier cannot see a straddling connected divisor — for any adaptation,
in any degree.**

`hx₀`/`hy₁` are the witnesses that the support genuinely meets both pinned vertical fibres:
a point outside `V₀` and a point outside `V₁`.  Note that no leak hypothesis appears — clause
(c1) of `IsCertified` supplies it, which is what makes this a statement about the interface
rather than about a failed proof attempt. -/
theorem forall_not_isCertified_of_straddling
    {d : (relCurve C R).LocalEquations}
    (hconn : _root_.IsPreconnected d.supportLocus)
    {x y : relCurve C R} (hx : x ∈ d.supportLocus) (hy : y ∈ d.supportLocus)
    (hx₀ : x ∉ ((relCover C R (fiberTwoCover pi)).V₀ : Set (relCurve C R)))
    (hy₁ : y ∉ ((relCover C R (fiberTwoCover pi)).V₁ : Set (relCurve C R))) :
    ∀ (A : DivisorAdaptation C R pi d) (n : ℕ), ¬ A.IsCertified n :=
  fun A _ => A.not_isCertified_of_isPreconnected_of_witnesses hconn hx hy hx₀ hy₁

/-! ## The widened side: a certificate exists

Nothing here is new mathematics — it is `exists_isCertified_of_swallowing_affineOpen` with the
cover existentially closed, so that the separation statement below reads as a comparison of two
carriers rather than as a comparison of two cover shapes. -/

/-- **The widened carrier does certify it**, from the Stacks `0B8B` input in its subordinate
form together with the fibrewise and rank data.  Stated with the cover packaged away. -/
theorem exists_affAdaptation_isCertified_of_straddling [IsNoetherianRing R]
    {n : ℕ} (d : (relCurve C R).LocalEquations)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : d.supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ d.cover.opens z₀)
    (hfib : ∀ (D : AffCoverData C R) (A : AffAdaptation D d) (j : D.index)
      (p : PrimeSpectrum R),
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors (Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField))
    (hrank : ∀ (D : AffCoverData C R) (A : AffAdaptation D d) (p : PrimeSpectrum R),
      Module.rankAtStalk A.Glued p = n) :
    ∃ (D : AffCoverData C R) (A : AffAdaptation D d), A.IsCertified n :=
  exists_isCertified_of_swallowing_affineOpen C R d hW hsub z₀ hWle hfib hrank

/-! ## The separation

This is the theorem the lane existed to produce.  Read the two conjuncts together: the same
divisor `d`, in the same degree `n`, over the same base — certified on an arbitrary affine-open
cover, and refutably uncertifiable on any cover subordinate to the pinned chart pair. -/

/-- **THE R2 PAYOFF: the widening is strict.**

For a connected divisor straddling both pinned vertical fibres of `pi`, given the Stacks
`0B8B` input (an affine open `W` containing its support, inside a member of its cover):

* **some** widened adaptation is certified in degree `n`;
* **no** chart-typed adaptation is certified, in **any** degree.

So `isLocallyCertifiedAff_of_isLocallyCertified` is a strictly-increasing comparison and not a
repackaging: there is a divisor on the widened side of it and nothing on the chart-typed side
can reach.  This is what protection `I-0492` bought, and until now it was asserted only in a
docstring (`DivisorFamilyAffCompare.lean:249`).

**No hypothesis on `|P¹(k)|` appears in either half.** That is the field-uniformity R2 was
chosen for: enlarging the field is not what makes the chart-typed side fail, so it is not what
the widening repairs.

**Conditional, and not certified non-vacuous** — see the SCOPE section of the module docstring.
The hypothesis set is inhabited mathematically over every field (ADDENDUM 4 §4.3) but no witness
is constructible in this tree (§4.5), and the existing `n = 0` non-vacuity witnesses are
incompatible with `hx`/`hy`, which force the support to be nonempty. -/
theorem isCertified_affine_and_not_isCertified_chart [IsNoetherianRing R]
    {n : ℕ} (d : (relCurve C R).LocalEquations)
    (hconn : _root_.IsPreconnected d.supportLocus)
    {x y : relCurve C R} (hx : x ∈ d.supportLocus) (hy : y ∈ d.supportLocus)
    (hx₀ : x ∉ ((relCover C R (fiberTwoCover pi)).V₀ : Set (relCurve C R)))
    (hy₁ : y ∉ ((relCover C R (fiberTwoCover pi)).V₁ : Set (relCurve C R)))
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : d.supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ d.cover.opens z₀)
    (hfib : ∀ (D : AffCoverData C R) (A : AffAdaptation D d) (j : D.index)
      (p : PrimeSpectrum R),
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors (Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField))
    (hrank : ∀ (D : AffCoverData C R) (A : AffAdaptation D d) (p : PrimeSpectrum R),
      Module.rankAtStalk A.Glued p = n) :
    (∃ (D : AffCoverData C R) (A : AffAdaptation D d), A.IsCertified n)
      ∧ ∀ (A : DivisorAdaptation C R pi d) (m : ℕ), ¬ A.IsCertified m :=
  ⟨exists_affAdaptation_isCertified_of_straddling d hW hsub z₀ hWle hfib hrank,
    forall_not_isCertified_of_straddling hconn hx hy hx₀ hy₁⟩

end AlgebraicGeometry
