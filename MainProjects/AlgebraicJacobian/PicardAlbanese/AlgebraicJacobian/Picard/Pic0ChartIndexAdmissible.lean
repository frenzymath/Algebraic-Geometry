/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ThetaShift
import AlgebraicJacobian.RiemannRoch.SectionSpaces

/-!
# The chart-index binder `hdeg` is EXACTLY "`n` is a divisor degree" — and the θ-exponent is idle

**Twenty-one** files in the chart layer bind the same hypothesis verbatim
(`Pic0ChartPair.lean:176`, `Pic0ChartRestrictedFibre.lean:147`, `Pic0SigmaSheaf`'s consumers
through `abelSigmaChart`, …).  A first draft of this line said twenty-three; re-measure rather
than quote it — the count is
`grep -rl "classDeg k (thetaCechClass C) - (n : ℤ))" AlgebraicJacobian/`, excluding this file and
`Pic0ChartIndexLedgerFeed`.  Counting *any* spelling of the shape (so including the per-index
`(nn i : ℤ)` form) gives 26, and 65 files bind a hypothesis *named* `hdeg` in some form; the
figure that matters for this file is the first, since it is the exact binder the theorems below
are about.  The hypothesis:

  `hdeg : deg_k Z = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)`

with `m : ℕ` the twist exponent, `Z` the chart index and `n` the chart parameter.  **No file
produces one.**  Every declaration mentioning it takes it as an argument, and the two theorems
that conclude an `∃` over `(m, Z)` — `exists_chartIndex_mem_chartLocus_of_ledgerIndex`
(`Pic0ChartCoverageThreshold.lean:349`) and `Pic0ChartCoverageNoDrop.lean:265` — take the same
constraint as a hypothesis and say so in their docstrings.  So the whole chart layer is
quantified over a datum whose inhabitation nothing had measured.

This file measures it, and the answer is an equivalence with no geometry in it.

## What is proved

`chartIndex_iff_isDegree`: for any target `c : ℤ`,

  `(∃ m Z, deg_k Z = m·d₁ − c)  ↔  (∃ W, deg_k W = c)`

so the binder carries **exactly** the information that `c` lies in the image of
`deg_k : CurveDivisor → ℤ`, and nothing else.

Two consequences worth stating separately, because both correct a live pricing:

* **The θ-exponent `m` is idle.**  The backward direction takes `m = 0` and `Z = −W`
  (`chartIndex_of_isDegree`).  Every consumer's `m` is therefore free to be chosen for
  *other* reasons; `hdeg` places no constraint on it, and a lane that reads the binder as
  coupling `m` to `n` (the shape `Pic0ChartCoverageIndexSlack`'s `ledger_forces_b_eq_n`
  suggests) is reading a coupling that the *chart parameter* creates, not this hypothesis.
* **Admissibility is shift-invariant and subgroup-closed** (`isDegree_add_mul_iff`,
  `isDegree_sub`): the admissible targets are an additive subgroup of `ℤ` containing every
  multiple of `d₁`.  So admissibility at `n` and at `n + a·d₁` are the same statement — which
  is what bears on parameter matching (`I-1345`): moving a chart parameter by a multiple of the
  θ-degree is free on the `hdeg` side.

## What this does NOT do, stated plainly

It does **not** exhibit an admissible `n` other than the multiples of `d₁`.  The equivalence is
a reduction, not an inhabitation: over an arbitrary base field `deg_k` is weighted by residue
degrees (`RiemannRoch/Divisor.lean:61`), so its image is a proper subgroup `index·ℤ` in general,
and the tree's only route to a residue-degree-one point needs `[IsSepClosed k]`
(`Curve/SepPointsDense.lean:278`), which `archon-protected.yaml`'s arbitrary-field statement
forbids assuming.  **So `hdeg` at `n = g` is NOT known to be satisfiable**, and this file does
not claim it is.  What it establishes is that the question is arithmetic — the image of one
group homomorphism — rather than anything about charts, certificates or representability.

Nor does it discharge any antecedent of `pic0RepresentableByOfCharts`: `IsChartUniv`, coverage
and `rep` are untouched.  What it removes is an obligation nobody had noticed was there, and it
tells three other rows which parameter moves are free.

## Main declarations

* `AlgebraicGeometry.IsDivisorDegree` — the predicate "`c` is the degree of some divisor".
* `AlgebraicGeometry.chartIndex_of_isDegree` — the producer, with `m = 0`.
* `AlgebraicGeometry.isDegree_of_chartIndex` — the converse, so nothing is weakened.
* `AlgebraicGeometry.chartIndex_iff_isDegree` — the equivalence.
* `AlgebraicGeometry.isDegree_mul_thetaDeg` — every multiple of `d₁` is admissible.
* `AlgebraicGeometry.isDegree_add_mul_iff` — shift-invariance by multiples of `d₁`.
* `AlgebraicGeometry.isDegree_mul_thetaDeg_add_iff` — the same, with the multiple written first,
  which is the shape the ledger consumer's target `M·δ + g` has.
* `AlgebraicGeometry.isDegree_sub` — subgroup closure.
-/

set_option autoImplicit false
/- Statements mix `relCurve`-style spellings with the product `(C ⊗ overSpec k k).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-! ## The predicate -/

variable (C) in
/-- **`c` is a divisor degree on the base-changed curve `C_k = (C ⊗ overSpec k k).left`.**

Named rather than inlined so that the three shift/closure facts below are about one object and
are findable by a name search, and so that consumers of `hdeg` can cite the reduction rather
than re-deriving it (the `I-1341` lesson: an inlined `have` is invisible to every search). -/
def IsDivisorDegree (c : ℤ) : Prop :=
  ∃ W : (C ⊗ overSpec k k).left.CurveDivisor, Scheme.CurveDivisor.deg k W = c

/-! ## The equivalence -/

variable (C) in
/-- **The producer: `hdeg` at parameter `c` from a divisor of degree `c`, with `m = 0`.**

The witness is `⟨0, -W⟩`.  This is the direction that matters for the 23 consumers, and the
fact that `m = 0` works is the measurement that the θ-exponent is *not* coupled to the chart
parameter by this hypothesis. -/
theorem chartIndex_of_isDegree {c : ℤ} (h : IsDivisorDegree C c) :
    ∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor),
      Scheme.CurveDivisor.deg k Z = (m : ℤ) * classDeg k (thetaCechClass C) - c := by
  obtain ⟨W, hW⟩ := h
  refine ⟨0, -W, ?_⟩
  rw [Scheme.CurveDivisor.deg_neg, hW]
  ring

variable (C) in
/-- **The converse**, so this file claims no reduction it has not earned (the `I-0896`
criterion): from any legal chart index at parameter `c`, the parameter *is* a divisor degree.

The witness is `m • F − Z` for `F` the fibre Weil divisor of `thetaP1 C`, whose degree is
`d₁ = classDeg k (thetaCechClass C)` by `classDeg_fiberTwist_one`. -/
theorem isDegree_of_chartIndex {c : ℤ} (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - c) :
    IsDivisorDegree C c := by
  haveI := isFinite_thetaP1 (C := C)
  haveI := isDominant_thetaP1 (C := C)
  refine ⟨m • fiberWeilDivisor (thetaP1 C) - Z, ?_⟩
  rw [Scheme.CurveDivisor.deg_sub' k, Scheme.CurveDivisor.deg_nsmul' k, hdeg,
    ← classDeg_fiberTwist_one (thetaP1 C)]
  change (m : ℤ) * classDeg k (thetaCechClass C)
    - ((m : ℤ) * classDeg k (thetaCechClass C) - c) = c
  ring

variable (C) in
/-- **THE MEASUREMENT**: the chart-index binder carries exactly "`c` is a divisor degree".

Both directions are one rewrite each.  The content is not the proof — it is that the question
"is the chart layer's `hdeg` inhabitable, and at which parameters?" is the question "what is the
image of `deg_k`?", with no chart, certificate or representation in it. -/
theorem chartIndex_iff_isDegree (c : ℤ) :
    (∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor),
      Scheme.CurveDivisor.deg k Z = (m : ℤ) * classDeg k (thetaCechClass C) - c)
    ↔ IsDivisorDegree C c :=
  ⟨fun ⟨m, Z, hZ⟩ => isDegree_of_chartIndex C m Z hZ, chartIndex_of_isDegree C⟩

/-! ## What IS inhabited, and how admissibility moves -/

variable (C) in
/-- **Every multiple of the θ-degree is admissible** — `a` copies of the fibre divisor.

This is the only inhabitation this file offers, and it is honest about being weak: it says the
chart layer can be run at `n` a multiple of `d₁`, and says nothing about `n = g`. -/
theorem isDegree_mul_thetaDeg (a : ℕ) :
    IsDivisorDegree C ((a : ℤ) * classDeg k (thetaCechClass C)) := by
  haveI := isFinite_thetaP1 (C := C)
  haveI := isDominant_thetaP1 (C := C)
  refine ⟨a • fiberWeilDivisor (thetaP1 C), ?_⟩
  rw [Scheme.CurveDivisor.deg_nsmul' k, ← classDeg_fiberTwist_one (thetaP1 C)]
  rfl

variable (C) in
/-- **Shift-invariance by multiples of `d₁`**, in both directions.

This is the fact that bears on parameter matching (`I-1345`, and `Pic0ChartAtlasParamFree`'s
question "at which parameters is `divFunctor C π n` representable?"): on the `hdeg` side,
moving a chart parameter by a multiple of the θ-degree costs nothing.  It does **not** say the
`rep` side moves — that is the open half. -/
theorem isDegree_add_mul_iff (c : ℤ) (a : ℕ) :
    IsDivisorDegree C c
      ↔ IsDivisorDegree C (c + (a : ℤ) * classDeg k (thetaCechClass C)) := by
  haveI := isFinite_thetaP1 (C := C)
  haveI := isDominant_thetaP1 (C := C)
  have hF : Scheme.CurveDivisor.deg k (a • fiberWeilDivisor (thetaP1 C))
      = (a : ℤ) * classDeg k (thetaCechClass C) := by
    rw [Scheme.CurveDivisor.deg_nsmul' k, ← classDeg_fiberTwist_one (thetaP1 C)]
    rfl
  constructor
  · rintro ⟨W, hW⟩
    exact ⟨W + a • fiberWeilDivisor (thetaP1 C), by
      rw [Scheme.CurveDivisor.deg_add, hW, hF]⟩
  · rintro ⟨W, hW⟩
    refine ⟨W - a • fiberWeilDivisor (thetaP1 C), ?_⟩
    rw [Scheme.CurveDivisor.deg_sub' k, hW, hF]
    ring

omit [IsProper C.hom] in
variable (C) in
/-- **The admissible targets are closed under subtraction** — hence an additive subgroup of
`ℤ`, since `0` is admissible by `W = 0`.

Recorded because it is what makes "the image of `deg_k` is `index·ℤ`" a *theorem shape* rather
than a docstring remark: three files assert the `index·ℤ` form in prose
(`JacobianDataAbelDegreeWindow.lean:23`, `:200`, `JacobianDataAbelEffective.lean:128`) and none
states it. -/
theorem isDegree_sub {c c' : ℤ} (h : IsDivisorDegree C c) (h' : IsDivisorDegree C c') :
    IsDivisorDegree C (c - c') := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨W', hW'⟩ := h'
  exact ⟨W - W', by rw [Scheme.CurveDivisor.deg_sub' k, hW, hW']⟩

omit [IsProper C.hom] in
variable (C) in
/-- `0` is admissible, by the zero divisor — the subgroup's unit. -/
theorem isDegree_zero : IsDivisorDegree C 0 :=
  ⟨0, by simp⟩

variable (C) in
/-- **A target of the shape `a·d₁ + c` is admissible exactly when `c` is** — the form the
ledger consumer meets, with the summands in the order the ledger writes them.

`isDegree_add_mul_iff` with the sum commuted.  Recorded separately because the coverage
consumer's target is `M·δ + g`, i.e. the multiple **first**, and a consumer should not have to
insert a `ring` step to use the shift.  This is the fact that turns the residue of
`Pic0ChartIndexLedgerFeed`'s ledger theorem into a question about the **genus** rather than
about the ledger constants — *provided* `M·δ` is a multiple of `d₁`, which is a separate
hypothesis about `π` versus `thetaP1 C` and is **not** proved anywhere.

What *is* free, measured by `rfl` and recorded so nobody prices it: `windowδ (thetaP1 C)` and
`classDeg k (thetaCechClass C)` are the same term, both unfolding to
`classDeg k (fiberTwist (thetaP1 C) 1)`.  So no `windowδ`-versus-`classDeg` plumbing is owed.

A first draft added "so the open gap is two maps to `ℙ¹` on **two different curves**", and that
was **false** — the two curves differ by base change along `k → k`, which is an isomorphism, and
`Pic0ChartIndexLedgerFeed.isDivisorDegree_iff_left` transports this whole predicate to `C.left`
from declarations that were already in scope.  Withdrawn.  The open gap is the two **maps** on
**one** curve: is `deg (fibre of π)` commensurable with `deg (fibre of thetaP1 C)`? -/
theorem isDegree_mul_thetaDeg_add_iff (a : ℕ) (c : ℤ) :
    IsDivisorDegree C ((a : ℤ) * classDeg k (thetaCechClass C) + c)
      ↔ IsDivisorDegree C c := by
  have hcomm : c + (a : ℤ) * classDeg k (thetaCechClass C)
      = (a : ℤ) * classDeg k (thetaCechClass C) + c := by ring
  refine ⟨fun h => (isDegree_add_mul_iff C c a).mpr (by rwa [hcomm]), fun h => ?_⟩
  have := (isDegree_add_mul_iff C c a).mp h
  rwa [hcomm] at this

end AlgebraicGeometry
