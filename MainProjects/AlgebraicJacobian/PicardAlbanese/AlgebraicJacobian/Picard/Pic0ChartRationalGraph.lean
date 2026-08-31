/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageDegree
import AlgebraicJacobian.Picard.Pic0ChartIndexAdmissible
import AlgebraicJacobian.RiemannRoch.GraphDegree

/-!
# Base-changing the chart index — via GRAPH classes, not via divisors

**TITLE CORRECTED and the framing below narrowed (2026-07-28, issue I-0615).**  This file was
titled "COV-1 input 3" and presented as serving `w4-datb` §1.2 step 6.  **COV-1 does not need
it**: coverage needs no drop, hence no repackaging of a drop divisor as a chart index, because
`IsSplitWitness` asks for `h¹ = 0` and for neither effectivity nor degree `g`
(`Picard/Pic0ChartCoverageNoDrop.lean`).  What is below is still true and still useful — it is the
right tool wherever a `k`-rational point's divisor class must reach a fibre field, which is what
DAT-C's canonical section and GAP-2 uniqueness need — but it is not a coverage input.

The obligation as originally framed: `w4-datb` §1.2 step 6 has to package the drop divisor as a
chart index, and the chart index
`Z` is a `CurveDivisor` on the **base** curve `(C ⊗ overSpec k k).left` (frozen, `w4-datc`
§3.2) while the drop of `RiemannRoch/CoverageDrop.lean` produces its divisor over the
**fibre field** `L`.  Relating the two looks like it needs a base-change operation on
`CurveDivisor`.

**There is none in the tree, and none is needed.**  What the coverage argument actually has to
compare is not two divisors but their two *Picard classes*, and for the divisors that occur —
one-point divisors at `k`-rational points, which is exactly what the density oracle
(`Curve/SepPointsDense.lean`) supplies — the class-level base change is **already landed**:

  `Over.graphLocalEquations_base_change` (`Curve/GraphDivisor.lean:263`) :
      `graphPicClass C (g ≫ t) = CechPic.map (C ◁ g).left (graphPicClass C t)`

and a `k`-rational point's graph class *is* the class of its one-point divisor:

  `Over.graphPicClass C t = picClass K (single (graphPoint C t) (ord …))`
      (`presentationDivisor_graphLocalEquations`, `RiemannRoch/GraphDegree.lean:422`,
       through `picClass_presentationDivisor`),

with `classDeg = 1` on the nose (`classDeg_graphPicClass`, `:445`).

So the route is: **never base-change a divisor; base-change the graph class of the point and
re-present it downstairs.**  A `k`-point `p : overSpec k k ⟶ C` has a graph class over the base
curve; restricting it along `overSpecMap (Algebra.ofId k L)` gives the graph class of the same
point read over `L`, which is a one-point class of degree one there.

## Why this is the right shape for the chart index

The chart index constraint is a statement about `deg_k Z`.  Summing `e` graph classes of
`k`-points gives a base-curve class of degree `e` whose base change to any `L` is the
corresponding sum downstairs — so the constraint is checked once, at `k`, and transported for
free.  Nothing per-field, no ledger constant crossing (the I-0204 discipline).

## Main declarations

* `AlgebraicGeometry.graphPicClass_base_of_field` — the graph class of a `k`-point
  base-changes to the graph class of the induced `L`-point, in the `Algebra.ofId` spelling
  the chart layer uses.
* `AlgebraicGeometry.classDeg_graphPicClass_base` — its degree is one at every field, by
  E-iv-alg composed with the landed degree-one certificate.
* `AlgebraicGeometry.isDivisorDegree_nat_of_point` — a rational point makes every natural
  parameter a divisor degree.
* `AlgebraicGeometry.exists_chartIndex_of_point` — the resulting legal chart index at any
  natural parameter, in particular at the genus after a point-producing base change.
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
attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The graph class of a `k`-point, base-changed -/

omit [GeometricallyIrreducible C.hom] in
variable (C) in
/-- **The graph class of a `k`-point base-changes to the graph class of the induced
`L`-point** — the class-level replacement for the divisor base change the tree does not have.

`p : overSpec k k ⟶ C` is a `k`-point; `overSpecMap (Algebra.ofId k L) ≫ p` is the same point
read over `L`.  This is `Over.graphLocalEquations_base_change` at
`g := Over.overSpecMap (Algebra.ofId k L)`, recorded in the spelling the chart layer uses
(`(C ◁ Over.overSpecMap (Algebra.ofId k L)).left`, which is `relCurveMap C k L`).

Why it substitutes for a divisor base change: the coverage argument compares the chart index's
contribution to the twisted class at `k` with the drop divisor's contribution at `L`.  Both
comparisons are between *classes*, and this identity is the whole content — no coefficient
function is transported, so no `CurveDivisor.pullback` is required. -/
theorem graphPicClass_base_of_field (L : Type u) [Field L] [Algebra k L]
    (p : overSpec k k ⟶ C) :
    Over.graphPicClass C (Over.overSpecMap (Algebra.ofId k L) ≫ p)
      = Scheme.CechPic.map ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left)
          (Over.graphPicClass C p) :=
  Over.graphLocalEquations_base_change C (Over.overSpecMap (Algebra.ofId k L)) p

variable (C) in
/-- **The base-changed graph class still has degree one.**

Two independent readings agree, which is the useful part: the landed degree-one certificate
`classDeg_graphPicClass` applied at `L` directly, and E-iv-alg
(`classDeg_cechPicMap_base_of_field`) applied to the `k`-level certificate.  Stated as the
`classDeg = 1` fact at `L` because that is what the chart-index degree constraint consumes.

This is what lets the coverage argument check its degree bookkeeping **once, at `k`**: a sum of
`e` such classes has degree `e` at the base and degree `e` at every fibre field, with no
per-field computation. -/
theorem classDeg_graphPicClass_base (L : Type u) [Field L] [Algebra k L]
    (p : overSpec k k ⟶ C) :
    classDeg L (Scheme.CechPic.map ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left)
        (Over.graphPicClass C p)) = 1 := by
  rw [classDeg_cechPicMap_base_of_field C L]
  exact classDeg_graphPicClass C p

/-! ## Legal chart indices after acquiring a rational point -/

variable (C) in
/-- A rational point produces a divisor of degree one.  The graph class has class degree one,
and surjectivity of the divisor-class map re-presents it by an actual Weil divisor. -/
theorem isDivisorDegree_one_of_point (p : overSpec k k ⟶ C) :
    IsDivisorDegree C 1 := by
  obtain ⟨D, hD⟩ :=
    Scheme.CurveDivisor.exists_picClass_eq k (Over.graphPicClass C p)
  refine ⟨D, ?_⟩
  rw [← classDeg_picClass, hD]
  exact classDeg_graphPicClass C p

variable (C) in
/-- Once the curve has a rational point, every natural number is a divisor degree: take the
corresponding multiple of a degree-one divisor. -/
theorem isDivisorDegree_nat_of_point (p : overSpec k k ⟶ C) (n : ℕ) :
    IsDivisorDegree C (n : ℤ) := by
  obtain ⟨D, hD⟩ := isDivisorDegree_one_of_point C p
  refine ⟨n • D, ?_⟩
  rw [Scheme.CurveDivisor.deg_nsmul' k, hD]
  simp

variable (C) in
/-- A rational point supplies a legal chart index at every natural parameter.  Applied to a
finite base change on which the curve acquires a point, this produces the genus chart
without assuming that the genus is a divisor degree over the original field. -/
theorem exists_chartIndex_of_point (p : overSpec k k ⟶ C) (n : ℕ) :
    ∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor),
      Scheme.CurveDivisor.deg k Z
        = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ) :=
  chartIndex_of_isDegree C (isDivisorDegree_nat_of_point C p n)

end

end AlgebraicGeometry
