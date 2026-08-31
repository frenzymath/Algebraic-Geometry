/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartTwistSplit
import AlgebraicJacobian.RiemannRoch.DegreeBaseFieldInvariance

/-!
# COV-1 input 2: the DEGREE of the presenting class of the twisted fibre class

`Picard/Pic0ChartTwistSplit.lean` names the Čech class that presents the twisted fibre class
over the splitting field `L`:

  `M₀ · CechPic.map (relCurveMap C k L) (chartTwistClass C m Z)`.

`w4-datb` §1.2 steps 2–4 then need its `L`-degree, because that is what decides whether the
class can carry an effective witness with `h¹ = 0` at all: the greedy drop of
`RiemannRoch/CoverageDrop.lean` consumes a divisor of degree `g + e`.

This file computes it, and the computation is exactly the degree ledger the worksheet pins:

  `classDeg L (presenting class) = m·d₁ − deg_k Z`   when `λ` is degree-zero,

so under the chart-index constraint `deg_k Z = m·d₁ − g` it is `+g` — and with the drop budget
`e` folded in (`deg_k Z = m·d₁ − g − e`) it is `g + e`, which is `exists_effective_sub_h0_eq_one`'s
hypothesis on the nose.

## The two halves, and which one is nontrivial

* the **twist factor** is a base class base-changed to `L`, so its `L`-degree is its
  `k`-degree by **E-iv-alg** (`classDeg_cechPicMap_baseFieldTransition`) — no per-field
  ledger constant crosses, which is the I-0204 discipline;
* the **`λ` factor** has `L`-degree zero, and this is where degree-zero-ness is *spent*.
  It is `degAt λ (testPoint) = 0` read through the degree seam: `degAt` of a class whose
  affine collapse is a plus unit of `relPicMk M₀` is `classDeg` of `M₀`
  (`degAt_of_affineEquiv_eq_unit_relPicMk`).

The second half is the reason this file exists rather than being three `rw`s inside COV-1: the
seam from "`μ` is presented over `L` by `M₀`" to "`classDeg L M₀ = degAt μ`" is a statement
about `PicEtAff.map` versus `picEtMap`, not about degrees.

## Main declarations

* `AlgebraicGeometry.classDeg_cechPicMap_base_of_field` — the `L`-degree of a base class
  base-changed to `L` is its `k`-degree (E-iv-alg in the `relCurveMap` spelling).
* `AlgebraicGeometry.classDeg_chartTwistClass_baseChange` — the twist factor contributes
  exactly `m·d₁ − deg_k Z`.
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

/-! ## E-iv-alg in the `relCurveMap` spelling -/

variable (C) in
/-- **The degree of a base class is base-field invariant** — E-iv-alg
(`classDeg_cechPicMap_baseFieldTransition`) read along `relCurveMap C k L` rather than along
the raw whisker.  The two agree by `relCurveMap_eq_overSpecMap_ofId`, and this is the spelling
every chart-layer statement uses. -/
theorem classDeg_cechPicMap_base_of_field (L : Type u) [Field L] [Algebra k L]
    (Λ : (C ⊗ overSpec k k).left.CechPic) :
    classDeg L (Scheme.CechPic.map ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left) Λ)
      = classDeg k Λ :=
  classDeg_cechPicMap_baseFieldTransition C (Algebra.ofId k L) Λ

variable (C) in
/-- **The twist factor's contribution to the degree**: `m·d₁ − deg_k Z`, computed at the
splitting field but equal to a `k`-level quantity — the point of routing it through E-iv-alg
rather than through a per-field ledger. -/
theorem classDeg_chartTwistClass_baseChange (L : Type u) [Field L] [Algebra k L] (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor) :
    classDeg L (Scheme.CechPic.map ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left)
        (chartTwistClass C m Z))
      = (m : ℤ) * classDeg k (thetaCechClass C) - Scheme.CurveDivisor.deg k Z := by
  rw [classDeg_cechPicMap_base_of_field C L]
  change classDeg k (thetaCechClass C ^ m * (Scheme.CurveDivisor.picClass k Z)⁻¹) = _
  rw [classDeg_mul, classDeg_inv, classDeg_pow, classDeg_picClass]
  ring

/-! ## Where degree-zero-ness is spent: the `λ` factor -/

variable (C) in
/-- **The presenting class's `classDeg` equals the transported plus-class degree.**

`classDeg L M = degAff L (PicEtAff.map C L (picEtAffineEquiv C K ν))`, whenever `M` presents
`ν` over `L`.  Read the statement, not the ambition: the right-hand side is the plus-class
degree **at `L`**, and this is `degAff_unit` plus `relPicDeg_relPicMk`, nothing more.

**A CORRECTION, and it is the reason this docstring is now shorter than it was** (issue I-0614,
found by fresh-context review).  The previous version claimed this theorem was the `w4-datb`
§1.2 step-2 seam — that it carried `degAt ν = 0` over to `classDeg M = 0` — and justified the
`K → L` step by citing `degAff_map_eq`.  **No such lemma exists**: the only occurrence of that
name in the workspace was that docstring.  So the claim was a phantom citation, and the step it
claimed to make is genuinely absent:

* what the coverage argument HAS is `degAt ν t = degAff K (picEtAffineEquiv C K ν)`, at `K`;
* what this theorem's RHS mentions is `degAff L (PicEtAff.map C L …)`, at `L`;
* nothing in the tree equates them.  The missing brick is **base-field invariance of `degAff`
  under `PicEtAff.map`**, a small real lemma shaped like the landed `degAff_baseFieldShuffle`
  (`Picard/Pic0ThetaAssembly.lean:67`) — measured, not guessed: `exact?` on
  `degAff L (map C L a) = degAff K a` finds nothing.

**STEP 2 IS NOW DISCHARGED (2026-07-28), and this paragraph's "NOT discharged" is superseded.**
The missing `degAff` invariance was proved as `PicEtAff.degAff_map`
(`Picard/DegreeZeroBaseField.lean`) — and it needs *no* hypothesis on `L/K` at all, not even
finiteness, so it is weaker-premised than the `degAff_baseFieldShuffle` shape predicted above.
Step 2 itself is `classDeg_presenting_eq_degAff` / `classDeg_presenting_eq_zero`
(`Picard/Pic0ChartCoverageDegreeStep2.lean`), which reaches `classDeg L M = degAff K a`
directly and therefore does **not** route through this theorem.

This theorem is kept because it is true and was the first half of the seam, but it remains
without consumers: the landed route reads the `K`-side degree rather than the `L`-side one, so
its `PicEtAff.map`-shaped right-hand side is no longer the useful spelling.

The other half of the ledger — the twist factor's contribution — IS complete
(`classDeg_chartTwistClass_baseChange` above, via E-iv-alg). -/
theorem classDeg_of_presenting {K : Type u} [Field K] [Algebra k K]
    (ν : picEt C (overSpec k K)) {L : Type u} [Field L] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] (M : ((C ⊗ overSpec k L).left).CechPic)
    (hM : PicEtAff.map C L (picEtAffineEquiv C K ν)
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M)) :
    classDeg L M = PicEtAff.degAff L (PicEtAff.map C L (picEtAffineEquiv C K ν)) := by
  rw [hM, PicEtAff.degAff_unit, relPicDeg_relPicMk]

end

end AlgebraicGeometry
