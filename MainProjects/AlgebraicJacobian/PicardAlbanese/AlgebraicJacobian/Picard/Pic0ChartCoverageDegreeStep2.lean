/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageDegree
import AlgebraicJacobian.Picard.DegreeZeroBaseField

/-!
# COV-1 / `w4-datb` §1.2 STEP 2, DISCHARGED

`Picard/Pic0ChartCoverageDegree.lean` computes the twist factor's contribution to the degree
of the presenting class and then states plainly (issue I-0614) that the `λ` factor's
contribution is *not* discharged: the coverage argument holds `degAt λ t` at the fibre field
`K`, the presenting class `M₀` lives over the splitting field `L`, and nothing in the tree
equated the two readings.

`Picard/DegreeZeroBaseField.lean` supplies exactly the missing equation
(`PicEtAff.degAff_map`, unconditional in `L/K`).  This file spends it, so that step 2 becomes
a landed theorem rather than a named gap, and then assembles the full degree ledger of the
presenting class of the TWISTED fibre class — which is what `Picard/Pic0ChartCoverageFibre.lean`
takes as its hypothesis `hdeg`.

## The ledger, in one line

For `λ` degree-zero at the fibre point and `M` presenting the twisted class over `L`:

  `classDeg L M = 0 + (m·d₁ − deg_k Z) = m·d₁ − deg_k Z`,

so the chart-index constraint `deg_k Z = m·d₁ − g − e` makes it `g + e`, which is
`exists_effective_sub_h0_eq_one`'s hypothesis on the nose.  **No per-field ledger constant
crosses a base-field boundary** (the I-0204 discipline): `d₁ = classDeg k Θ` is read at `k`
and reaches `L` by E-iv-alg, while the `λ` factor's contribution is *zero*, which transports
trivially.

## Main declarations

* `AlgebraicGeometry.classDeg_presenting_eq_degAff` — **step 2**: the `L`-degree of a class
  presenting a plus class over `K` is that plus class's degree at `K`.
* `AlgebraicGeometry.classDeg_presenting_eq_zero` — the degree-zero case, the form the
  coverage argument spends.
* `AlgebraicGeometry.classDeg_presenting_twist` — **the assembled ledger**: the `L`-degree of
  the presenting class of the twisted fibre class of a degree-zero `λ`.
* `AlgebraicGeometry.classDeg_presenting_twist_eq_add` — the same under the chart-index
  constraint, delivered in the `g + e` shape `Pic0ChartCoverageFibre` consumes.
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

/-! ## Step 2 itself -/

variable (C) in
/-- **COV-1 / `w4-datb` §1.2 step 2** — the seam I-0614 recorded as absent, now landed.

If the plus class `a` over the fibre field `K` is presented over an extension `L` by the Čech
class `M`, then `classDeg L M` is `a`'s own degree at `K`.

Both halves are one rewrite each: the `L`-side reading of the unit is `classDeg L M`
(`degAff_unit` + `relPicDeg_relPicMk`), and the base-field step is `PicEtAff.degAff_map`.  The
substance is entirely in that second lemma — and note what it does *not* require: `L/K` is an
arbitrary field extension here, not a finite separable one, so a consumer may present its class
over whatever extension the splitting produced. -/
theorem classDeg_presenting_eq_degAff {K : Type u} [Field K] [Algebra k K]
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (a : PicEtAff C K) (M : (C ⊗ overSpec k L).left.CechPic)
    (hM : PicEtAff.map C L a = PicEtAff.unit C L (relPicMk C (overSpec k L) M)) :
    classDeg L M = PicEtAff.degAff K a := by
  rw [← PicEtAff.degAff_map L a, hM, PicEtAff.degAff_unit, relPicDeg_relPicMk]

variable (C) in
/-- **Step 2 at a degree-zero class** — the form the coverage argument spends.

`degAt λ t = 0` is exactly what membership of `pic0Subgroup` gives at the fibre point, and the
plus-class degree of the restricted class is `degAt` by definition; so a presenting class of a
degree-zero fibre class has `classDeg L = 0` over **any** extension it is presented over. -/
theorem classDeg_presenting_eq_zero {K : Type u} [Field K] [Algebra k K]
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : overSpec k K ⟶ T)
    (hlam : degAt lam t = 0)
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (M : (C ⊗ overSpec k L).left.CechPic)
    (hM : PicEtAff.map C L (picEtAffineEquiv C K (picEtMap C t lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M)) :
    classDeg L M = 0 := by
  rw [classDeg_presenting_eq_degAff C L _ M hM]
  exact hlam

/-! ## The assembled ledger of the twisted class -/

variable (C) in
/-- **The degree of the presenting class of the TWISTED fibre class** (`w4-datb` §1.2
steps 2–4, assembled).

For a class `lam` whose fibre degree at `t` vanishes, presented over `L` by `M₀`, the twisted
presenting class of `Picard/Pic0ChartTwistSplit.lean` has

  `classDeg L (M₀ · CechPic.map (relCurveMap C k L) (chartTwistClass C m Z))
      = m · classDeg k Θ − deg_k Z`.

The two factors come from opposite sides and neither carries a per-field constant across a
base-field boundary: the twist factor is read at `k` and transported by E-iv-alg
(`classDeg_chartTwistClass_baseChange`), and the `λ` factor contributes `0`
(`classDeg_presenting_eq_zero`). -/
theorem classDeg_presenting_twist {K : Type u} [Field K] [Algebra k K]
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : overSpec k K ⟶ T)
    (hlam : degAt lam t = 0)
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (M₀ : (C ⊗ overSpec k L).left.CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K (picEtMap C t lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) :
    classDeg L (M₀ * Scheme.CechPic.map
        ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left) (chartTwistClass C m Z))
      = (m : ℤ) * classDeg k (thetaCechClass C) - Scheme.CurveDivisor.deg k Z := by
  rw [classDeg_mul, classDeg_presenting_eq_zero C lam t hlam L M₀ hM₀,
    classDeg_chartTwistClass_baseChange C L m Z, zero_add]

variable (C) in
/-- **The ledger in the `g + e` shape** — the hypothesis `Pic0ChartCoverageFibre`'s
`exists_isSplitWitness_of_drop` asks for (`hdeg`).

Under the chart-index constraint `deg_k Z = m·d₁ − g − e` (the drop budget `e` folded into the
chart index), the presenting class of the twisted fibre class has degree exactly `g + e`.  This
is where the chart index is *paid for*: the constraint is a hypothesis, because per `w4-datb`
§0.2.2 / I-0204 the exponent `m` must be chosen against the fibre's OWN vanishing bound and no
uniform choice exists. -/
theorem classDeg_presenting_twist_eq_add {K : Type u} [Field K] [Algebra k K]
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : overSpec k K ⟶ T)
    (hlam : degAt lam t = 0)
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (M₀ : (C ⊗ overSpec k L).left.CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K (picEtMap C t lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) (g e : ℕ)
    (hZ : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (g : ℤ) - (e : ℤ)) :
    classDeg L (M₀ * Scheme.CechPic.map
        ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left) (chartTwistClass C m Z))
      = (g : ℤ) + e := by
  rw [classDeg_presenting_twist C lam t hlam L M₀ hM₀ m Z, hZ]
  ring

end

end AlgebraicGeometry
