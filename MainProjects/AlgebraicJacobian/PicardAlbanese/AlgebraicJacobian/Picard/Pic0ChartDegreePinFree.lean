/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageIndexSlack
import AlgebraicJacobian.Picard.JacobianDataAbelDegreeWindow

/-!
# The `deg = g` pin on a coverage witness is DERIVED from the chart index, not assumed

`Picard/JacobianDataAbelDegreeWindow.lean` proves that at degree exactly `g` on a curve with
`χ(𝒪) = 1 − g`, vanishing `H¹` forces `h⁰ = 1`, so DAT-C GAP-2 goes from four inputs to three.
Its own honest-limit note then calls the remaining `deg = g` hypothesis "the honest residue":
`IsSplitWitness` asks for neither `0 ≤ W` nor `deg W = g` (`Pic0ChartCoverageNoDrop.lean`), so a
consumer appeared to have to supply the degree by hand.

**It does not have to.**  `Pic0ChartCoverageIndexSlack.lean` already proves the calibration that
supplies it, in the direction nobody read it in.

## The mechanism, and why it was already there

`ledger_forces_b_eq_n` (`Pic0ChartCoverageIndexSlack.lean:119`) is stated as a *constraint on the
threshold*: at a chart index legal at parameter `n` — the constraint
`deg_k Z = m·d₁ − n` that `chartValue_mem_pic0Subgroup` requires for the chart value to land in
`pic⁰` — the class-degree of the presenting twisted class is forced to equal `n`.  That file reads
this as "the chart index determines the threshold", i.e. as something the coverage lane must
*reconcile*.

Read in the other direction it is a *gift*: since every divisor of a class has that class's
degree (`classDeg_picClass`), the forcing applies to any representative.  So a witness `W` of the
presenting twisted class has `deg W = n` **derived** — and at the representability parameter
`n = g`, that is `deg W = g`, exactly the pin.

Composed with the rank anchor, a coverage witness at parameter `g` therefore carries `h⁰ = 1`
with **no degree hypothesis and no `h⁰` hypothesis at all**: only the chart-index constraint it
already satisfies and the `H¹`-vanishing `IsSplitWitness` already asserts.

## What this does and does not settle

It removes the degree hypothesis from the identity's consumer side.  It does **not** discharge
coverage, and it does **not** close any antecedent of `pic0RepresentableByOfCharts`:

* effectivity (`0 ≤ W`) is still not carried by `IsSplitWitness`, and GAP-2 still takes it on
  both divisors — that is the correction of record on the degree-window file, and it is the
  reason "coverage carries GAP-2's input" is false;
* whether a coverage witness at parameter `g` arrives with the `0 ≤ Σ` legality of the chart
  index discharged is `Pic0ChartCoverageIndexSlack.lean`'s own open question (its §"THE HONEST
  STATUS OF STEP 3", item 3), and nothing here touches it.

So the residue named on the degree-window file shrinks from "a degree pin plus effectivity" to
"effectivity, plus the `0 ≤ Σ` legality".

## Main declarations

* `AlgebraicGeometry.deg_eq_of_picClass_eq_presenting_twist` — the pin, derived: a divisor of
  the presenting twisted class at a chart index legal at parameter `n` has degree `n`.
* `AlgebraicGeometry.h0_eq_one_of_subsingleton_hModule_one_of_chartIndex` — hence at parameter
  `g` the `H¹`-vanishing of a witness gives `h⁰ = 1` with no degree hypothesis.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

variable (C) in
/-- **THE DEGREE PIN IS DERIVED.**  At a chart index legal at parameter `n`, every divisor of
the presenting twisted class has degree exactly `n`.

`ledger_forces_b_eq_n` (`Pic0ChartCoverageIndexSlack.lean:119`) forces the *class* degree to be
`n`; `classDeg_picClass` transports that to any representative.  The chart-index constraint `hZ`
is the one `chartValue_mem_pic0Subgroup` already requires for the chart value to land in `pic⁰`,
so this costs a consumer nothing it does not already have.

Read against `Pic0ChartCoverageIndexSlack`'s framing: that file states the same equation as a
*reconciliation burden* on the coverage lane ("the chart index determines the threshold").  In
this direction it is what supplies the degree hypothesis that
`JacobianDataAbelDegreeWindow.lean` had to assume. -/
theorem deg_eq_of_picClass_eq_presenting_twist {K : Type u} [Field K] [Algebra k K]
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : overSpec k K ⟶ T)
    (hlam : degAt lam t = 0)
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (M₀ : (C ⊗ overSpec k L).left.CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K (picEtMap C t lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (m n : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hZ : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (W : (C ⊗ overSpec k L).left.CurveDivisor)
    (hW : Scheme.CurveDivisor.picClass L W
      = M₀ * Scheme.CechPic.map
        ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left) (chartTwistClass C m Z)) :
    Scheme.CurveDivisor.deg L W = (n : ℤ) := by
  have hb := ledger_forces_b_eq_n C lam t hlam L M₀ hM₀ m n Z hZ
    (classDeg L (Scheme.CurveDivisor.picClass L W)) (by rw [hW])
  rw [← hb, classDeg_picClass L W]

variable (C) in
/-- **`h⁰ = 1` from a coverage witness, with NO degree hypothesis.**

At the representability parameter `n = g` the two previous results compose: the chart-index
constraint supplies `deg W = g` (`deg_eq_of_picClass_eq_presenting_twist`) and the rank anchor
turns the `H¹`-vanishing into `h⁰ = 1`
(`h0_eq_one_of_subsingleton_hModule_one_of_deg_eq`).

So a lane holding a coverage witness at parameter `g` — i.e. the `IsSplitWitness` data, whose
`H¹`-vanishing clause is `h1` here — gets GAP-2's `h⁰` input for free, and the degree-window
file's "honest residue" on the degree side is discharged.

**Still NOT free, and not touched here:** effectivity `0 ≤ W`, which `IsSplitWitness` does not
assert and which GAP-2 requires on *both* divisors; and the `0 ≤ Σ` legality of the chart index
at parameter `g` (`Pic0ChartCoverageIndexSlack`'s open question). -/
theorem h0_eq_one_of_subsingleton_hModule_one_of_chartIndex {K : Type u} [Field K] [Algebra k K]
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : overSpec k K ⟶ T)
    (hlam : degAt lam t = 0)
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [IsIntegral (C ⊗ overSpec k L).left]
    [SmoothOfRelativeDimension 1 ((C ⊗ overSpec k L).left ↘ Spec (CommRingCat.of L))]
    [QuasiCompact ((C ⊗ overSpec k L).left ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((C ⊗ overSpec k L).left.moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((C ⊗ overSpec k L).left.moduleKSheaf L) 1)]
    (g : ℕ) (hχ : Sheaf.chi ((C ⊗ overSpec k L).left.moduleKSheaf L) = 1 - (g : ℤ))
    (M₀ : (C ⊗ overSpec k L).left.CechPic)
    (hM₀ : PicEtAff.map C L (picEtAffineEquiv C K (picEtMap C t lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hZ : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (g : ℤ))
    (W : (C ⊗ overSpec k L).left.CurveDivisor)
    (hW : Scheme.CurveDivisor.picClass L W
      = M₀ * Scheme.CechPic.map
        ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left) (chartTwistClass C m Z))
    (h1 : Subsingleton
      (Sheaf.HModule ((C ⊗ overSpec k L).left.divisorSheaf L W) 1)) :
    Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L W) = 1 :=
  h0_eq_one_of_subsingleton_hModule_one_of_deg_eq g hχ W
    (deg_eq_of_picClass_eq_presenting_twist C lam t hlam L M₀ hM₀ m g Z hZ W hW) h1

end

end AlgebraicGeometry
