/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartShiftedDatum

/-!
# The chart twist collapses to ONE θ-family — and GAP-1's mul/tensor does not gate CHART-U(b)

This file retracts a standing claim of this project, and it is worth stating the claim
first because four roadmap/worksheet records rest on it:

> `informal/w4-datc-worksheet.md` §0.3 GAP-1 (Σ-INV) and `informal/w4-datb-worksheet.md`
> §1.6 both assert that the chart twist `λ·θᵐ·(−Σ)` "has no route" at the datum layer,
> because there is no `BasicOpenCocycleDatum.mul` or tensor anywhere in the tree; and
> `Picard/Pic0ChartLocusIsOpen.lean`'s header table lists "GAP-1 mul — a datum for a
> *product*, on a common cover refinement" as the ONE unlanded link of the openness route.

**Both halves of that are wrong, for two independent reasons, and this file proves it.**

## Reason 1: the twist is not a product of three families, it is one family

`sigmaFamily C Z T` is *by definition* `thetaFamily C (picClass k Z) T`
(`Picard/DivSchemeAbel.lean:326`, and `degAt_sigmaFamily` proves it by `change`), and
`thetaFamily C L₀ T` is `picEtMap C (toBaseTest T) ((picEtAffineEquiv C k).symm
(PicEtAff.unit C k (relPicMk C (overSpec k k) L₀)))` — a composite of **four group
homomorphisms** applied to `L₀`.  `Scheme.CechPic` is a `CommGroup` (`Picard/Pic.lean:117`).
So `thetaFamily` is multiplicative *in its class argument*:

* `thetaFamily_mul`, `thetaFamily_inv`, `thetaFamily_pow` — each proved by `map_mul` /
  `map_inv` / `map_pow` four times, nothing else.

Consequently `chartTwist C m Z T λ = λ · thetaFamily C (θ^m · (picClass k Z)⁻¹) T`
(`chartTwist_collapse`): the Σ-factor and the θᵐ-factor are *the same construction at two
classes*, and they fuse into one call at the single class `θ^m · (picClass k Z)⁻¹`, computed
entirely in `CechPic` over the FIXED base `overSpec k k`.  No datum-level product is
involved anywhere, because the multiplication happens in the Čech Picard *group* before any
datum is extracted.

## Reason 2: even for a genuine product, presentation is surjective, not constructive

`BasicOpenCocycleDatum.exists_cechPicClass_eq` (`Cohomology/GluedSheafExtraction.lean:301`)
says: for **every** `c : (relCurve C B).CechPic` there is a datum `D` with
`D.cechPicClass = c`.  It is a surjectivity statement over an arbitrary affine base.  So a
datum presenting a product `c · c'⁻¹` exists *outright* — one applies extraction to the
product class, rather than multiplying two data.  `exists_datum_cechPicClass_mul_inv` below
records this in exactly the shape the openness route wanted.

A `BasicOpenCocycleDatum.mul` on a common cover refinement would be a *stronger, structured*
statement — it would say the product datum can be built from the two factor data with a
computable cover.  That is a legitimate thing to want, and it is still absent.  It is simply
not what CHART-U(b) needs: the route needs *a* datum with the right class, and extraction
supplies one.

## What this does and does not resolve

Resolved: the openness route of `w4-datb` §1.6 (b-amendment) no longer has an unlanded
construction in it.  Its remaining input is the *identification* of the presenting datum's
fibre predicate with the split predicate at each point — `IsChartDatumPresentation`
(`Pic0ChartLocusIsOpen.lean`), which is a statement about `cechPicClass` naturality under
base change to residue fields, not about building a datum.

NOT resolved, and stated plainly so this file is not over-read: `cechPicClass_inv` (the
class law of `invDatum`) is still unproved, and `invDatum` is now revealed as unnecessary
for the twist — its value, if any, is elsewhere.  Nothing here proves
`IsChartDatumPresentation` for any particular class.

## Main declarations

* `AlgebraicGeometry.thetaFamily_mul` / `thetaFamily_inv` / `thetaFamily_pow` — the θ-family
  is a group homomorphism in its class argument.
* `AlgebraicGeometry.sigmaFamily_eq_thetaFamily` — the Σ-family IS a θ-family, recorded.
* **`AlgebraicGeometry.chartTwist_collapse`** — the chart twist is one θ-family.
* `AlgebraicGeometry.exists_datum_cechPicClass_chartTwistClass` — a presenting datum for the
  collapsed twist class exists, with no GAP-1 mul.
* `AlgebraicGeometry.exists_datum_cechPicClass_mul_inv` — the general form: extraction
  already presents any product/inverse.
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

/-! ## The θ-family is a homomorphism in its class argument

Each proof is `map_mul` (resp. `map_inv`, `map_pow`) applied four times, once per layer of
`thetaFamily`'s definition: `relPicMk`, `PicEtAff.unit`, the affine comparison
`picEtAffineEquiv C k` (a `MulEquiv`, so its `symm` is one too), and `picEtMap`.  That the
whole tower is homomorphic is what makes the collapse below possible, and it is the fact the
GAP-1 records missed. -/

variable (C) in
/-- **The θ-family is multiplicative in its class.** -/
theorem thetaFamily_mul (L L' : (C ⊗ overSpec k k).left.CechPic)
    (T : Over (Spec (.of k))) :
    thetaFamily C (L * L') T = thetaFamily C L T * thetaFamily C L' T := by
  unfold thetaFamily thetaBase
  rw [map_mul, map_mul, map_mul, map_mul]

variable (C) in
/-- **The θ-family sends inverses to inverses.** -/
theorem thetaFamily_inv (L : (C ⊗ overSpec k k).left.CechPic)
    (T : Over (Spec (.of k))) :
    thetaFamily C L⁻¹ T = (thetaFamily C L T)⁻¹ := by
  unfold thetaFamily thetaBase
  rw [map_inv, map_inv, map_inv, map_inv]

variable (C) in
/-- **The θ-family commutes with powers** — so `θ^m` may be read either as the `m`-th power
of the family or as the family of the `m`-th power of the class.  The chart twist uses the
former spelling and the collapse needs the latter. -/
theorem thetaFamily_pow (L : (C ⊗ overSpec k k).left.CechPic)
    (T : Over (Spec (.of k))) (m : ℕ) :
    thetaFamily C (L ^ m) T = thetaFamily C L T ^ m := by
  unfold thetaFamily thetaBase
  rw [map_pow, map_pow, map_pow, map_pow]

variable (C) in
/-- **The Σ-family is a θ-family** — true by definition (`DivSchemeAbel.lean:326`), recorded
as a lemma because the collapse below reads it as such and because the GAP-1 discussion
treats Σ and θ as two different constructions needing a product to combine.  They are one
construction at two classes. -/
theorem sigmaFamily_eq_thetaFamily (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) :
    sigmaFamily C Z T = thetaFamily C (Scheme.CurveDivisor.picClass k Z) T :=
  rfl

/-! ## The collapse -/

variable (C) in
/-- **The chart twist is ONE θ-family** (this file's headline).

`chartTwist C m Z T λ = λ · thetaFamily C (θ^m · (picClass k Z)⁻¹) T`.

The Σ-shift and the `m` inverse θ-powers fuse into a single θ-family at the single class
`θ^m · (picClass k Z)⁻¹`, which lives in `CechPic` over the FIXED base `overSpec k k` — a
`CommGroup`, where the multiplication and inversion are free.

Why this matters beyond tidiness: `w4-datc` §0.3 GAP-1 and `w4-datb` §1.6 both record that
the twist "has no route" at the datum layer for want of a `BasicOpenCocycleDatum.mul`.  The
premise of that record is that the twist is a product of *families* which must be realised
by a product of *data*.  It is not — it is one family, and the only multiplication happens
in `CechPic` before any datum enters the picture. -/
theorem chartTwist_collapse (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T) :
    chartTwist C m Z T lam
      = lam * thetaFamily C
          (thetaCechClass C ^ m * (Scheme.CurveDivisor.picClass k Z)⁻¹) T := by
  rw [chartTwist, thetaFamily_mul, thetaFamily_inv, thetaFamily_pow, mul_assoc]
  rfl

variable (C) in
/-- **The collapsed twist class**: the single `CechPic` class over the base that the chart
index `(m, Z)` contributes.  Named because it is what a presenting datum must present, and
because it makes the chart index's role visible — the whole twist is one class, and the
chart-index degree constraint `deg Z = m·d₁ − n` is a statement about *its* degree. -/
def chartTwistClass (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) :
    (C ⊗ overSpec k k).left.CechPic :=
  thetaCechClass C ^ m * (Scheme.CurveDivisor.picClass k Z)⁻¹

variable (C) in
theorem chartTwist_eq_mul_thetaFamily_chartTwistClass (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor) (T : Over (Spec (.of k)))
    (lam : picEt C T) :
    chartTwist C m Z T lam = lam * thetaFamily C (chartTwistClass C m Z) T :=
  chartTwist_collapse C m Z T lam

/-! ## Presentation needs no GAP-1 mul

`BasicOpenCocycleDatum.exists_cechPicClass_eq` is a **surjectivity** statement: every Čech
class over an affine base is the class of some datum.  So the datum the openness route needs
is obtained by extraction *at the product class*, not by multiplying data.  The two lemmas
below are one line each; they exist to make the point unmissable at the place a lane will
look for it. -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- **Extraction already presents any product or inverse of classes** — the general form.

This is the direct refutation of "there is no `BasicOpenCocycleDatum.mul`, so a datum for a
product has no route".  A datum for the product exists; what does not exist is a
*construction of it from the factors' data*, which is a different (and unneeded) statement. -/
theorem exists_datum_cechPicClass_mul_inv {B : Type u} [CommRing B] [Algebra k B]
    (c c' : (relCurve C B).CechPic) :
    ∃ D : BasicOpenCocycleDatum C B π, D.cechPicClass = c * c'⁻¹ :=
  BasicOpenCocycleDatum.exists_cechPicClass_eq _

/-- **A presenting datum for the collapsed twist class exists**, over any affine base and for
any chart index — with no GAP-1 mul, no `invDatum`, and no `cechPicClass_inv`.

`c` here is the honest Čech class of the plus class being tested (over the étale carrier,
supplied by the collapse of `w4-datb` §1.2 step 1, i.e. `Pic0ChartSplit`), and the twist
class is base-changed into `relCurve C B` along `relCurveMap`.  The conclusion is precisely
the input of `BasicOpenCocycleDatum.isOpen_setOf_exists_witness_h1_vanishing`. -/
theorem exists_datum_cechPicClass_chartTwistClass {B : Type u} [CommRing B] [Algebra k B]
    (c : (relCurve C B).CechPic) (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor) :
    ∃ D : BasicOpenCocycleDatum C B π,
      D.cechPicClass
        = c * Scheme.CechPic.map (relCurveMap C k B) (chartTwistClass C m Z) :=
  BasicOpenCocycleDatum.exists_cechPicClass_eq _

end

end AlgebraicGeometry
