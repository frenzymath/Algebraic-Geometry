/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PointDivisor
import AlgebraicJacobian.Picard.DivisorClassMeromorphic

/-!
# Collapsing `divisorClass` into the anchored `CurveDivisor.picClass`

For the curve bundle `X` (integral, smooth of relative dimension one and quasi-compact over
a field `K`) this file identifies the two divisor-to-class maps of the Jacobian rebuild:

* deg-D1's `AlgebraicGeometry.Scheme.divisorClass` — the finitely supported product of the
  point-divisor classes to their multiplicities; and
* deg-D2's anchored `AlgebraicGeometry.Scheme.CurveDivisor.picClass` — the class of any
  meromorphic presentation whose divisor is `D`.

Thanks to the strengthened `Scheme.exists_pointLocalEquation` (which now records that the
germ at `η` of the point equation is the chosen uniformizer, exported as
`Scheme.germGeneric_pointDivisorEqn_self`), the divisor cut out by `pointDivisor` is
provably `1 · x`. This pins its class, and the two maps agree on the whole divisor group.

## Main declarations

* `AlgebraicGeometry.Scheme.presentationDivisor_pointDivisor`: the divisor of the
  meromorphic presentation of `pointDivisor K hx` is `CurveDivisor.single hx 1` (mirrors
  `presentationDivisor_pointEquations`).
* `AlgebraicGeometry.Scheme.pointDivisor_picClass_eq`: the point-divisor class equals the
  anchored class of the one-point divisor,
  `(pointDivisor K hx).picClass = CurveDivisor.picClass K (CurveDivisor.single hx 1)`.
* `AlgebraicGeometry.Scheme.divisorClass_eq_picClass`: the collapse
  `divisorClass K D = CurveDivisor.picClass K D` for every Weil divisor `D`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace Scheme

open MeromorphicPresentation

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-! ## The divisor of the point-divisor presentation -/

/-- **The divisor of the point presentation is `1 · x`** (mirrors
`presentationDivisor_pointEquations`, now available for the deg-D1 `pointDivisor` thanks to
the tracked germ): the presentation of `pointDivisor K hx`'s local equations cuts out exactly
the one-point divisor. At `x` the trivializing element is the uniformizer (order `+1`); on
every other piece it is `1` (order `0`). -/
theorem presentationDivisor_pointDivisor {x : X} (hx : x ≠ genericPoint X) :
    presentationDivisor K (pointDivisor K hx).presentation = CurveDivisor.single hx 1 := by
  refine CurveDivisor.ext_coeffAt fun z hz => ?_
  rw [coeffAt_presentationDivisor]
  by_cases h : z = x
  · subst h
    have hval : ((pointDivisor K hx).presentation.elem z : X.functionField)
        = uniformizer K hx := by
      rw [LocalEquations.presentation_elem_val]
      exact germGeneric_pointDivisorEqn_self K hx _
    rw [ordZ_eq_ofAdd_one_of_val_eq_uniformizer K hx hval, CurveDivisor.coeffAt_single_self]
    rfl
  · have hval : (pointDivisor K hx).presentation.elem z = 1 := by
      refine Units.ext ?_
      rw [LocalEquations.presentation_elem_val, Units.val_one]
      change (X.presheaf.germ _ (genericPoint X) _).hom (pointDivisorEqn K hx z) = 1
      rw [pointDivisorEqn_of_ne K hx h, map_one]
    rw [hval, map_one, toAdd_one, CurveDivisor.coeffAt_single_of_ne hx hz h]

/-! ## Compatibility: the point-divisor class is the anchored one-point class -/

/-- **The point-divisor compatibility.** The Picard class of the deg-D1 point local equations
at `x` equals the anchored class of the one-point divisor `1 · x`:
`(pointDivisor K hx).picClass = CurveDivisor.picClass K (CurveDivisor.single hx 1)`. -/
theorem pointDivisor_picClass_eq {x : X} (hx : x ≠ genericPoint X) :
    (pointDivisor K hx).picClass = CurveDivisor.picClass K (CurveDivisor.single hx 1) := by
  rw [← presentationDivisor_pointDivisor K hx, CurveDivisor.picClass_presentationDivisor,
    LocalEquations.presentation_picClass]

/-! ## The collapse -/

/-- The point-divisor product form of `divisorClass` on a one-point divisor: the class of
`n · x` is the `n`-th power of the point-divisor class (mirrors
`divisorClass_single_eq_pointDivisor` for arbitrary multiplicity). -/
theorem divisorClass_single {x : X} (hx : x ≠ genericPoint X) (n : ℤ) :
    divisorClass K (CurveDivisor.single hx n) = (pointDivisor K hx).picClass ^ n := by
  rw [divisorClass, CurveDivisor.toFinsupp_single, Finsupp.prod_single_index (zpow_zero _)]

/-- Negation of Weil divisors inverts the anchored class: `𝒪(-D) = 𝒪(D)⁻¹`. -/
theorem picClass_neg (D : X.CurveDivisor) :
    CurveDivisor.picClass K (-D) = (CurveDivisor.picClass K D)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← CurveDivisor.picClass_add, neg_add_cancel,
    CurveDivisor.picClass_zero]

/-- The anchored class of `n · x` is the `n`-th power of the anchored class of `1 · x`. -/
theorem picClass_single_zpow {x : X} (hx : x ≠ genericPoint X) (n : ℤ) :
    CurveDivisor.picClass K (CurveDivisor.single hx 1) ^ n
      = CurveDivisor.picClass K (CurveDivisor.single hx n) := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, CurveDivisor.single_zero, CurveDivisor.picClass_zero]
  | succ n ih =>
    rw [zpow_add_one, ih, ← CurveDivisor.picClass_add, CurveDivisor.single_add]
  | pred n ih =>
    rw [zpow_sub_one, ih, ← picClass_neg, ← CurveDivisor.single_neg,
      ← CurveDivisor.picClass_add, CurveDivisor.single_add, sub_eq_add_neg]

/-- On a one-point divisor the two class maps agree, at arbitrary multiplicity. -/
theorem divisorClass_single_eq_picClass {x : X} (hx : x ≠ genericPoint X) (b : ℤ) :
    divisorClass K (CurveDivisor.single hx b)
      = CurveDivisor.picClass K (CurveDivisor.single hx b) := by
  rw [divisorClass_single, pointDivisor_picClass_eq, picClass_single_zpow]

/-- The deg-D1 class of the zero divisor is trivial. -/
theorem divisorClass_zero_eq : divisorClass K (0 : X.CurveDivisor) = 1 := by
  rw [divisorClass]
  exact Finsupp.prod_zero_index

/-- `divisorClass` packaged as an additive-to-multiplicative homomorphism (for the
extensionality argument collapsing it into `CurveDivisor.picClass`). -/
noncomputable def divisorClassHom : X.CurveDivisor →+ Additive X.CechPic where
  toFun D := Additive.ofMul (divisorClass K D)
  map_zero' := by rw [divisorClass_zero_eq]; rfl
  map_add' D D' := by rw [divisorClass_add]; rfl

/-- The anchored `CurveDivisor.picClass` packaged as an additive-to-multiplicative
homomorphism. -/
noncomputable def picClassHom : X.CurveDivisor →+ Additive X.CechPic where
  toFun D := Additive.ofMul (CurveDivisor.picClass K D)
  map_zero' := by rw [CurveDivisor.picClass_zero]; rfl
  map_add' D D' := by rw [CurveDivisor.picClass_add]; rfl

/-- **The collapse of `divisorClass` into `CurveDivisor.picClass`.** The deg-D1 divisor-class
map and the anchored deg-D2 class map agree on every Weil divisor:
`divisorClass K D = CurveDivisor.picClass K D`. Both maps are additive-to-multiplicative and
agree on one-point divisors, hence agree everywhere. -/
theorem divisorClass_eq_picClass (D : X.CurveDivisor) :
    divisorClass K D = CurveDivisor.picClass K D := by
  have key : (divisorClassHom K : X.CurveDivisor →+ Additive X.CechPic) = picClassHom K := by
    apply Finsupp.addHom_ext
    intro x y
    change Additive.ofMul (divisorClass K (Finsupp.single x y))
      = Additive.ofMul (CurveDivisor.picClass K (Finsupp.single x y))
    exact congrArg Additive.ofMul (divisorClass_single_eq_picClass K x.2 y)
  exact Additive.ofMul.injective (DFunLike.congr_fun key D)

end Scheme

end AlgebraicGeometry
