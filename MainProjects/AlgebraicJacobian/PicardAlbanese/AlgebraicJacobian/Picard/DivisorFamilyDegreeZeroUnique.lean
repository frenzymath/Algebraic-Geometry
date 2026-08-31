/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyDegreeZero
import AlgebraicJacobian.Picard.DivisorFamilyFieldEquiv
import AlgebraicJacobian.Picard.DivisorFamilyFieldCRT
import AlgebraicJacobian.Picard.DivSchemeAbel
import AlgebraicJacobian.RiemannRoch.SectionSpaces

/-!
# THE DEGREE-ZERO DIVISOR FUNCTOR VALUE IS A SINGLETON OVER A FIELD

`Picard/DivisorFamilyDegreeZero.lean` built the object side: `DivFamZar C R π 0` is inhabited
for **every** test ring `R`, unconditionally, because the colength certificate at degree `0` is
free.  Inhabitation alone does not represent a functor.  This file supplies the other half over
a field test, and the answer is as strong as it can be: the value is not merely small, it has
**exactly one element**.

## The argument, in one line each

A degree-`n` certified family cuts a divisor of degree exactly `n`
(`DivisorAdaptation.IsCertified.deg_presentationDivisor`), and the divisor a local-equation
system cuts is always **effective** (`Scheme.zero_le_coeffAt_presentationDivisor` — an
equation's order of vanishing is non-negative).  At `n = 0` an effective divisor of degree `0`
is **zero** (`Scheme.CurveDivisor.eq_zero_of_deg_le_zero`).  So every degree-`0` family cuts
the same divisor, and over a field equal presentation divisors force divisor-equality
(`Scheme.divEq_of_presentationDivisor_eq`), which is precisely the relation `DivFam` quotients
by.  Finally `DivFam.exists_toZar_eq` says `toZar` is surjective over a field, carrying the
subsingleton from the globally certified quotient to the **locally** certified one — the actual
functor carrier.

Note which direction each ingredient runs.  `deg_presentationDivisor` prices the certificate;
effectivity is a fact about local equations with no certificate at all; and it is only their
**conjunction** at `n = 0` that pins the divisor.  At `n > 0` the same two facts leave a
positive-degree effective divisor entirely free, which is why this argument is specific to `0`
and not a general uniqueness theorem in disguise.

## Main declarations

* `AlgebraicGeometry.presentationDivisor_eq_zero_of_isCertified_zero` — a degree-`0` certified
  family cuts the **zero** divisor.
* `AlgebraicGeometry.divEq_of_isCertified_zero` — hence any two are divisor-equal.
* `AlgebraicGeometry.instSubsingletonDivFamZero` — `DivFam C K π 0` is a subsingleton.
* `AlgebraicGeometry.instSubsingletonDivFamZarZero` — **and so is the functor carrier**
  `DivFamZar C K π 0`, by field surjectivity of `toZar`.
* `AlgebraicGeometry.DivFamZar.uniqueZeroOfField` — combining with
  `DivFamZar.instNonemptyDivFamZarZero`, the value is a `Unique`: exactly one degree-zero class
  over a field.

## What this does and does not give the seam

**Does**: the degree-zero divisor functor restricted to *field* tests is the one-point functor,
so on that subcategory it is represented by the terminal object.  That is a genuine
`RepresentableBy` statement about a restriction, and it is the first place in this tree where
the divisor functor is pinned rather than assumed.

**Does not**: `divFunctor C π 0` is a presheaf on the **whole** slice `Over (Spec k)`, not just
field points, and `mixedParamChart` consumes `rep` at that full functor.  The subsingleton
above needs `Field K` twice — once for `divEq_of_presentationDivisor_eq`, which is stated over
a field because a non-reduced base has divisor-inequivalent systems with equal presentation
divisors, and once for `DivFam.exists_toZar_eq`.  Whether `DivFamZar C R π 0` is a subsingleton
for a general `R` is **open and not measured here**; the inhabitation half of the previous file
holds for every `R`, the uniqueness half does not transfer, and I do not claim it does.

So the honest summary is: at parameter `0` the object side is unconditional and the uniqueness
side is field-local.  Closing the gap between them is the general-test rung, and it is the same
rung `CertifiedDivisorFamily.windowGen` owes on the widened route.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C K, ·)` with opens on the product spelling. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]

/-! ## A degree-zero family cuts the zero divisor -/

/-- **The degree-zero pin.**  A certified family of degree `0` cuts the *zero* divisor: its
presentation divisor is effective because orders of vanishing of an equation are non-negative,
and has degree `0` by the certificate, and an effective divisor of degree `≤ 0` is zero.

Both inputs are needed and neither suffices: effectivity holds at every `n` and says nothing
about which divisor; the degree identity holds at every `n` and pins nothing until the degree is
`0`. -/
theorem presentationDivisor_eq_zero_of_isCertified_zero
    {d : (relCurve C K).LocalEquations} (A : DivisorAdaptation C K pi d)
    (hc : A.IsCertified 0) :
    Scheme.presentationDivisor K d.presentation = 0 := by
  refine Scheme.CurveDivisor.eq_zero_of_deg_le_zero K (fun x => ?_) ?_
  · exact Scheme.zero_le_coeffAt_presentationDivisor K d x.2
  · rw [DivisorAdaptation.IsCertified.deg_presentationDivisor (A := A) hc]
    norm_num

/-- **Any two degree-zero certified families are divisor-equal**, since both cut the zero
divisor and over a field equal presentation divisors force `DivEq`. -/
theorem divEq_of_isCertified_zero
    {d d' : (relCurve C K).LocalEquations}
    (A : DivisorAdaptation C K pi d) (hc : A.IsCertified 0)
    (A' : DivisorAdaptation C K pi d') (hc' : A'.IsCertified 0) :
    Scheme.LocalEquations.DivEq d d' :=
  Scheme.divEq_of_presentationDivisor_eq K
    ((presentationDivisor_eq_zero_of_isCertified_zero A hc).trans
      (presentationDivisor_eq_zero_of_isCertified_zero A' hc').symm)

/-! ## The quotients are subsingletons -/

/-- **`DivFam C K π 0` has at most one element.**  `divFamSetoid` relates two families exactly
when their systems are divisor-equal, and `divEq_of_isCertified_zero` says that always holds at
degree `0`. -/
instance instSubsingletonDivFamZero : Subsingleton (DivFam C K pi 0) := by
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.ind with | _ F =>
  induction y using Quotient.ind with | _ G =>
  exact Quotient.sound (divEq_of_isCertified_zero F.adaptation F.certified
    G.adaptation G.certified)

/-- **And so does the functor carrier `DivFamZar C K π 0`.**  Over a field `toZar` is surjective
(`DivFam.exists_toZar_eq`), so the subsingleton transports from the globally certified quotient
to the locally certified one — which is the type `divFunctor C π 0` actually takes as its value
at `Spec K`. -/
instance instSubsingletonDivFamZarZero : Subsingleton (DivFamZar C K pi 0) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨G, hG⟩ := DivFam.exists_toZar_eq (C := C) (K := K) (π := pi) (n := 0) x
  obtain ⟨H, hH⟩ := DivFam.exists_toZar_eq (C := C) (K := K) (π := pi) (n := 0) y
  rw [← hG, ← hH, Subsingleton.elim G H]

/-- **EXACTLY ONE degree-zero divisor class over a field**: `Nonempty` from the unconditional
`DivFamZar.trivZar`, `Subsingleton` from the pin above. -/
@[reducible] noncomputable def DivFamZar.uniqueZeroOfField : Unique (DivFamZar C K pi 0) :=
  uniqueOfSubsingleton (DivFamZar.trivZar C K pi)

end AlgebraicGeometry
