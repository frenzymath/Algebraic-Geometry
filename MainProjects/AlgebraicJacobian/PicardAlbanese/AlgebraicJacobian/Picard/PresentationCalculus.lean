/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PresentationDivisor

/-!
# The calculus of meromorphic presentations

Meromorphic presentations (`AlgebraicJacobian.Picard.MeromorphicPresentation`) multiply,
invert, and have a unit — pointwise on the trivializing elements, by restriction to the
common refinement on the cocycles. This file provides this calculus, its effect on the
presented Picard class, and its effect on the divisor of the presentation:

* `1`, `P * Q`, `P⁻¹` (`One`/`Mul`/`Inv` instances; no group laws are claimed — the
  covers of `(P * Q) * R` and `P * (Q * R)` differ by associativity of `⊓` — and none
  are needed: all identifications happen at the level of `picClass`);
* `MeromorphicPresentation.principal`: the principal presentation of `g ∈ K(X)ˣ` — the
  trivial cocycle on the top cover trivialized by the constant `g` — presenting the
  trivial class with divisor `div g`;
* `picClass_one`, `picClass_mul`, `picClass_inv`, `picClass_principal`: the class map is
  multiplicative;
* `presentationDivisor_one`, `presentationDivisor_mul`, `presentationDivisor_inv`,
  `presentationDivisor_principal`: the divisor map is additive.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-- The pair values of the inverse of a unit Čech cocycle are the inverses of the pair
values. Mirrors `Scheme.mul_unitsEvInf`. -/
@[simp]
lemma inv_unitsEvInf {𝒰 : X.PointedCover} (γ : X.unitsCocycle 𝒰) (i j : X) :
    unitsEvInf γ⁻¹ i j = (unitsEvInf γ i j)⁻¹ :=
  rfl

namespace MeromorphicPresentation

variable [IsIntegral X]

/-! ## The unit, product, and inverse presentations -/

noncomputable instance : One X.MeromorphicPresentation where
  one :=
    { cover := ⊤
      cocycle := 1
      elem := fun _ => 1
      ratio := fun x y => by rw [one_unitsEvInf, map_one, inv_one, mul_one] }

@[simp] lemma one_cover : (1 : X.MeromorphicPresentation).cover = ⊤ := rfl

@[simp] lemma one_cocycle : (1 : X.MeromorphicPresentation).cocycle = 1 := rfl

@[simp] lemma one_elem (x : X) : (1 : X.MeromorphicPresentation).elem x = 1 := rfl

noncomputable instance : Inv X.MeromorphicPresentation where
  inv P :=
    { cover := P.cover
      cocycle := P.cocycle⁻¹
      elem := fun x => (P.elem x)⁻¹
      ratio := fun x y => by rw [inv_unitsEvInf, map_inv, ← P.ratio x y, mul_inv] }

@[simp] lemma inv_cover (P : X.MeromorphicPresentation) : (P⁻¹).cover = P.cover := rfl

@[simp] lemma inv_cocycle (P : X.MeromorphicPresentation) :
    (P⁻¹).cocycle = P.cocycle⁻¹ := rfl

@[simp] lemma inv_elem (P : X.MeromorphicPresentation) (x : X) :
    (P⁻¹).elem x = (P.elem x)⁻¹ := rfl

noncomputable instance : Mul X.MeromorphicPresentation where
  mul P Q :=
    { cover := P.cover ⊓ Q.cover
      cocycle :=
        P.cocycle.res (fun x =>
            homOfLE ((inf_le_left : P.cover ⊓ Q.cover ≤ P.cover) x))
          * Q.cocycle.res (fun x =>
              homOfLE ((inf_le_right : P.cover ⊓ Q.cover ≤ Q.cover) x))
      elem := fun x => P.elem x * Q.elem x
      ratio := fun x y => by
        rw [mul_unitsEvInf, map_mul, res_unitsEvInf, res_unitsEvInf,
          germGenericUnits_unitsRestrict, germGenericUnits_unitsRestrict,
          ← P.ratio x y, ← Q.ratio x y, mul_inv, mul_mul_mul_comm] }

@[simp] lemma mul_cover (P Q : X.MeromorphicPresentation) :
    (P * Q).cover = P.cover ⊓ Q.cover := rfl

@[simp] lemma mul_elem (P Q : X.MeromorphicPresentation) (x : X) :
    (P * Q).elem x = P.elem x * Q.elem x := rfl

lemma mul_cocycle (P Q : X.MeromorphicPresentation) :
    (P * Q).cocycle
      = P.cocycle.res (fun x =>
          homOfLE ((inf_le_left : P.cover ⊓ Q.cover ≤ P.cover) x))
        * Q.cocycle.res (fun x =>
            homOfLE ((inf_le_right : P.cover ⊓ Q.cover ≤ Q.cover) x)) := rfl

/-- The principal presentation of a rational function `g ∈ K(X)ˣ`: the trivial cocycle
on the top cover, trivialized by the constant `g`. It presents the trivial Picard class
(`picClass_principal`), and its divisor is the principal divisor `div g`
(`presentationDivisor_principal`). -/
def principal (g : X.functionFieldˣ) : X.MeromorphicPresentation where
  cover := ⊤
  cocycle := 1
  elem _ := g
  ratio x y := by rw [one_unitsEvInf, map_one, mul_inv_cancel]

@[simp] lemma principal_cover (g : X.functionFieldˣ) : (principal g).cover = ⊤ := rfl

@[simp] lemma principal_cocycle (g : X.functionFieldˣ) : (principal g).cocycle = 1 := rfl

@[simp] lemma principal_elem (g : X.functionFieldˣ) (x : X) :
    (principal g).elem x = g := rfl

/-! ## The Picard classes of the calculus -/

@[simp]
lemma picClass_one : (1 : X.MeromorphicPresentation).picClass = 1 := by
  change CechPic.mk ⊤ (1 : X.unitsCocycle ⊤).class = 1
  rw [OneCocycle.class_one, CechPic.mk_one]

@[simp]
lemma picClass_principal (g : X.functionFieldˣ) : (principal g).picClass = 1 := by
  change CechPic.mk ⊤ (1 : X.unitsCocycle ⊤).class = 1
  rw [OneCocycle.class_one, CechPic.mk_one]

@[simp]
lemma picClass_inv (P : X.MeromorphicPresentation) : (P⁻¹).picClass = P.picClass⁻¹ := by
  change CechPic.mk P.cover (P.cocycle⁻¹).class
    = (CechPic.mk P.cover P.cocycle.class)⁻¹
  rw [OneCocycle.class_inv, CechPic.mk_inv]

@[simp]
lemma picClass_mul (P Q : X.MeromorphicPresentation) :
    (P * Q).picClass = P.picClass * Q.picClass := by
  change CechPic.mk (P.cover ⊓ Q.cover) (OneCocycle.class _) = _
  rw [mul_cocycle, OneCocycle.class_mul,
    ← unitsRes_class (inf_le_left : P.cover ⊓ Q.cover ≤ P.cover) P.cocycle,
    ← unitsRes_class (inf_le_right : P.cover ⊓ Q.cover ≤ Q.cover) Q.cocycle,
    ← CechPic.mk_mul_mk_inf]
  rfl

/-! ## The divisors of the calculus -/

variable (K : Type u) [Field K] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

@[simp]
theorem presentationDivisor_one :
    presentationDivisor K (1 : X.MeromorphicPresentation) = 0 := by
  refine CurveDivisor.ext_coeffAt fun x hx => ?_
  rw [coeffAt_presentationDivisor, one_elem, map_one, toAdd_one,
    CurveDivisor.coeffAt_zero]

@[simp]
theorem presentationDivisor_inv (P : X.MeromorphicPresentation) :
    presentationDivisor K P⁻¹ = -presentationDivisor K P := by
  refine CurveDivisor.ext_coeffAt fun x hx => ?_
  rw [coeffAt_presentationDivisor, inv_elem, map_inv, toAdd_inv,
    CurveDivisor.coeffAt_neg, coeffAt_presentationDivisor]

@[simp]
theorem presentationDivisor_mul (P Q : X.MeromorphicPresentation) :
    presentationDivisor K (P * Q) = presentationDivisor K P + presentationDivisor K Q := by
  refine CurveDivisor.ext_coeffAt fun x hx => ?_
  rw [coeffAt_presentationDivisor, mul_elem, map_mul, toAdd_mul,
    CurveDivisor.coeffAt_add, coeffAt_presentationDivisor, coeffAt_presentationDivisor]

/-- The divisor of the principal presentation of `g` is the principal divisor `div g`. -/
@[simp]
theorem presentationDivisor_principal (g : X.functionFieldˣ) :
    presentationDivisor K (principal g)
      = Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g := by
  refine CurveDivisor.ext_coeffAt fun x hx => ?_
  rw [coeffAt_presentationDivisor, principal_elem,
    CurveDivisor.coeffAt_divOf (X ↘ Spec (CommRingCat.of K)) g hx]

end MeromorphicPresentation

end Scheme

end AlgebraicGeometry
