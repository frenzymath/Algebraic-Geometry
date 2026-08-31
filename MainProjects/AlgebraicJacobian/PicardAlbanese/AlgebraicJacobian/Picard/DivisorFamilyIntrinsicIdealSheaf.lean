/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorIntrinsicIdealSheaf
import AlgebraicJacobian.Picard.DivisorFamilyAffZar

/-!
# The intrinsic ideal sheaf of a widened divisor-family class

The intrinsic Cartier ideal sheaf is invariant under `DivEq`, so it descends from locally
certified local-equation systems to the widened divisor-family quotient `DivFamZarAff`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]

namespace DivFamZarAff

/-- The intrinsic Cartier ideal sheaf of a widened locally certified divisor-family class. -/
noncomputable def cartierIdealData [IsProper C.hom] {n : ℕ}
    (F : DivFamZarAff C R n) : (relCurve C R).IdealSheafData :=
  Quotient.lift
    (fun d : {d : (relCurve C R).LocalEquations // IsLocallyCertifiedAff n d} ↦
      d.1.cartierIdealData)
    (fun _ _ h ↦ Scheme.LocalEquations.cartierIdealData_eq_of_divEq h) F

@[simp]
theorem cartierIdealData_mk [IsProper C.hom] {n : ℕ}
    (d : (relCurve C R).LocalEquations) (hd : IsLocallyCertifiedAff n d) :
    cartierIdealData (mk d hd) = d.cartierIdealData :=
  rfl

end DivFamZarAff

end AlgebraicGeometry
