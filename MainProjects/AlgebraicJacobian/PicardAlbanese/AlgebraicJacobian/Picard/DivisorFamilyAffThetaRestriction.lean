/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafAffineProjective
import AlgebraicJacobian.Cohomology.RelCurveCollapse
import AlgebraicJacobian.Picard.DivisorFamilyAffAdaptation
import AlgebraicJacobian.Picard.InvertibleModuleTransfer

/-!
# Intrinsic theta restrictions on widened divisor-family pieces

The widened cover of `AffAdaptation` consists of arbitrary affine opens.  It therefore
cannot use a pinned-chart trivialization of the theta cocycle.  Instead, on each piece
`D.pieces j` we choose the affine sections model of the intrinsic cocycle-glued theta
line bundle `(thetaChartDatum C R π a).sheaf`.  Its sections are an invertible module
over the piece ring.

Base change along the quotient
`Gamma(D.pieces j) -> A.colength j = Gamma(D.pieces j) / (A.eqn j)` gives the intrinsic
restriction of the theta line bundle to the piece of the finite divisor.  Invertibility
is preserved by this base change.  A widened certificate then makes the colength algebra
finite projective over `R`, so the existing invertible-module transfer gives finite and
projective `R`-modules without any chart typing or additional hypothesis.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

/-- The intrinsic theta sections on the widened affine piece `j`. -/
noncomputable abbrev ThetaPieceSections (_A : AffAdaptation D d) (a : ℕ)
    (j : D.index) : Type u :=
  (thetaChartDatum C R π a).sheaf.obj.obj (op (D.pieces j))

/-- A canonical choice of the finite projective invertible sections model of the
intrinsic theta line bundle on the widened affine piece `j`.  The choice internally
refines the arbitrary piece by basic opens subordinate to the theta cover; it does not
type the piece itself into either pinned chart. -/
noncomputable def thetaPieceSectionsModel (_A : AffAdaptation D d) (a : ℕ) (j : D.index) :
    (thetaChartDatum C R π a).AffineSectionsModel (D.pieces j) :=
  Classical.choice ((thetaChartDatum C R π a).nonempty_affineSectionsModel
    (D.pieces j) (D.isAffineOpen j))

/-- The piece-ring action on intrinsic theta sections selected by
`thetaPieceSectionsModel`. -/
@[reducible]
noncomputable def thetaPieceSectionsModule (A : AffAdaptation D d) (a : ℕ) (j : D.index) :
    Module Γ(relCurve C R, D.pieces j) (A.ThetaPieceSections (π := π) a j) :=
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf (D.pieces j) :=
    (A.thetaPieceSectionsModel (π := π) a j).qcoh
  Scheme.QcohOn.moduleOfLE (F := (thetaChartDatum C R π a).sheaf)
    (le_refl (D.pieces j))

/-- The intrinsic restriction of `O(a Theta)` to the divisor inside the widened piece
`j`: tensor theta sections with the equation quotient `A.colength j`. -/
noncomputable abbrev ThetaPieceRestriction (A : AffAdaptation D d) (a : ℕ)
    (j : D.index) : Type u :=
  letI : Module Γ(relCurve C R, D.pieces j) (A.ThetaPieceSections (π := π) a j) :=
    A.thetaPieceSectionsModule (π := π) a j
  A.colength j ⊗[Γ(relCurve C R, D.pieces j)] A.ThetaPieceSections (π := π) a j

/-- The intrinsic theta restriction is invertible over the piece-local colength algebra.
This is base-change stability of invertible modules. -/
theorem invertible_thetaPieceRestriction (A : AffAdaptation D d) (a : ℕ) (j : D.index) :
    Module.Invertible (A.colength j) (A.ThetaPieceRestriction (π := π) a j) := by
  let M := A.thetaPieceSectionsModel (π := π) a j
  letI : Scheme.QcohOn (thetaChartDatum C R π a).sheaf (D.pieces j) := M.qcoh
  letI : Module Γ(relCurve C R, D.pieces j) (A.ThetaPieceSections (π := π) a j) :=
    A.thetaPieceSectionsModule (π := π) a j
  haveI : Module.Invertible Γ(relCurve C R, D.pieces j)
      (A.ThetaPieceSections (π := π) a j) := M.invertible
  change Module.Invertible (A.colength j)
    (A.colength j ⊗[Γ(relCurve C R, D.pieces j)]
      A.ThetaPieceSections (π := π) a j)
  infer_instance

/-- Under the existing widened certificate, every intrinsic theta restriction is finite
over the test ring. -/
theorem IsCertified.finite_thetaPieceRestriction (A : AffAdaptation D d) {n : ℕ}
    (hc : A.IsCertified n) (a : ℕ) (j : D.index) :
    Module.Finite R (A.ThetaPieceRestriction (π := π) a j) := by
  letI : Module Γ(relCurve C R, D.pieces j) (A.ThetaPieceSections (π := π) a j) :=
    A.thetaPieceSectionsModule (π := π) a j
  haveI : Module.Invertible (A.colength j)
      (A.ThetaPieceRestriction (π := π) a j) :=
    A.invertible_thetaPieceRestriction (π := π) a j
  haveI : Module.Finite R (A.colength j) := hc.finite_colength j
  exact Module.Invertible.finite_trans (A := A.colength j)

/-- Under the existing widened certificate, every intrinsic theta restriction is
projective over the test ring. -/
theorem IsCertified.projective_thetaPieceRestriction (A : AffAdaptation D d) {n : ℕ}
    (hc : A.IsCertified n) (a : ℕ) (j : D.index) :
    Module.Projective R (A.ThetaPieceRestriction (π := π) a j) := by
  letI : Module Γ(relCurve C R, D.pieces j) (A.ThetaPieceSections (π := π) a j) :=
    A.thetaPieceSectionsModule (π := π) a j
  haveI : Module.Invertible (A.colength j)
      (A.ThetaPieceRestriction (π := π) a j) :=
    A.invertible_thetaPieceRestriction (π := π) a j
  haveI : Module.Projective R (A.colength j) := hc.projective_colength j
  exact Module.Invertible.projective_trans (A := A.colength j)

end AffAdaptation

end AlgebraicGeometry
