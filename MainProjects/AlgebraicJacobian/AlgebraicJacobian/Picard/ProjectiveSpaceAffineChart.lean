/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ProjectiveSpace

/-!
# The standard affine chart of relative projective space

This file constructs the standard chart `D_+(X_none)` of
`P(Option n; S)` as the base change of Mathlib's affine chart
`Proj.awayι`. The identification of its chart ring with a polynomial ring,
and hence of this scheme with `A(n; S)`, is deliberately a separate algebraic
step.
-/

open CategoryTheory Limits MvPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

variable (n : Type u) (S : Scheme.{u})

local notation3 "P[" n "]" =>
  homogeneousSubmodule (Option n) (ULift ℤ)

/-- The distinguished homogenizing coordinate has degree one. -/
private lemma X_none_mem_deg_one :
    (X none : MvPolynomial (Option n) (ULift.{u} ℤ)) ∈ P[n] 1 :=
  isHomogeneous_X _ _

/-- The standard `D_+(X_none)` chart of relative projective space. It is the
pullback of the corresponding affine open of the integral `Proj` model. -/
def affineChart : Scheme.{u} :=
  pullback (toProjInt (Option n) S)
    (Proj.awayι P[n] (X none) (X_none_mem_deg_one n) Nat.zero_lt_one)

namespace affineChart

/-- The inclusion of the standard chart into relative projective space. -/
def incl : affineChart n S ⟶ ℙ(Option n; S) :=
  pullback.fst (toProjInt (Option n) S)
    (Proj.awayι P[n] (X none) (X_none_mem_deg_one n) Nat.zero_lt_one)

instance : IsOpenImmersion (incl n S) := by
  dsimp [incl]
  exact MorphismProperty.pullback_fst _ _
    (Proj.instIsOpenImmersionAwayι P[n] (X none)
      (X_none_mem_deg_one n) Nat.zero_lt_one)

/-- The chart inclusion followed by the integral-model projection is the
other pullback projection followed by `Proj.awayι`. -/
@[reassoc]
theorem incl_toProjInt :
    incl n S ≫ toProjInt (Option n) S =
      pullback.snd (toProjInt (Option n) S)
          (Proj.awayι P[n] (X none) (X_none_mem_deg_one n) Nat.zero_lt_one) ≫
        Proj.awayι P[n] (X none) (X_none_mem_deg_one n) Nat.zero_lt_one :=
  pullback.condition

instance : (affineChart n S).CanonicallyOver S where
  hom := incl n S ≫ (ℙ(Option n; S) ↘ S)

@[simp]
theorem over_eq : affineChart n S ↘ S = incl n S ≫ (ℙ(Option n; S) ↘ S) :=
  rfl

/-- The chart is exactly the inverse image of `D_+(X_none)` in the integral
model. -/
theorem opensRange_incl :
    (incl n S).opensRange =
      toProjInt (Option n) S ⁻¹ᵁ
        Proj.basicOpen P[n] (X none) := by
  change (pullback.fst (toProjInt (Option n) S)
      (Proj.awayι P[n] (X none) (X_none_mem_deg_one n) Nat.zero_lt_one)).opensRange = _
  rw [Scheme.Hom.opensRange_pullbackFst, Proj.opensRange_awayι]

end affineChart

end ProjectiveSpace

end AlgebraicGeometry
