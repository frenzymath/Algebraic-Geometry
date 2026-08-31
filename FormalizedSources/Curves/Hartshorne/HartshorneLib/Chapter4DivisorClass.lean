/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4PrincipalDivisors

/-!
# Hartshorne II.6: linear equivalence and the divisor class group

Two divisors are linearly equivalent when their difference is principal. This
file records the equivalence relation, constructs the quotient by the subgroup
of principal divisors, and identifies linear equivalence with equality in that
quotient.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-- Two curve divisors are linearly equivalent when their difference is a
principal divisor. -/
def LinearlyEquivalent (D E : CurveDivisor k X) : Prop :=
  D - E ∈ principalDivisors

/-- The divisor class group, obtained by quotienting divisors by principal
divisors. -/
noncomputable def DivisorClassGroup : Type u :=
  CurveDivisor k X ⧸ principalDivisors

noncomputable instance : AddCommGroup (DivisorClassGroup (k := k) (X := X)) :=
  inferInstanceAs (AddCommGroup (CurveDivisor k X ⧸ principalDivisors))

/-- The class of a divisor in the divisor class group. -/
noncomputable def divisorClass :
    CurveDivisor k X →+ DivisorClassGroup (k := k) (X := X) :=
  QuotientAddGroup.mk' principalDivisors

/-- Linear equivalence is exactly equality of divisor classes. -/
theorem linearlyEquivalent_iff_divisorClass_eq (D E : CurveDivisor k X) :
    LinearlyEquivalent D E ↔ divisorClass D = divisorClass E := by
  simp only [LinearlyEquivalent, divisorClass]
  exact QuotientAddGroup.eq_iff_sub_mem.symm

/-- Linear equivalence is reflexive. -/
theorem linearlyEquivalent_refl (D : CurveDivisor k X) :
    LinearlyEquivalent D D :=
  (linearlyEquivalent_iff_divisorClass_eq D D).mpr rfl

/-- Linear equivalence is symmetric. -/
theorem linearlyEquivalent_symm {D E : CurveDivisor k X}
    (h : LinearlyEquivalent D E) : LinearlyEquivalent E D :=
  (linearlyEquivalent_iff_divisorClass_eq E D).mpr
    ((linearlyEquivalent_iff_divisorClass_eq D E).mp h).symm

/-- Linear equivalence is transitive. -/
theorem linearlyEquivalent_trans {D E F : CurveDivisor k X}
    (hDE : LinearlyEquivalent D E) (hEF : LinearlyEquivalent E F) :
    LinearlyEquivalent D F :=
  (linearlyEquivalent_iff_divisorClass_eq D F).mpr
    ((linearlyEquivalent_iff_divisorClass_eq D E).mp hDE |>.trans
      ((linearlyEquivalent_iff_divisorClass_eq E F).mp hEF))

/-- Linear equivalence bundled as a setoid on curve divisors. -/
def linearEquivalenceSetoid : Setoid (CurveDivisor k X) where
  r := LinearlyEquivalent
  iseqv := ⟨linearlyEquivalent_refl, fun h => linearlyEquivalent_symm h,
    fun hDE hEF => linearlyEquivalent_trans hDE hEF⟩

/-- Source-style characterization of linear equivalence by one nonzero
rational function. -/
theorem linearlyEquivalent_iff_exists (D E : CurveDivisor k X) :
    LinearlyEquivalent D E ↔
      ∃ g : X.left.functionFieldˣ, D - E = principalDivisor g := by
  rw [LinearlyEquivalent, mem_principalDivisors_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, hg.symm⟩

/-- Every principal divisor represents the zero divisor class. -/
@[simp]
theorem divisorClass_principalDivisor (g : X.left.functionFieldˣ) :
    divisorClass (principalDivisor g) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff (principalDivisor g)).mpr
  exact (mem_principalDivisors_iff (principalDivisor g)).mpr ⟨g, rfl⟩

/-- Two divisors have the same class exactly when their difference is principal. -/
theorem divisorClass_eq_iff_exists_principal (D E : CurveDivisor k X) :
    divisorClass D = divisorClass E ↔
      ∃ g : X.left.functionFieldˣ, D - E = principalDivisor g := by
  rw [← linearlyEquivalent_iff_divisorClass_eq,
    linearlyEquivalent_iff_exists]

/-- A divisor represents the zero class exactly when it is principal. -/
theorem divisorClass_eq_zero_iff_exists_principal (D : CurveDivisor k X) :
    divisorClass D = 0 ↔
      ∃ g : X.left.functionFieldˣ, D = principalDivisor g := by
  rw [← divisorClass_principalDivisor (1 : X.left.functionFieldˣ)]
  rw [← linearlyEquivalent_iff_divisorClass_eq,
    linearlyEquivalent_iff_exists]
  simp

end Hartshorne
