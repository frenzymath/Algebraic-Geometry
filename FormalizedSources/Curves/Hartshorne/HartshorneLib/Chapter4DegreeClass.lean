/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorClass

/-!
# Hartshorne II.6: degree on divisor classes

The geometric assertion that a principal divisor on a complete nonsingular
curve has degree zero is kept as an explicit input here.  Once that input is
available, the already-defined divisor degree descends canonically to the
divisor class group.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-! The missing geometric input in the degree descent is isolated explicitly. -/

/-- Every principal divisor has degree zero.

This is the valuation-theoretic statement of Hartshorne II.6.10.  It is an
explicit hypothesis so that the quotient construction below does not conceal
an unproved geometric assertion.
-/
def PrincipalDivisorsHaveDegreeZero : Prop :=
  ∀ g : X.left.functionFieldˣ, CurveDivisor.degree (principalDivisor g) = 0

theorem principalDivisors_le_degreeHom_ker
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X)) :
    principalDivisors ≤ (CurveDivisor.degreeHom (k := k) (X := X)).ker := by
  intro D hD
  rw [AddMonoidHom.mem_ker]
  obtain ⟨g, hg⟩ := (mem_principalDivisors_iff D).mp hD
  rw [← hg]
  rw [CurveDivisor.degreeHom_apply]
  exact hzero g

/-- The degree homomorphism induced on the divisor class group. -/
noncomputable def degreeClass
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X)) :
    DivisorClassGroup (k := k) (X := X) →+ ℤ :=
  QuotientAddGroup.lift principalDivisors
    (CurveDivisor.degreeHom (k := k) (X := X))
    (principalDivisors_le_degreeHom_ker hzero)

@[simp]
theorem degreeClass_divisorClass
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    (D : CurveDivisor k X) :
    degreeClass hzero (divisorClass D) = CurveDivisor.degree D := by
  change (QuotientAddGroup.lift principalDivisors
      (CurveDivisor.degreeHom (k := k) (X := X)) _) 
      (D : CurveDivisor k X ⧸ principalDivisors) = _
  rw [QuotientAddGroup.lift_mk']
  exact CurveDivisor.degreeHom_apply D

@[simp]
theorem degreeClass_zero
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X)) :
    degreeClass hzero (0 : DivisorClassGroup (k := k) (X := X)) = 0 :=
  map_zero (degreeClass hzero)

/-! The quotient map sends every principal divisor to the zero class, so the
degree descended above vanishes on principal classes as well. -/

@[simp]
theorem degreeClass_principalDivisor
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    (g : X.left.functionFieldˣ) :
    degreeClass hzero (divisorClass (principalDivisor g)) = 0 := by
  rw [divisorClass_principalDivisor, degreeClass_zero]

theorem degreeClass_add
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    (a b : DivisorClassGroup (k := k) (X := X)) :
    degreeClass hzero (a + b) = degreeClass hzero a + degreeClass hzero b :=
  map_add (degreeClass hzero) a b

/-! ## Degree-zero classes and the degree splitting attached to a point -/

/-- The subgroup of divisor classes of degree zero. -/
noncomputable def degreeZeroDivisorClasses
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X)) :
    AddSubgroup (DivisorClassGroup (k := k) (X := X)) :=
  (degreeClass hzero).ker

@[simp]
theorem mem_degreeZeroDivisorClasses_iff
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    (a : DivisorClassGroup (k := k) (X := X)) :
    a ∈ degreeZeroDivisorClasses hzero ↔ degreeClass hzero a = 0 :=
  AddMonoidHom.mem_ker

@[simp]
theorem divisorClass_mem_degreeZeroDivisorClasses_iff
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    (D : CurveDivisor k X) :
    divisorClass D ∈ degreeZeroDivisorClasses hzero ↔
      CurveDivisor.degree D = 0 := by
  rw [mem_degreeZeroDivisorClasses_iff, degreeClass_divisorClass]

/-- Multiples of a non-generic point, viewed in the divisor class group. -/
noncomputable def pointClassHom
    (x : {x : X.left // x ≠ genericPoint X.left}) :
    ℤ →+ DivisorClassGroup (k := k) (X := X) :=
  divisorClass.comp (Finsupp.singleAddHom x)

@[simp]
theorem pointClassHom_apply
    (x : {x : X.left // x ≠ genericPoint X.left}) (n : ℤ) :
    pointClassHom (k := k) x n = divisorClass (Finsupp.single x n) :=
  rfl

@[simp]
theorem degreeClass_pointClassHom
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    (x : {x : X.left // x ≠ genericPoint X.left}) (n : ℤ) :
    degreeClass hzero (pointClassHom (k := k) x n) = n := by
  rw [pointClassHom_apply, degreeClass_divisorClass,
    CurveDivisor.degree_single]

/-- The class attached to `n` is the `n`-fold multiple of the point class. -/
theorem pointClassHom_eq_zsmul
    (x : {x : X.left // x ≠ genericPoint X.left}) (n : ℤ) :
    pointClassHom (k := k) x n = n • pointClassHom (k := k) x 1 := by
  simpa using (map_zsmul (pointClassHom (k := k) x) n (1 : ℤ))

/-- A chosen non-generic point gives a section of the degree map. -/
theorem degreeClass_comp_pointClassHom
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    (x : {x : X.left // x ≠ genericPoint X.left}) :
    (degreeClass hzero).comp (pointClassHom (k := k) x) =
      AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext
  intro n
  rw [AddMonoidHom.comp_apply, degreeClass_pointClassHom]
  rfl

/-- If the curve has a non-generic point, every integer occurs as the degree of
a divisor class. -/
theorem degreeClass_surjective_of_point
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    (x : {x : X.left // x ≠ genericPoint X.left}) :
    Function.Surjective (degreeClass hzero) := by
  intro n
  exact ⟨pointClassHom (k := k) x n, degreeClass_pointClassHom hzero x n⟩

/-- Relative to a chosen non-generic point, every divisor class is the sum of
a degree-zero class and a canonical point class of the same degree. -/
theorem exists_degreeZero_add_pointClass
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    (x : {x : X.left // x ≠ genericPoint X.left})
    (a : DivisorClassGroup (k := k) (X := X)) :
    ∃ a₀ : DivisorClassGroup (k := k) (X := X),
      a₀ ∈ degreeZeroDivisorClasses hzero ∧
        a = a₀ + pointClassHom (k := k) x (degreeClass hzero a) := by
  let px := pointClassHom (k := k) x (degreeClass hzero a)
  refine ⟨a - px, ?_, ?_⟩
  · have hpx : degreeClass hzero px = degreeClass hzero a := by
      change degreeClass hzero
        (pointClassHom (k := k) x (degreeClass hzero a)) = _
      exact degreeClass_pointClassHom hzero x (degreeClass hzero a)
    rw [mem_degreeZeroDivisorClasses_iff, map_sub, hpx, sub_self]
  · dsimp [px]
    abel

/-- Degree is invariant under linear equivalence once principal divisors have
degree zero. -/
theorem degree_eq_of_linearlyEquivalent
    (hzero : PrincipalDivisorsHaveDegreeZero (k := k) (X := X))
    {D E : CurveDivisor k X} (h : LinearlyEquivalent D E) :
    CurveDivisor.degree D = CurveDivisor.degree E := by
  have hker : D - E ∈
      (CurveDivisor.degreeHom (k := k) (X := X)).ker :=
    principalDivisors_le_degreeHom_ker hzero h
  have hsub : CurveDivisor.degree (D - E) = 0 :=
    (AddMonoidHom.mem_ker.mp hker)
  rw [CurveDivisor.degree_sub] at hsub
  exact sub_eq_zero.mp hsub

/-- The descended degree does not depend on the chosen proof of the geometric
degree-zero assertion. -/
theorem degreeClass_proof_irrel
    (h₁ h₂ : PrincipalDivisorsHaveDegreeZero (k := k) (X := X)) :
    degreeClass h₁ = degreeClass h₂ := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective principalDivisors q
  change degreeClass h₁ (divisorClass D) = degreeClass h₂ (divisorClass D)
  rw [degreeClass_divisorClass]

/-- The subgroup of degree-zero classes is independent of the proof used to
descend degree to the divisor class group. -/
theorem degreeZeroDivisorClasses_proof_irrel
    (h₁ h₂ : PrincipalDivisorsHaveDegreeZero (k := k) (X := X)) :
    degreeZeroDivisorClasses h₁ = degreeZeroDivisorClasses h₂ := by
  unfold degreeZeroDivisorClasses
  rw [degreeClass_proof_irrel h₁ h₂]

end Hartshorne
