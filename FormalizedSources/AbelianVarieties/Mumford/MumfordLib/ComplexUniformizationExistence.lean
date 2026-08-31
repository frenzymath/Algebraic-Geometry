/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ComplexUniformization

/-!
# The exponential boundary of complex uniformization

The analytic existence theorem is most naturally supplied as a surjective
additive exponential with the prescribed period kernel.  This module packages
that input and proves that it is exactly equivalent to the quotient witness
used by the rest of `MumfordLib`.
-/

set_option autoImplicit false

namespace Mumford
namespace Uniformization

noncomputable section

/-- The analytic data needed to build a complex period-quotient witness. -/
structure ComplexTorusExponentialData (X : Type*) [AddCommGroup X] (g : ℕ) where
  /-- The additive exponential from the complex tangent model. -/
  exponential : GenusComplexVector g →+ X
  /-- The exponential reaches every point of the target. -/
  surjective : Function.Surjective exponential
  /-- Its kernel is the prescribed period lattice. -/
  kernel : exponential.ker = complexPeriodLattice g

theorem ComplexTorusExponentialData.ext_of_exponential_eq
    {X : Type*} [AddCommGroup X] {g : ℕ}
    {d₁ d₂ : ComplexTorusExponentialData X g}
    (h : d₁.exponential = d₂.exponential) : d₁ = d₂ := by
  cases d₁
  cases d₂
  cases h
  rfl

/-- Turn analytic exponential data into the quotient uniformization witness. -/
def ComplexTorusExponentialData.toUniformization
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (d : ComplexTorusExponentialData X g) : ComplexTorusUniformization X g :=
  ComplexTorusUniformization.ofExponential d.exponential d.surjective d.kernel

/-- Extract the exponential data from a quotient uniformization witness. -/
def ComplexTorusUniformization.toExponentialData
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) : ComplexTorusExponentialData X g :=
  { exponential := u.exponential
    surjective := u.exponential_surjective
    kernel := u.exponential_ker }

@[simp]
theorem ComplexTorusUniformization.toExponentialData_exponential
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) :
    u.toExponentialData.exponential = u.exponential :=
  rfl

@[simp]
theorem ComplexTorusExponentialData.toUniformization_exponential
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (d : ComplexTorusExponentialData X g) :
    d.toUniformization.exponential = d.exponential := by
  apply AddMonoidHom.ext
  intro z
  change d.toUniformization.equiv.symm
      (QuotientAddGroup.mk' (complexPeriodLattice g) z) = d.exponential z
  exact ComplexTorusUniformization.ofExponential_equiv_symm_mk
    d.exponential d.surjective d.kernel z

@[simp]
theorem ComplexTorusExponentialData.toUniformization_toExponentialData
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (d : ComplexTorusExponentialData X g) :
    d.toUniformization.toExponentialData = d := by
  apply ComplexTorusExponentialData.ext_of_exponential_eq
  exact d.toUniformization_exponential

@[simp]
theorem ComplexTorusUniformization.toExponentialData_toUniformization
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) :
    u.toExponentialData.toUniformization = u := by
  exact ComplexTorusUniformization.ofExponential_exponential u

/-- Quotient witnesses and surjective exponentials with the canonical kernel
are equivalent data.  The analytic Lie-group theorem is precisely the
existence of an element on the right for the intended target `X`. -/
def complexTorusUniformizationEquivExponentialData
    {X : Type*} [AddCommGroup X] {g : ℕ} :
    ComplexTorusUniformization X g ≃ ComplexTorusExponentialData X g where
  toFun := ComplexTorusUniformization.toExponentialData
  invFun := ComplexTorusExponentialData.toUniformization
  left_inv := ComplexTorusUniformization.toExponentialData_toUniformization
  right_inv := ComplexTorusExponentialData.toUniformization_toExponentialData

@[simp]
theorem complexTorusUniformization_nonempty_iff_exists_exponential
    {X : Type*} [AddCommGroup X] {g : ℕ} :
    Nonempty (ComplexTorusUniformization X g) ↔
      ∃ exponential : GenusComplexVector g →+ X,
        Function.Surjective exponential ∧
          exponential.ker = complexPeriodLattice g := by
  constructor
  · rintro ⟨u⟩
    exact ⟨u.exponential, u.exponential_surjective, u.exponential_ker⟩
  · rintro ⟨exponential, hsurj, hkernel⟩
    exact ⟨ComplexTorusUniformization.ofExponential exponential hsurj hkernel⟩

/-- The standard coordinate exponential supplies the canonical witness for the
explicit genus torus model. -/
def standardComplexTorusUniformization (g : ℕ) :
    ComplexTorusUniformization (GenusTorus g) g :=
  { equiv := (complexGenusQuotientAddEquiv g).symm }

@[simp]
theorem standardComplexTorusUniformization_equiv_apply (g : ℕ)
    (x : GenusTorus g) :
    (standardComplexTorusUniformization g).equiv x =
      (complexGenusQuotientAddEquiv g).symm x :=
  rfl

@[simp]
theorem standardComplexTorusUniformization_exponential_apply (g : ℕ)
    (z : GenusComplexVector g) :
    (standardComplexTorusUniformization g).exponential z =
      complexGenusTorusExponential g z := by
  change (complexGenusQuotientAddEquiv g).symm.symm
      (QuotientAddGroup.mk' (complexPeriodLattice g) z) = _
  simpa only [AddEquiv.symm_symm] using
    (complexGenusQuotientAddEquiv_mk g z)

end
end Uniformization
end Mumford
