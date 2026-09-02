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

/-- A chosen exponential certificate gives division by every positive natural.

This is the divisibility half of the analytic torsion statement, expressed at
the explicit-data boundary so that it does not assert existence of an
exponential for an arbitrary target. -/
theorem ComplexTorusExponentialData.exists_division
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (d : ComplexTorusExponentialData X g) (x : X) (hn : 0 < n) :
    ∃ y : X, (n : ℤ) • y = x := by
  let u := d.toUniformization.toGenusTorusUniformization
  have hnz : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  exact exists_division_of_uniformization u x hnz

/-- The positive-natural torsion equivalence attached to an exponential
certificate. -/
noncomputable def ComplexTorusExponentialData.natCast_zsmulTorsion_addEquiv
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (d : ComplexTorusExponentialData X g) (hn : 0 < n) :
    zsmulTorsionSubgroup X (n : ℤ) ≃+
      (Fin (2 * g) → ZMod n) :=
  natCast_zsmulTorsion_addEquiv_of_uniformization
    d.toUniformization.toGenusTorusUniformization hn

/-- Combined proposition-valued form of divisibility and finite torsion for a
chosen exponential certificate.  `Nonempty` records the equivalence as a
proposition, since an additive equivalence itself is data rather than a
proposition. -/
theorem ComplexTorusExponentialData.division_and_torsion
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (d : ComplexTorusExponentialData X g) (x : X) (hn : 0 < n) :
    (∃ y : X, (n : ℤ) • y = x) ∧
      Nonempty (zsmulTorsionSubgroup X (n : ℤ) ≃+
        (Fin (2 * g) → ZMod n)) := by
  refine ⟨d.exists_division x hn, ?_⟩
  exact ⟨d.natCast_zsmulTorsion_addEquiv hn⟩

/- The signed-integer torsion classification is the primary API; the
   positive-natural version above is a specialization of it. -/
noncomputable def ComplexTorusExponentialData.zsmulTorsion_addEquiv
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (d : ComplexTorusExponentialData X g) (hn : n ≠ 0) :
    zsmulTorsionSubgroup X n ≃+
      (Fin (2 * g) → ZMod n.natAbs) :=
  complexUniformization_zsmulTorsion_addEquiv d.toUniformization hn

/- The data-boundary equivalence agrees with the canonical complex-quotient
   factorization of the underlying uniformization witness. -/
theorem ComplexTorusExponentialData.zsmulTorsion_addEquiv_eq_trans
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (d : ComplexTorusExponentialData X g) (hn : n ≠ 0) :
    d.zsmulTorsion_addEquiv hn =
      (zsmulTorsion_addEquiv_of_addEquiv d.toUniformization.equiv n).trans
        (complexGenusQuotient_zsmulTorsion_addEquiv hn) := by
  exact complexUniformization_zsmulTorsion_addEquiv_eq_trans
    d.toUniformization hn

@[simp]
theorem ComplexTorusExponentialData.zsmulTorsion_addEquiv_apply
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (d : ComplexTorusExponentialData X g) (hn : n ≠ 0)
    (x : zsmulTorsionSubgroup X n) :
    ((d.zsmulTorsion_addEquiv hn) x : Fin (2 * g) → ZMod n.natAbs) =
      (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)
        ((zsmulTorsion_addEquiv_of_addEquiv
          d.toUniformization.toGenusTorusUniformization.equiv n) x) := by
  exact complexUniformization_zsmulTorsion_addEquiv_apply
    d.toUniformization hn x

/-- Cardinality of signed-integer torsion under an exponential certificate. -/
theorem ComplexTorusExponentialData.zsmulTorsion_card
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (d : ComplexTorusExponentialData X g) (hn : n ≠ 0) :
    Nat.card (zsmulTorsionSubgroup X n) = n.natAbs ^ (2 * g) := by
  exact complexUniformization_zsmulTorsion_card d.toUniformization hn

/-- Finiteness of signed-integer torsion under an exponential certificate. -/
theorem ComplexTorusExponentialData.zsmulTorsion_finite
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (d : ComplexTorusExponentialData X g) (hn : n ≠ 0) :
    Finite (zsmulTorsionSubgroup X n) := by
  exact complexUniformization_zsmulTorsion_finite d.toUniformization hn

/-- Signed divisibility and finite torsion packaged as one proposition. -/
theorem ComplexTorusExponentialData.division_and_zsmulTorsion
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (d : ComplexTorusExponentialData X g) (x : X) (hn : n ≠ 0) :
    (∃ y : X, n • y = x) ∧
      Nonempty (zsmulTorsionSubgroup X n ≃+
        (Fin (2 * g) → ZMod n.natAbs)) := by
  refine ⟨?_, ⟨d.zsmulTorsion_addEquiv hn⟩⟩
  exact complexUniformization_exists_division d.toUniformization x hn

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
