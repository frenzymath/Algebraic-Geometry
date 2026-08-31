/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Support of a finite module after base change

For a finite `A`-module `M`, base change to an `A`-algebra `B` neither creates nor
removes support above a prime of `A`.  The reverse implication in
`support_baseChange_finite` is the missing carrier direction needed to compare a
fibre of a schematic support with the schematic support of a fibre.
-/

set_option autoImplicit false

open TensorProduct

namespace AlgebraicGeometry

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The support of a finite module commutes with arbitrary base change, pointwise. -/
theorem support_baseChange_finite (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (q : PrimeSpectrum B) :
    q ∈ Module.support B (B ⊗[A] M) ↔
      PrimeSpectrum.comap (algebraMap A B) q ∈ Module.support A M := by
  set p := PrimeSpectrum.comap (algebraMap A B) q with hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  have hcom : p.asIdeal = q.asIdeal.comap (algebraMap A B) := rfl
  letI phi : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) hcom
  letI algPhi : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := phi.toAlgebra
  haveI tower : IsScalarTower A p.asIdeal.ResidueField q.asIdeal.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change (algebraMap A q.asIdeal.ResidueField) a = phi _
    rw [Ideal.ResidueField.map_algebraMap,
      IsScalarTower.algebraMap_apply A B q.asIdeal.ResidueField]
  have cancelB : Nontrivial (q.asIdeal.ResidueField ⊗[B] (B ⊗[A] M)) ↔
      Nontrivial (q.asIdeal.ResidueField ⊗[A] M) :=
    (AlgebraTensorModule.cancelBaseChange A B q.asIdeal.ResidueField
      q.asIdeal.ResidueField M).toEquiv.nontrivial_congr
  have factorResidue : Nontrivial (q.asIdeal.ResidueField ⊗[A] M) ↔
      Nontrivial (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
        (p.asIdeal.ResidueField ⊗[A] M)) :=
    ((AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField
      q.asIdeal.ResidueField q.asIdeal.ResidueField M).toEquiv.nontrivial_congr).symm
  have faithful : Nontrivial (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
        (p.asIdeal.ResidueField ⊗[A] M)) ↔
      Nontrivial (p.asIdeal.ResidueField ⊗[A] M) :=
    Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
      p.asIdeal.ResidueField q.asIdeal.ResidueField
  rw [cancelB, factorResidue, faithful]

/-- Set-level form of `support_baseChange_finite`. -/
theorem support_baseChange_finite_eq (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    Module.support B (B ⊗[A] M) =
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' Module.support A M := by
  ext q
  simpa using support_baseChange_finite M q

/-- Empty support is preserved by base change for finite modules. -/
theorem support_baseChange_finite_eq_empty_of_isEmpty (M : Type u) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (h : Module.support A M = ∅) :
    Module.support B (B ⊗[A] M) = ∅ := by
  rw [support_baseChange_finite_eq, h, Set.preimage_empty]

end AlgebraicGeometry
