/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import MilneLib.Isogeny

/-!
# Multiplication and torsion kernels

For a commutative group object, the `n`-fold power of the identity
endomorphism is the categorical multiplication-by-`n` morphism.  This file
packages its underlying scheme map and the corresponding kernel scheme, which
is Milne's notation `A_n`.
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry

namespace MilneLib

variable {K : Type u} [Field K]
variable {A : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]

/-- The categorical multiplication-by-`n` morphism on a commutative group
scheme, obtained from the `n`-fold power of its identity homomorphism. -/
noncomputable def multiplicationBy (A : Over (Spec (.of K)))
    [GrpObj A] [IsCommMonObj A] (n : ℕ) : A ⟶ A :=
  ((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ n).hom.hom

/-- Multiplication-by-`n` is a homomorphism of group objects. -/
noncomputable instance multiplicationBy_isMonHom (n : ℕ) :
    IsMonHom (multiplicationBy A n) := by
  exact ((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ n).hom.isMonHom_hom

/-- On every generalized point, multiplication-by-`n` is the `n`-fold sum. -/
@[simp]
theorem comp_multiplicationBy {X : Over (Spec (.of K))}
    (a : X ⟶ A) (n : ℕ) :
    a ≫ multiplicationBy A n = a ^ n := by
  dsimp [multiplicationBy]
  have hp := CategoryTheory.Grp.Hom.hom_pow
    (𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) n
  have hp' := congrArg (fun q => q.hom) hp
  rw [hp']
  simpa using (CategoryTheory.MonObj.comp_pow (𝟙 A : A ⟶ A) n a)

/- The powers used to define multiplication-by-`n` inherit the expected
   additive and compositional laws.  Keeping these laws at the categorical
   level avoids choosing coordinates on the group scheme. -/
@[simp]
theorem multiplicationBy_zero :
    multiplicationBy A 0 = (toUnit A ≫ η[A]) := by
  change ((1 : Grp.mk A ⟶ Grp.mk A).hom.hom) = _
  rw [CategoryTheory.Grp.Hom.hom_one]
  rfl

@[simp]
theorem multiplicationBy_one :
    multiplicationBy A 1 = 𝟙 A := by
  change (((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ 1).hom.hom) = _
  simp

theorem multiplicationBy_add (m n : ℕ) :
    multiplicationBy A (m + n) =
      multiplicationBy A m * multiplicationBy A n := by
  change ((((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ (m + n)).hom.hom)) =
    ((((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ m).hom.hom) *
      (((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ n).hom.hom))
  have hp := congrArg (fun q : Grp.mk A ⟶ Grp.mk A => q.hom.hom)
    (pow_add (𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) m n)
  exact hp

theorem multiplicationBy_comp (m n : ℕ) :
    multiplicationBy A m ≫ multiplicationBy A n =
      multiplicationBy A (m * n) := by
  rw [comp_multiplicationBy]
  let q : Grp.mk A ⟶ Grp.mk A :=
    (𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ m
  have hp := CategoryTheory.Grp.Hom.hom_pow q n
  have hp' := congrArg
    (fun r : (Grp.toMon (Grp.mk A) ⟶ Grp.toMon (Grp.mk A)) => r.hom) hp
  change ((((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ m).hom.hom) ^ n) =
    (((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ (m * n)).hom.hom)
  calc
    ((((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ m).hom.hom) ^ n) =
        (q.hom ^ n).hom := by simp [q]
    _ = (q ^ n).hom.hom := hp'.symm
    _ = (((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ (m * n)).hom.hom) := by
      simpa [q] using (congrArg (fun r : Grp.mk A ⟶ Grp.mk A => r.hom.hom)
        (pow_mul (𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) m n)).symm

/-- Every homomorphism of commutative group schemes commutes with
    multiplication-by-`n`. -/
theorem multiplicationBy_naturality
    {B : Over (Spec (.of K))} [GrpObj B] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    f ≫ multiplicationBy B n = multiplicationBy A n ≫ f := by
  rw [comp_multiplicationBy]
  change f ^ n =
    (((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ n).hom.hom) ≫ f
  have h := MonObj.pow_comp (𝟙 A : A ⟶ A) n f
  simpa [multiplicationBy] using h.symm

/-- The `n`-torsion group scheme, as the kernel fibre of multiplication-by-`n`.
-/
noncomputable def nTorsion (A : Over (Spec (.of K)))
    [GrpObj A] [IsCommMonObj A] (n : ℕ) : Scheme :=
  isogenyKernel (multiplicationBy A n)

/-- The structure morphism of the `n`-torsion group scheme over the base. -/
noncomputable def nTorsionToBase (A : Over (Spec (.of K)))
    [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    nTorsion A n ⟶ Spec (.of K) :=
  isogenyKernelToBase (multiplicationBy A n)

@[simp]
theorem nTorsion_eq_isogenyKernel (n : ℕ) :
    nTorsion A n = isogenyKernel (multiplicationBy A n) := rfl

@[simp]
theorem nTorsion_zero :
    nTorsion A 0 = isogenyKernel (toUnit A ≫ η[A]) := by
  rw [nTorsion_eq_isogenyKernel, multiplicationBy_zero]

@[simp]
theorem nTorsion_one :
    nTorsion A 1 = isogenyKernel (𝟙 A) := by
  rw [nTorsion_eq_isogenyKernel, multiplicationBy_one]

@[simp]
theorem nTorsionToBase_eq_isogenyKernelToBase (n : ℕ) :
    nTorsionToBase A n = isogenyKernelToBase (multiplicationBy A n) := rfl

@[simp]
theorem nTorsionToBase_isFinite_one :
    IsFinite (nTorsionToBase A 1) := by
  change IsFinite (isogenyKernelToBase (multiplicationBy A 1))
  rw [multiplicationBy_one]
  exact (Isogeny.id A).2

/-- A finite multiplication map has a finite `n`-torsion kernel. -/
theorem nTorsionToBase_isFinite_of_finite (n : ℕ)
    [IsFinite (multiplicationBy A n).left] :
    IsFinite (nTorsionToBase A n) := by
  exact isogenyKernelToBase_isFinite_of_finite (multiplicationBy A n)

/-- A finite multiplication map is an isogeny exactly when it is surjective. -/
theorem multiplicationBy_isogeny_iff_of_finite (n : ℕ)
    [IsFinite (multiplicationBy A n).left] :
    Isogeny (multiplicationBy A n) ↔
      Surjective (multiplicationBy A n).left := by
  exact Isogeny.iff_surjective_of_finite (multiplicationBy A n)

end MilneLib
