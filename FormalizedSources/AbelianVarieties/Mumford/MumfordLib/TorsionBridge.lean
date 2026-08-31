/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import Mathlib.Algebra.Module.Torsion.Basic
import MumfordLib.Uniformization

/-!
# Compatibility with Mathlib's torsion subgroup

`zsmulTorsionSubgroup` is the signed-integer torsion API used by the
uniformization development.  This file identifies it with Mathlib's
`AddSubgroup.torsionBy`, allowing results about the latter (including its
`ZMod n` module structure) to be reused without additional assumptions.
-/

namespace Mumford.Uniformization

@[simp]
theorem zsmulTorsionSubgroup_eq_torsionBy {X : Type*} [AddCommGroup X] (n : ℤ) :
    zsmulTorsionSubgroup X n = AddSubgroup.torsionBy X n := by
  ext x
  rfl

theorem mem_zsmulTorsionSubgroup_iff_torsionBy {X : Type*} [AddCommGroup X]
    (n : ℤ) (x : X) :
    x ∈ zsmulTorsionSubgroup X n ↔ x ∈ AddSubgroup.torsionBy X n := by
  rw [zsmulTorsionSubgroup_eq_torsionBy]

@[simp]
theorem natCast_zsmulTorsionSubgroup_eq_torsionBy {X : Type*} [AddCommGroup X]
    (n : ℕ) :
    zsmulTorsionSubgroup X (n : ℤ) = AddSubgroup.torsionBy X n := by
  exact zsmulTorsionSubgroup_eq_torsionBy (X := X) n

/- The standard `ZMod n`-module structure on Mathlib's torsion subgroup is
   available on the signed-integer presentation as well. -/
noncomputable instance zsmulTorsionSubgroup_zmodModule
    (X : Type*) [AddCommGroup X] (n : ℕ) :
    Module (ZMod n) (zsmulTorsionSubgroup X (n : ℤ)) :=
  AddSubgroup.torsionBy.zmodModule

theorem natCast_zsmulTorsionSubgroup_nsmul
    {X : Type*} [AddCommGroup X] {n : ℕ}
    (x : zsmulTorsionSubgroup X (n : ℤ)) :
    n • x = 0 := by
  apply Subtype.ext
  change n • (x : X) = 0
  have hx : (n : ℤ) • (x : X) = 0 := x.property
  exact_mod_cast hx

end Mumford.Uniformization
