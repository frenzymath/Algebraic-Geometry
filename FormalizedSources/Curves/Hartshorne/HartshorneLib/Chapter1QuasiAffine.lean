/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1Variety

/-!
# Hartshorne I.1: quasi-affine varieties

An open subset of an affine variety carries the induced topology.  The subtype
preimage in the definition below makes that relative-topology requirement
explicit while retaining the source-facing ambient subset `Y`.
-/

namespace Hartshorne

noncomputable section

section QuasiAffine

variable (k : Type*) [Field k] (n : Nat)

/-- A quasi-affine variety is an open subset of an affine variety. -/
def IsQuasiAffineVariety (Y : Set (AffinePoint k n)) : Prop :=
  ∃ X : Set (AffinePoint k n),
    IsAffineVariety k n X ∧ Y ⊆ X ∧
      IsOpen ((fun p : X => (p : AffinePoint k n)) ⁻¹' Y)

theorem isQuasiAffineVariety_iff (Y : Set (AffinePoint k n)) :
    IsQuasiAffineVariety k n Y ↔
      ∃ X : Set (AffinePoint k n),
        IsAffineVariety k n X ∧ Y ⊆ X ∧
          IsOpen ((fun p : X => (p : AffinePoint k n)) ⁻¹' Y) := Iff.rfl

/-- Every affine variety is quasi-affine via the whole-subset presentation. -/
theorem IsAffineVariety.isQuasiAffineVariety
    {X : Set (AffinePoint k n)} (hX : IsAffineVariety k n X) :
    IsQuasiAffineVariety k n X := by
  refine ⟨X, hX, subset_rfl, ?_⟩
  rw [Subtype.coe_preimage_self X]
  exact isOpen_univ

/-- An ambient open subset of an affine variety is quasi-affine. -/
theorem isQuasiAffineVariety_of_isOpen
    {X Y : Set (AffinePoint k n)} (hX : IsAffineVariety k n X)
    (hYX : Y ⊆ X) (hY : IsOpen Y) :
    IsQuasiAffineVariety k n Y := by
  refine ⟨X, hX, hYX, ?_⟩
  exact hY.preimage continuous_subtype_val

end QuasiAffine

end

end Hartshorne
