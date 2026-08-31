/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1Topology
import Mathlib.Topology.Irreducible

/-!
# Hartshorne I.1: affine varieties

An affine variety is an irreducible algebraic set.  The topology and the
irreducibility predicate are supplied by Mathlib; this file records the
source-facing conjunction and its closed-set form.
-/

namespace Hartshorne

noncomputable section

section AffineVariety

variable (k : Type*) [Field k] (n : Nat)

/-- An affine algebraic variety is an irreducible algebraic subset of affine space. -/
def IsAffineVariety (Y : Set (AffinePoint k n)) : Prop :=
  IsAlgebraicSet k n Y ∧ IsIrreducible Y

theorem isAffineVariety_iff (Y : Set (AffinePoint k n)) :
    IsAffineVariety k n Y ↔ IsAlgebraicSet k n Y ∧ IsIrreducible Y := Iff.rfl

theorem IsAffineVariety.isAlgebraicSet {Y : Set (AffinePoint k n)}
    (hY : IsAffineVariety k n Y) : IsAlgebraicSet k n Y :=
  hY.1

theorem IsAffineVariety.isIrreducible {Y : Set (AffinePoint k n)}
    (hY : IsAffineVariety k n Y) : IsIrreducible Y :=
  hY.2

theorem IsAffineVariety.nonempty {Y : Set (AffinePoint k n)}
    (hY : IsAffineVariety k n Y) : Y.Nonempty :=
  hY.2.nonempty

theorem isAffineVariety_iff_isClosed_and_isIrreducible (Y : Set (AffinePoint k n)) :
    IsAffineVariety k n Y ↔ IsClosed Y ∧ IsIrreducible Y := by
  constructor
  · rintro ⟨hY, hI⟩
    exact ⟨(isClosed_iff_isAlgebraicSet k n Y).2 hY, hI⟩
  · rintro ⟨hY, hI⟩
    exact ⟨(isClosed_iff_isAlgebraicSet k n Y).1 hY, hI⟩

theorem isClosed_of_isAffineVariety {Y : Set (AffinePoint k n)}
    (hY : IsAffineVariety k n Y) : IsClosed Y :=
  (isClosed_iff_isAlgebraicSet k n Y).2 hY.isAlgebraicSet

theorem not_isAffineVariety_empty :
    ¬ IsAffineVariety k n (∅ : Set (AffinePoint k n)) := by
  intro hY
  simpa using hY.nonempty

end AffineVariety

end

end Hartshorne
