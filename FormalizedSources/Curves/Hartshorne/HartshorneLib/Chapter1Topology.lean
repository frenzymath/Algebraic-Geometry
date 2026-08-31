/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice

/-!
# Hartshorne I.1: the Zariski topology on affine space

The affine algebraic sets form the closed sets of a topology. The only
additional ingredient beyond the affine zero-set API is closure under arbitrary
intersections, obtained by taking the union of all defining polynomial families.
-/

namespace Hartshorne

noncomputable section

section AffineZariski

variable (k : Type*) [Field k] (n : Nat)

theorem commonZeroSet_iUnion {ι : Type*} (T : ι -> Set (AffinePolynomial k n)) :
    commonZeroSet k n (⋃ i, T i) = ⋂ i, commonZeroSet k n (T i) := by
  ext P
  simp only [commonZeroSet, Set.mem_iInter]
  constructor
  · intro hP i f hf
    exact hP f (Set.mem_iUnion.mpr ⟨i, hf⟩)
  · intro hP f hf
    rcases Set.mem_iUnion.mp hf with ⟨i, hfi⟩
    exact hP i f hfi

theorem isAlgebraicSet_sInter {ι : Type*} (Y : ι -> Set (AffinePoint k n))
    (hY : ∀ i, IsAlgebraicSet k n (Y i)) :
    IsAlgebraicSet k n (⋂ i, Y i) := by
  choose T hT using hY
  refine ⟨⋃ i, T i, ?_⟩
  rw [commonZeroSet_iUnion, show (⋂ i, commonZeroSet k n (T i)) = ⋂ i, Y i by
    congr 1
    funext i
    exact hT i]

/-- The Zariski topology whose closed sets are the affine algebraic sets. -/
@[reducible]
def affineZariskiTopology : TopologicalSpace (AffinePoint k n) :=
  TopologicalSpace.ofClosed
    {Y | IsAlgebraicSet k n Y}
    (isAlgebraicSet_empty k n)
    (by
      intro A hA
      change IsAlgebraicSet k n (⋂₀ A)
      have hAi : ∀ a : A, IsAlgebraicSet k n (a : Set (AffinePoint k n)) :=
        fun a => hA a.2
      simpa only [Set.sInter_eq_iInter] using
        (isAlgebraicSet_sInter k n (fun a : A => (a : Set (AffinePoint k n))) hAi))
    (by
      intro A hA B hB
      exact isAlgebraicSet_union k n hA hB)

/-- The affine Zariski topology is opt-in because `AffinePoint` is definitionally
the same function type as Mathlib's product topology. -/
scoped instance affineZariskiTopology_inst : TopologicalSpace (AffinePoint k n) :=
  affineZariskiTopology k n

theorem isClosed_iff_isAlgebraicSet (Y : Set (AffinePoint k n)) :
    IsClosed Y ↔ IsAlgebraicSet k n Y := by
  constructor
  · intro h
    have hopen : IsOpen (Yᶜ) := h.isOpen_compl
    change IsAlgebraicSet k n ((Yᶜ)ᶜ) at hopen
    simpa using hopen
  · intro h
    constructor
    change IsAlgebraicSet k n ((Yᶜ)ᶜ)
    simpa using h

theorem isClosed_zeroSet (f : AffinePolynomial k n) :
    IsClosed (zeroSet k n f) :=
  (isClosed_iff_isAlgebraicSet k n _).2 (isAlgebraicSet_zeroSet k n f)

theorem isClosed_commonZeroSet (T : Set (AffinePolynomial k n)) :
    IsClosed (commonZeroSet k n T) := by
  exact (isClosed_iff_isAlgebraicSet k n _).2 ⟨T, rfl⟩

end AffineZariski

end

end Hartshorne
