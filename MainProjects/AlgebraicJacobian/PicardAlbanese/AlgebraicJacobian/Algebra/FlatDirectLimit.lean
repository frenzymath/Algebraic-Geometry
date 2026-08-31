/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import Mathlib.Algebra.Colimit.Module
import Mathlib.Data.Finset.Order
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Flatness of directed limits

A directed limit of flat modules is flat.  This is the algebraic colimit step needed by
arguments that present an affine chart quotient as the limit of projective bounded-degree
quotients.  The geometric presentation and flatness of those bounded stages are separate
hypotheses; this file only supplies the general module-theoretic passage to the limit.
-/

set_option autoImplicit false

universe u v w

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {ι : Type v} [DecidableEq ι] [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable {G : ι → Type w}
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable [DirectedSystem G (f · · ·)]

/-- A directed limit of flat modules is flat. -/
theorem directLimit [∀ i, Module.Flat R (G i)] :
    Module.Flat R (Module.DirectLimit G f) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l c x hrel
  classical
  choose stage value hvalue using fun i =>
    Module.DirectLimit.exists_of (R := R) (G := G) (f := f) (x i)
  obtain ⟨common, hcommon⟩ := Finset.exists_le (Finset.univ.image stage)
  have hstage (i : Fin l) : stage i ≤ common :=
    hcommon (stage i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let y : Fin l → G common := fun i => f (stage i) common (hstage i) (value i)
  have hy (i : Fin l) :
      Module.DirectLimit.of R ι G f common (y i) = x i := by
    rw [show y i = f (stage i) common (hstage i) (value i) by rfl,
      Module.DirectLimit.of_f, hvalue i]
  have hcommonRel :
      Module.DirectLimit.of R ι G f common (∑ i, c i • y i) = 0 := by
    rw [map_sum]
    simp_rw [map_smul, hy]
    exact hrel
  obtain ⟨later, hlater, hlaterRel⟩ :=
    Module.DirectLimit.of.zero_exact (f := f) hcommonRel
  let z : Fin l → G later := fun i => f common later hlater (y i)
  have hzrel : ∑ i, c i • z i = 0 := by
    rw [show (∑ i, c i • z i) =
        f common later hlater (∑ i, c i • y i) by
      simp only [map_sum, map_smul, z]]
    exact hlaterRel
  obtain ⟨k, a, w, hw, ha⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hzrel
  refine ⟨k, a, fun j => Module.DirectLimit.of R ι G f later (w j), ?_, ha⟩
  intro i
  rw [← hy i, ← Module.DirectLimit.of_f (hij := hlater)]
  change Module.DirectLimit.of R ι G f later (z i) = _
  rw [hw i, map_sum]
  simp only [map_smul]

end Module.Flat
