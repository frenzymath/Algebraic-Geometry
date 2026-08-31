/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Algebra.FlatDirectLimit
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Directed limits of increasing quotients

For a directed monotone family of submodules `N i ⊆ M`, the transition maps
`M / N i → M / N j` make the quotients into a directed system, and its direct limit is
canonically `M / ⨆ i, N i`.

This is the algebraic colimit interface used by bounded-window presentations: the geometric
work is reduced to identifying the bounded relations `N i`, proving their monotonicity, and
showing that their supremum is the full relation submodule.
-/

set_option autoImplicit false

universe u v w

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type w} [Preorder ι]

/-- The quotient map induced by an inclusion in a monotone family of submodules. -/
noncomputable def directedQuotientMap (N : ι → Submodule R M) (hN : Monotone N)
    (i j : ι) (hij : i ≤ j) : (M ⧸ N i) →ₗ[R] (M ⧸ N j) :=
  (N i).mapQ (N j) LinearMap.id (by simpa using hN hij)

@[simp]
theorem directedQuotientMap_mk (N : ι → Submodule R M) (hN : Monotone N)
    (i j : ι) (hij : i ≤ j) (x : M) :
    directedQuotientMap N hN i j hij (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  rw [directedQuotientMap, Submodule.mapQ_apply, LinearMap.id_apply]

noncomputable instance directedSystem_directedQuotientMap
    (N : ι → Submodule R M) (hN : Monotone N) :
    DirectedSystem (fun i ↦ M ⧸ N i) (directedQuotientMap N hN · · ·) where
  map_self _ x := by
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact directedQuotientMap_mk N hN _ _ _ x
  map_map _ _ _ hij hjk x := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [directedQuotientMap_mk, directedQuotientMap_mk,
        directedQuotientMap_mk]

section Directed

variable [DecidableEq ι] [Nonempty ι] [IsDirectedOrder ι]

/-- The quotient map from one bounded stage to the quotient by the supremum. -/
noncomputable def directedQuotientMapToISup (N : ι → Submodule R M) (i : ι) :
    (M ⧸ N i) →ₗ[R] M ⧸ (⨆ j, N j) :=
  (N i).mapQ (⨆ j, N j) LinearMap.id (by simpa using le_iSup N i)

omit [Preorder ι] [DecidableEq ι] [Nonempty ι] [IsDirectedOrder ι] in
@[simp]
theorem directedQuotientMapToISup_mk (N : ι → Submodule R M) (i : ι) (x : M) :
    directedQuotientMapToISup N i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  rw [directedQuotientMapToISup, Submodule.mapQ_apply, LinearMap.id_apply]

/-- The canonical map from the direct limit of the increasing quotients to the quotient by
their supremum. -/
noncomputable def directLimitQuotientToISup (N : ι → Submodule R M) (hN : Monotone N) :
    Module.DirectLimit (fun i ↦ M ⧸ N i) (directedQuotientMap N hN) →ₗ[R]
      M ⧸ (⨆ i, N i) :=
  Module.DirectLimit.lift R ι _ _
    (directedQuotientMapToISup N)
    (fun i j hij x ↦ by
      induction x using Submodule.Quotient.induction_on with
      | _ x => rw [directedQuotientMap_mk, directedQuotientMapToISup_mk,
          directedQuotientMapToISup_mk])

omit [Nonempty ι] [IsDirectedOrder ι] in
@[simp]
theorem directLimitQuotientToISup_of_mk (N : ι → Submodule R M) (hN : Monotone N)
    (i : ι) (x : M) :
    directLimitQuotientToISup N hN
        (Module.DirectLimit.of R ι _ (directedQuotientMap N hN) i
          (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x := by
  rw [directLimitQuotientToISup, Module.DirectLimit.lift_of,
    directedQuotientMapToISup_mk]

/-- The direct limit of quotients by a directed increasing family is the quotient by the
supremum of that family. -/
noncomputable def directLimitQuotientEquivISup
    (N : ι → Submodule R M) (hN : Monotone N) :
    Module.DirectLimit (fun i ↦ M ⧸ N i) (directedQuotientMap N hN) ≃ₗ[R]
      M ⧸ (⨆ i, N i) :=
  LinearEquiv.ofBijective (directLimitQuotientToISup N hN) ⟨by
    have hker : ∀ z, directLimitQuotientToISup N hN z = 0 → z = 0 := by
      intro z hz
      obtain ⟨i, y, hy⟩ := Module.DirectLimit.exists_of z
      obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (N i) y
      rw [← hy, ← hx] at hz ⊢
      simp only [Submodule.mkQ_apply] at hz ⊢
      rw [directLimitQuotientToISup_of_mk] at hz
      have hxSup : x ∈ ⨆ i, N i := (Submodule.Quotient.mk_eq_zero _).mp hz
      rw [Submodule.mem_iSup_of_directed N hN.directed_le] at hxSup
      obtain ⟨j, hxj⟩ := hxSup
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      rw [← Module.DirectLimit.of_f (hij := hik), directedQuotientMap_mk,
        (Submodule.Quotient.mk_eq_zero _).mpr (hN hjk hxj), map_zero]
    intro z w hzw
    apply sub_eq_zero.mp (hker (z - w) ?_)
    rw [map_sub, hzw, sub_self],
  by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (⨆ i, N i) y
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    exact ⟨Module.DirectLimit.of R ι _ (directedQuotientMap N hN) i
      (Submodule.Quotient.mk x), directLimitQuotientToISup_of_mk N hN i x⟩⟩

set_option linter.unusedSectionVars false in
@[simp]
theorem directLimitQuotientEquivISup_apply_of_mk
    (N : ι → Submodule R M) (hN : Monotone N) (i : ι) (x : M) :
    directLimitQuotientEquivISup N hN
        (Module.DirectLimit.of R ι _ (directedQuotientMap N hN) i
          (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x :=
  directLimitQuotientToISup_of_mk N hN i x

end Directed

section FlatDirected

variable [Nonempty ι] [IsDirectedOrder ι]

/-- If all bounded quotients are flat, then the quotient by the supremum of their
relations is flat. -/
theorem flat_quotient_iSup_of_monotone
    (N : ι → Submodule R M) (hN : Monotone N)
    [∀ i, Module.Flat R (M ⧸ N i)] :
    Module.Flat R (M ⧸ (⨆ i, N i)) := by
  classical
  letI : Module.Flat R
      (Module.DirectLimit (fun i ↦ M ⧸ N i) (directedQuotientMap N hN)) :=
    Module.Flat.directLimit (directedQuotientMap N hN)
  exact Module.Flat.of_linearEquiv (directLimitQuotientEquivISup N hN).symm

/-- A version of `flat_quotient_iSup_of_monotone` with the limiting relation submodule
identified separately. -/
theorem flat_quotient_of_iSup_eq
    (N : ι → Submodule R M) (hN : Monotone N)
    [∀ i, Module.Flat R (M ⧸ N i)] {P : Submodule R M}
    (hP : (⨆ i, N i) = P) : Module.Flat R (M ⧸ P) := by
  rw [← hP]
  exact flat_quotient_iSup_of_monotone N hN

end FlatDirected

end Submodule
