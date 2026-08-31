/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowPencilTheta
import AlgebraicJacobian.RiemannRoch.PFibPack

/-!
# Cohomology bounds for the high-window pencil

For `B_n = N + nS - D`, a basepoint-free pair in `H^0(O(S))`
produces two translated divisors of degree `deg(B_n)`.  Their supremum is
`B_{n+1}`, so degree additivity for infimum and supremum puts their
intersection at degree

`deg(N) + (n - 1) deg(S) - deg(D)`.

The `P-fib` descent budget
`beta + 2g + deg(S) <= deg(N)` is exactly strong enough even when `n = 0`.
This file packages the five resulting `H^1` vanishings consumed by the
arbitrary-pair Koszul theorem.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.functionFieldOverModule

variable {K : Type u} [Field K]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- The uniform five-term `H^1` package for a basepoint-free pair at every
high window.  The worst divisor is the pair intersection at `n = 0`, whose
degree is `deg(N) - deg(S) - g`; the stated descent budget still places it
above `beta`. -/
theorem highWindow_pencil_h1
    (g : ℕ) (N S D : X.CurveDivisor) (β : ℤ)
    (hvan : ∀ W : X.CurveDivisor, β ≤ CurveDivisor.deg K W →
      Subsingleton (Sheaf.HModule (X.divisorSheaf K W) 1))
    (hSdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K S)
    (hβN : β + 2 * (g : ℤ) + CurveDivisor.deg K S ≤ CurveDivisor.deg K N)
    (hDdeg : CurveDivisor.deg K D = (g : ℤ)) (n : ℕ)
    (v0 v1 : X.functionFieldˣ)
    (hbpf : (S + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0) ⊓
        (S + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1) = 0) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K (N + n • S - D)) 1) ∧
      Subsingleton (Sheaf.HModule (X.divisorSheaf K
        ((N + n • S - D) - Scheme.divOf
          (X ↘ Spec (CommRingCat.of K)) v0)) 1) ∧
      Subsingleton (Sheaf.HModule (X.divisorSheaf K
        ((N + n • S - D) - Scheme.divOf
          (X ↘ Spec (CommRingCat.of K)) v1)) 1) ∧
      Subsingleton (Sheaf.HModule (X.divisorSheaf K
        (((N + n • S - D) - Scheme.divOf
            (X ↘ Spec (CommRingCat.of K)) v0) ⊓
          ((N + n • S - D) - Scheme.divOf
            (X ↘ Spec (CommRingCat.of K)) v1))) 1) ∧
      Subsingleton (Sheaf.HModule (X.divisorSheaf K
        (((N + n • S - D) - Scheme.divOf
            (X ↘ Spec (CommRingCat.of K)) v0) ⊔
          ((N + n • S - D) - Scheme.divOf
            (X ↘ Spec (CommRingCat.of K)) v1))) 1) := by
  have hS0 : 0 ≤ CurveDivisor.deg K S := by omega
  have hnS : 0 ≤ (n : ℤ) * CurveDivisor.deg K S :=
    mul_nonneg (Int.natCast_nonneg _) hS0
  have hNn : CurveDivisor.deg K (N + n • S) =
      CurveDivisor.deg K N + (n : ℤ) * CurveDivisor.deg K S := by
    rw [CurveDivisor.deg_add, Scheme.CurveDivisor.deg_nsmul']
  have hBdeg : CurveDivisor.deg K (N + n • S - D) =
      CurveDivisor.deg K N + (n : ℤ) * CurveDivisor.deg K S -
        CurveDivisor.deg K D := by
    rw [Scheme.CurveDivisor.deg_sub', hNn]
  have hBβ : β ≤ CurveDivisor.deg K (N + n • S - D) := by
    rw [hBdeg]
    omega
  have hv0deg : CurveDivisor.deg K
      ((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0) =
        CurveDivisor.deg K (N + n • S - D) := by
    rw [Scheme.CurveDivisor.deg_sub', deg_divOf, sub_zero]
  have hv1deg : CurveDivisor.deg K
      ((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1) =
        CurveDivisor.deg K (N + n • S - D) := by
    rw [Scheme.CurveDivisor.deg_sub', deg_divOf, sub_zero]
  have hv0β : β ≤ CurveDivisor.deg K
      ((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0) := by
    rw [hv0deg]
    exact hBβ
  have hv1β : β ≤ CurveDivisor.deg K
      ((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1) := by
    rw [hv1deg]
    exact hBβ
  have hA : N + (n + 1) • S - D = (N + n • S - D) + S := by
    rw [add_nsmul, one_nsmul]
    abel
  have hlat := divisor_pencil_lattice_of_basepointFree
    (A := N + (n + 1) • S - D) (B := N + n • S - D) S v0 v1 hA hbpf
  have hInfdeg : CurveDivisor.deg K
      (((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0) ⊓
        ((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1)) =
      CurveDivisor.deg K N + ((n : ℤ) - 1) * CurveDivisor.deg K S -
        CurveDivisor.deg K D := by
    have hbal := Scheme.CurveDivisor.deg_inf_add_deg_sup K
      ((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0)
      ((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1)
    rw [hlat.1, hv0deg, hv1deg, hBdeg] at hbal
    have hAdeg : CurveDivisor.deg K (N + (n + 1) • S - D) =
        CurveDivisor.deg K N + ((n + 1 : ℕ) : ℤ) * CurveDivisor.deg K S -
          CurveDivisor.deg K D := by
      rw [Scheme.CurveDivisor.deg_sub', CurveDivisor.deg_add,
        Scheme.CurveDivisor.deg_nsmul']
    rw [hAdeg] at hbal
    push_cast at hbal ⊢
    linarith
  have hInfβ : β ≤ CurveDivisor.deg K
      (((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0) ⊓
        ((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1)) := by
    rw [hInfdeg]
    have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
    nlinarith [hβN, hDdeg, hnS]
  have hSupβ : β ≤ CurveDivisor.deg K
      (((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0) ⊔
        ((N + n • S - D) - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1)) := by
    rw [hlat.1]
    have hAdeg : CurveDivisor.deg K (N + (n + 1) • S - D) =
        CurveDivisor.deg K N + ((n + 1 : ℕ) : ℤ) * CurveDivisor.deg K S -
          CurveDivisor.deg K D := by
      rw [Scheme.CurveDivisor.deg_sub', CurveDivisor.deg_add,
        Scheme.CurveDivisor.deg_nsmul']
    rw [hAdeg]
    have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
    nlinarith [hβN, hDdeg, hnS, hS0]
  exact ⟨hvan _ hBβ, hvan _ hv0β, hvan _ hv1β,
    hvan _ hInfβ, hvan _ hSupβ⟩

end AlgebraicGeometry
