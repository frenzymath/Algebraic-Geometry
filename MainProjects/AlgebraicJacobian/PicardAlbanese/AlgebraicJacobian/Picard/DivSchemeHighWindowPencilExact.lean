/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowPencilVanishing

/-!
# Exact multiplication relations in every high window

This file assembles the field-level high-window theorem.  For

`B_n = N + nS - D`, `A_n = N + (n+1)S - D`,

the canonical finite Koszul boundary from `B_n` presents the complete kernel
of the multiplication map into `A_n`, provided `H^0(O(S))` contains a
basepoint-free pair and the `P-fib` descent budget holds.
-/

set_option autoImplicit false

universe u v

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
variable {ι : Type v} [Fintype ι]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- Multiplication by a section of `S` sends the `n`-th divisor window into
the next one. -/
theorem Scheme.mul_mem_divisorSections_highWindow
    (N S D : X.CurveDivisor) (n : ℕ)
    (a : divisorSections K S ⊤) (z : divisorSections K (N + n • S - D) ⊤) :
    (a : X.functionField) * (z : X.functionField) ∈
      divisorSections K (N + (n + 1) • S - D) ⊤ := by
  have hmul := mul_mem_divisorSections_top K a.property z.property
  convert hmul using 1
  rw [add_nsmul, one_nsmul]
  abel_nf

/-- The canonical finite Koszul boundary between consecutive high windows. -/
noncomputable def Scheme.highWindowMulKoszulBoundary
    (N S D : X.CurveDivisor) (n : ℕ)
    (b : Module.Basis ι K ↑(divisorSections K S ⊤)) :
    (ι × ι → ↑(divisorSections K (N + n • S - D) ⊤)) →ₗ[K]
      (ι → ↑(divisorSections K (N + (n + 1) • S - D) ⊤)) :=
  Scheme.finiteMulKoszulBoundary
    (divisorSections K S ⊤)
    (divisorSections K (N + n • S - D) ⊤)
    (divisorSections K (N + (n + 1) • S - D) ⊤) b
    (fun i z => Scheme.mul_mem_divisorSections_highWindow N S D n (b i) z)

/-- A basepoint-free pair in the multiplier window gives the complete
field-level relation theorem at every high-window stage. -/
theorem Scheme.ker_finiteMulMap_eq_range_highWindowMulKoszulBoundary_of_pair
    (g : ℕ) (N S D : X.CurveDivisor) (β : ℤ)
    (hvan : ∀ W : X.CurveDivisor, β ≤ CurveDivisor.deg K W →
      Subsingleton (Sheaf.HModule (X.divisorSheaf K W) 1))
    (hSdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K S)
    (hβN : β + 2 * (g : ℤ) + CurveDivisor.deg K S ≤ CurveDivisor.deg K N)
    (hDdeg : CurveDivisor.deg K D = (g : ℤ)) (n : ℕ)
    (b : Module.Basis ι K ↑(divisorSections K S ⊤))
    (v0 v1 : X.functionFieldˣ)
    (hv0 : (v0 : X.functionField) ∈ divisorSections K S ⊤)
    (hv1 : (v1 : X.functionField) ∈ divisorSections K S ⊤)
    (hbpf : (S + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0) ⊓
      (S + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1) = 0) :
    LinearMap.ker
        (Scheme.finiteMulMap (divisorSections K S ⊤)
          (divisorSections K (N + (n + 1) • S - D) ⊤) b) =
      LinearMap.range (Scheme.highWindowMulKoszulBoundary N S D n b) := by
  have hA : N + (n + 1) • S - D = (N + n • S - D) + S := by
    rw [add_nsmul, one_nsmul]
    abel_nf
  have hlat := divisor_pencil_lattice_of_basepointFree
    (A := N + (n + 1) • S - D) (B := N + n • S - D) S v0 v1 hA hbpf
  have hH := highWindow_pencil_h1 g N S D β hvan hSdeg hβN hDdeg n v0 v1 hbpf
  have hexact :=
    Scheme.ker_finiteMulMap_eq_range_finiteMulKoszulBoundary_of_divisor_pair
      (divisorSections K S ⊤) b
      (N + (n + 1) • S - D) (N + n • S - D) v0 v1 hv0 hv1
      (fun i z => Scheme.mul_mem_divisorSections_highWindow N S D n (b i) z)
      hlat.1 hlat.2 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2
  simpa only [Scheme.highWindowMulKoszulBoundary] using hexact

end AlgebraicGeometry
