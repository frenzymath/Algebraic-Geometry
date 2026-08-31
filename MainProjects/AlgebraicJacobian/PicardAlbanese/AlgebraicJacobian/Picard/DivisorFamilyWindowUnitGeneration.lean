/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivisorFamilyThetaSections
import AlgebraicJacobian.Picard.DivisorFamilyWindow
import AlgebraicJacobian.Picard.DivSchemeFamilySide

/-!
# Unit generation by a finite theta-window basis

The two canonical relative theta sections `(t₀ᵃ, 1)` and `(1, t₁ᵃ)` have a unit
component on the second and first pinned charts respectively.  Pulling either section
back through `relThetaWindowEquiv` and expanding it in a base-changed finite basis shows
that the corresponding chart readings of that basis generate `1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

section Basis

variable {k R M B : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [CommRing B] [Algebra R B]
variable [Fintype ι]

/-- If an `R`-linear map out of `R ⊗[k] M` takes some element to `1`, then the
images of the scalar extensions of a finite `k`-basis of `M` generate `1` in `B`. -/
theorem exists_basis_baseChange_mul_eq_one (basis : Module.Basis ι k M)
    (f : R ⊗[k] M →ₗ[R] B) (x : R ⊗[k] M) (hx : f x = 1) :
    ∃ c : ι → B, ∑ t, c t * f (1 ⊗ₜ basis t) = 1 := by
  classical
  let basisR := basis.baseChange R
  refine ⟨fun t => (basisR.repr x t) • 1, ?_⟩
  calc
    ∑ t, ((basisR.repr x t) • 1) * f (1 ⊗ₜ basis t) =
        ∑ t, (basisR.repr x t) • f (basisR t) := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [basisR, Module.Basis.baseChange_apply, Algebra.smul_def, mul_one]
    _ = f (∑ t, (basisR.repr x t) • basisR t) := by
      rw [map_sum]
      simp only [map_smul]
    _ = f x := by rw [basisR.sum_repr]
    _ = 1 := hx

end Basis

section ThetaWindow

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftWindowUnit : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable (a : ℕ)

/-- The window equivalence followed by the pinned-chart component reading. -/
noncomputable def relThetaWindowChartRead
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (b : Bool) :
    R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤) →ₗ[R]
      Γ(relCurve C R, relPinnedChart C R π b) :=
  (relThetaResSide a b le_rfl).comp (relThetaWindowEquiv C R π a hH1).toLinearMap

/-- The readings of any finite basis of a theta window generate `1` on either pinned
chart after scalar extension. -/
theorem exists_basis_relThetaWindowChartRead_mul_eq_one {ι : Type v} [Fintype ι]
    (basis : Module.Basis ι k
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (b : Bool) :
    ∃ c : ι → Γ(relCurve C R, relPinnedChart C R π b),
      ∑ t, c t * relThetaWindowChartRead C R π a hH1 b (1 ⊗ₜ basis t) = 1 := by
  cases b
  · apply exists_basis_baseChange_mul_eq_one basis
      (relThetaWindowChartRead C R π a hH1 false)
      ((relThetaWindowEquiv C R π a hH1).symm (relThetaSectionSnd C R π a))
    change relThetaResFst a (le_inf le_top le_rfl)
      ((relThetaWindowEquiv C R π a hH1)
        ((relThetaWindowEquiv C R π a hH1).symm (relThetaSectionSnd C R π a))) = 1
    rw [LinearEquiv.apply_symm_apply]
    exact relThetaResFst_relThetaSectionSnd C R π a
  · apply exists_basis_baseChange_mul_eq_one basis
      (relThetaWindowChartRead C R π a hH1 true)
      ((relThetaWindowEquiv C R π a hH1).symm (relThetaSectionFst C R π a))
    change relThetaResSnd a (le_inf le_top le_rfl)
      ((relThetaWindowEquiv C R π a hH1)
        ((relThetaWindowEquiv C R π a hH1).symm (relThetaSectionFst C R π a))) = 1
    rw [LinearEquiv.apply_symm_apply]
    exact relThetaResSnd_relThetaSectionFst C R π a

end ThetaWindow

end AlgebraicGeometry
