/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngine4BaseChange
import AlgebraicJacobian.RiemannRoch.ThetaSectionsIso

/-!
# DD-4 (Task 2) — the relative theta twist sheaf and its on-the-nose `H⁰` base change

The relative half of the W6-lite transport seam of the DAT-D campaign
(`informal/dat-d-worksheet.md` §2.1). The field-level bridge `Θⁿ ≅ 𝒪(n·F)`
(`RiemannRoch/ThetaSections*`) is now instantiated on the **pinned relative cover** of the
relative curve `C_R`, and the rigid engine's on-the-nose `H⁰` base-change clause
(`RigidEngine4BaseChange.relTwistH0BaseChange`) is fired at the fiber-twist cocycle.

* `AlgebraicGeometry.relThetaCocycle` — the fiber-twist unit cocycle `t₀ⁿ = (thetaUnit π)ⁿ`
  pulled back to the base-changed two-cover of `relCurve C R`
  (`relUnitCocycle` of the field-level `thetaUnit π ^ n`).
* `AlgebraicGeometry.relThetaTwistSheaf` — **the relative `𝒪(Θⁿ)`**: the cocycle-glued
  twisted sheaf `relTwistSheaf C R (fiberTwoCover π) (relThetaCocycle …)`, a sheaf of
  `R`-modules on `relCurve C R`.
* `AlgebraicGeometry.relThetaCocycle_baseChange` — **cocycle functoriality**: the
  fiber-twist cocycle base-changes to itself,
  `relCocycleBaseChange (relThetaCocycle C k π n) = relThetaCocycle C R π n`
  (from `relSectionsMap_pullback`).
* `AlgebraicGeometry.relThetaTwistH0BaseChange` — **DD-4 (2), the on-the-nose base change**:
  `R ⊗[k] H⁰(C_k, Θⁿ) ≃ₗ[R] H⁰(C_R, Θⁿ)` for the pinned relative twist, the
  `relTwistH0BaseChange` clause specialised at base ring `k`, test ring `R`, and the
  fiber-twist cocycle, threaded onto `relThetaTwistSheaf C R π n` by the cocycle
  functoriality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

section RelTheta

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k) [IsFinite π] (n : ℕ)

/-- **The relative theta cocycle** `t₀ⁿ` on the pinned relative cover of `C_R`: the
field-level fiber-twist unit `thetaUnit π ^ n ∈ Γ(C.left, V₀ ⊓ V₁)ˣ` pulled back along the
first projection to a unit cocycle on the base-changed two-cover of `relCurve C R`. Its
overlap lives on `(fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁ = fiberChart₀ π ⊓ fiberChart₁ π`
where `thetaUnit π ^ n` is defined. -/
noncomputable def relThetaCocycle :
    Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
      (relCover C R (fiberTwoCover π)).V₁)ˣ :=
  relUnitCocycle C R (fiberTwoCover π) (thetaUnit π ^ n)

/-- **The relative `𝒪(Θⁿ)`** on `relCurve C R`: the cocycle-glued twisted sheaf of the
relative theta cocycle, a sheaf of `R`-modules — the engine-side spelling of the fiber
twist over the affine test ring `R`. -/
noncomputable def relThetaTwistSheaf :
    Sheaf (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
      (ModuleCat.{u} R) :=
  relTwistSheaf C R (fiberTwoCover π) (relThetaCocycle C R π n)

end RelTheta

section BaseChange

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k) [IsFinite π] (n : ℕ)

/-- **Cocycle functoriality**: the relative theta cocycle over the base field `k`
base-changes to the relative theta cocycle over `R`. This is `relSectionsMap_pullback`
(pullback of a curve section commutes with the relative-curve comparison map) packaged at
the `Units.map` level. -/
theorem relThetaCocycle_baseChange :
    relCocycleBaseChange C k R (fiberTwoCover π) (relThetaCocycle C k π n)
      = relThetaCocycle C R π n := by
  refine Units.ext ?_
  change relSectionsMap C k R (fiberChart₀ π ⊓ fiberChart₁ π)
      ((relUnitCocycle C k (fiberTwoCover π) (thetaUnit π ^ n)).val)
    = (relUnitCocycle C R (fiberTwoCover π) (thetaUnit π ^ n)).val
  change relSectionsMap C k R (fiberChart₀ π ⊓ fiberChart₁ π)
      (relPullbackSection C k (fiberChart₀ π ⊓ fiberChart₁ π)
        ((thetaUnit π ^ n : Γ(C.left, _)ˣ) : Γ(C.left, _)))
    = relPullbackSection C R (fiberChart₀ π ⊓ fiberChart₁ π)
        ((thetaUnit π ^ n : Γ(C.left, _)ˣ) : Γ(C.left, _))
  exact relSectionsMap_pullback C k R (fiberChart₀ π ⊓ fiberChart₁ π) _

/-- **DD-4 (2), the on-the-nose base change** (`informal/dat-d-worksheet.md` §2.1, mirror
of `RigidEngine4BaseChange.relTwistH0BaseChange`): on the `H¹`-vanishing locus, the
degree-zero cohomology of the relative theta twist commutes with base change from the base
field `k` to the affine test ring `R`,

`R ⊗[k] H⁰(C_k, Θⁿ) ≃ₗ[R] H⁰(C_R, Θⁿ)`.

The right-hand side is `H⁰(relThetaTwistSheaf C R π n)`, obtained from the engine's
`relCocycleBaseChange` output by the cocycle functoriality `relThetaCocycle_baseChange`. -/
noncomputable def relThetaTwistH0BaseChange
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π n)).H1) :
    R ⊗[k] Sheaf.HModule (relThetaTwistSheaf C k π n) 0 ≃ₗ[R]
      Sheaf.HModule (relThetaTwistSheaf C R π n) 0 :=
  (relTwistH0BaseChange C k R π (relThetaCocycle C k π n) hH1).trans
    (Sheaf.HModule.mapEquiv
      (eqToIso (congrArg (relTwistSheaf C R (fiberTwoCover π))
        (relThetaCocycle_baseChange C R π n))) 0)

end BaseChange

end AlgebraicGeometry
