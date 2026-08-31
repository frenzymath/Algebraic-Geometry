/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.FLVClass
import AlgebraicJacobian.RiemannRoch.DegreeBaseFieldInvariance

/-!
# DAT-0b — Θ-positivity of the fiber twist

For the curve bundle `Y` (integral, smooth of relative dimension one, locally of finite type
and quasi-compact over a field `K`) carrying a **dominant** morphism `π : Y ⟶ ℙ¹`, the fiber
twist `Θ₁ = fiberTwist π 1` (`RiemannRoch/FiberTwist.lean`) has degree exactly the degree of
the fiber Weil divisor `F = fiberWeilDivisor π` (`RiemannRoch/FLVFiberToolkit.lean`):

`AlgebraicGeometry.classDeg_fiberTwist_one`:
`classDeg K (fiberTwist π 1) = CurveDivisor.deg K (fiberWeilDivisor π)`,

and, when `π` is moreover **finite** (hence surjective onto `ℙ¹`), this degree is strictly
positive:

`AlgebraicGeometry.one_le_classDeg_fiberTwist_one`:
`1 ≤ classDeg K (fiberTwist π 1)`.

This is the **Θ-positivity** pre-brick of the Wave-4 datum campaign
(`informal/w4-datum-worksheet.md` §2.4, §4 DAT-0b). It supplies FLV's `1 ≤ classDeg θ`
threshold at every fibre — note that `deg Θ₁ = deg π` is **not** load-bearing on this route
(worksheet §2.4); only positivity is needed.

## The route (worksheet §2.4, pinned chain)

`fiberTwist π 1` is `(fiberDivisor π 1).picClass`, the class of the pinned two-cover
local-equation system `(t₀ on V₀, 1 on V₁)`. Its meromorphic presentation
(`LocalEquations.presentation`) has trivializing element `t₀` on the chart `V₀` and the
constant `1` on `V₁`; the associated presentation divisor
(`Scheme.presentationDivisor`) reads off the orders of `t₀`, which by the fiber order table
is exactly the fiber Weil divisor `F = (div u)⁺`:

* `presentationDivisor_presentation_fiberDivisor_one`: the ord-of-`t₀` computation
  identifying the two divisors, point by point via `Scheme.CurveDivisor.ext_coeffAt`;
* `LocalEquations.presentation_picClass` + `CurveDivisor.picClass_presentationDivisor`
  transport this to a class identity `fiberTwist π 1 = 𝒪(F)`;
* E-i `classDeg_picClass` reads off `classDeg K (fiberTwist π 1) = deg F`;
* `zero_lt_deg_fiberWeilDivisor` (surjectivity of the finite dominant `π`) gives `0 < deg F`.

## The `k → K` fibre transport

For the challenge curve `C : Over (Spec k)`, the constant `1 ≤ classDeg` transports along any
base-field transition `φ : K₁ →ₐ[k] K₂` by E-iv-alg
(`classDeg_cechPicMap_baseFieldTransition`):
`AlgebraicGeometry.one_le_classDeg_cechPicMap_baseFieldTransition_of_one_le` — so FLV consumers
obtain `1 ≤ classDeg θ` over **every** field of the pack from the single base-field value.
-/

set_option autoImplicit false
/- Scheme-theoretic unification (mixing `P1 K` with `Proj 𝒜`, `Γ(Y, U)` with functor
applications) needs defeq checks through semireducible definitions, as in mathlib's own
algebraic-geometry files and the companion `FiberTwist`/`FLVFiberToolkit`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

/-! ## The presentation divisor of the fiber divisor -/

section Presentation

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (π : Y ⟶ P1 K) [IsDominant π]

/-- **The presentation divisor of the unit fiber divisor is the fiber Weil divisor.** The
trivializing element of the meromorphic presentation of `fiberDivisor π 1` is `t₀ = germ_η t₀`
on the chart `V₀` and the constant `1` on `V₁`; its order table is exactly that of the fiber
unit `u`, so the presentation divisor `∑ₓ ord_x (elem x) · x` equals the fiber Weil divisor
`F = (div u)⁺`. Point-by-point comparison through `Scheme.CurveDivisor.ext_coeffAt`. -/
theorem presentationDivisor_presentation_fiberDivisor_one :
    presentationDivisor K (fiberDivisor π 1).presentation = fiberWeilDivisor π := by
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  rw [coeffAt_presentationDivisor]
  by_cases h : x ∈ fiberChart₀ π
  · -- on `V₀` the trivializing element is the fiber unit `u = fiberCoordUnit π`
    have hunit : (fiberDivisor π 1).presentation.elem x = fiberCoordUnit π := by
      refine Units.ext ?_
      rw [Scheme.LocalEquations.presentation_elem_val, fiberCoordUnit_val]
      simp only [fiberDivisor_cover, fiberDivisor_eqn]
      rw [fiberEqn_of_mem π 1 h, Y.presheaf.germ_res_apply, pow_one]
    rw [hunit, ← CurveDivisor.coeffAt_divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π) hx,
      fiberWeilDivisor_coeffAt_of_mem_chart₀ π hx h]
  · -- off `V₀` (hence on `V₁`) the trivializing element is the constant `1`
    have hx1 : x ∈ fiberChart₁ π := by
      have hz : x ∈ fiberChart₀ π ⊔ fiberChart₁ π := by
        rw [preimage_chartOpen_sup]; trivial
      exact (TopologicalSpace.Opens.mem_sup.mp hz).resolve_left h
    have hunit : (fiberDivisor π 1).presentation.elem x = 1 := by
      refine Units.ext ?_
      rw [Scheme.LocalEquations.presentation_elem_val]
      simp only [fiberDivisor_cover, fiberDivisor_eqn]
      rw [fiberEqn_of_notMem π 1 h, map_one, Units.val_one]
    rw [hunit, fiberWeilDivisor_coeffAt_of_mem_chart₁ π hx hx1, map_one, toAdd_one]

end Presentation

/-! ## The degree of the fiber twist -/

section Degree

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
  (π : Y ⟶ P1 K) [IsDominant π]

omit [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)] in
/-- **The unit fiber twist is the class of the fiber Weil divisor**: `Θ₁ = 𝒪(F)`. From the
presentation-divisor identity `presentationDivisor_presentation_fiberDivisor_one` transported
to classes by `LocalEquations.presentation_picClass` and
`CurveDivisor.picClass_presentationDivisor`. -/
theorem fiberTwist_one_eq_picClass_fiberWeilDivisor :
    fiberTwist π 1 = CurveDivisor.picClass K (fiberWeilDivisor π) := by
  have h1 : fiberTwist π 1 = (fiberDivisor π 1).picClass := rfl
  rw [h1, ← Scheme.LocalEquations.presentation_picClass,
    ← CurveDivisor.picClass_presentationDivisor K,
    presentationDivisor_presentation_fiberDivisor_one π]

/-- **DAT-0b, degree form.** The degree of the unit fiber twist equals the degree of the fiber
Weil divisor: `classDeg K (fiberTwist π 1) = deg F`. E-i (`classDeg_picClass`) on the class
identity `Θ₁ = 𝒪(F)`. -/
theorem classDeg_fiberTwist_one :
    classDeg K (fiberTwist π 1) = CurveDivisor.deg K (fiberWeilDivisor π) := by
  rw [fiberTwist_one_eq_picClass_fiberWeilDivisor π, classDeg_picClass]

/-- **DAT-0b, Θ-positivity (strict).** For a **finite** dominant `π : Y ⟶ ℙ¹`, the unit fiber
twist has strictly positive degree: `0 < classDeg K (fiberTwist π 1)`. The degree equals
`deg F` (`classDeg_fiberTwist_one`), and `0 < deg F` unconditionally
(`zero_lt_deg_fiberWeilDivisor`, from surjectivity of the finite dominant `π`). -/
theorem zero_lt_classDeg_fiberTwist_one [IsFinite π] :
    0 < classDeg K (fiberTwist π 1) := by
  rw [classDeg_fiberTwist_one π]
  exact zero_lt_deg_fiberWeilDivisor π

/-- **DAT-0b, Θ-positivity (FLV threshold form).** `1 ≤ classDeg K (fiberTwist π 1)` for a
finite dominant `π`. This is the `1 ≤ classDeg θ` hypothesis consumed by the FLV class form
(`exists_subsingleton_hModule_one_of_one_le_classDeg_of_isFinite_toP1`). -/
theorem one_le_classDeg_fiberTwist_one [IsFinite π] :
    1 ≤ classDeg K (fiberTwist π 1) := by
  have h := zero_lt_classDeg_fiberTwist_one π
  omega

end Degree

/-! ## The `k → K` fibre transport of the positivity constant (E-iv-alg) -/

section Transport

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  {K₁ K₂ : Type u} [Field K₁] [Algebra k K₁] [Field K₂] [Algebra k K₂]

/-- **The Θ-positivity constant transports across base-field transitions.** For the challenge
curve `C : Over (Spec k)`, a base-field transition `φ : K₁ →ₐ[k] K₂`, and a Čech Picard class
`L` on `C_{K₁}` with `1 ≤ classDeg K₁ L`, the pulled-back class on `C_{K₂}` retains the
threshold: `1 ≤ classDeg K₂ (CechPic.map π L)`, where `π := (C ◁ Over.overSpecMap φ).left`.
Immediate from E-iv-alg (`classDeg_cechPicMap_baseFieldTransition`): the degree is
base-field-invariant. With `L` the Θ-class this delivers FLV's `1 ≤ classDeg θ` over every
field of the pack from the single base value. -/
theorem one_le_classDeg_cechPicMap_baseFieldTransition_of_one_le (φ : K₁ →ₐ[k] K₂)
    (L : (C ⊗ overSpec k K₁).left.CechPic) (hL : 1 ≤ classDeg K₁ L) :
    1 ≤ classDeg K₂ (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left) L) := by
  rw [classDeg_cechPicMap_baseFieldTransition]
  exact hL

end Transport

end AlgebraicGeometry
