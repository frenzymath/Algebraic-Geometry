/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PresentationClassLaw
import AlgebraicJacobian.Picard.PresentationCalculus

/-!
# Extraction: equal classes differ by a principal divisor

For the curve bundle `X` (integral, smooth of relative dimension one and quasi-compact
over a field `K`), this file proves the extraction half of the meromorphic bridge
(deg-D2 W4): if two meromorphic presentations present the same Čech Picard class, their
divisors differ by the principal divisor of a single rational function.

## Route

Equal classes are, on a common refinement `𝒲`, cohomologous cocycles: there is a
`0`-cochain of unit sections `α` conjugating one into the other. The elements
`c x := P.elem x · (Q.elem x)⁻¹ · germ_η (α x) ∈ K(X)ˣ` then agree for all `x` — the
coboundary identity pushed to `η` is literal equality of field elements (decision D1: no
sheaf gluing) — so they are *one* rational function `g`, and `div g = D_P − D_Q` because
`germ_η (α x)` has trivial order at `x` (`Scheme.ordZ_germGenericUnits`).

Together with the class law this gives the full characterization
`MeromorphicPresentation.picClass_eq_iff_exists_divOf`: two presentations present the
same class iff their divisors differ by a principal divisor.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

namespace MeromorphicPresentation

/-- Constancy extraction in a commutative group: if `A · (pₓ / p_y) = (qₓ / q_y) · B`
(the coboundary identity at `η`), then `pₓ / qₓ · A = p_y / q_y · B` (the two candidate
rational functions agree). -/
private lemma comm_group_const {G : Type u} [CommGroup G] {A B px py qx qy : G}
    (h : A * (px * py⁻¹) = qx * qy⁻¹ * B) :
    px * qx⁻¹ * A = py * qy⁻¹ * B := by
  have h' := congrArg (· * (py * qx⁻¹)) h
  simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel_left] at h' ⊢
  exact h'

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **Extraction** (the W4 keystone): if two meromorphic presentations present the same
Čech Picard class, their divisors differ by the principal divisor of a single rational
function. The cobounding unit sections are glued inside `K(X)ˣ`: the elements
`P.elem x · (Q.elem x)⁻¹ · germ_η (α x)` agree as field elements, and their common value
is the required function. -/
theorem exists_divOf_of_picClass_eq {P Q : X.MeromorphicPresentation}
    (h : P.picClass = Q.picClass) :
    ∃ g : X.functionFieldˣ,
      presentationDivisor K P - presentationDivisor K Q
        = Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g := by
  have hmk : CechPic.mk P.cover P.cocycle.class = CechPic.mk Q.cover Q.cocycle.class := h
  obtain ⟨𝒲, h₁, h₂, e⟩ := CechPic.mk_eq_mk_iff.mp hmk
  have hcoh : (P.cocycle.res fun k => homOfLE (h₁ k)).IsCohomologous
      (Q.cocycle.res fun k => homOfLE (h₂ k)) :=
    (OneCocycle.class_eq_iff (P.cocycle.res fun k => homOfLE (h₁ k))
      (Q.cocycle.res fun k => homOfLE (h₂ k))).mp e
  obtain ⟨α, hα⟩ := (OneCocycle.isCohomologous_iff_evInf _ _).mp hcoh
  -- the coboundary identity, in `Γ`-typed form
  have hα' : ∀ x y : X,
      X.unitsRestrict (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x) (α x)
          * unitsEvInf (P.cocycle.res fun k => homOfLE (h₁ k)) x y
        = unitsEvInf (Q.cocycle.res fun k => homOfLE (h₂ k)) x y
          * X.unitsRestrict (inf_le_right : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens y) (α y) :=
    fun x y => hα x y
  -- the candidate rational functions agree as field elements (D1: gluing is equality)
  have hconst : ∀ x y : X,
      P.elem x * (Q.elem x)⁻¹
          * germGenericUnits (𝒲.genericPoint_mem_opens x) (α x)
        = P.elem y * (Q.elem y)⁻¹
          * germGenericUnits (𝒲.genericPoint_mem_opens y) (α y) := by
    intro x y
    have key := congrArg (germGenericUnits (𝒲.genericPoint_mem_inf x y)) (hα' x y)
    rw [map_mul, map_mul, germGenericUnits_unitsRestrict, germGenericUnits_unitsRestrict,
      P.germGenericUnits_unitsEvInf_res h₁ x y, Q.germGenericUnits_unitsEvInf_res h₂ x y]
      at key
    exact comm_group_const key
  -- the common value, read off at the generic-point index
  refine ⟨P.elem (genericPoint X) * (Q.elem (genericPoint X))⁻¹
      * germGenericUnits (𝒲.genericPoint_mem_opens (genericPoint X))
        (α (genericPoint X)), ?_⟩
  refine CurveDivisor.ext_coeffAt fun z hz => ?_
  have hval : Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz
      (P.elem z * (Q.elem z)⁻¹
        * germGenericUnits (𝒲.genericPoint_mem_opens z) (α z))
      = Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (P.elem z)
        * (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (Q.elem z))⁻¹ := by
    rw [map_mul, map_mul, map_inv,
      ordZ_germGenericUnits K (𝒲.genericPoint_mem_opens z) (α z) hz (𝒲.mem_opens z),
      mul_one]
  rw [CurveDivisor.coeffAt_sub, coeffAt_presentationDivisor, coeffAt_presentationDivisor,
    CurveDivisor.coeffAt_divOf, hconst (genericPoint X) z, hval, toAdd_mul, toAdd_inv,
    sub_eq_add_neg]

/-- **The meromorphic characterization of the Čech Picard group**: two presentations
present the same class iff their divisors differ by a principal divisor. -/
theorem picClass_eq_iff_exists_divOf {P Q : X.MeromorphicPresentation} :
    P.picClass = Q.picClass
      ↔ ∃ g : X.functionFieldˣ,
          presentationDivisor K P - presentationDivisor K Q
            = Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g := by
  refine ⟨exists_divOf_of_picClass_eq K, ?_⟩
  rintro ⟨g, hg⟩
  have hdiv : presentationDivisor K (Q * principal g) = presentationDivisor K P := by
    rw [presentationDivisor_mul, presentationDivisor_principal, ← hg]
    abel
  have hcl := picClass_eq_of_presentationDivisor_eq K hdiv
  rw [picClass_mul, picClass_principal, mul_one] at hcl
  exact hcl.symm

end MeromorphicPresentation

end Scheme

end AlgebraicGeometry
