/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyFieldDegree
import AlgebraicJacobian.Picard.DivisorFamilyExtraction

/-!
# The backward realization of the field dictionary (`informal/spec-dd-1.md` §3 (f), `hsurj`)

Over a field `K` the forward map `divFamDivisor` sends a certified divisor family to its Weil
divisor. This file builds the **backward** ingredients: from an effective divisor `D` of degree
`n`, an explicit local-equation system realizing it, on the way to a certified support-separated
family presenting `D` (the `hsurj` slot of `divFamFieldEquivOfDegOfSurj`).

## Stage 1 — additivity of the presentation divisor along products

`Scheme.LocalEquations.mul` (`AlgebraicJacobian.Picard.DivisorClass`) multiplies two
local-equation systems pointwise on the common refinement; its Weil divisor is the *sum* of the
two divisors. This is the `LocalEquations`-level companion of the
`MeromorphicPresentation`-level `presentationDivisor_mul`: the trivializing element of the
product presentation is the product of the trivializing elements
(`Scheme.LocalEquations.mul_presentation_elem`), and `ordZ` is a group homomorphism, so orders —
hence divisor coefficients — add.

* `Scheme.LocalEquations.mul_presentation_elem` — `(d.mul d').presentation.elem x
  = d.presentation.elem x * d'.presentation.elem x`.
* `Scheme.LocalEquations.presentationDivisor_mul` — `presentationDivisor K (d.mul d').presentation
  = presentationDivisor K d.presentation + presentationDivisor K d'.presentation`.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme

namespace LocalEquations

variable {X : Scheme.{u}} [IsIntegral X]

/-- **The trivial (unit) local-equation system**: the constant equation `1` on the top cover.
Its equations are regular (`1` is a nonzerodivisor) and pairwise unit-related (ratio `1`); it cuts
out the *zero* divisor and is the base case of the point-product realization of an effective
divisor. -/
noncomputable def unitEquations : X.LocalEquations where
  cover := ⊤
  eqn _ := 1
  regular _ y _ := by rw [map_one]; exact one_mem _
  ratio_isUnit _ _ := ⟨1, by simp⟩

omit [IsIntegral X] in
@[simp]
lemma unitEquations_eqn (x : X) : (unitEquations : X.LocalEquations).eqn x = 1 := rfl

/-- **The trivializing element of a product presentation is the product of the trivializing
elements.** The equation of `d.mul d'` at `x` is, by definition, the product of the restrictions
of `d`'s and `d'`'s equations to the common refinement, so its germ at `η` — the trivializing
element of the presentation — is the product of the two germs at `η`. -/
lemma mul_presentation_elem (d d' : X.LocalEquations) (x : X) :
    (d.mul d').presentation.elem x = d.presentation.elem x * d'.presentation.elem x := by
  refine Units.ext ?_
  have hη : genericPoint X ∈ d.cover.opens x ⊓ d'.cover.opens x :=
    ⟨d.cover.genericPoint_mem_opens x, d'.cover.genericPoint_mem_opens x⟩
  rw [Units.val_mul, presentation_elem_val, presentation_elem_val, presentation_elem_val,
    ← X.presheaf.germ_res_apply (homOfLE (inf_le_left :
        d.cover.opens x ⊓ d'.cover.opens x ≤ d.cover.opens x)) (genericPoint X) hη (d.eqn x),
    ← X.presheaf.germ_res_apply (homOfLE (inf_le_right :
        d.cover.opens x ⊓ d'.cover.opens x ≤ d'.cover.opens x)) (genericPoint X) hη (d'.eqn x),
    ← map_mul]
  rfl

variable (K : Type u) [Field K] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **Additivity of the presentation divisor along products** (`informal/spec-dd-1.md` §3 (f),
DD-1c backward stage 1): the Weil divisor of the product local-equation system `d.mul d'` is the
sum of the two Weil divisors. The trivializing element multiplies
(`mul_presentation_elem`) and `ordZ` is a group homomorphism, so the coefficients — orders of
vanishing — add. The `LocalEquations`-level companion of
`Scheme.MeromorphicPresentation.presentationDivisor_mul`. -/
theorem presentationDivisor_mul (d d' : X.LocalEquations) :
    presentationDivisor K (d.mul d').presentation
      = presentationDivisor K d.presentation + presentationDivisor K d'.presentation := by
  refine CurveDivisor.ext_coeffAt fun x hx => ?_
  rw [coeffAt_presentationDivisor, mul_presentation_elem, map_mul, toAdd_mul,
    CurveDivisor.coeffAt_add, coeffAt_presentationDivisor, coeffAt_presentationDivisor]

/-- The trivial local-equation system cuts out the zero divisor: its trivializing element is the
field unit `1` at every point, whose order of vanishing is `0`. -/
@[simp]
theorem presentationDivisor_unitEquations :
    presentationDivisor K (unitEquations : X.LocalEquations).presentation = 0 := by
  refine CurveDivisor.ext_coeffAt fun x hx => ?_
  rw [coeffAt_presentationDivisor]
  have hone : (unitEquations : X.LocalEquations).presentation.elem x = 1 := by
    refine Units.ext ?_
    rw [presentation_elem_val, Units.val_one, unitEquations_eqn, map_one]
  rw [hone, map_one, toAdd_one, CurveDivisor.coeffAt_zero]

/-- **Realization of an effective divisor by explicit local equations** (`informal/spec-dd-1.md`
§3 (f), the DD-1c backward realization core, `hsurj` half 1): every *effective* Weil divisor `D`
on the curve is the divisor of an explicit local-equation system — a product of tracked
point-uniformizer equations (`Scheme.pointEquations`), one factor per unit of multiplicity at each
support point. The `LocalEquations`-level companion of `exists_presentationDivisor_eq` (which lands
a `MeromorphicPresentation`); effectivity is what keeps the construction inside the regular
`LocalEquations` (no inverse factors, which would introduce poles).

The point-uniformizer products (`presentationDivisor_pointEquations` gives `single hx 1` per
factor) add up to `D` through the additivity lemma `presentationDivisor_mul`; the trivial system
`unitEquations` is the empty product (the zero divisor). This supplies the anchor equations `eqns`
of a certified family realizing `D`; the certified support-separated adaptation is the remaining
`hsurj` obligation. -/
theorem exists_localEquations_presentationDivisor_eq (D : X.CurveDivisor) (hD : 0 ≤ D) :
    ∃ E : X.LocalEquations, presentationDivisor K E.presentation = D := by
  classical
  -- a one-point divisor with nonnegative multiplicity, by induction on the multiplicity
  have hsingle : ∀ (x : X) (hx : x ≠ genericPoint X) (n : ℕ),
      ∃ E : X.LocalEquations,
        presentationDivisor K E.presentation = CurveDivisor.single hx (n : ℤ) := by
    intro x hx n
    induction n with
    | zero =>
      exact ⟨unitEquations, by
        rw [presentationDivisor_unitEquations, Nat.cast_zero, CurveDivisor.single_zero]⟩
    | succ n ih =>
      obtain ⟨E, hE⟩ := ih
      refine ⟨(pointEquations K hx (pointUniformizerData K hx)).mul E, ?_⟩
      rw [presentationDivisor_mul, presentationDivisor_pointEquations, hE,
        CurveDivisor.single_add]
      congr 1
      push_cast
      ring
  -- the general effective case, by induction on the finitely supported function
  have hmain : ∀ D : X.CurveDivisor, 0 ≤ D →
      ∃ E : X.LocalEquations, presentationDivisor K E.presentation = D := by
    intro D
    induction D using Finsupp.induction with
    | zero => intro _; exact ⟨unitEquations, presentationDivisor_unitEquations K⟩
    | single_add p b f hpf hb ih =>
      intro hle
      have hfp : f p = 0 := Finsupp.notMem_support_iff.mp hpf
      have hbnn : 0 ≤ b := by
        have h := Finsupp.le_def.mp hle p
        rw [Finsupp.add_apply, Finsupp.single_eq_same, hfp, add_zero] at h
        exact h
      have hfnn : (0 : X.CurveDivisor) ≤ f := by
        refine Finsupp.le_def.mpr fun q => ?_
        rcases eq_or_ne q p with rfl | hq
        · rw [hfp]; exact le_rfl
        · have h := Finsupp.le_def.mp hle q
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hq, zero_add] at h
          exact h
      obtain ⟨E, hE⟩ := ih hfnn
      obtain ⟨F, hF⟩ := hsingle p.1 p.2 b.toNat
      refine ⟨F.mul E, ?_⟩
      rw [presentationDivisor_mul, hF, hE, Int.toNat_of_nonneg hbnn]
      rfl
  exact hmain D hD

end LocalEquations

end Scheme

end AlgebraicGeometry
