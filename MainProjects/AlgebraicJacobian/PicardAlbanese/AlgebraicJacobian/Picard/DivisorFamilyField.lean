/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamily
import AlgebraicJacobian.Picard.DivisorClassMeromorphic
import AlgebraicJacobian.RiemannRoch.MulEquiv

/-!
# The field dictionary for divisor families: the forward map (`informal/spec-dd-1.md` §3 (f))

Over a field `K` the relative curve `X = relCurve C K` is an integral, smooth, quasi-compact
curve, so the meromorphic bridge (`AlgebraicJacobian.Picard.PresentationDivisor`) applies: a
local-equation system `d` on `X` has a meromorphic presentation `d.presentation` and hence a
Weil divisor `presentationDivisor K d.presentation`. This file lands the **forward map** of the
DD-1c field dictionary `divFamFieldEquiv`:

`divFamDivisor : DivFam C K π n → (relCurve C K).CurveDivisor`,

the Weil divisor cut out by the anchor equations of a certified divisor family, together with
the two facts that make it land in the effective divisors:

* `Scheme.presentationDivisor_eq_of_divEq` — **DivEq-invariance** of `presentationDivisor`: two
  local-equation systems that are divisor-equal (a common refinement on which the equations
  agree up to units, `Scheme.LocalEquations.DivEq`) cut out the *same* Weil divisor. This is
  finer than the landed `picClass`-invariance (`picClass_eq_of_divEq`): distinct divisors share
  a Picard class, but the *divisor* itself is a `DivEq`-invariant because the order of the
  equation at each closed point only changes by the (trivial) order of a unit germ.
* `Scheme.zero_le_coeffAt_presentationDivisor` — **effectivity**: the divisor of a
  local-equation system is effective, since each anchor equation is a genuine section of the
  structure sheaf, integral at every point, hence has nonnegative order there.
* `AlgebraicGeometry.divFamDivisor` — the descent to the setoid quotient `DivFam C K π n`, with
  `divFamDivisor_mk`, `coeffAt_divFamDivisor`, and effectivity `zero_le_divFamDivisor`.

The degree computation `deg K (divFamDivisor F) = n` is LANDED (hypothesis-free) as
`deg_divFamDivisor` in `AlgebraicJacobian.Picard.DivisorFamilyFieldCRT` (the stalk-eval
CRT across the glued equalizer, I-0230); the backward map remains the open DD-1c stage.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme

/-! ## DivEq-invariance and effectivity of `presentationDivisor` -/

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **DivEq-invariance of the presentation divisor.** Two divisor-equal local-equation systems
(`Scheme.LocalEquations.DivEq`: a common refinement on which the equations agree up to units at
every point) cut out the same Weil divisor. Finer than `picClass_eq_of_divEq`: the order of the
equation at a closed point only changes by the trivial order of a unit germ. -/
theorem presentationDivisor_eq_of_divEq {d₁ d₂ : X.LocalEquations}
    (h : LocalEquations.DivEq d₁ d₂) :
    presentationDivisor K d₁.presentation = presentationDivisor K d₂.presentation := by
  obtain ⟨𝒲, h₁, h₂, H⟩ := h
  refine CurveDivisor.ext_coeffAt fun x hx => ?_
  rw [coeffAt_presentationDivisor, coeffAt_presentationDivisor]
  obtain ⟨u, hu⟩ := H x
  -- the trivializing element of `d₁` is the unit germ of `u` times that of `d₂`
  have hkey : d₁.presentation.elem x
      = germGenericUnits (𝒲.genericPoint_mem_opens x) u * d₂.presentation.elem x := by
    refine Units.ext ?_
    rw [Units.val_mul, germGenericUnits_val, LocalEquations.presentation_elem_val,
      LocalEquations.presentation_elem_val,
      ← X.presheaf.germ_res_apply (homOfLE (h₁ x)) (genericPoint X)
        (𝒲.genericPoint_mem_opens x) (d₁.eqn x),
      ← X.presheaf.germ_res_apply (homOfLE (h₂ x)) (genericPoint X)
        (𝒲.genericPoint_mem_opens x) (d₂.eqn x), ← map_mul, ← hu]
  rw [hkey, map_mul,
    ordZ_germGenericUnits K (𝒲.genericPoint_mem_opens x) u hx (𝒲.mem_opens x), one_mul]

/-- **Effectivity of the presentation divisor.** Each anchor equation of a local-equation
system is a genuine section of the structure sheaf near the closed point `x`, hence integral at
`x` (order `≤ 1`), so its order of vanishing is nonnegative: the divisor of a local-equation
system is effective. -/
theorem zero_le_coeffAt_presentationDivisor (E : X.LocalEquations) {x : X}
    (hx : x ≠ genericPoint X) :
    0 ≤ coeffAt hx (presentationDivisor K E.presentation) := by
  rw [coeffAt_presentationDivisor]
  -- the trivializing element is integral at `x`
  have hval : (E.presentation.elem x : X.functionField)
      = algebraMap (X.presheaf.stalk x) X.functionField
          ((X.presheaf.germ (E.cover.opens x) x (E.cover.mem_opens x)).hom (E.eqn x)) := by
    rw [LocalEquations.presentation_elem_val]
    exact germ_generic_eq_algebraMap_germ (E.cover.genericPoint_mem_opens x)
      (E.cover.mem_opens x) (E.eqn x)
  have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
      (E.presentation.elem x : X.functionField) ≤ 1 := by
    rw [hval]; exact ord_algebraMap_stalk_le_one K hx _
  -- `ord ≤ 1` ⟺ `1 ≤ ordZ` ⟺ `0 ≤ toAdd (ordZ)`
  rw [ord_val_eq_ordZ K (E.presentation.elem x) hx] at hord
  rw [show (1 : WithZero (Multiplicative ℤ)) = ((1 : Multiplicative ℤ) : WithZero _) from rfl,
    WithZero.coe_le_coe] at hord
  have h1le : (1 : Multiplicative ℤ)
      ≤ Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx (E.presentation.elem x) :=
    inv_le_one'.mp hord
  rw [show (0 : ℤ) = Multiplicative.toAdd (1 : Multiplicative ℤ) from rfl]
  exact h1le

end Scheme

/-! ## The forward map on `DivFam` over a field -/

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
variable {n : ℕ}

/-- **The Weil divisor of a divisor family over a field** (the forward map of the DD-1c field
dictionary): the divisor cut out by the anchor equations of any certified representative. Well
defined on the setoid quotient by `Scheme.presentationDivisor_eq_of_divEq` (DivEq-invariance,
finer than the `picClass` descent). -/
noncomputable def divFamDivisor (F : DivFam C K π n) : (relCurve C K).CurveDivisor :=
  Quotient.liftOn F (fun G => Scheme.presentationDivisor K G.eqns.presentation)
    (fun _ _ h => Scheme.presentationDivisor_eq_of_divEq K h)

@[simp]
lemma divFamDivisor_mk (F : CertifiedDivisorFamily C K π n) :
    divFamDivisor (DivFam.mk F) = Scheme.presentationDivisor K F.eqns.presentation :=
  rfl

/-- The multiplicity of the divisor of a family at a closed point `x` is the order of vanishing
of the anchor equation of the piece indexed by `x`. -/
lemma coeffAt_divFamDivisor (F : CertifiedDivisorFamily C K π n) {x : relCurve C K}
    (hx : x ≠ genericPoint (relCurve C K)) :
    coeffAt hx (divFamDivisor (DivFam.mk F))
      = Multiplicative.toAdd (Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hx
          (F.eqns.presentation.elem x)) := by
  rw [divFamDivisor_mk, Scheme.coeffAt_presentationDivisor]

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **The field half of the degree identity.** Over a field every module is free, so the
constant fibre rank `rankAtStalk` of the glued colength module equals its `K`-dimension: a
certificate of degree `n` forces `finrank K W(d) = n`. The geometric half —
the colength↔degree identity `finrank K W(d) = deg` — is LANDED in
`AlgebraicJacobian.Picard.DivisorFamilyFieldCRT` (`DivisorAdaptation.deg_presentationDivisor`,
adaptation-independent, I-0230). -/
theorem DivisorAdaptation.IsCertified.finrank_glued
    {d : (relCurve C K).LocalEquations} {A : DivisorAdaptation C K π d}
    (hc : A.IsCertified n) : Module.finrank K A.Glued = n := by
  haveI : Module.Free K A.Glued := Module.Free.of_divisionRing K A.Glued
  have h := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := A.Glued))
    (⊥ : PrimeSpectrum K)
  rw [hc.rankAtStalk_glued ⊥] at h
  simpa using h.symm

/-- **The divisor of a family is effective**: the anchor equations are genuine sections of the
structure sheaf, integral at every closed point. -/
theorem zero_le_divFamDivisor (F : DivFam C K π n) : 0 ≤ divFamDivisor F := by
  induction F using Quotient.ind with
  | _ G =>
    refine Finsupp.le_def.mpr fun p => ?_
    exact Scheme.zero_le_coeffAt_presentationDivisor K G.eqns p.2

end AlgebraicGeometry
