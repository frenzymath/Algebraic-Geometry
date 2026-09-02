/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4LinearSystems
import HartshorneLib.Chapter4RiemannRochEuler
import HartshorneLib.Chapter4DivisorMultiplication
import HartshorneLib.Chapter4ProductFormulaBridge

/-!
# Hartshorne IV.1.2: sections and effective representatives

This file identifies positive degree-zero cohomology with the existence of a
nonzero rational section, in the unit-and-divisor form used by the divisor API.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
private lemma top_nonempty : ((⊤ : X.left.Opens) : Set X.left).Nonempty :=
  ⟨genericPoint X.left, trivial⟩

/-- A positive-dimensional space of global sections gives an effective translate. -/
theorem exists_unit_nonneg_of_h0_pos (D : CurveDivisor k X)
    (hD : 0 < CategoryTheory.Sheaf.h0 (divisorSheaf D)) :
    ∃ g : X.left.functionFieldˣ, 0 ≤ principalDivisor g + D := by
  haveI : Nontrivial (CategoryTheory.Sheaf.HModule
      (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D) 0) :=
    Module.nontrivial_of_finrank_pos hD
  obtain ⟨t, ht⟩ := exists_ne (0 : CategoryTheory.Sheaf.HModule
    (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D) 0)
  set s := (CategoryTheory.Sheaf.HModule.linearEquiv₀
    (isTerminalTop : IsTerminal (⊤ : X.left.Opens)) (divisorSheaf D)) t
  have hsne : s ≠ 0 := by
    exact (LinearEquiv.map_ne_zero_iff _).mpr ht
  set g : X.left.functionField := divisorVal s
  have hgmem : g ∈ divisorSections D ⊤ := divisorVal_mem s
  have hgne : g ≠ 0 := by
    intro h
    apply hsne
    apply divisorSection_ext (D := D) (W := ⊤)
    change divisorVal s = divisorVal (0 : (divisorPresheaf D).obj (op (⊤ : X.left.Opens)))
    rw [show divisorVal s = g from rfl, h]
    rfl
  let u : X.left.functionFieldˣ := Units.mk0 g hgne
  refine ⟨u, ?_⟩
  rw [CurveDivisor.le_iff_coeffAt]
  intro x hx
  have hb := (mem_divisorSections_of_nonempty top_nonempty).mp hgmem x hx trivial
  have hgu : (u : X.left.functionField) = g := rfl
  rw [← hgu, orderAt_eq_divisorBound_neg_principalDivisor u hx] at hb
  simp only [divisorBound, WithZero.coe_le_coe, Multiplicative.ofAdd_le] at hb
  change -CurveDivisor.coeffAt hx (principalDivisor u) ≤ CurveDivisor.coeffAt hx D at hb
  change (0 : ℤ) ≤ CurveDivisor.coeffAt hx (principalDivisor u) + CurveDivisor.coeffAt hx D
  omega

/-- A nonzero rational section produces a positive global-section rank. -/
theorem h0_pos_of_hasNonzeroRationalSection
    {D : CurveDivisor k X}
    (hD : HasNonzeroRationalSection D) :
    0 < CategoryTheory.Sheaf.h0 (divisorSheaf D) := by
  obtain ⟨g, hg⟩ := hD
  have hgmem : (g : X.left.functionField) ∈ divisorSections D ⊤ := by
    rw [mem_divisorSections_of_nonempty top_nonempty]
    intro x hx _
    have hcoeff := (CurveDivisor.le_iff_coeffAt.mp hg) x hx
    rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_zero] at hcoeff
    rw [orderAt_eq_divisorBound_neg_principalDivisor g hx]
    rw [divisorBound_eq_coeffAt hx (-principalDivisor g),
      divisorBound_eq_coeffAt hx D]
    simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
    rw [CurveDivisor.coeffAt_neg, coeffAt_principalDivisor]
    rw [coeffAt_principalDivisor] at hcoeff
    omega
  let s : (divisorPresheaf D).obj (op (⊤ : X.left.Opens)) :=
    ⟨(g : X.left.functionField), hgmem⟩
  have hsne : s ≠ 0 := by
    intro hs
    have : (g : X.left.functionField) = 0 := by
      exact congrArg divisorVal hs
    exact Units.ne_zero g this
  let e := CategoryTheory.Sheaf.HModule.linearEquiv₀
    (isTerminalTop : IsTerminal (⊤ : X.left.Opens)) (divisorSheaf D)
  let t := e.symm s
  have htne : t ≠ 0 := by
    intro ht
    apply hsne
    calc
      s = e (e.symm s) := (e.apply_symm_apply s).symm
      _ = e 0 := by rw [show e.symm s = t from rfl, ht]
      _ = 0 := e.map_zero
  letI : Module.Finite k (CategoryTheory.Sheaf.HModule
      (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D) 0) :=
    (hasFiniteDivisorCohomology_of_smoothProperIntegralCurve (k := k) X D).1
  change 0 < Module.finrank k (CategoryTheory.Sheaf.HModule
    (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D) 0)
  exact (Module.finrank_pos_iff_exists_ne_zero).mpr ⟨t, htne⟩

/-- The rank-zero cohomology criterion for a nonzero rational section. -/
theorem h0_ne_zero_iff_hasNonzeroRationalSection (D : CurveDivisor k X)
    :
    CategoryTheory.Sheaf.h0 (divisorSheaf D) ≠ 0 ↔ HasNonzeroRationalSection D := by
  constructor
  · intro h
    have hpos : 0 < CategoryTheory.Sheaf.h0 (divisorSheaf D) := Nat.pos_of_ne_zero h
    exact (exists_unit_nonneg_of_h0_pos D hpos)
  · intro h
    exact Nat.ne_of_gt (h0_pos_of_hasNonzeroRationalSection h)

/-- A nonzero `h⁰` forces nonnegative divisor degree, using the smooth-proper
curve product-formula producer. -/
theorem degree_nonneg_of_h0_ne_zero
    {D : CurveDivisor k X}
    (hD : CategoryTheory.Sheaf.h0 (divisorSheaf D) ≠ 0) :
    0 ≤ CurveDivisor.degree D := by
  exact degree_nonneg_of_hasNonzeroRationalSection
    (principalDivisorsHaveDegreeZero_of_smoothProperIntegralCurve (X := X))
    ((h0_ne_zero_iff_hasNonzeroRationalSection D).mp hD)

/-- In degree zero, `h⁰` is nonzero exactly for the trivial divisor class. -/
theorem h0_ne_zero_iff_linearlyEquivalent_zero_of_degree_zero
    {D : CurveDivisor k X} (hD : CurveDivisor.degree D = 0) :
    CategoryTheory.Sheaf.h0 (divisorSheaf D) ≠ 0 ↔ LinearlyEquivalent D 0 := by
  constructor
  · intro h
    exact (hasNonzeroRationalSection_iff_linearlyEquivalent_zero_of_smoothProperIntegralCurve
      (X := X) hD).mp ((h0_ne_zero_iff_hasNonzeroRationalSection D).mp h)
  · intro h
    exact Nat.ne_of_gt (h0_pos_of_hasNonzeroRationalSection
      (hasNonzeroRationalSection_of_linearlyEquivalent_zero h))

end Hartshorne
