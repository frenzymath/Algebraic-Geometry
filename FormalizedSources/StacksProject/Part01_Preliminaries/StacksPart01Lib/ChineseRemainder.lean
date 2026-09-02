/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The Chinese remainder theorem

Wrappers around Mathlib's ideal-theoretic Chinese remainder theorem (Stacks,
Tag 00DT).  The finite-family statements use an indexed family of pairwise
coprime ideals; the maximal-ideal corollary packages the usual coprimality
argument.
-/

namespace StacksPart01

open Function

/-- For a finite pairwise-coprime family of ideals, the product equals the
intersection (written as an indexed infimum). -/
theorem chinese_remainder_inf_eq_prod
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) :
    (⨅ i, I i) = ∏ i, I i := by
  symm
  have h := Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := I) (by
      rw [Finset.coe_univ, Set.pairwise_univ]
      exact hI)
  simpa [Finset.inf_eq_iInf] using h

/-- The Chinese remainder ring equivalence for a finite family of pairwise
coprime ideals. -/
noncomputable def chinese_remainder
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) :
    (R ⧸ ⨅ i, I i) ≃+* ∀ i, R ⧸ I i :=
  Ideal.quotientInfRingEquivPiQuotient I hI

/-- The Chinese remainder ring equivalence with the product ideal as source.
This is the finite-family form of the statement in the Stacks Project. -/
noncomputable def chinese_remainder_prod
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) :
    (R ⧸ ∏ i, I i) ≃+* ∀ i, R ⧸ I i := by
  exact (Ideal.quotEquivOfEq (chinese_remainder_inf_eq_prod I hI).symm).trans
    (Ideal.quotientInfRingEquivPiQuotient I hI)

/-- Chinese remainder for two pairwise-coprime ideals. -/
noncomputable def chinese_remainder_two
    {R : Type*} [CommRing R] (I J : Ideal R)
    (hIJ : IsCoprime I J) :
    (R ⧸ I ⊓ J) ≃+* (R ⧸ I) × R ⧸ J :=
  Ideal.quotientInfEquivQuotientProd I J hIJ

/-- Pairwise distinct maximal ideals are pairwise coprime, hence satisfy the
Chinese remainder theorem. -/
noncomputable def chinese_remainder_maximal
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (m : ι → Ideal R) (hm : ∀ i, (m i).IsMaximal)
    (hne : Pairwise (fun i j ↦ m i ≠ m j)) :
    (R ⧸ ⨅ i, m i) ≃+* ∀ i, R ⧸ m i := by
  apply chinese_remainder m
  intro i j hij
  letI : (m i).IsMaximal := hm i
  letI : (m j).IsMaximal := hm j
  exact Ideal.isCoprime_of_isMaximal (hne hij)

end StacksPart01
