/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ThetaDuality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Complex theta duality

Finite abelian duality over the complex scalars removes the abstract
divisibility and character-cardinality hypotheses from the theta pairing
results.  The statements remain group-theoretic specializations; they do not
assert the geometric construction of a theta group.
-/

set_option autoImplicit false

universe u w

namespace Mumford
namespace ThetaExtension

/-- The multiplicative group of nonzero complex numbers is divisible by
positive natural powers. -/
@[implicit_reducible]
noncomputable def complexUnitsDivisibleByNat :
    DivisibleBy (Additive ℂˣ) ℕ :=
  divisibleByOfSMulRightSurj (Additive ℂˣ) ℕ (by
    intro n hn x
    obtain ⟨z, hz⟩ :=
      IsAlgClosed.exists_pow_nat_eq
        ((Additive.toMul x : ℂˣ) : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      rw [zero_pow hn] at hz
      exact (Additive.toMul x).ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    change (Units.mk0 z hz0) ^ n = Additive.toMul x
    apply Units.ext
    exact hz)

/-- The multiplicative group of nonzero complex numbers is divisible by
integer powers. -/
@[implicit_reducible]
noncomputable def complexUnitsDivisibleByInt :
    DivisibleBy (Additive ℂˣ) ℤ := by
  letI : DivisibleBy (Additive ℂˣ) ℕ := complexUnitsDivisibleByNat
  exact AddGroup.divisibleByIntOfDivisibleByNat (Additive ℂˣ)

/-- A finite abelian group is additively equivalent to its group of complex
multiplicative characters. -/
noncomputable def complexCharacterAddEquiv
    (A : Type*) [AddCommGroup A] [Finite A] :
    (A →+ Additive ℂˣ) ≃+ A :=
  AddMonoidHom.toMultiplicativeLeftAddEquiv.trans
    (Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
        (Multiplicative A) ℂ)).toAdditive |>.trans
    (AddEquiv.additiveMultiplicative A)

/-- Complex character duality preserves the cardinality of a finite abelian
group. -/
theorem natCard_complexCharacter_eq
    (A : Type*) [AddCommGroup A] [Finite A] :
    Nat.card (A →+ Additive ℂˣ) = Nat.card A :=
  Nat.card_congr (complexCharacterAddEquiv A).toEquiv

/-- The finite structure on the complex character group transported through
finite abelian duality. -/
@[implicit_reducible]
noncomputable def complexCharacterFintype
    (A : Type*) [AddCommGroup A] [Finite A] :
    Fintype (A →+ Additive ℂˣ) := by
  letI : Fintype A := Fintype.ofFinite A
  exact Fintype.ofEquiv A (complexCharacterAddEquiv A).symm.toEquiv

/-- A nondegenerate finite complex theta pairing realizes every character of
each subgroup. -/
theorem commutatorPairingRestriction_surjective_complex
    {G : Type u} {K : Type w} [Group G] [AddCommGroup K]
    (E : ThetaExtension G ℂˣ K) (H : AddSubgroup K) [Finite K]
    (hE : E.IsNondegenerate) :
    Function.Surjective (E.commutatorPairingRestriction H) := by
  letI : DivisibleBy (Additive ℂˣ) ℤ := complexUnitsDivisibleByInt
  letI : Fintype (K →+ Additive ℂˣ) := complexCharacterFintype K
  exact E.commutatorPairingRestriction_surjective_of_isNondegenerate H
    (natCard_complexCharacter_eq K).symm hE

/-- A maximal isotropic quotient is the complex character group of the
maximal isotropic subgroup. -/
noncomputable def quotientMaximalIsotropicAddEquiv_complex
    {G : Type u} {K : Type w} [Group G] [AddCommGroup K]
    (E : ThetaExtension G ℂˣ K) (H : AddSubgroup K) [Finite K]
    (hmax : E.IsMaximalIsotropic H) (hE : E.IsNondegenerate) :
    K ⧸ H ≃+ (H →+ Additive ℂˣ) :=
  E.quotientMaximalIsotropicAddEquiv H hmax
    (E.commutatorPairingRestriction_surjective_complex H hE)

/-- Complex character self-duality identifies a maximal isotropic quotient
with the maximal isotropic subgroup itself. -/
noncomputable def quotientMaximalIsotropicSelfAddEquiv_complex
    {G : Type u} {K : Type w} [Group G] [AddCommGroup K]
    (E : ThetaExtension G ℂˣ K) (H : AddSubgroup K) [Finite K]
    (hmax : E.IsMaximalIsotropic H) (hE : E.IsNondegenerate) :
    K ⧸ H ≃+ H :=
  (E.quotientMaximalIsotropicAddEquiv_complex H hmax hE).trans
    (complexCharacterAddEquiv H)

/-- For a finite nondegenerate complex theta pairing, taking the commutator
orthogonal twice recovers the original subgroup. -/
theorem commutatorPairingOrthogonal_orthogonal_eq_complex
    {G : Type u} {K : Type w} [Group G] [AddCommGroup K]
    (E : ThetaExtension G ℂˣ K) (H : AddSubgroup K) [Finite K]
    (hE : E.IsNondegenerate) :
    E.commutatorPairingOrthogonal
        (E.commutatorPairingOrthogonal H) = H := by
  letI : DivisibleBy (Additive ℂˣ) ℤ := complexUnitsDivisibleByInt
  letI : Fintype (K →+ Additive ℂˣ) := complexCharacterFintype K
  exact E.commutatorPairingOrthogonal_orthogonal_eq_of_isNondegenerate H
    (natCard_complexCharacter_eq K).symm hE
    (natCard_complexCharacter_eq H)
    (natCard_complexCharacter_eq (E.commutatorPairingOrthogonal H))

/-- The order of a finite nondegenerate complex theta quotient is the product
of the orders of a subgroup and its commutator orthogonal. -/
theorem natCard_eq_orthogonal_mul_subgroup_complex
    {G : Type u} {K : Type w} [Group G] [AddCommGroup K]
    (E : ThetaExtension G ℂˣ K) (H : AddSubgroup K) [Finite K]
    (hE : E.IsNondegenerate) :
    Nat.card K =
      Nat.card (E.commutatorPairingOrthogonal H) * Nat.card H := by
  letI : DivisibleBy (Additive ℂˣ) ℤ := complexUnitsDivisibleByInt
  letI : Fintype (K →+ Additive ℂˣ) := complexCharacterFintype K
  exact E.natCard_eq_orthogonal_mul_subgroup_of_isNondegenerate H
    (natCard_complexCharacter_eq K).symm hE
    (natCard_complexCharacter_eq H)

/-- A maximal isotropic subgroup of a finite nondegenerate complex theta
quotient has square order equal to the order of the quotient. -/
theorem natCard_eq_square_of_isMaximalIsotropic_complex
    {G : Type u} {K : Type w} [Group G] [AddCommGroup K]
    (E : ThetaExtension G ℂˣ K) (H : AddSubgroup K) [Finite K]
    (hmax : E.IsMaximalIsotropic H) (hE : E.IsNondegenerate) :
    Nat.card K = Nat.card H ^ 2 := by
  letI : DivisibleBy (Additive ℂˣ) ℤ := complexUnitsDivisibleByInt
  letI : Fintype (K →+ Additive ℂˣ) := complexCharacterFintype K
  exact E.natCard_eq_square_of_isMaximalIsotropic_of_isNondegenerate H
    hmax (natCard_complexCharacter_eq K).symm hE
    (natCard_complexCharacter_eq H)

/-- Every finite nondegenerate complex theta quotient has a maximal isotropic
subgroup whose order realizes the square-order formula. -/
theorem exists_isMaximalIsotropic_natCard_eq_square_complex
    {G : Type u} {K : Type w} [Group G] [AddCommGroup K]
    (E : ThetaExtension G ℂˣ K) [Finite K]
    (hE : E.IsNondegenerate) :
    ∃ H : AddSubgroup K,
      E.IsMaximalIsotropic H ∧ Nat.card K = Nat.card H ^ 2 := by
  obtain ⟨H, hmax⟩ := E.exists_isMaximalIsotropic
  exact ⟨H, hmax,
    E.natCard_eq_square_of_isMaximalIsotropic_complex H hmax hE⟩

end ThetaExtension
end Mumford
