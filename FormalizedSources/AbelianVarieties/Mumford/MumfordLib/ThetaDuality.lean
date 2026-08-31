/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ThetaIsotropic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite theta duality

The orthogonal operation attached to a skew commutator pairing is always a
Galois connection.  This file records the finite converse: once the two
restricted pairings realize all characters and finite character duality has
the expected cardinality, taking orthogonals twice recovers the subgroup.
-/

set_option autoImplicit false

universe u v w

namespace Mumford
namespace ThetaExtension

variable {G : Type u} {S : Type v} {K : Type w}
  [Group G] [CommGroup S] [AddCommGroup K]

/-- Finite additive subgroups with an inclusion and equal cardinalities coincide. -/
private theorem finite_addSubgroup_eq_of_le_of_natCard_eq
    [Finite K] {H J : AddSubgroup K} (hHJ : H ≤ J)
    (hcard : Nat.card H = Nat.card J) : H = J := by
  letI : Finite H := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite J := Finite.of_injective Subtype.val Subtype.val_injective
  have hb : Function.Bijective (AddSubgroup.inclusion hHJ) :=
    (Nat.bijective_iff_injective_and_card (AddSubgroup.inclusion hHJ)).mpr
      ⟨AddSubgroup.inclusion_injective hHJ, hcard⟩
  apply le_antisymm hHJ
  intro j hj
  obtain ⟨i, hi⟩ := hb.2 ⟨j, hj⟩
  have hv : (i : K) = (j : K) := congrArg Subtype.val hi
  rw [← hv]
  exact i.property

/-- A finite skew pairing has double orthogonal equal to the original subgroup
when both restricted pairing maps realize all characters and finite character
cardinality is preserved. -/
theorem commutatorPairingOrthogonal_orthogonal_eq_of_surjective_restrictions
    (E : ThetaExtension G S K) (H : AddSubgroup K) [Finite K]
    (hsurjH : Function.Surjective (E.commutatorPairingRestriction H))
    (hsurjHperp :
      Function.Surjective
        (E.commutatorPairingRestriction (E.commutatorPairingOrthogonal H)))
    (hdualH : Nat.card (H →+ Additive S) = Nat.card H)
    (hdualHperp :
      Nat.card
          (E.commutatorPairingOrthogonal H →+ Additive S) =
        Nat.card (E.commutatorPairingOrthogonal H)) :
    E.commutatorPairingOrthogonal
        (E.commutatorPairingOrthogonal H) = H := by
  let P := E.commutatorPairingOrthogonal H
  let Q := E.commutatorPairingOrthogonal P
  letI : Finite P := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite Q := Finite.of_injective Subtype.val Subtype.val_injective
  have hH :=
    E.natCard_eq_orthogonal_mul_character_of_surjective_restriction H hsurjH
  have hP :=
    E.natCard_eq_orthogonal_mul_character_of_surjective_restriction P
      hsurjHperp
  have hprod : Nat.card P * Nat.card H = Nat.card Q * Nat.card P := by
    calc
      Nat.card P * Nat.card H = Nat.card P * Nat.card (H →+ Additive S) := by
        rw [hdualH]
      _ = Nat.card (H →+ Additive S) * Nat.card P := Nat.mul_comm _ _
      _ = Nat.card K := by simpa [P, Nat.mul_comm] using hH.symm
      _ = Nat.card Q * Nat.card (P →+ Additive S) := by
        simpa [P, Q] using hP
      _ = Nat.card Q * Nat.card P := by rw [hdualHperp]
  have hcard : Nat.card H = Nat.card Q := by
    apply Nat.mul_right_cancel (Nat.card_pos : 0 < Nat.card P)
    simpa [Nat.mul_comm] using hprod
  have hle : H ≤ Q := by
    exact (E.le_commutatorPairingOrthogonal_iff H P).2 le_rfl
  have heq : H = Q := finite_addSubgroup_eq_of_le_of_natCard_eq hle hcard
  exact heq.symm

end ThetaExtension
end Mumford
