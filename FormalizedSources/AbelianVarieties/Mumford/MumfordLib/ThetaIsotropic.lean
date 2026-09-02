/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.Theta
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Isotropic subgroups of theta extensions

The commutator orthogonal is the kernel of restriction to a subgroup's
character group. Maximal isotropic subgroups coincide with their orthogonal.
-/

set_option autoImplicit false

universe u v w

namespace Mumford
namespace ThetaExtension

variable {G : Type u} {S : Type v} {K : Type w}
  [Group G] [CommGroup S] [AddCommGroup K]

/-- Restrict the second variable of the commutator pairing to a subgroup. -/
noncomputable def commutatorPairingRestriction
    (E : ThetaExtension G S K) (H : AddSubgroup K) :
    K →+ (H →+ Additive S) :=
  (AddMonoidHom.compHom' H.subtype).comp E.commutatorPairingBihom

/-- A divisible character group lets a globally surjective commutator pairing
restrict surjectively to every subgroup. -/
theorem commutatorPairingRestriction_surjective_of_divisible
    (E : ThetaExtension G S K) (H : AddSubgroup K)
    [DivisibleBy (Additive S) ℤ]
    (hpair : Function.Surjective E.commutatorPairingBihom) :
    Function.Surjective (E.commutatorPairingRestriction H) := by
  let hext : Function.Surjective
      (AddMonoidHom.compHom' H.subtype :
        (K →+ Additive S) →+ (H →+ Additive S)) := by
    intro chi
    obtain ⟨psi, hpsi⟩ :=
      (Module.Baer.of_divisible (Additive S)).extension_property_addMonoidHom
        H.subtype H.subtype_injective chi
    exact ⟨psi, hpsi⟩
  intro chi
  obtain ⟨psi, hpsi⟩ := hext chi
  obtain ⟨k, hk⟩ := hpair psi
  refine ⟨k, ?_⟩
  ext h
  have h1 := congrArg (fun f : K →+ Additive S => f (h : K)) hk
  have h2 := congrArg (fun f : H →+ Additive S => f h) hpsi
  change Additive.ofMul (E.commutatorPairing k (h : K)) = chi h
  change E.commutatorPairingBihom k (h : K) = psi (h : K) at h1
  change (H.subtype.compHom' psi) h = chi h at h2
  calc
    Additive.ofMul (E.commutatorPairing k (h : K)) = psi (h : K) := by
      simpa only [E.commutatorPairingBihom_apply] using h1
    _ = chi h := by simpa using h2

/-- The commutator orthogonal of a subgroup. -/
noncomputable def commutatorPairingOrthogonal
    (E : ThetaExtension G S K) (H : AddSubgroup K) : AddSubgroup K :=
  (E.commutatorPairingRestriction H).ker

/-- If the restricted commutator pairing is onto, its quotient by the
    orthogonal subgroup is the corresponding character group. -/
noncomputable def quotientOrthogonalAddEquivOfSurjectiveRestriction
    (E : ThetaExtension G S K) (H : AddSubgroup K)
    (hsurj : Function.Surjective (E.commutatorPairingRestriction H)) :
    K ⧸ E.commutatorPairingOrthogonal H ≃+ (H →+ Additive S) := by
  change K ⧸ (E.commutatorPairingRestriction H).ker ≃+
      (H →+ Additive S)
  exact QuotientAddGroup.quotientKerEquivOfSurjective
    (E.commutatorPairingRestriction H) hsurj

@[simp]
theorem quotientOrthogonalAddEquivOfSurjectiveRestriction_mk
    (E : ThetaExtension G S K) (H : AddSubgroup K)
    (hsurj : Function.Surjective (E.commutatorPairingRestriction H))
    (k : K) :
    E.quotientOrthogonalAddEquivOfSurjectiveRestriction H hsurj
      (QuotientAddGroup.mk' (E.commutatorPairingOrthogonal H) k) =
      E.commutatorPairingRestriction H k := by
  change (QuotientAddGroup.quotientKerEquivOfSurjective
      (E.commutatorPairingRestriction H) hsurj)
      (QuotientAddGroup.mk' (E.commutatorPairingRestriction H).ker k) =
      E.commutatorPairingRestriction H k
  rfl

@[simp]
theorem mem_commutatorPairingOrthogonal_iff
    (E : ThetaExtension G S K) (H : AddSubgroup K) (k : K) :
    k ∈ E.commutatorPairingOrthogonal H ↔
      ∀ h : H, E.commutatorPairing k h = 1 := by
  rw [commutatorPairingOrthogonal, AddMonoidHom.mem_ker]
  constructor
  · intro hk h
    have hh := DFunLike.congr_fun hk h
    change Additive.ofMul (E.commutatorPairing k h) = 0 at hh
    change E.commutatorPairing k h = 1 at hh
    exact hh
  · intro hk
    ext h
    change Additive.ofMul (E.commutatorPairing k h) = 0
    change E.commutatorPairing k h = 1
    exact hk h

/-! The orthogonal operation reverses subgroup inclusions and exchanges joins
with intersections.  These elementary lattice identities are useful when
building and comparing isotropic subgroups. -/

theorem commutatorPairingOrthogonal_anti
    (E : ThetaExtension G S K) {H J : AddSubgroup K} (hHJ : H ≤ J) :
    E.commutatorPairingOrthogonal J ≤ E.commutatorPairingOrthogonal H := by
  intro k hk
  rw [E.mem_commutatorPairingOrthogonal_iff J k] at hk
  rw [E.mem_commutatorPairingOrthogonal_iff H k]
  intro h
  exact hk ⟨h, hHJ h.property⟩

/- The skew symmetry makes orthogonality a Galois connection: either
   inclusion determines the corresponding inclusion in the opposite order. -/
theorem le_commutatorPairingOrthogonal_iff
    (E : ThetaExtension G S K) (H J : AddSubgroup K) :
    H ≤ E.commutatorPairingOrthogonal J ↔
      J ≤ E.commutatorPairingOrthogonal H := by
  constructor
  · intro h j hj
    rw [E.mem_commutatorPairingOrthogonal_iff H j]
    intro i
    have hp : E.commutatorPairing (i : K) j = 1 := by
      exact (E.mem_commutatorPairingOrthogonal_iff J (i : K)).mp
        (h i.property) ⟨j, hj⟩
    rw [E.commutatorPairing_swap, hp, inv_one]
  · intro h i hi
    rw [E.mem_commutatorPairingOrthogonal_iff J i]
    intro j
    have hp : E.commutatorPairing (j : K) i = 1 := by
      exact (E.mem_commutatorPairingOrthogonal_iff H (j : K)).mp
        (h j.property) ⟨i, hi⟩
    rw [E.commutatorPairing_swap, hp, inv_one]

theorem commutatorPairingOrthogonal_sup
    (E : ThetaExtension G S K) (H J : AddSubgroup K) :
    E.commutatorPairingOrthogonal (H ⊔ J) =
      E.commutatorPairingOrthogonal H ⊓
        E.commutatorPairingOrthogonal J := by
  apply le_antisymm
  · intro k hk
    rw [E.mem_commutatorPairingOrthogonal_iff (H ⊔ J) k] at hk
    rw [AddSubgroup.mem_inf]
    constructor
    · rw [E.mem_commutatorPairingOrthogonal_iff H k]
      intro h
      exact hk ⟨h, AddSubgroup.mem_sup_left h.property⟩
    · rw [E.mem_commutatorPairingOrthogonal_iff J k]
      intro h
      exact hk ⟨h, AddSubgroup.mem_sup_right h.property⟩
  · intro k hk
    rw [AddSubgroup.mem_inf] at hk
    rw [E.mem_commutatorPairingOrthogonal_iff (H ⊔ J) k]
    intro h
    rcases AddSubgroup.mem_sup.mp h.property with ⟨hH, hhH, hJ, hhJ, heq⟩
    have h1 := (E.mem_commutatorPairingOrthogonal_iff H k).mp hk.1 ⟨hH, hhH⟩
    have h2 := (E.mem_commutatorPairingOrthogonal_iff J k).mp hk.2 ⟨hJ, hhJ⟩
    rw [← heq, E.commutatorPairing_add_right, h1, h2, mul_one]

theorem commutatorPairingOrthogonal_top
    (E : ThetaExtension G S K) :
    E.commutatorPairingOrthogonal (⊤ : AddSubgroup K) =
      E.commutatorPairingRadical := by
  apply le_antisymm
  · intro k hk
    rw [E.mem_commutatorPairingOrthogonal_iff (⊤ : AddSubgroup K) k] at hk
    rw [E.mem_commutatorPairingRadical_iff k]
    intro l
    exact hk ⟨l, AddSubgroup.mem_top l⟩
  · intro k hk
    rw [E.mem_commutatorPairingRadical_iff k] at hk
    rw [E.mem_commutatorPairingOrthogonal_iff (⊤ : AddSubgroup K) k]
    intro l
    exact hk l

/-- Every element is orthogonal to the trivial subgroup. -/
@[simp]
theorem commutatorPairingOrthogonal_bot
    (E : ThetaExtension G S K) :
    E.commutatorPairingOrthogonal (⊥ : AddSubgroup K) =
      (⊤ : AddSubgroup K) := by
  apply AddSubgroup.ext
  intro k
  constructor
  · intro hk
    exact AddSubgroup.mem_top k
  · intro hk
    rw [E.mem_commutatorPairingOrthogonal_iff (⊥ : AddSubgroup K) k]
    intro h
    have hzero : (h : K) = 0 := by
      exact AddSubgroup.mem_bot.mp h.property
    rw [hzero, E.commutatorPairing_zero_right]

/-- A subgroup is isotropic when its pairing restricts trivially. -/
def IsIsotropic (E : ThetaExtension G S K) (H : AddSubgroup K) : Prop :=
  H ≤ E.commutatorPairingOrthogonal H

/-- The trivial subgroup is isotropic. -/
theorem isIsotropic_bot (E : ThetaExtension G S K) :
    E.IsIsotropic (⊥ : AddSubgroup K) := by
  rw [IsIsotropic, E.commutatorPairingOrthogonal_bot]
  exact bot_le

theorem isIsotropic_iff
    (E : ThetaExtension G S K) (H : AddSubgroup K) :
    E.IsIsotropic H ↔
      ∀ ⦃k⦄, k ∈ H → ∀ ⦃l⦄, l ∈ H →
        E.commutatorPairing k l = 1 := by
  constructor
  · intro h k hk l hl
    exact (E.mem_commutatorPairingOrthogonal_iff H k).mp (h hk) ⟨l, hl⟩
  · intro h k hk
    rw [E.mem_commutatorPairingOrthogonal_iff]
    intro l
    exact h hk l.property

/- The join of isotropic subgroups remains isotropic when the two subgroups
   are mutually orthogonal. -/
theorem isIsotropic_sup_of_isIsotropic
    (E : ThetaExtension G S K) (H J : AddSubgroup K)
    (hH : E.IsIsotropic H) (hJ : E.IsIsotropic J)
    (hHJ : H ≤ E.commutatorPairingOrthogonal J) :
    E.IsIsotropic (H ⊔ J) := by
  rw [E.isIsotropic_iff]
  intro a ha b hb
  rcases AddSubgroup.mem_sup.mp ha with ⟨aH, haH, aJ, haJ, rfl⟩
  rcases AddSubgroup.mem_sup.mp hb with ⟨bH, hbH, bJ, hbJ, rfl⟩
  have hHH : E.commutatorPairing aH bH = 1 :=
    (E.isIsotropic_iff H).mp hH haH hbH
  have hJJ : E.commutatorPairing aJ bJ = 1 :=
    (E.isIsotropic_iff J).mp hJ haJ hbJ
  have hHJ' : E.commutatorPairing aH bJ = 1 :=
    (E.mem_commutatorPairingOrthogonal_iff J aH).mp (hHJ haH) ⟨bJ, hbJ⟩
  have hJH : E.commutatorPairing aJ bH = 1 := by
    have h : E.commutatorPairing bH aJ = 1 :=
      (E.mem_commutatorPairingOrthogonal_iff J bH).mp (hHJ hbH) ⟨aJ, haJ⟩
    rw [E.commutatorPairing_swap, h, inv_one]
  rw [E.commutatorPairing_add_left, E.commutatorPairing_add_right,
    E.commutatorPairing_add_right, hHH, hHJ', hJH, hJJ]
  simp

/- A join is isotropic exactly when its two factors are isotropic and
   mutually orthogonal. -/
theorem isIsotropic_sup_iff
    (E : ThetaExtension G S K) (H J : AddSubgroup K) :
    E.IsIsotropic (H ⊔ J) ↔
      E.IsIsotropic H ∧ E.IsIsotropic J ∧
        H ≤ E.commutatorPairingOrthogonal J := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply (E.isIsotropic_iff H).2
      intro k hk l hl
      exact (E.isIsotropic_iff (H ⊔ J)).1 h
        (AddSubgroup.mem_sup_left hk) (AddSubgroup.mem_sup_left hl)
    · apply (E.isIsotropic_iff J).2
      intro k hk l hl
      exact (E.isIsotropic_iff (H ⊔ J)).1 h
        (AddSubgroup.mem_sup_right hk) (AddSubgroup.mem_sup_right hl)
    · intro k hk
      rw [E.mem_commutatorPairingOrthogonal_iff J k]
      intro j
      exact (E.isIsotropic_iff (H ⊔ J)).1 h
        (AddSubgroup.mem_sup_left hk) (AddSubgroup.mem_sup_right j.property)
  · rintro ⟨hH, hJ, hHJ⟩
    exact E.isIsotropic_sup_of_isIsotropic H J hH hJ hHJ

theorem commutatorPairing_zsmul_left
    (E : ThetaExtension G S K) (n : ℤ) (k l : K) :
    E.commutatorPairing (n • k) l = E.commutatorPairing k l ^ n := by
  have h := congrArg (fun f : K →+ Additive S => f l)
    (E.commutatorPairingBihom.map_zsmul n k)
  change Additive.ofMul (E.commutatorPairing (n • k) l) =
    n • Additive.ofMul (E.commutatorPairing k l) at h
  exact h

theorem commutatorPairing_zsmul_right
    (E : ThetaExtension G S K) (n : ℤ) (k l : K) :
    E.commutatorPairing k (n • l) = E.commutatorPairing k l ^ n := by
  have h := (E.commutatorPairingHom k).map_zsmul n l
  change Additive.ofMul (E.commutatorPairing k (n • l)) =
    n • Additive.ofMul (E.commutatorPairing k l) at h
  exact h

/-- An isotropic subgroup maximal under inclusion. -/
def IsMaximalIsotropic
    (E : ThetaExtension G S K) (H : AddSubgroup K) : Prop :=
  E.IsIsotropic H ∧
    ∀ J : AddSubgroup K, H ≤ J → E.IsIsotropic J → J ≤ H

/-- A finite theta quotient has a maximal isotropic subgroup. -/
theorem exists_isMaximalIsotropic
    (E : ThetaExtension G S K) [Finite K] :
    ∃ H : AddSubgroup K, E.IsMaximalIsotropic H := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (AddSubgroup K) := Finite.of_injective
    (fun H : AddSubgroup K => (H : Set K))
    SetLike.coe_injective
  obtain ⟨H, _, hH, hmax⟩ :=
    Finite.exists_le_maximal (p := fun H : AddSubgroup K => E.IsIsotropic H)
      (a := ⊥) E.isIsotropic_bot
  exact ⟨H, ⟨hH, fun J hHJ hJ => hmax hJ hHJ⟩⟩

/-- A maximal isotropic subgroup equals its commutator orthogonal. -/
theorem eq_commutatorPairingOrthogonal_of_isMaximalIsotropic
    (E : ThetaExtension G S K) (H : AddSubgroup K)
    (hmax : E.IsMaximalIsotropic H) :
    H = E.commutatorPairingOrthogonal H := by
  apply le_antisymm hmax.1
  intro k hk
  let J : AddSubgroup K := H ⊔ AddSubgroup.zmultiples k
  have hJ : E.IsIsotropic J := by
    rw [E.isIsotropic_iff]
    intro a ha b hb
    rcases AddSubgroup.mem_sup.mp ha with ⟨aH, haH, ak, hak, rfl⟩
    rcases AddSubgroup.mem_sup.mp hb with ⟨bH, hbH, bk, hbk, rfl⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp hak with ⟨n, rfl⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp hbk with ⟨m, rfl⟩
    have hHH : E.commutatorPairing aH bH = 1 :=
      (E.isIsotropic_iff H).mp hmax.1 haH hbH
    have hkH : E.commutatorPairing k bH = 1 :=
      (E.mem_commutatorPairingOrthogonal_iff H k).mp hk ⟨bH, hbH⟩
    have hHk : E.commutatorPairing aH k = 1 := by
      rw [← inv_eq_one, ← E.commutatorPairing_swap]
      exact (E.mem_commutatorPairingOrthogonal_iff H k).mp hk ⟨aH, haH⟩
    rw [E.commutatorPairing_add_left, E.commutatorPairing_add_right,
      E.commutatorPairing_add_right, E.commutatorPairing_zsmul_right,
      E.commutatorPairing_zsmul_left, E.commutatorPairing_zsmul_left,
      E.commutatorPairing_zsmul_right, hHH, hHk, hkH,
      E.commutatorPairing_self]
    simp
  apply hmax.2 J le_sup_left hJ
  exact (le_sup_right : AddSubgroup.zmultiples k ≤ J)
    (AddSubgroup.mem_zmultiples k)

/- A self-orthogonal subgroup is maximal isotropic, giving the converse to
   `eq_commutatorPairingOrthogonal_of_isMaximalIsotropic`. -/
theorem isMaximalIsotropic_iff_eq_commutatorPairingOrthogonal
    (E : ThetaExtension G S K) (H : AddSubgroup K) :
    E.IsMaximalIsotropic H ↔
      H = E.commutatorPairingOrthogonal H := by
  constructor
  · exact E.eq_commutatorPairingOrthogonal_of_isMaximalIsotropic H
  · intro hEq
    refine ⟨le_of_eq hEq, ?_⟩
    intro J hHJ hJ
    rw [hEq]
    intro j hj
    exact (E.commutatorPairingOrthogonal_anti hHJ) (hJ hj)

/-- A maximal isotropic subgroup identifies the quotient with its character
group whenever restriction of the commutator pairing is surjective. -/
noncomputable def quotientMaximalIsotropicAddEquiv
    (E : ThetaExtension G S K) (H : AddSubgroup K)
    (hmax : E.IsMaximalIsotropic H)
    (hsurj : Function.Surjective (E.commutatorPairingRestriction H)) :
    K ⧸ H ≃+ (H →+ Additive S) := by
  have hker : (E.commutatorPairingRestriction H).ker = H := by
    change E.commutatorPairingOrthogonal H = H
    exact (E.eq_commutatorPairingOrthogonal_of_isMaximalIsotropic H hmax).symm
  exact (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (E.commutatorPairingRestriction H) hsurj)

@[simp]
theorem quotientMaximalIsotropicAddEquiv_mk
    (E : ThetaExtension G S K) (H : AddSubgroup K)
    (hmax : E.IsMaximalIsotropic H)
    (hsurj : Function.Surjective (E.commutatorPairingRestriction H))
    (k : K) :
    E.quotientMaximalIsotropicAddEquiv H hmax hsurj
      (QuotientAddGroup.mk' H k) =
      E.commutatorPairingRestriction H k := by
  rfl

/-- The cardinality of the quotient by an orthogonal subgroup is the
cardinality of the character image whenever the restricted pairing is
surjective. -/
theorem natCard_eq_orthogonal_mul_character_of_surjective_restriction
    (E : ThetaExtension G S K) (H : AddSubgroup K)
    (hsurj : Function.Surjective (E.commutatorPairingRestriction H)) :
    Nat.card K =
      Nat.card (E.commutatorPairingOrthogonal H) *
        Nat.card (H →+ Additive S) := by
  calc
    Nat.card K =
        Nat.card (K ⧸ E.commutatorPairingOrthogonal H) *
          Nat.card (E.commutatorPairingOrthogonal H) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (E.commutatorPairingOrthogonal H)
    _ = Nat.card (H →+ Additive S) *
          Nat.card (E.commutatorPairingOrthogonal H) := by
      let e : K ⧸ (E.commutatorPairingRestriction H).ker ≃+
          (H →+ Additive S) :=
        QuotientAddGroup.quotientKerEquivOfSurjective
          (E.commutatorPairingRestriction H) hsurj
      have hc :
          Nat.card (K ⧸ E.commutatorPairingOrthogonal H) =
            Nat.card (H →+ Additive S) := by
        apply Nat.card_congr
        simpa only [commutatorPairingOrthogonal] using e.toEquiv
      rw [hc]
    _ = Nat.card (E.commutatorPairingOrthogonal H) *
        Nat.card (H →+ Additive S) := by rw [Nat.mul_comm]

/-- A maximal isotropic subgroup has square order when restriction of the
commutator pairing realizes all of its characters and finite character duality
preserves cardinality. -/
theorem natCard_eq_square_of_isMaximalIsotropic
    (E : ThetaExtension G S K) (H : AddSubgroup K)
    (hmax : E.IsMaximalIsotropic H)
    (hsurj : Function.Surjective (E.commutatorPairingRestriction H))
    (hdual : Nat.card (H →+ Additive S) = Nat.card H) :
    Nat.card K = Nat.card H ^ 2 := by
  calc
    Nat.card K = Nat.card (K ⧸ H) * Nat.card H :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
    _ = Nat.card (H →+ Additive S) * Nat.card H := by
      rw [Nat.card_congr
        (E.quotientMaximalIsotropicAddEquiv H hmax hsurj).toEquiv]
    _ = Nat.card H ^ 2 := by rw [hdual, pow_two]

end ThetaExtension
end Mumford
