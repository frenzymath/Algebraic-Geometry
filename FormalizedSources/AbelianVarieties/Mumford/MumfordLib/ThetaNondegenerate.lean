/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.Theta
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Theta nondegeneracy

The commutator radical, injectivity of the bihomomorphism, and the scalar
center condition give equivalent formulations of nondegeneracy.
-/

set_option autoImplicit false

namespace Mumford

universe u v w

namespace ThetaExtension

variable {G : Type u} {S : Type v} {K : Type w}
  [Group G] [CommGroup S] [AddCommGroup K] (E : ThetaExtension G S K)

/-- The theta commutator pairing is nondegenerate when its radical is trivial. -/
def IsNondegenerate : Prop := E.commutatorPairingRadical = ⊥

theorem isNondegenerate_iff_commutatorPairingBihom_injective :
    E.IsNondegenerate ↔ Function.Injective E.commutatorPairingBihom := by
  unfold IsNondegenerate
  constructor
  · intro h
    apply (AddMonoidHom.ker_eq_bot_iff E.commutatorPairingBihom).mp
    rw [E.commutatorPairingBihom_ker_eq_radical, h]
  · intro h
    rw [← E.commutatorPairingBihom_ker_eq_radical]
    exact (AddMonoidHom.ker_eq_bot_iff E.commutatorPairingBihom).mpr h

theorem commutatorPairingBihom_injective (hE : E.IsNondegenerate) :
    Function.Injective E.commutatorPairingBihom :=
  (E.isNondegenerate_iff_commutatorPairingBihom_injective).mp hE

theorem center_eq_includeScalar_range_of_isNondegenerate
    (hE : E.IsNondegenerate) :
    Subgroup.center G = E.includeScalar.range :=
  E.center_eq_includeScalar_range_of_commutatorPairingRadical_eq_bot hE

theorem isNondegenerate_iff_center_eq_includeScalar_range :
    E.IsNondegenerate ↔ Subgroup.center G = E.includeScalar.range := by
  constructor
  · intro hE
    exact E.center_eq_includeScalar_range_of_isNondegenerate hE
  · intro hcenter
    unfold IsNondegenerate
    apply (AddSubgroup.eq_bot_iff_forall E.commutatorPairingRadical).mpr
    intro k hk
    have hq : E.quotient (E.quotientLift k) = k := by
      unfold quotient
      rw [E.quotientHom_quotientLift]
      rfl
    have hcentral : E.quotientLift k ∈ Subgroup.center G := by
      apply (E.mem_center_iff_mem_commutatorPairingRadical _).mpr
      rw [hq]
      exact hk
    rw [hcenter] at hcentral
    obtain ⟨s, hs⟩ := hcentral
    have hqzero : E.quotient (E.quotientLift k) = 0 := by
      rw [← hs, E.quotient_includeScalar]
    exact hq.symm.trans hqzero

/-! For a finite quotient whose character group has the same cardinality,
nondegeneracy upgrades the commutator map from injective to bijective. -/

theorem commutatorPairingBihom_bijective_of_isNondegenerate
    [Finite K] [Finite (K →+ Additive S)]
    (hcard : Nat.card K = Nat.card (K →+ Additive S))
    (hE : E.IsNondegenerate) :
    Function.Bijective E.commutatorPairingBihom := by
  have hinj := E.commutatorPairingBihom_injective hE
  let e : K ≃ (K →+ Additive S) :=
    Classical.choice ((Finite.card_eq).mp hcard)
  exact ⟨hinj, (Finite.injective_iff_surjective_of_equiv e).mp hinj⟩

theorem isNondegenerate_iff_commutatorPairingBihom_bijective
    [Finite K] [Finite (K →+ Additive S)]
    (hcard : Nat.card K = Nat.card (K →+ Additive S)) :
    E.IsNondegenerate ↔ Function.Bijective E.commutatorPairingBihom := by
  constructor
  · exact E.commutatorPairingBihom_bijective_of_isNondegenerate hcard
  · intro hbij
    exact E.isNondegenerate_iff_commutatorPairingBihom_injective.mpr hbij.1

/-- Under finite character duality, the scalar-center condition is equivalent
to the commutator map being an isomorphism of the underlying finite groups. -/
theorem center_eq_includeScalar_range_iff_commutatorPairingBihom_bijective
    [Finite K] [Finite (K →+ Additive S)]
    (hcard : Nat.card K = Nat.card (K →+ Additive S)) :
    Subgroup.center G = E.includeScalar.range ↔
      Function.Bijective E.commutatorPairingBihom :=
  E.isNondegenerate_iff_center_eq_includeScalar_range.symm.trans
    (E.isNondegenerate_iff_commutatorPairingBihom_bijective hcard)

/-- A nondegenerate finite theta commutator identifies the quotient with its
character group. -/
noncomputable def commutatorPairingAddEquiv
    [Finite K] [Finite (K →+ Additive S)]
    (hcard : Nat.card K = Nat.card (K →+ Additive S))
    (hE : E.IsNondegenerate) :
    K ≃+ (K →+ Additive S) :=
  AddEquiv.ofBijective E.commutatorPairingBihom
    (E.commutatorPairingBihom_bijective_of_isNondegenerate hcard hE)

end ThetaExtension

end Mumford
