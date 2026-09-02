/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.Theta

/-!
# Factor sets of theta extensions

A normalized section of an abstract theta extension identifies its underlying
set with scalar-section coordinates.  The resulting factor set satisfies the
multiplicative two-cocycle identity, gives the twisted coordinate group law,
and recovers the commutator pairing by antisymmetrization.

This is the group-theoretic content of the factor-set description.  It does not
assert that a geometric theta group is globally split as a group scheme.
-/

set_option autoImplicit false

open scoped commutatorElement

universe u v w

namespace Mumford
namespace ThetaExtension

variable {G : Type u} {S : Type v} {K : Type w}
  [Group G] [CommGroup S] [AddCommGroup K] (E : ThetaExtension G S K)

/-- A quotient section normalized to take zero to the identity. -/
noncomputable def normalizedQuotientLift (k : K) : G := by
  classical
  exact if k = 0 then 1 else E.quotientLift k

@[simp]
theorem normalizedQuotientLift_zero :
    E.normalizedQuotientLift (0 : K) = 1 := by
  simp [normalizedQuotientLift]

@[simp]
theorem quotientHom_normalizedQuotientLift (k : K) :
    E.quotientHom (E.normalizedQuotientLift k) = Multiplicative.ofAdd k := by
  classical
  by_cases hk : k = 0
  · subst k
    simp
  · simp [normalizedQuotientLift, hk, E.quotientHom_quotientLift]

@[simp]
theorem quotient_normalizedQuotientLift (k : K) :
    E.quotient (E.normalizedQuotientLift k) = k := by
  unfold quotient
  rw [E.quotientHom_normalizedQuotientLift]
  rfl

/-- Two section values differ from the section value of the sum by a unique
scalar. -/
theorem exists_factorSet_scalar (k l : K) :
    ∃ s : S, E.normalizedQuotientLift k * E.normalizedQuotientLift l =
      E.includeScalar s * E.normalizedQuotientLift (k + l) := by
  have hk : E.normalizedQuotientLift k * E.normalizedQuotientLift l *
      (E.normalizedQuotientLift (k + l))⁻¹ ∈ E.quotientHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      E.quotientHom_normalizedQuotientLift,
      E.quotientHom_normalizedQuotientLift,
      E.quotientHom_normalizedQuotientLift]
    rw [← ofAdd_neg, ← ofAdd_add, ← ofAdd_add]
    simp
  obtain ⟨s, hs⟩ := (E.mem_quotientHom_ker_iff
    (E.normalizedQuotientLift k * E.normalizedQuotientLift l *
      (E.normalizedQuotientLift (k + l))⁻¹)).mp hk
  refine ⟨s, ?_⟩
  calc
    E.normalizedQuotientLift k * E.normalizedQuotientLift l =
        (E.normalizedQuotientLift k * E.normalizedQuotientLift l *
          (E.normalizedQuotientLift (k + l))⁻¹) *
            E.normalizedQuotientLift (k + l) := by simp
    _ = E.includeScalar s * E.normalizedQuotientLift (k + l) := by rw [← hs]

/-- The normalized scalar factor attached to the chosen quotient section. -/
noncomputable def factorSet (k l : K) : S :=
  Classical.choose (E.exists_factorSet_scalar k l)

/-- Multiplication of section values is twisted by the factor set. -/
theorem normalizedQuotientLift_mul (k l : K) :
    E.normalizedQuotientLift k * E.normalizedQuotientLift l =
      E.includeScalar (E.factorSet k l) * E.normalizedQuotientLift (k + l) :=
  Classical.choose_spec (E.exists_factorSet_scalar k l)

@[simp]
theorem factorSet_zero_left (k : K) : E.factorSet 0 k = 1 := by
  apply E.includeScalar_injective
  apply mul_right_cancel (b := E.normalizedQuotientLift k)
  simpa using (E.normalizedQuotientLift_mul 0 k).symm

@[simp]
theorem factorSet_zero_right (k : K) : E.factorSet k 0 = 1 := by
  apply E.includeScalar_injective
  apply mul_right_cancel (b := E.normalizedQuotientLift k)
  simpa using (E.normalizedQuotientLift_mul k 0).symm

/-- The factor set satisfies the multiplicative two-cocycle identity. -/
theorem factorSet_cocycle (k l m : K) :
    E.factorSet (k + l) m * E.factorSet k l =
      E.factorSet k (l + m) * E.factorSet l m := by
  have hc : E.factorSet k l * E.factorSet (k + l) m =
      E.factorSet l m * E.factorSet k (l + m) := by
    apply E.includeScalar_injective
    apply mul_right_cancel (b := E.normalizedQuotientLift (k + l + m))
    calc
      E.includeScalar (E.factorSet k l * E.factorSet (k + l) m) *
          E.normalizedQuotientLift (k + l + m) =
          E.includeScalar (E.factorSet k l) *
            (E.includeScalar (E.factorSet (k + l) m) *
              E.normalizedQuotientLift (k + l + m)) := by
                rw [map_mul, mul_assoc]
      _ = E.includeScalar (E.factorSet k l) *
            (E.normalizedQuotientLift (k + l) * E.normalizedQuotientLift m) :=
              congrArg (fun x : G => E.includeScalar (E.factorSet k l) * x)
                (E.normalizedQuotientLift_mul (k + l) m).symm
      _ = (E.includeScalar (E.factorSet k l) *
            E.normalizedQuotientLift (k + l)) * E.normalizedQuotientLift m :=
              (mul_assoc _ _ _).symm
      _ = (E.normalizedQuotientLift k * E.normalizedQuotientLift l) *
            E.normalizedQuotientLift m :=
              congrArg (fun x : G => x * E.normalizedQuotientLift m)
                (E.normalizedQuotientLift_mul k l).symm
      _ = E.normalizedQuotientLift k *
            (E.normalizedQuotientLift l * E.normalizedQuotientLift m) :=
              mul_assoc _ _ _
      _ = E.normalizedQuotientLift k *
            (E.includeScalar (E.factorSet l m) * E.normalizedQuotientLift (l + m)) :=
              congrArg (fun x : G => E.normalizedQuotientLift k * x)
                (E.normalizedQuotientLift_mul l m)
      _ = (E.normalizedQuotientLift k * E.includeScalar (E.factorSet l m)) *
            E.normalizedQuotientLift (l + m) := (mul_assoc _ _ _).symm
      _ = (E.includeScalar (E.factorSet l m) * E.normalizedQuotientLift k) *
            E.normalizedQuotientLift (l + m) := by
              rw [(E.includeScalar_commute (E.factorSet l m)
                (E.normalizedQuotientLift k)).eq.symm]
      _ = E.includeScalar (E.factorSet l m) *
            (E.normalizedQuotientLift k * E.normalizedQuotientLift (l + m)) :=
              mul_assoc _ _ _
      _ = E.includeScalar (E.factorSet l m) *
            (E.includeScalar (E.factorSet k (l + m)) *
              E.normalizedQuotientLift (k + (l + m))) :=
              congrArg (fun x : G => E.includeScalar (E.factorSet l m) * x)
                (E.normalizedQuotientLift_mul k (l + m))
      _ = E.includeScalar (E.factorSet l m * E.factorSet k (l + m)) *
            E.normalizedQuotientLift (k + l + m) := by
              rw [map_mul, add_assoc, mul_assoc]
  simpa [mul_comm] using hc

/-- Scalar-section coordinates for the extension. -/
noncomputable def sectionCoordinates (p : S × K) : G :=
  E.includeScalar p.1 * E.normalizedQuotientLift p.2

/-! The chosen section gives unique scalar/quotient coordinates. -/

theorem sectionCoordinates_injective :
    Function.Injective E.sectionCoordinates := by
  intro p q h
  rcases p with ⟨s, k⟩
  rcases q with ⟨t, l⟩
  change E.includeScalar s * E.normalizedQuotientLift k =
    E.includeScalar t * E.normalizedQuotientLift l at h
  have hquot := congrArg E.quotient h
  have hkl : k = l := by
    simpa using hquot
  subst l
  have hscalar : E.includeScalar s = E.includeScalar t := by
    exact mul_right_cancel h
  have hst : s = t := E.includeScalar_injective hscalar
  simp [hst]

/-- The group law in scalar-section coordinates is twisted by the factor set. -/
theorem sectionCoordinates_mul (s t : S) (k l : K) :
    E.sectionCoordinates (s, k) * E.sectionCoordinates (t, l) =
      E.sectionCoordinates (s * t * E.factorSet k l, k + l) := by
  unfold sectionCoordinates
  dsimp only
  calc
    (E.includeScalar s * E.normalizedQuotientLift k) *
        (E.includeScalar t * E.normalizedQuotientLift l) =
      E.includeScalar s *
        (E.normalizedQuotientLift k * E.includeScalar t) *
          E.normalizedQuotientLift l := by simp only [mul_assoc]
    _ = E.includeScalar s *
        (E.includeScalar t * E.normalizedQuotientLift k) *
          E.normalizedQuotientLift l := by
            rw [(E.includeScalar_commute t
              (E.normalizedQuotientLift k)).eq.symm]
    _ = (E.includeScalar s * E.includeScalar t) *
        (E.normalizedQuotientLift k * E.normalizedQuotientLift l) := by
          simp only [mul_assoc]
    _ = E.includeScalar (s * t) *
        (E.includeScalar (E.factorSet k l) *
          E.normalizedQuotientLift (k + l)) := by
            rw [map_mul, ← E.normalizedQuotientLift_mul]
    _ = E.includeScalar (s * t * E.factorSet k l) *
        E.normalizedQuotientLift (k + l) := by
          simp only [map_mul, mul_assoc]

private theorem commutatorPairing_eq_factorSet_div_of_section
    (E : ThetaExtension G S K) (σ : K → G)
    (hσ : ∀ k, E.quotientHom (σ k) = Multiplicative.ofAdd k)
    (f : K → K → S)
    (hf : ∀ k l, σ k * σ l = E.includeScalar (f k l) * σ (k + l))
    (k l : K) : E.commutatorPairing k l = f k l * (f l k)⁻¹ := by
  have hq (a : K) : E.quotient (σ a) = a := by
    unfold quotient
    rw [hσ]
    rfl
  have hpair : E.commutatorPairing k l = E.commutatorScalar (σ k) (σ l) := by
    have h := E.commutatorPairing_quotient_eq_commutatorScalar (σ k) (σ l)
    rw [hq k, hq l] at h
    exact h
  rw [hpair]
  apply E.includeScalar_injective
  rw [E.includeScalar_commutatorScalar, map_mul, map_inv]
  have htwist : σ k * σ l =
      E.includeScalar (f k l * (f l k)⁻¹) * (σ l * σ k) := by
    calc
      σ k * σ l = E.includeScalar (f k l) * σ (k + l) := hf k l
      _ = E.includeScalar (f k l) * σ (l + k) := by rw [add_comm]
      _ = E.includeScalar (f k l) *
          ((E.includeScalar (f l k))⁻¹ *
            (E.includeScalar (f l k) * σ (l + k))) := by simp
      _ = E.includeScalar (f k l) *
          ((E.includeScalar (f l k))⁻¹ * (σ l * σ k)) := by
            rw [← hf l k]
      _ = E.includeScalar (f k l * (f l k)⁻¹) * (σ l * σ k) := by
            simp only [map_mul, map_inv, mul_assoc]
  rw [commutatorElement_def, htwist]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  simp only [map_mul, map_inv]

/-- The commutator pairing is the antisymmetrization of the factor set. -/
theorem commutatorPairing_eq_factorSet_div (k l : K) :
    E.commutatorPairing k l = E.factorSet k l * (E.factorSet l k)⁻¹ :=
  commutatorPairing_eq_factorSet_div_of_section E
    E.normalizedQuotientLift E.quotientHom_normalizedQuotientLift
    E.factorSet E.normalizedQuotientLift_mul k l

/-- Every set-theoretic quotient section differs from the normalized chosen
section by a scalar. -/
theorem exists_sectionScalar
    (σ : K → G)
    (hσ : ∀ k, E.quotientHom (σ k) = Multiplicative.ofAdd k)
    (k : K) :
    ∃ c : S, σ k = E.includeScalar c * E.normalizedQuotientLift k := by
  have hk : σ k * (E.normalizedQuotientLift k)⁻¹ ∈ E.quotientHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ,
      E.quotientHom_normalizedQuotientLift]
    simp
  obtain ⟨c, hc⟩ :=
    (E.mem_quotientHom_ker_iff
      (σ k * (E.normalizedQuotientLift k)⁻¹)).mp hk
  refine ⟨c, ?_⟩
  calc
    σ k = (σ k * (E.normalizedQuotientLift k)⁻¹) *
        E.normalizedQuotientLift k := by simp
    _ = E.includeScalar c * E.normalizedQuotientLift k := by rw [← hc]

/-- The scalar one-cochain comparing a quotient section with the normalized
chosen section. -/
noncomputable def sectionScalar
    (σ : K → G)
    (hσ : ∀ k, E.quotientHom (σ k) = Multiplicative.ofAdd k)
    (k : K) : S :=
  Classical.choose (E.exists_sectionScalar σ hσ k)

theorem section_eq_includeScalar_sectionScalar_mul
    (σ : K → G)
    (hσ : ∀ k, E.quotientHom (σ k) = Multiplicative.ofAdd k)
    (k : K) :
    σ k = E.includeScalar (E.sectionScalar σ hσ k) *
      E.normalizedQuotientLift k :=
  Classical.choose_spec (E.exists_sectionScalar σ hσ k)

/-- Changing the quotient section changes its factor set by the coboundary of
the scalar comparison cochain. -/
theorem factorSet_change_of_section
    (σ : K → G)
    (hσ : ∀ k, E.quotientHom (σ k) = Multiplicative.ofAdd k)
    (f : K → K → S)
    (hf : ∀ k l, σ k * σ l = E.includeScalar (f k l) * σ (k + l))
    (k l : K) :
    f k l =
      E.sectionScalar σ hσ k * E.sectionScalar σ hσ l *
        E.factorSet k l * (E.sectionScalar σ hσ (k + l))⁻¹ := by
  let c : K → S := E.sectionScalar σ hσ
  have hc (a : K) :
      σ a = E.includeScalar (c a) * E.normalizedQuotientLift a :=
    E.section_eq_includeScalar_sectionScalar_mul σ hσ a
  have hscalar :
      f k l * c (k + l) = c k * c l * E.factorSet k l := by
    apply E.includeScalar_injective
    apply mul_right_cancel (b := E.normalizedQuotientLift (k + l))
    calc
      E.includeScalar (f k l * c (k + l)) *
          E.normalizedQuotientLift (k + l) =
        E.includeScalar (f k l) *
          (E.includeScalar (c (k + l)) *
            E.normalizedQuotientLift (k + l)) := by
              rw [map_mul, mul_assoc]
      _ = E.includeScalar (f k l) * σ (k + l) :=
        congrArg (fun x : G => E.includeScalar (f k l) * x)
          (hc (k + l)).symm
      _ = σ k * σ l := (hf k l).symm
      _ = E.sectionCoordinates (c k, k) *
          E.sectionCoordinates (c l, l) := by
            rw [hc k, hc l]
            rfl
      _ = E.sectionCoordinates
          (c k * c l * E.factorSet k l, k + l) :=
        E.sectionCoordinates_mul (c k) (c l) k l
      _ = E.includeScalar (c k * c l * E.factorSet k l) *
          E.normalizedQuotientLift (k + l) := rfl
  change f k l = c k * c l * E.factorSet k l * (c (k + l))⁻¹
  calc
    f k l = (f k l * c (k + l)) * (c (k + l))⁻¹ := by simp
    _ = (c k * c l * E.factorSet k l) * (c (k + l))⁻¹ := by
      rw [hscalar]

end ThetaExtension
end Mumford
