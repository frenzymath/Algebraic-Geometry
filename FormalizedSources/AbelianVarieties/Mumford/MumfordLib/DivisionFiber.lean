/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.Uniformization
import MumfordLib.ComplexUniformization

/-!
# Fibres of multiplication by a nonzero integer

For a divisible additive group, every nonempty fibre of the map `[n]` is a
torsor under the subgroup killed by `n`.  This is the elementary group-theory
form of the finite-division-point statement used by the analytic theory.
-/

namespace Mumford
namespace Uniformization

noncomputable section

/-- The fibre of multiplication by `n` over `x`, as a subtype. -/
abbrev zsmulDivisionFiber (X : Type*) [AddCommGroup X] (n : ℤ) (x : X) :=
  {y : X // n • y = x}

/-- Translation by a chosen divided point identifies torsion with a division
fibre. -/
noncomputable def zsmulDivisionFiberEquiv
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x : X) (hn : n ≠ 0) :
    zsmulTorsionSubgroup X n ≃ zsmulDivisionFiber X n x := by
  let d : X := DivisibleBy.div x n
  let f : zsmulTorsionSubgroup X n → zsmulDivisionFiber X n x := fun t =>
    ⟨(t : X) + d, by
      rw [zsmul_add, t.property, zero_add, DivisibleBy.div_cancel x hn]⟩
  let g : zsmulDivisionFiber X n x → zsmulTorsionSubgroup X n := fun y =>
    ⟨(y : X) - d, by
      change n • ((y : X) - d) = 0
      rw [zsmul_sub, y.property, DivisibleBy.div_cancel x hn, sub_self]⟩
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro t
        apply Subtype.ext
        dsimp [f, g, d]
        exact add_sub_cancel_right (t : X) (DivisibleBy.div x n)
      right_inv := by
        intro y
        apply Subtype.ext
        dsimp [f, g, d]
        exact sub_add_cancel (y : X) (DivisibleBy.div x n) }

@[simp]
theorem zsmulDivisionFiberEquiv_apply
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x : X) (hn : n ≠ 0) (t : zsmulTorsionSubgroup X n) :
    ((zsmulDivisionFiberEquiv n x hn) t : X) =
      (t : X) + DivisibleBy.div x n := by
  rfl

@[simp]
theorem zsmulDivisionFiberEquiv_symm_apply
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x : X) (hn : n ≠ 0) (y : zsmulDivisionFiber X n x) :
    ((zsmulDivisionFiberEquiv n x hn).symm y : X) =
      (y : X) - DivisibleBy.div x n := by
  rfl

/-- Translation through the common torsion subgroup identifies any two
nonzero-integer division fibres. -/
noncomputable def zsmulDivisionFiberEquivBetween
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x y : X) (hn : n ≠ 0) :
    zsmulDivisionFiber X n x ≃ zsmulDivisionFiber X n y :=
  (zsmulDivisionFiberEquiv n x hn).symm.trans
    (zsmulDivisionFiberEquiv n y hn)

@[simp]
theorem zsmulDivisionFiberEquivBetween_apply
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x y : X) (hn : n ≠ 0)
    (a : zsmulDivisionFiber X n x) :
    ((zsmulDivisionFiberEquivBetween n x y hn) a : X) =
      (a : X) - DivisibleBy.div x n + DivisibleBy.div y n := by
  rfl

@[simp]
theorem zsmulDivisionFiberEquivBetween_refl
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x : X) (hn : n ≠ 0) :
    zsmulDivisionFiberEquivBetween n x x hn = Equiv.refl _ := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  simp

@[simp]
theorem zsmulDivisionFiberEquivBetween_symm
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x y : X) (hn : n ≠ 0) :
    (zsmulDivisionFiberEquivBetween n x y hn).symm =
      zsmulDivisionFiberEquivBetween n y x hn := by
  rfl

theorem zsmulDivisionFiberEquivBetween_trans
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x y z : X) (hn : n ≠ 0) :
    (zsmulDivisionFiberEquivBetween n x y hn).trans
        (zsmulDivisionFiberEquivBetween n y z hn) =
      zsmulDivisionFiberEquivBetween n x z hn := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  simp only [Equiv.trans_apply, zsmulDivisionFiberEquivBetween_apply]
  abel

/- Two points in one nonzero-integer division fibre differ by a unique
   torsion point.  This is the pointwise torsor law behind the fibre
   equivalences above. -/
theorem existsUnique_zsmulTorsion_add_eq
    {X : Type*} [AddCommGroup X]
    {n : ℤ} {x : X} (p q : zsmulDivisionFiber X n x) :
    ∃! t : zsmulTorsionSubgroup X n,
      (t : X) + (p : X) = (q : X) := by
  let t : zsmulTorsionSubgroup X n :=
    ⟨(q : X) - (p : X), by
      change n • ((q : X) - (p : X)) = 0
      rw [zsmul_sub, q.property, p.property, sub_self]⟩
  have ht : (t : X) + (p : X) = (q : X) := by
    change ((q : X) - (p : X)) + (p : X) = (q : X)
    exact sub_add_cancel _ _
  refine ⟨t, ht, ?_⟩
  intro s hs
  apply Subtype.ext
  apply add_right_cancel (b := (p : X))
  exact hs.trans ht.symm

/-- All fibres of multiplication by a fixed nonzero integer have the same
cardinality in a divisible group. -/
theorem zsmulDivisionFiber_card_eq
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x y : X) (hn : n ≠ 0) :
    Nat.card (zsmulDivisionFiber X n x) =
      Nat.card (zsmulDivisionFiber X n y) := by
  exact Nat.card_congr (zsmulDivisionFiberEquivBetween n x y hn)

/-- Finiteness of one nonzero-integer division fibre is equivalent to
finiteness of every other fibre. -/
theorem zsmulDivisionFiber_finite_iff_finite
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x y : X) (hn : n ≠ 0) :
    Finite (zsmulDivisionFiber X n x) ↔
      Finite (zsmulDivisionFiber X n y) :=
  Equiv.finite_iff (zsmulDivisionFiberEquivBetween n x y hn)

/-- All nonzero-integer division fibres have the cardinality of torsion. -/
theorem zsmulDivisionFiber_card
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x : X) (hn : n ≠ 0) :
    Nat.card (zsmulDivisionFiber X n x) =
      Nat.card (zsmulTorsionSubgroup X n) := by
  exact Nat.card_congr (zsmulDivisionFiberEquiv n x hn).symm

/-- Every nonzero-integer division fibre is inhabited in a divisible group. -/
theorem zsmulDivisionFiber_nonempty
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x : X) (hn : n ≠ 0) :
    Nonempty (zsmulDivisionFiber X n x) := by
  refine ⟨⟨DivisibleBy.div x n, ?_⟩⟩
  exact DivisibleBy.div_cancel x hn

/-- Finiteness of a nonzero-integer division fibre is equivalent to finiteness
of the corresponding torsion subgroup. -/
theorem zsmulDivisionFiber_finite_iff
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    (n : ℤ) (x : X) (hn : n ≠ 0) :
    Finite (zsmulDivisionFiber X n x) ↔
      Finite (zsmulTorsionSubgroup X n) :=
  (Equiv.finite_iff (zsmulDivisionFiberEquiv n x hn)).symm

/-- Positive-natural specialization of the elementary fibre cardinality
interface. -/
theorem zsmulDivisionFiber_natCast_card
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    {n : ℕ} (x : X) (hn : 0 < n) :
    Nat.card (zsmulDivisionFiber X (n : ℤ) x) =
      Nat.card (zsmulTorsionSubgroup X (n : ℤ)) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  exact zsmulDivisionFiber_card (n : ℤ) x hne

/-- Positive-natural specialization of fibre inhabitation. -/
theorem zsmulDivisionFiber_natCast_nonempty
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    {n : ℕ} (x : X) (hn : 0 < n) :
    Nonempty (zsmulDivisionFiber X (n : ℤ) x) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  exact zsmulDivisionFiber_nonempty (n : ℤ) x hne

/-- Positive-natural specialization of the fibre/torsion finiteness
equivalence. -/
theorem zsmulDivisionFiber_natCast_finite_iff
    {X : Type*} [AddCommGroup X] [DivisibleBy X ℤ]
    {n : ℕ} (x : X) (hn : 0 < n) :
    Finite (zsmulDivisionFiber X (n : ℤ) x) ↔
      Finite (zsmulTorsionSubgroup X (n : ℤ)) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  exact zsmulDivisionFiber_finite_iff (n : ℤ) x hne

/-- Under a genus-torus uniformization, every nonzero-integer division fibre
has cardinality `|n|^(2g)`. -/
theorem zsmulDivisionFiber_card_of_uniformization
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) (n : ℤ) (x : X) (hn : n ≠ 0) :
    Nat.card (zsmulDivisionFiber X n x) = n.natAbs ^ (2 * g) := by
  letI : DivisibleBy X ℤ := divisibleBy_of_uniformization u
  rw [zsmulDivisionFiber_card n x hn]
  exact zsmulTorsion_card_of_uniformization u hn

/-- Under a genus-torus uniformization, every nonzero-integer division fibre
is finite. -/
theorem zsmulDivisionFiber_finite_of_uniformization
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) (n : ℤ) (x : X) (hn : n ≠ 0) :
    Finite (zsmulDivisionFiber X n x) := by
  letI : DivisibleBy X ℤ := divisibleBy_of_uniformization u
  have ht : Finite (zsmulTorsionSubgroup X n) :=
    zsmulTorsion_finite_of_uniformization u hn
  exact (zsmulDivisionFiberEquiv n x hn).finite_iff.mp ht

/-- The positive-natural division-fibre cardinality under a genus-torus
uniformization. -/
theorem zsmulDivisionFiber_natCast_card_of_uniformization
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : GenusTorusUniformization X g) (x : X) (hn : 0 < n) :
    Nat.card (zsmulDivisionFiber X (n : ℤ) x) = n ^ (2 * g) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  simpa using zsmulDivisionFiber_card_of_uniformization u (n : ℤ) x hne

/-- The positive-natural division fibres are finite under a genus-torus
uniformization. -/
theorem zsmulDivisionFiber_natCast_finite_of_uniformization
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : GenusTorusUniformization X g) (x : X) (hn : 0 < n) :
    Finite (zsmulDivisionFiber X (n : ℤ) x) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  exact zsmulDivisionFiber_finite_of_uniformization u (n : ℤ) x hne

/-- The positive-natural division fibres are inhabited under a genus-torus
uniformization. -/
theorem zsmulDivisionFiber_natCast_nonempty_of_uniformization
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : GenusTorusUniformization X g) (x : X) (hn : 0 < n) :
    Nonempty (zsmulDivisionFiber X (n : ℤ) x) := by
  letI : DivisibleBy X ℤ := divisibleBy_of_uniformization u
  exact zsmulDivisionFiber_natCast_nonempty x hn

/-- The same division-fibre cardinality for a complex uniformization witness. -/
theorem zsmulDivisionFiber_card_of_complex_uniformization
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) (n : ℤ) (x : X) (hn : n ≠ 0) :
    Nat.card (zsmulDivisionFiber X n x) = n.natAbs ^ (2 * g) := by
  exact zsmulDivisionFiber_card_of_uniformization
    u.toGenusTorusUniformization n x hn

/-- The same division-fibre finiteness for a complex uniformization witness. -/
theorem zsmulDivisionFiber_finite_of_complex_uniformization
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) (n : ℤ) (x : X) (hn : n ≠ 0) :
    Finite (zsmulDivisionFiber X n x) := by
  exact zsmulDivisionFiber_finite_of_uniformization
    u.toGenusTorusUniformization n x hn

/-- The positive-natural division-fibre cardinality for a complex
uniformization witness. -/
theorem zsmulDivisionFiber_natCast_card_of_complex_uniformization
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : ComplexTorusUniformization X g) (x : X) (hn : 0 < n) :
    Nat.card (zsmulDivisionFiber X (n : ℤ) x) = n ^ (2 * g) := by
  exact zsmulDivisionFiber_natCast_card_of_uniformization
    u.toGenusTorusUniformization x hn

/-- The positive-natural division fibres are finite for a complex
uniformization witness. -/
theorem zsmulDivisionFiber_natCast_finite_of_complex_uniformization
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : ComplexTorusUniformization X g) (x : X) (hn : 0 < n) :
    Finite (zsmulDivisionFiber X (n : ℤ) x) := by
  exact zsmulDivisionFiber_natCast_finite_of_uniformization
    u.toGenusTorusUniformization x hn

/-- The positive-natural division fibres are inhabited for a complex
uniformization witness. -/
theorem zsmulDivisionFiber_natCast_nonempty_of_complex_uniformization
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : ComplexTorusUniformization X g) (x : X) (hn : 0 < n) :
    Nonempty (zsmulDivisionFiber X (n : ℤ) x) := by
  exact zsmulDivisionFiber_natCast_nonempty_of_uniformization
    u.toGenusTorusUniformization x hn

/- The canonical quotient itself is a valid uniformization target via the
   identity equivalence; these specializations do not assert existence of a
   uniformization for an arbitrary analytic abelian variety. -/
theorem zsmulDivisionFiber_card_of_complex_quotient
    {g : ℕ} (n : ℤ)
    (x : GenusComplexVector g ⧸ complexPeriodLattice g) (hn : n ≠ 0) :
    Nat.card (zsmulDivisionFiber
      (GenusComplexVector g ⧸ complexPeriodLattice g) n x) =
      n.natAbs ^ (2 * g) := by
  let u : ComplexTorusUniformization
      (GenusComplexVector g ⧸ complexPeriodLattice g) g :=
    ⟨AddEquiv.refl _⟩
  exact zsmulDivisionFiber_card_of_complex_uniformization u n x hn

theorem zsmulDivisionFiber_natCast_card_of_complex_quotient
    {g n : ℕ} (x : GenusComplexVector g ⧸ complexPeriodLattice g) (hn : 0 < n) :
    Nat.card (zsmulDivisionFiber
      (GenusComplexVector g ⧸ complexPeriodLattice g) (n : ℤ) x) =
      n ^ (2 * g) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  simpa using zsmulDivisionFiber_card_of_complex_quotient (n : ℤ) x hne

end
end Uniformization
end Mumford
