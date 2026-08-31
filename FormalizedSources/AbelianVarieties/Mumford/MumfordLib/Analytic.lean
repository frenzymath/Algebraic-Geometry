/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import Mathlib.Topology.Instances.AddCircle.Real

/-!
# MumfordLib.Analytic

Elementary analytic-torus consequences used in the first chapter of Mumford.
-/

namespace Mumford

noncomputable section

/-- A real product torus, represented as a product of unit additive circles.

This is the elementary real Lie-group model used in the proof of Mumford's
divisibility and torsion proposition (`mumford-frag-torsion`).
-/
abbrev ProductTorus (d : Type*) := UnitAddTorus d

/-- Every product torus admits division by a nonzero integer. -/
theorem productTorus_division {d : Type*} (x : ProductTorus d) {n : ℤ} (hn : n ≠ 0) :
    n • DivisibleBy.div x n = x :=
  DivisibleBy.div_cancel x hn

/-- Membership in the `n`-torsion of a product torus is coordinatewise. -/
theorem mem_productTorus_torsion_iff {d : Type*} {n : ℕ} (x : ProductTorus d) :
    x ∈ {x : ProductTorus d | n • x = 0} ↔ ∀ i, n • x i = 0 := by
  constructor
  · intro hx i
    have hi := congrFun hx i
    simpa only [Pi.smul_apply, Pi.zero_apply] using hi
  · intro hx
    change n • x = 0
    funext i
    exact hx i

/-- Membership in integer-scalar torsion of a product torus is coordinatewise. -/
theorem mem_productTorus_zsmul_torsion_iff {d : Type*} {n : ℤ} (x : ProductTorus d) :
    x ∈ {x : ProductTorus d | n • x = 0} ↔ ∀ i, n • x i = 0 := by
  constructor
  · intro hx i
    have hi := congrFun hx i
    simpa only [Pi.smul_apply, Pi.zero_apply] using hi
  · intro hx
    change n • x = 0
    funext i
    exact hx i

/-- The `n`-torsion of a finite product torus is finite. -/
theorem productTorus_torsion_finite {d : Type*} [Finite d] {n : ℕ} (hn : 0 < n) :
    {x : ProductTorus d | n • x = 0}.Finite := by
  have hpi : (Set.univ.pi (fun _ : d => {u : UnitAddCircle | n • u = 0})).Finite :=
    Set.Finite.pi (fun i => AddCircle.finite_torsion (1 : ℝ) hn)
  apply hpi.subset
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro i _
  change n • x i = 0
  have hi := congrFun hx i
  simpa only [Pi.smul_apply, Pi.zero_apply] using hi

private theorem real_isSMulRegular_int (n : ℤ) (hn : n ≠ 0) : IsSMulRegular ℝ n := by
  exact .of_right_eq_zero_of_smul (fun (x : ℝ) (h : n • x = 0) => by
    rw [zsmul_eq_mul] at h
    have hc : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rcases mul_eq_zero.mp h with h0 | hx
    · exact (hc h0).elim
    · exact hx)

/-- The nonzero-integer torsion of a finite product torus is finite. -/
theorem productTorus_zsmul_torsion_finite {d : Type*} [Finite d] {n : ℤ} (hn : n ≠ 0) :
    {x : ProductTorus d | n • x = 0}.Finite := by
  have hpi :
      (Set.univ.pi (fun _ : d => {u : UnitAddCircle | n • u = 0})).Finite :=
    Set.Finite.pi (fun _ => AddCircle.finite_torsion_of_isSMulRegular_int
      (1 : ℝ) n (real_isSMulRegular_int n hn))
  apply hpi.subset
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro i _
  change n • x i = 0
  have hi := congrFun hx i
  simpa only [Pi.smul_apply, Pi.zero_apply] using hi

/-!
The quotient description of the additive circle gives an explicit model for
its finite torsion.  We keep the equivalence at the subtype level so that the
annihilation equation remains available to coordinatewise constructions.
-/

/-- The `n`-torsion of the unit additive circle is `ZMod n`. -/
def unitAddCircle_torsion_equiv_zmod {n : ℕ} (hn : 0 < n) :
    {u : UnitAddCircle | n • u = 0} ≃ ZMod n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hmem (j : ZMod n) : n • ZMod.toAddCircle j = 0 := by
    apply (AddCircle.nsmul_eq_zero_iff hn).2
    refine ⟨j.val, j.val_lt, ?_⟩
    rw [ZMod.toAddCircle_apply]
    norm_num
  let f : ZMod n → {u : UnitAddCircle | n • u = 0} :=
    fun j => ⟨ZMod.toAddCircle j, hmem j⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact ZMod.toAddCircle_injective n (Subtype.mk.inj hab)
    · intro u
      obtain ⟨m, hm, hu⟩ := (AddCircle.nsmul_eq_zero_iff hn).1 u.property
      refine ⟨(m : ZMod n), ?_⟩
      apply Subtype.ext
      change ZMod.toAddCircle (m : ZMod n) = u.val
      rw [ZMod.toAddCircle_apply]
      simpa [Nat.mod_eq_of_lt hm] using hu
  exact (Equiv.ofBijective f hf).symm

/-- The torsion of a product torus is the corresponding product of `ZMod`s. -/
def productTorus_torsion_equiv_pi_zmod {d : Type*} {n : ℕ} (hn : 0 < n) :
    {x : ProductTorus d | n • x = 0} ≃ (d → ZMod n) := by
  let e := unitAddCircle_torsion_equiv_zmod hn
  let f : (d → ZMod n) → {x : ProductTorus d | n • x = 0} := fun z =>
    ⟨fun i => (e.symm (z i)).val, by
      apply (mem_productTorus_torsion_iff (n := n) (fun i => (e.symm (z i)).val)).2
      intro i
      exact (e.symm (z i)).property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      funext i
      have hi : (e.symm (a i)).val = (e.symm (b i)).val :=
        congrFun (Subtype.mk.inj hab) i
      have heq : e.symm (a i) = e.symm (b i) := Subtype.ext hi
      simpa using congrArg e heq
    · intro x
      have hx : ∀ i, n • x.val i = 0 :=
        (mem_productTorus_torsion_iff (n := n) x.val).1 x.property
      refine ⟨fun i => e ⟨x.val i, hx i⟩, ?_⟩
      apply Subtype.ext
      funext i
      change (e.symm (e ⟨x.val i, hx i⟩)).val = x.val i
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x.val i, hx i⟩)
  exact (Equiv.ofBijective f hf).symm

/-- The finite `n`-torsion of a finite product torus has cardinality `n ^ |d|`. -/
theorem productTorus_torsion_card {d : Type*} [Fintype d] {n : ℕ} (hn : 0 < n) :
    Nat.card {x : ProductTorus d | n • x = 0} = n ^ Fintype.card d := by
  rw [Nat.card_congr (productTorus_torsion_equiv_pi_zmod hn)]
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]

/-- Integer scalar torsion agrees with natural torsion at the absolute value. -/
def unitAddCircle_zsmul_torsion_equiv_zmod {n : ℤ} (hn : n ≠ 0) :
    {u : UnitAddCircle | n • u = 0} ≃ ZMod n.natAbs := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  let f : {u : UnitAddCircle | n • u = 0} ≃
      {u : UnitAddCircle | n.natAbs • u = 0} :=
    { toFun := fun u => ⟨u.val, (natAbs_nsmul_eq_zero).2 u.property⟩
      invFun := fun u => ⟨u.val, (natAbs_nsmul_eq_zero).1 u.property⟩
      left_inv := by intro u; exact Subtype.ext rfl
      right_inv := by intro u; exact Subtype.ext rfl }
  exact f.trans (unitAddCircle_torsion_equiv_zmod hpos)

/-- The cardinality of positive torsion on the unit additive circle. -/
theorem unitAddCircle_torsion_card {n : ℕ} (hn : 0 < n) :
    Nat.card {u : UnitAddCircle | n • u = 0} = n := by
  rw [Nat.card_congr (unitAddCircle_torsion_equiv_zmod hn), Nat.card_zmod]

/-- The cardinality of nonzero-integer torsion on the unit additive circle. -/
theorem unitAddCircle_zsmul_torsion_card {n : ℤ} (hn : n ≠ 0) :
    Nat.card {u : UnitAddCircle | n • u = 0} = n.natAbs := by
  rw [Nat.card_congr (unitAddCircle_zsmul_torsion_equiv_zmod hn), Nat.card_zmod]

/-- The cardinality formula for nonzero-integer torsion on a finite product torus. -/
theorem productTorus_zsmul_torsion_card {d : Type*} [Fintype d] {n : ℤ} (hn : n ≠ 0) :
    Nat.card {x : ProductTorus d | n • x = 0} = n.natAbs ^ Fintype.card d := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  let e : {x : ProductTorus d | n • x = 0} ≃
      {x : ProductTorus d | n.natAbs • x = 0} :=
    { toFun := fun x => ⟨x.val, (natAbs_nsmul_eq_zero).2 x.property⟩
      invFun := fun x => ⟨x.val, (natAbs_nsmul_eq_zero).1 x.property⟩
      left_inv := by intro x; exact Subtype.ext rfl
      right_inv := by intro x; exact Subtype.ext rfl }
  rw [Nat.card_congr e]
  exact productTorus_torsion_card hpos

/-!
The torsion carriers are additive subgroups, so the preceding type
equivalences can be upgraded to additive equivalences.  This is the group
level form needed for the abstract-group statement in the blueprint.
-/

/-- The positive `n`-torsion additive subgroup of the unit additive circle. -/
def unitAddCircle_torsionSubgroup (n : ℕ) : AddSubgroup UnitAddCircle where
  carrier := {u : UnitAddCircle | n • u = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [nsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [neg_nsmul, ha, neg_zero]

/-- The unit-circle torsion subgroup is additively equivalent to `ZMod n`. -/
def unitAddCircle_torsion_addEquiv_zmod {n : ℕ} (hn : 0 < n) :
    unitAddCircle_torsionSubgroup n ≃+ ZMod n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hmem (j : ZMod n) : ZMod.toAddCircle j ∈ unitAddCircle_torsionSubgroup n := by
    change n • ZMod.toAddCircle j = 0
    apply (AddCircle.nsmul_eq_zero_iff hn).2
    refine ⟨j.val, j.val_lt, ?_⟩
    rw [ZMod.toAddCircle_apply]
    norm_num
  let f : ZMod n →+ unitAddCircle_torsionSubgroup n :=
    ZMod.toAddCircle.codRestrict (unitAddCircle_torsionSubgroup n) hmem
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply ZMod.toAddCircle_injective n
      exact congrArg Subtype.val hab
    · intro u
      obtain ⟨m, hm, hu⟩ := (AddCircle.nsmul_eq_zero_iff hn).1 u.property
      refine ⟨(m : ZMod n), ?_⟩
      apply Subtype.ext
      change ZMod.toAddCircle (m : ZMod n) = u.val
      rw [ZMod.toAddCircle_apply]
      simpa [Nat.mod_eq_of_lt hm] using hu
  exact (AddEquiv.ofBijective f hf).symm

/-- The positive `n`-torsion additive subgroup of a product torus. -/
def productTorus_torsionSubgroup (d : Type*) (n : ℕ) :
    AddSubgroup (ProductTorus d) where
  carrier := {x : ProductTorus d | n • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [nsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [neg_nsmul, ha, neg_zero]

/-- Product-torus torsion is additively equivalent to a product of `ZMod`s. -/
def productTorus_torsion_addEquiv_pi_zmod {d : Type*} {n : ℕ} (hn : 0 < n) :
    productTorus_torsionSubgroup d n ≃+ (d → ZMod n) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let H := productTorus_torsionSubgroup d n
  have hmem (z : d → ZMod n) :
      (AddMonoidHom.piMap (fun _ : d => ZMod.toAddCircle)) z ∈ H := by
    change n • (AddMonoidHom.piMap (fun _ : d => ZMod.toAddCircle)) z = 0
    funext i
    rw [Pi.smul_apply, AddMonoidHom.piMap_apply]
    apply (AddCircle.nsmul_eq_zero_iff hn).2
    refine ⟨(z i).val, (z i).val_lt, ?_⟩
    rw [ZMod.toAddCircle_apply]
    norm_num
  let f : (d → ZMod n) →+ H :=
    (AddMonoidHom.piMap (fun _ : d => ZMod.toAddCircle)).codRestrict H hmem
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      funext i
      apply ZMod.toAddCircle_injective n
      have hi := congrFun (congrArg Subtype.val hab) i
      change ZMod.toAddCircle (a i) = ZMod.toAddCircle (b i) at hi
      exact hi
    · intro x
      have hx : ∀ i, n • x.val i = 0 :=
        (mem_productTorus_torsion_iff (n := n) x.val).1 x.property
      have hex (i : d) : ∃ z : ZMod n, ZMod.toAddCircle z = x.val i := by
        obtain ⟨m, hm, hu⟩ := (AddCircle.nsmul_eq_zero_iff hn).1 (hx i)
        refine ⟨(m : ZMod n), ?_⟩
        rw [ZMod.toAddCircle_apply]
        simpa [Nat.mod_eq_of_lt hm] using hu
      choose z hz using hex
      refine ⟨z, ?_⟩
      apply Subtype.ext
      funext i
      change (AddMonoidHom.piMap (fun _ : d => ZMod.toAddCircle)) z i = x.val i
      rw [AddMonoidHom.piMap_apply]
      exact hz i
  exact (AddEquiv.ofBijective f hf).symm

/-- The nonzero-integer torsion additive subgroup of the unit circle. -/
def unitAddCircle_zsmul_torsionSubgroup (n : ℤ) : AddSubgroup UnitAddCircle where
  carrier := {u : UnitAddCircle | n • u = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [zsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [zsmul_neg, ha, neg_zero]

/- Signed torsion is the natural torsion subgroup at the absolute value. -/
theorem unitAddCircle_zsmul_torsionSubgroup_eq_torsion (n : ℤ) :
    unitAddCircle_zsmul_torsionSubgroup n =
      unitAddCircle_torsionSubgroup n.natAbs := by
  apply AddSubgroup.ext
  intro u
  change n • u = 0 ↔ n.natAbs • u = 0
  exact natAbs_nsmul_eq_zero.symm

/-- Integer torsion on the unit circle is additively equivalent to `ZMod |n|`. -/
def unitAddCircle_zsmul_torsion_addEquiv_zmod {n : ℤ} (hn : n ≠ 0) :
    unitAddCircle_zsmul_torsionSubgroup n ≃+ ZMod n.natAbs := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  let f : unitAddCircle_zsmul_torsionSubgroup n ≃+
      unitAddCircle_torsionSubgroup n.natAbs :=
    { toFun := fun u => ⟨u.val, (natAbs_nsmul_eq_zero).2 u.property⟩
      invFun := fun u => ⟨u.val, (natAbs_nsmul_eq_zero).1 u.property⟩
      left_inv := by intro u; exact Subtype.ext rfl
      right_inv := by intro u; exact Subtype.ext rfl
      map_add' := by intro a b; rfl }
  exact f.trans (unitAddCircle_torsion_addEquiv_zmod hpos)

/-- The nonzero-integer torsion additive subgroup of a product torus. -/
def productTorus_zsmul_torsionSubgroup (d : Type*) (n : ℤ) :
    AddSubgroup (ProductTorus d) where
  carrier := {x : ProductTorus d | n • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [zsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [zsmul_neg, ha, neg_zero]

/- The product-torus version of the absolute-value identification. -/
theorem productTorus_zsmul_torsionSubgroup_eq_torsion (d : Type*) (n : ℤ) :
    productTorus_zsmul_torsionSubgroup d n =
      productTorus_torsionSubgroup d n.natAbs := by
  apply AddSubgroup.ext
  intro x
  change n • x = 0 ↔ n.natAbs • x = 0
  exact natAbs_nsmul_eq_zero.symm

/-- Integer product-torus torsion is additively equivalent to a product of `ZMod`s. -/
def productTorus_zsmul_torsion_addEquiv_pi_zmod {d : Type*} {n : ℤ} (hn : n ≠ 0) :
    productTorus_zsmul_torsionSubgroup d n ≃+ (d → ZMod n.natAbs) := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  let f : productTorus_zsmul_torsionSubgroup d n ≃+
      productTorus_torsionSubgroup d n.natAbs :=
    { toFun := fun x => ⟨x.val, (natAbs_nsmul_eq_zero).2 x.property⟩
      invFun := fun x => ⟨x.val, (natAbs_nsmul_eq_zero).1 x.property⟩
      left_inv := by intro x; exact Subtype.ext rfl
      right_inv := by intro x; exact Subtype.ext rfl
      map_add' := by intro a b; rfl }
  exact f.trans (productTorus_torsion_addEquiv_pi_zmod hpos)

/-! The additive-subgroup carriers inherit the explicit cardinality formulas. -/

/-- The positive `n`-torsion subgroup of the unit circle has order `n`. -/
theorem unitAddCircle_torsionSubgroup_card {n : ℕ} (hn : 0 < n) :
    Nat.card (unitAddCircle_torsionSubgroup n) = n := by
  simpa [unitAddCircle_torsionSubgroup] using (unitAddCircle_torsion_card hn)

/-- The nonzero-integer torsion subgroup of the unit circle has order `|n|`. -/
theorem unitAddCircle_zsmul_torsionSubgroup_card {n : ℤ} (hn : n ≠ 0) :
    Nat.card (unitAddCircle_zsmul_torsionSubgroup n) = n.natAbs := by
  simpa [unitAddCircle_zsmul_torsionSubgroup] using
    (unitAddCircle_zsmul_torsion_card hn)

/-- The positive `n`-torsion subgroup of a finite product torus has order
`n ^ |d|`. -/
theorem productTorus_torsionSubgroup_card {d : Type*} [Fintype d] {n : ℕ}
    (hn : 0 < n) :
    Nat.card (productTorus_torsionSubgroup d n) = n ^ Fintype.card d := by
  simpa [productTorus_torsionSubgroup] using (productTorus_torsion_card (d := d) hn)

/-- The nonzero-integer torsion subgroup of a finite product torus has order
`|n| ^ |d|`. -/
theorem productTorus_zsmul_torsionSubgroup_card {d : Type*} [Fintype d] {n : ℤ}
    (hn : n ≠ 0) :
    Nat.card (productTorus_zsmul_torsionSubgroup d n) = n.natAbs ^ Fintype.card d := by
  simpa [productTorus_zsmul_torsionSubgroup] using
    (productTorus_zsmul_torsion_card (d := d) hn)

/-! The set-level finiteness statements also apply directly to subgroup
carriers, which is useful when switching between set and additive-subgroup
interfaces. -/

/-- The positive torsion subgroup has a finite carrier on a finite product torus. -/
theorem productTorus_torsionSubgroup_carrier_finite
    {d : Type*} [Finite d] {n : ℕ} (hn : 0 < n) :
    ((productTorus_torsionSubgroup d n : AddSubgroup (ProductTorus d)) :
      Set (ProductTorus d)).Finite := by
  simpa [productTorus_torsionSubgroup] using
    (productTorus_torsion_finite (d := d) hn)

/-- The nonzero-integer torsion subgroup has a finite carrier on a finite
product torus. -/
theorem productTorus_zsmul_torsionSubgroup_carrier_finite
    {d : Type*} [Finite d] {n : ℤ} (hn : n ≠ 0) :
    ((productTorus_zsmul_torsionSubgroup d n : AddSubgroup (ProductTorus d)) :
      Set (ProductTorus d)).Finite := by
  simpa [productTorus_zsmul_torsionSubgroup] using
    (productTorus_zsmul_torsion_finite (d := d) hn)

end

end Mumford
