/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.Analytic

/-!
# Uniformization interfaces

The analytic uniformization of a complex torus of dimension `g` has a real
`2 * g`-dimensional torus as its underlying additive group.  This file records
the algebraic consequences of a chosen additive equivalence to that model.
-/

namespace Mumford
namespace Uniformization

noncomputable section

/-- The real torus with `2 * g` circle factors. -/
abbrev GenusTorus (g : ℕ) := ProductTorus (Fin (2 * g))

/-- A chosen additive uniformization of a group by the real `2g`-torus model. -/
structure GenusTorusUniformization (X : Type*) [AddCommGroup X] (g : ℕ) where
  equiv : X ≃+ GenusTorus g

/- A uniformization transports the division operation on the model torus. -/
@[reducible]
noncomputable def divisibleBy_of_uniformization {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) : DivisibleBy X ℤ where
  div x n := u.equiv.symm (DivisibleBy.div (u.equiv x) n)
  div_zero x := by
    apply u.equiv.injective
    simp only [AddEquiv.apply_symm_apply, map_zero]
    exact DivisibleBy.div_zero _
  div_cancel {n} x hn := by
    apply u.equiv.injective
    simp only [AddEquiv.apply_symm_apply, map_zsmul]
    exact DivisibleBy.div_cancel (u.equiv x) hn

/-- The subgroup annihilated by a (possibly negative) integer scalar. -/
def zsmulTorsionSubgroup (X : Type*) [AddCommGroup X] (n : ℤ) : AddSubgroup X where
  carrier := {x : X | n • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [zsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [zsmul_neg, ha, neg_zero]

/- At a natural scalar, the signed subgroup has the usual `n`-torsion
   membership predicate. -/
theorem zsmulTorsionSubgroup_natCast_mem_iff
    {X : Type*} [AddCommGroup X] {n : ℕ} (x : X) :
    x ∈ zsmulTorsionSubgroup X (n : ℤ) ↔ n • x = 0 := by
  change (n : ℤ) • x = 0 ↔ n • x = 0
  rw [Nat.cast_smul_eq_nsmul]

/- Divisibility of scalars induces inclusion of the corresponding torsion. -/
theorem zsmulTorsionSubgroup_mono_of_dvd {X : Type*} [AddCommGroup X]
    {n m : ℤ} (h : n ∣ m) :
    zsmulTorsionSubgroup X n ≤ zsmulTorsionSubgroup X m := by
  rintro x hx
  rcases h with ⟨k, rfl⟩
  change n • x = 0 at hx
  calc
    (n * k) • x = k • (n • x) := by rw [mul_comm, smul_smul]
    _ = 0 := by rw [hx, smul_zero]

/- The subgroup inclusion associated to scalar divisibility. -/
def zsmulTorsion_inclusion_of_dvd {X : Type*} [AddCommGroup X]
    {n m : ℤ} (h : n ∣ m) :
    zsmulTorsionSubgroup X n →+ zsmulTorsionSubgroup X m :=
  AddSubgroup.inclusion (zsmulTorsionSubgroup_mono_of_dvd h)

@[simp]
theorem zsmulTorsion_inclusion_of_dvd_apply {X : Type*} [AddCommGroup X]
    {n m : ℤ} (h : n ∣ m) (x : zsmulTorsionSubgroup X n) :
    ((zsmulTorsion_inclusion_of_dvd h) x : X) = (x : X) := by
  exact AddSubgroup.coe_inclusion _ _

theorem zsmulTorsion_inclusion_of_dvd_injective {X : Type*} [AddCommGroup X]
    {n m : ℤ} (h : n ∣ m) :
    Function.Injective (zsmulTorsion_inclusion_of_dvd (X := X) h) := by
  exact AddSubgroup.inclusion_injective _

@[simp]
theorem zsmulTorsion_inclusion_of_dvd_refl {X : Type*} [AddCommGroup X] (n : ℤ) :
    zsmulTorsion_inclusion_of_dvd (X := X) (dvd_refl n) =
      AddMonoidHom.id (zsmulTorsionSubgroup X n) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

theorem zsmulTorsion_inclusion_of_dvd_comp {X : Type*} [AddCommGroup X]
    {n m k : ℤ} (hnm : n ∣ m) (hmk : m ∣ k) :
    (zsmulTorsion_inclusion_of_dvd (X := X) hmk).comp
        (zsmulTorsion_inclusion_of_dvd (X := X) hnm) =
      zsmulTorsion_inclusion_of_dvd (X := X) (dvd_trans hnm hmk) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

/- The same inclusion can be indexed by natural scalars. -/
def natCast_zsmulTorsion_inclusion_of_dvd {X : Type*} [AddCommGroup X]
    {n m : ℕ} (h : n ∣ m) :
    zsmulTorsionSubgroup X (n : ℤ) →+ zsmulTorsionSubgroup X (m : ℤ) :=
  zsmulTorsion_inclusion_of_dvd (X := X) (Int.ofNat_dvd.mpr h)

@[simp]
theorem natCast_zsmulTorsion_inclusion_of_dvd_apply {X : Type*} [AddCommGroup X]
    {n m : ℕ} (h : n ∣ m) (x : zsmulTorsionSubgroup X (n : ℤ)) :
    ((natCast_zsmulTorsion_inclusion_of_dvd h) x : X) = (x : X) := by
  change ((zsmulTorsion_inclusion_of_dvd (X := X) (Int.ofNat_dvd.mpr h)) x : X) =
    (x : X)
  exact AddSubgroup.coe_inclusion _ _

theorem natCast_zsmulTorsion_inclusion_of_dvd_injective {X : Type*} [AddCommGroup X]
    {n m : ℕ} (h : n ∣ m) :
    Function.Injective (natCast_zsmulTorsion_inclusion_of_dvd (X := X) h) := by
  change Function.Injective
    (zsmulTorsion_inclusion_of_dvd (X := X) (Int.ofNat_dvd.mpr h))
  exact AddSubgroup.inclusion_injective _

theorem natCast_zsmulTorsion_inclusion_of_dvd_comp {X : Type*} [AddCommGroup X]
    {n m k : ℕ} (hnm : n ∣ m) (hmk : m ∣ k) :
    (natCast_zsmulTorsion_inclusion_of_dvd (X := X) hmk).comp
        (natCast_zsmulTorsion_inclusion_of_dvd (X := X) hnm) =
      natCast_zsmulTorsion_inclusion_of_dvd (X := X) (Nat.dvd_trans hnm hmk) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

/- Additive maps restrict functorially to integer torsion subgroups. -/
def zsmulTorsion_map {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (n : ℤ) :
    zsmulTorsionSubgroup X n →+ zsmulTorsionSubgroup Y n :=
  (f.comp (zsmulTorsionSubgroup X n).subtype).codRestrict _
    (fun x => by
      change n • f (x : X) = 0
      rw [← map_zsmul, x.property, map_zero])

@[simp]
theorem zsmulTorsion_map_apply {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (n : ℤ) (x : zsmulTorsionSubgroup X n) :
    ((zsmulTorsion_map f n) x : Y) = f (x : X) := by
  rfl

theorem zsmulTorsion_map_injective {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (n : ℤ) (hf : Function.Injective f) :
    Function.Injective (zsmulTorsion_map f n) := by
  intro x y hxy
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val hxy

@[simp]
theorem zsmulTorsion_map_id {X : Type*} [AddCommGroup X] (n : ℤ) :
    zsmulTorsion_map (AddMonoidHom.id X) n = AddMonoidHom.id _ := by
  ext x
  rfl

theorem zsmulTorsion_map_comp {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] (f : X →+ Y) (g : Y →+ Z) (n : ℤ) :
    zsmulTorsion_map (g.comp f) n =
      (zsmulTorsion_map g n).comp (zsmulTorsion_map f n) := by
  ext x
  rfl

/- Additive maps commute with the canonical inclusions of torsion subgroups. -/
theorem zsmulTorsion_map_inclusion_of_dvd {X Y : Type*} [AddCommGroup X]
    [AddCommGroup Y] (f : X →+ Y) {n m : ℤ} (h : n ∣ m) :
    (zsmulTorsion_map f m).comp
        (zsmulTorsion_inclusion_of_dvd (X := X) h) =
      (zsmulTorsion_inclusion_of_dvd (X := Y) h).comp
        (zsmulTorsion_map f n) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

/-- An additive equivalence transports the corresponding integer torsion subgroups. -/
def zsmulTorsion_addEquiv_of_addEquiv {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) :
    zsmulTorsionSubgroup X n ≃+ zsmulTorsionSubgroup Y n := by
  have hpres (x : X) : n • x = 0 ↔ n • e x = 0 := by
    constructor
    · intro hx
      have h := congrArg e hx
      simpa only [map_zsmul, map_zero] using h
    · intro hx
      apply e.injective
      simpa only [map_zsmul, map_zero] using hx
  let q : zsmulTorsionSubgroup X n ≃ zsmulTorsionSubgroup Y n :=
    e.toEquiv.subtypeEquiv (fun x => by
      change n • (x : X) = 0 ↔ n • e (x : X) = 0
      exact hpres (x : X))
  exact
    { toFun := q
      invFun := q.symm
      left_inv := q.left_inv
      right_inv := q.right_inv
      map_add' := by
        intro a b
        apply Subtype.ext
        exact e.map_add (a : X) (b : X) }

@[simp]
theorem zsmulTorsion_addEquiv_of_addEquiv_apply {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) (x : zsmulTorsionSubgroup X n) :
    ((zsmulTorsion_addEquiv_of_addEquiv e n) x : Y) = e (x : X) := by
  rfl

@[simp]
theorem zsmulTorsion_addEquiv_of_addEquiv_symm_apply {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) (y : zsmulTorsionSubgroup Y n) :
    ((zsmulTorsion_addEquiv_of_addEquiv e n).symm y : X) = e.symm (y : Y) := by
  rfl

theorem zsmulTorsion_map_of_addEquiv {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) :
    zsmulTorsion_map e.toAddMonoidHom n =
      (zsmulTorsion_addEquiv_of_addEquiv e n).toAddMonoidHom := by
  ext x
  rfl

/- Torsion transport is coherent with composition of additive equivalences. -/
theorem zsmulTorsion_addEquiv_of_addEquiv_trans
    {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (e : X ≃+ Y) (f : Y ≃+ Z) (n : ℤ) :
    zsmulTorsion_addEquiv_of_addEquiv (e.trans f) n =
      (zsmulTorsion_addEquiv_of_addEquiv e n).trans
        (zsmulTorsion_addEquiv_of_addEquiv f n) := by
  apply AddEquiv.ext
  intro x
  rfl

/- The same transport commutes with taking the inverse equivalence. -/
theorem zsmulTorsion_addEquiv_of_addEquiv_symm
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) :
    zsmulTorsion_addEquiv_of_addEquiv e.symm n =
      (zsmulTorsion_addEquiv_of_addEquiv e n).symm := by
  apply AddEquiv.ext
  intro x
  rfl

/- The torsion cardinality is invariant under an additive equivalence.  Keeping
this as a separate theorem avoids repeating the subtype-equivalence argument
when a uniformization is composed with another group isomorphism. -/
theorem zsmulTorsion_card_eq_of_addEquiv {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) :
    Nat.card (zsmulTorsionSubgroup X n) = Nat.card (zsmulTorsionSubgroup Y n) := by
  exact Nat.card_congr (zsmulTorsion_addEquiv_of_addEquiv e n).toEquiv

/- The finiteness of integer torsion is invariant under an additive equivalence. -/
theorem zsmulTorsion_finite_iff_of_addEquiv {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (n : ℤ) :
    Finite (zsmulTorsionSubgroup X n) ↔ Finite (zsmulTorsionSubgroup Y n) := by
  exact (zsmulTorsion_addEquiv_of_addEquiv e n).toEquiv.finite_iff

/-- Nonzero integer division exists on the genus torus model. -/
theorem genusTorus_exists_division (g : ℕ) (x : GenusTorus g) {n : ℤ} (hn : n ≠ 0) :
    ∃ y : GenusTorus g, n • y = x := by
  exact ⟨DivisibleBy.div x n, DivisibleBy.div_cancel x hn⟩

/-- Integer torsion of the genus torus is a product of cyclic groups. -/
def genusTorus_zsmulTorsion_addEquiv (g : ℕ) {n : ℤ} (hn : n ≠ 0) :
    zsmulTorsionSubgroup (GenusTorus g) n ≃+ (Fin (2 * g) → ZMod n.natAbs) := by
  exact (zsmulTorsion_addEquiv_of_addEquiv (AddEquiv.refl _) n).trans
    (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)

/-- The integer torsion of the genus torus has cardinality `|n| ^ (2 * g)`. -/
theorem genusTorus_zsmulTorsion_card (g : ℕ) {n : ℤ} (hn : n ≠ 0) :
    Nat.card (zsmulTorsionSubgroup (GenusTorus g) n) = n.natAbs ^ (2 * g) := by
  rw [Nat.card_congr (genusTorus_zsmulTorsion_addEquiv g hn).toEquiv]
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The torsion classification transported across a chosen genus-torus uniformization. -/
def zsmulTorsion_addEquiv_of_uniformization {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0) :
    zsmulTorsionSubgroup X n ≃+ (Fin (2 * g) → ZMod n.natAbs) := by
  exact (zsmulTorsion_addEquiv_of_addEquiv u.equiv n).trans
    (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)

/-- A chosen genus-torus uniformization gives divisibility by every nonzero integer. -/
theorem exists_division_of_uniformization {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) (x : X) {n : ℤ} (hn : n ≠ 0) :
    ∃ y : X, n • y = x := by
  letI : DivisibleBy X ℤ := divisibleBy_of_uniformization u
  exact ⟨DivisibleBy.div x n, DivisibleBy.div_cancel x hn⟩

/-- The torsion cardinality transported across a chosen genus-torus uniformization. -/
theorem zsmulTorsion_card_of_uniformization {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0) :
    Nat.card (zsmulTorsionSubgroup X n) = n.natAbs ^ (2 * g) := by
  calc
    Nat.card (zsmulTorsionSubgroup X n) =
        Nat.card (zsmulTorsionSubgroup (GenusTorus g) n) :=
      zsmulTorsion_card_eq_of_addEquiv u.equiv n
    _ = n.natAbs ^ (2 * g) := genusTorus_zsmulTorsion_card g hn

/- The same formula in the natural-number notation used for positive torsion. -/
theorem natCast_zsmulTorsion_card_of_uniformization {X : Type*} [AddCommGroup X]
    {g n : ℕ} (u : GenusTorusUniformization X g) (hn : 0 < n) :
    Nat.card (zsmulTorsionSubgroup X (n : ℤ)) = n ^ (2 * g) := by
  have hne : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simpa using (zsmulTorsion_card_of_uniformization u hne)

/-- The positive-natural torsion classification for a chosen uniformization. -/
noncomputable def natCast_zsmulTorsion_addEquiv_of_uniformization
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : GenusTorusUniformization X g) (hn : 0 < n) :
    zsmulTorsionSubgroup X (n : ℤ) ≃+ (Fin (2 * g) → ZMod n) := by
  have hne : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact zsmulTorsion_addEquiv_of_uniformization u hne

/-- A chosen genus-torus uniformization makes every nonzero-integer torsion
subgroup finite. -/
theorem zsmulTorsion_finite_of_uniformization {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0) :
    Finite (zsmulTorsionSubgroup X n) := by
  rw [zsmulTorsion_finite_iff_of_addEquiv u.equiv n]
  letI : NeZero n.natAbs := ⟨Int.natAbs_pos.mpr hn |>.ne'⟩
  exact Finite.of_injective
    (productTorus_zsmul_torsion_addEquiv_pi_zmod (d := Fin (2 * g)) hn).toEquiv
    (productTorus_zsmul_torsion_addEquiv_pi_zmod (d := Fin (2 * g)) hn).injective

end
end Uniformization
end Mumford
