/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Abstract theta extensions

This module records the elementary group-theoretic interface for a theta
group.  The scalar group is written multiplicatively, while the quotient is
written additively.  Geometric representability and local splitting are left
to later modules; the fields below expose the exact sequence and centrality
facts needed by its algebraic consequences.
-/

set_option autoImplicit false

open scoped commutatorElement

universe u v w

namespace Mumford

/-- The elementary group-theoretic data underlying a theta-group extension. -/
structure ThetaExtension (G : Type u) (S : Type v) (K : Type w)
    [Group G] [CommGroup S] [AddCommGroup K] where
  /-- Inclusion of scalar automorphisms. -/
  includeScalar : S →* G
  /-- Projection to the additive quotient, represented as a multiplicative group. -/
  quotientHom : G →* Multiplicative K
  /-- The scalar inclusion has trivial kernel. -/
  includeScalar_ker : includeScalar.ker = ⊥
  /-- The quotient map is onto. -/
  quotientHom_range : quotientHom.range = ⊤
  /-- Exactness: the scalar image is the kernel of the quotient map. -/
  exact : includeScalar.range = quotientHom.ker
  /-- Scalars commute with every element of the extension. -/
  central : ∀ s g, Commute (includeScalar s) g

namespace ThetaExtension

variable {G : Type u} {S : Type v} {K : Type w}
  [Group G] [CommGroup S] [AddCommGroup K] (E : ThetaExtension G S K)

/-- The quotient map, written additively. -/
def quotient (g : G) : K :=
  Multiplicative.toAdd (E.quotientHom g)

@[simp]
theorem quotient_one : E.quotient 1 = 0 := by
  change Multiplicative.toAdd (E.quotientHom 1) = 0
  rw [map_one]
  rfl

@[simp]
theorem quotient_mul (x y : G) :
    E.quotient (x * y) = E.quotient x + E.quotient y := by
  change Multiplicative.toAdd (E.quotientHom (x * y)) =
    Multiplicative.toAdd (E.quotientHom x) + Multiplicative.toAdd (E.quotientHom y)
  rw [map_mul]
  rfl

@[simp]
theorem quotient_inv (x : G) :
    E.quotient x⁻¹ = -E.quotient x := by
  change Multiplicative.toAdd (E.quotientHom x⁻¹) =
    -Multiplicative.toAdd (E.quotientHom x)
  rw [map_inv]
  rfl

/-- The scalar inclusion is injective, as witnessed by its kernel field. -/
theorem includeScalar_injective : Function.Injective E.includeScalar :=
  (MonoidHom.ker_eq_bot_iff E.includeScalar).mp E.includeScalar_ker

/-- The quotient homomorphism is surjective, as witnessed by its range field. -/
theorem quotientHom_surjective : Function.Surjective E.quotientHom :=
  MonoidHom.range_eq_top.mp E.quotientHom_range

/-- A scalar commutes with every element of the extension. -/
theorem includeScalar_commute (s : S) (g : G) :
    Commute (E.includeScalar s) g :=
  E.central s g

/-- Every scalar lies in the kernel of the quotient map. -/
theorem includeScalar_mem_ker (s : S) :
    E.includeScalar s ∈ E.quotientHom.ker := by
  rw [← E.exact]
  exact ⟨s, rfl⟩

@[simp]
theorem quotient_includeScalar (s : S) :
    E.quotient (E.includeScalar s) = 0 := by
  change Multiplicative.toAdd (E.quotientHom (E.includeScalar s)) = 0
  have h := E.includeScalar_mem_ker s
  rw [MonoidHom.mem_ker] at h
  rw [h]
  rfl

/-- Kernel elements are exactly the scalar elements. -/
theorem mem_quotientHom_ker_iff (g : G) :
    g ∈ E.quotientHom.ker ↔ ∃ s, E.includeScalar s = g := by
  rw [← E.exact]
  rfl

/-- Every extension commutator projects to the identity in the quotient. -/
theorem commutator_mem_ker (x y : G) :
    ⁅x, y⁆ ∈ E.quotientHom.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

/-- Every commutator belongs to the scalar image. -/
theorem commutator_mem_includeScalar_range (x y : G) :
    ⁅x, y⁆ ∈ E.includeScalar.range := by
  rw [E.exact]
  exact E.commutator_mem_ker x y

/-- A commutator admits a scalar lift. -/
theorem exists_scalar_eq_commutator (x y : G) :
    ∃ s, E.includeScalar s = ⁅x, y⁆ :=
  (E.mem_quotientHom_ker_iff ⁅x, y⁆).mp (E.commutator_mem_ker x y)

/-! The central exact sequence makes the commutator a scalar-valued
bihomomorphism.  This is the algebraic core of the theta commutator pairing;
the quotient-level pairing is obtained after choosing lifts in a later layer. -/

include E

theorem commutator_commute (x y z : G) :
    Commute ⁅x, y⁆ z := by
  obtain ⟨s, hs⟩ := E.exists_scalar_eq_commutator x y
  rw [← hs]
  exact E.includeScalar_commute s z

noncomputable def commutatorScalar (x y : G) : S :=
  Classical.choose (E.exists_scalar_eq_commutator x y)

@[simp]
theorem includeScalar_commutatorScalar (x y : G) :
    E.includeScalar (E.commutatorScalar x y) = ⁅x, y⁆ :=
  Classical.choose_spec (E.exists_scalar_eq_commutator x y)

theorem commutatorScalar_unique (x y : G) {s : S}
    (hs : E.includeScalar s = ⁅x, y⁆) :
    s = E.commutatorScalar x y :=
  E.includeScalar_injective (hs.trans (E.includeScalar_commutatorScalar x y).symm)

@[simp]
theorem commutatorScalar_one_left (y : G) :
    E.commutatorScalar 1 y = 1 := by
  apply E.includeScalar_injective
  rw [E.includeScalar_commutatorScalar, commutatorElement_one_left, map_one]

@[simp]
theorem commutatorScalar_one_right (x : G) :
    E.commutatorScalar x 1 = 1 := by
  apply E.includeScalar_injective
  rw [E.includeScalar_commutatorScalar, commutatorElement_one_right, map_one]

@[simp]
theorem commutatorScalar_self (x : G) :
    E.commutatorScalar x x = 1 := by
  apply E.includeScalar_injective
  rw [E.includeScalar_commutatorScalar, commutatorElement_self, map_one]

theorem commutatorScalar_swap (x y : G) :
    E.commutatorScalar y x = (E.commutatorScalar x y)⁻¹ := by
  apply E.includeScalar_injective
  calc
    E.includeScalar (E.commutatorScalar y x) = ⁅y, x⁆ :=
      E.includeScalar_commutatorScalar y x
    _ = ⁅x, y⁆⁻¹ := by rw [commutatorElement_inv]
    _ = (E.includeScalar (E.commutatorScalar x y))⁻¹ :=
      congrArg Inv.inv (E.includeScalar_commutatorScalar x y).symm
    _ = E.includeScalar ((E.commutatorScalar x y)⁻¹) :=
      (map_inv E.includeScalar _).symm

@[simp]
theorem commutatorScalar_includeScalar_left (s : S) (y : G) :
    E.commutatorScalar (E.includeScalar s) y = 1 := by
  apply E.includeScalar_injective
  rw [E.includeScalar_commutatorScalar,
    (E.includeScalar_commute s y).commutator_eq, map_one]

@[simp]
theorem commutatorScalar_includeScalar_right (x : G) (s : S) :
    E.commutatorScalar x (E.includeScalar s) = 1 := by
  rw [E.commutatorScalar_swap, E.commutatorScalar_includeScalar_left, inv_one]

theorem commutatorScalar_mul_left (x y z : G) :
    E.commutatorScalar (x * y) z =
      E.commutatorScalar x z * E.commutatorScalar y z := by
  apply E.includeScalar_injective
  rw [map_mul, E.includeScalar_commutatorScalar, E.includeScalar_commutatorScalar,
    E.includeScalar_commutatorScalar, commutatorElement_mul_left_eq_conj_mul,
    (E.commutator_commute y z x).symm.mul_inv_cancel,
    (E.commutator_commute x z ⁅y, z⁆).eq]

theorem commutatorScalar_mul_right (x y z : G) :
    E.commutatorScalar x (y * z) =
      E.commutatorScalar x y * E.commutatorScalar x z := by
  apply E.includeScalar_injective
  rw [map_mul, E.includeScalar_commutatorScalar, E.includeScalar_commutatorScalar,
    E.includeScalar_commutatorScalar, commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ =
        ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by simp only [mul_assoc]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by
      rw [(E.commutator_commute x z y).symm.mul_inv_cancel]

theorem commutatorScalar_inv_left (x y : G) :
    E.commutatorScalar x⁻¹ y = (E.commutatorScalar x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← E.commutatorScalar_mul_left x⁻¹ x y]
  simp

theorem commutatorScalar_inv_right (x y : G) :
    E.commutatorScalar x y⁻¹ = (E.commutatorScalar x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← E.commutatorScalar_mul_right x y⁻¹ y]
  simp

noncomputable def commutatorHom (x : G) : G →* S where
  toFun := E.commutatorScalar x
  map_one' := E.commutatorScalar_one_right x
  map_mul' := E.commutatorScalar_mul_right x

@[simp]
theorem commutatorHom_apply (x y : G) :
    E.commutatorHom x y = E.commutatorScalar x y :=
  rfl

noncomputable def commutatorBihom : G →* G →* S where
  toFun := E.commutatorHom
  map_one' := by ext y; exact E.commutatorScalar_one_left y
  map_mul' x y := by ext z; exact E.commutatorScalar_mul_left x y z

@[simp]
theorem commutatorBihom_apply (x y : G) :
    E.commutatorBihom x y = E.commutatorScalar x y :=
  rfl

/-! Passing to the quotient makes the scalar commutator independent of the
chosen lifts.  We encode the scalar group additively in the resulting
`AddMonoidHom`, matching the additive structure on the quotient. -/

noncomputable def quotientLift (k : K) : G :=
  Classical.choose (E.quotientHom_surjective (Multiplicative.ofAdd k))

@[simp]
theorem quotientHom_quotientLift (k : K) :
    E.quotientHom (E.quotientLift k) = Multiplicative.ofAdd k :=
  Classical.choose_spec (E.quotientHom_surjective (Multiplicative.ofAdd k))

theorem commutatorScalar_eq_of_quotient_eq_left {x x' y : G}
    (h : E.quotientHom x = E.quotientHom x') :
    E.commutatorScalar x y = E.commutatorScalar x' y := by
  have hk : x * x'⁻¹ ∈ E.quotientHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨s, hs⟩ := (E.mem_quotientHom_ker_iff (x * x'⁻¹)).mp hk
  have hx : E.includeScalar s * x' = x := by
    calc
      E.includeScalar s * x' = (x * x'⁻¹) * x' := by rw [hs]
      _ = x := by simp
  rw [← hx, E.commutatorScalar_mul_left,
    E.commutatorScalar_includeScalar_left, one_mul]

theorem commutatorScalar_eq_of_quotient_eq_right {x y y' : G}
    (h : E.quotientHom y = E.quotientHom y') :
    E.commutatorScalar x y = E.commutatorScalar x y' := by
  have hh := E.commutatorScalar_eq_of_quotient_eq_left
    (x := y) (x' := y') (y := x) h
  calc
    E.commutatorScalar x y = (E.commutatorScalar y x)⁻¹ := by
      simpa using (congrArg Inv.inv (E.commutatorScalar_swap x y)).symm
    _ = (E.commutatorScalar y' x)⁻¹ := congrArg Inv.inv hh
    _ = E.commutatorScalar x y' := by
      simpa using congrArg Inv.inv (E.commutatorScalar_swap x y')

noncomputable def commutatorPairing (k l : K) : S :=
  E.commutatorScalar (E.quotientLift k) (E.quotientLift l)

@[simp]
theorem commutatorPairing_zero_left (l : K) :
    E.commutatorPairing 0 l = 1 := by
  unfold commutatorPairing
  calc
    E.commutatorScalar (E.quotientLift 0) (E.quotientLift l) =
        E.commutatorScalar (1 : G) (E.quotientLift l) :=
      E.commutatorScalar_eq_of_quotient_eq_left (by
        rw [E.quotientHom_quotientLift, map_one]
        simp)
    _ = 1 := E.commutatorScalar_one_left _

@[simp]
theorem commutatorPairing_zero_right (k : K) :
    E.commutatorPairing k 0 = 1 := by
  unfold commutatorPairing
  calc
    E.commutatorScalar (E.quotientLift k) (E.quotientLift 0) =
        E.commutatorScalar (E.quotientLift k) (1 : G) :=
      E.commutatorScalar_eq_of_quotient_eq_right (by
        rw [E.quotientHom_quotientLift, map_one]
        simp)
    _ = 1 := E.commutatorScalar_one_right _

theorem commutatorPairing_add_left (k₁ k₂ l : K) :
    E.commutatorPairing (k₁ + k₂) l =
      E.commutatorPairing k₁ l * E.commutatorPairing k₂ l := by
  unfold commutatorPairing
  calc
    E.commutatorScalar (E.quotientLift (k₁ + k₂)) (E.quotientLift l) =
        E.commutatorScalar (E.quotientLift k₁ * E.quotientLift k₂)
          (E.quotientLift l) :=
      E.commutatorScalar_eq_of_quotient_eq_left (by
        rw [E.quotientHom_quotientLift, map_mul, E.quotientHom_quotientLift,
          E.quotientHom_quotientLift]
        rfl)
    _ = E.commutatorScalar (E.quotientLift k₁) (E.quotientLift l) *
        E.commutatorScalar (E.quotientLift k₂) (E.quotientLift l) :=
      E.commutatorScalar_mul_left _ _ _

theorem commutatorPairing_add_right (k l₁ l₂ : K) :
    E.commutatorPairing k (l₁ + l₂) =
      E.commutatorPairing k l₁ * E.commutatorPairing k l₂ := by
  unfold commutatorPairing
  calc
    E.commutatorScalar (E.quotientLift k) (E.quotientLift (l₁ + l₂)) =
        E.commutatorScalar (E.quotientLift k)
          (E.quotientLift l₁ * E.quotientLift l₂) :=
      E.commutatorScalar_eq_of_quotient_eq_right (by
        rw [E.quotientHom_quotientLift, map_mul, E.quotientHom_quotientLift,
          E.quotientHom_quotientLift]
        rfl)
    _ = E.commutatorScalar (E.quotientLift k) (E.quotientLift l₁) *
        E.commutatorScalar (E.quotientLift k) (E.quotientLift l₂) :=
      E.commutatorScalar_mul_right _ _ _

@[simp]
theorem commutatorPairing_self (k : K) :
    E.commutatorPairing k k = 1 := by
  unfold commutatorPairing
  exact E.commutatorScalar_self _

theorem commutatorPairing_swap (k l : K) :
    E.commutatorPairing l k = (E.commutatorPairing k l)⁻¹ := by
  unfold commutatorPairing
  exact E.commutatorScalar_swap _ _

theorem commutatorPairing_neg_left (k l : K) :
    E.commutatorPairing (-k) l = (E.commutatorPairing k l)⁻¹ := by
  unfold commutatorPairing
  rw [E.commutatorScalar_eq_of_quotient_eq_left
    (x := E.quotientLift (-k)) (x' := (E.quotientLift k)⁻¹)
    (y := E.quotientLift l)]
  · exact E.commutatorScalar_inv_left _ _
  calc
    E.quotientHom (E.quotientLift (-k)) = Multiplicative.ofAdd (-k) :=
      E.quotientHom_quotientLift (-k)
    _ = (Multiplicative.ofAdd k)⁻¹ := ofAdd_neg k
    _ = (E.quotientHom (E.quotientLift k))⁻¹ :=
      congrArg Inv.inv (E.quotientHom_quotientLift k).symm
    _ = E.quotientHom (E.quotientLift k)⁻¹ :=
      (map_inv E.quotientHom _).symm

theorem commutatorPairing_neg_right (k l : K) :
    E.commutatorPairing k (-l) = (E.commutatorPairing k l)⁻¹ := by
  unfold commutatorPairing
  rw [E.commutatorScalar_eq_of_quotient_eq_right
    (x := E.quotientLift k) (y := E.quotientLift (-l))
    (y' := (E.quotientLift l)⁻¹)]
  · exact E.commutatorScalar_inv_right _ _
  calc
    E.quotientHom (E.quotientLift (-l)) = Multiplicative.ofAdd (-l) :=
      E.quotientHom_quotientLift (-l)
    _ = (Multiplicative.ofAdd l)⁻¹ := ofAdd_neg l
    _ = (E.quotientHom (E.quotientLift l))⁻¹ :=
      congrArg Inv.inv (E.quotientHom_quotientLift l).symm
    _ = E.quotientHom (E.quotientLift l)⁻¹ :=
      (map_inv E.quotientHom _).symm

/- The alternating law can be used without unpacking the inverse identity. -/
theorem commutatorPairing_mul_swap_eq_one (k l : K) :
    E.commutatorPairing k l * E.commutatorPairing l k = 1 := by
  calc
    E.commutatorPairing k l * E.commutatorPairing l k =
        E.commutatorPairing k l * (E.commutatorPairing k l)⁻¹ := by
      rw [E.commutatorPairing_swap k l]
    _ = 1 := mul_inv_cancel _

/-- The quotient commutator pairing detects commutativity of its chosen lifts. -/
theorem commutatorPairing_eq_one_iff_commute (k l : K) :
    E.commutatorPairing k l = 1 ↔
      Commute (E.quotientLift k) (E.quotientLift l) := by
  unfold commutatorPairing
  constructor
  · intro h
    apply commutatorElement_eq_one_iff_commute.mp
    calc
      ⁅E.quotientLift k, E.quotientLift l⁆ =
          E.includeScalar (E.commutatorScalar (E.quotientLift k)
            (E.quotientLift l)) :=
        (E.includeScalar_commutatorScalar _ _).symm
      _ = E.includeScalar 1 := by rw [h]
      _ = 1 := map_one E.includeScalar
  · intro h
    apply E.includeScalar_injective
    rw [E.includeScalar_commutatorScalar,
      commutatorElement_eq_one_iff_commute.mpr h, map_one]

noncomputable def commutatorPairingHom (k : K) : K →+ Additive S where
  toFun l := Additive.ofMul (E.commutatorPairing k l)
  map_zero' := by
    change Additive.ofMul (E.commutatorPairing k 0) = Additive.ofMul 1
    rw [E.commutatorPairing_zero_right]
  map_add' l₁ l₂ := by
    change Additive.ofMul (E.commutatorPairing k (l₁ + l₂)) =
      Additive.ofMul (E.commutatorPairing k l₁ * E.commutatorPairing k l₂)
    rw [E.commutatorPairing_add_right]

@[simp]
theorem commutatorPairingHom_apply (k l : K) :
    E.commutatorPairingHom k l =
      Additive.ofMul (E.commutatorPairing k l) :=
  rfl

noncomputable def commutatorPairingBihom : K →+ K →+ Additive S where
  toFun k := E.commutatorPairingHom k
  map_zero' := by
    ext l
    change Additive.ofMul (E.commutatorPairing 0 l) = Additive.ofMul 1
    rw [E.commutatorPairing_zero_left]
  map_add' k₁ k₂ := by
    ext l
    change Additive.ofMul (E.commutatorPairing (k₁ + k₂) l) =
      Additive.ofMul (E.commutatorPairing k₁ l * E.commutatorPairing k₂ l)
    rw [E.commutatorPairing_add_left]

@[simp]
theorem commutatorPairingBihom_apply (k l : K) :
    E.commutatorPairingBihom k l =
      Additive.ofMul (E.commutatorPairing k l) :=
  rfl

/-! The radical records the quotient classes whose chosen lifts commute with
    every quotient lift.  The next results identify it with the image of the
    center and recover the usual theta-group centralizer criterion. -/

/-- The radical of the quotient commutator pairing. -/
def commutatorPairingRadical : AddSubgroup K where
  carrier := {k | ∀ l, E.commutatorPairing k l = 1}
  zero_mem' := by
    intro l
    exact E.commutatorPairing_zero_left l
  add_mem' := by
    intro k₁ k₂ hk₁ hk₂ l
    rw [E.commutatorPairing_add_left, hk₁ l, hk₂ l, one_mul]
  neg_mem' := by
    intro k hk l
    rw [E.commutatorPairing_neg_left, hk l, inv_one]

@[simp]
theorem mem_commutatorPairingRadical_iff (k : K) :
    k ∈ E.commutatorPairingRadical ↔
      ∀ l, E.commutatorPairing k l = 1 :=
  Iff.rfl

/-- The kernel of the additive pairing homomorphism is the pairing radical. -/
theorem mem_commutatorPairingBihom_ker_iff (k : K) :
    k ∈ (E.commutatorPairingBihom).ker ↔
      ∀ l, E.commutatorPairing k l = 1 := by
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h l
    have hl := congrArg (fun f => f l) h
    have hl' : Additive.ofMul (E.commutatorPairing k l) = 0 := by
      simpa using hl
    change E.commutatorPairing k l = 1 at hl'
    exact hl'
  · intro h
    ext l
    change Additive.ofMul (E.commutatorPairing k l) = 0
    rw [h l]
    rfl

theorem commutatorPairingBihom_ker_eq_radical :
    (E.commutatorPairingBihom).ker = E.commutatorPairingRadical := by
  ext k
  exact E.mem_commutatorPairingBihom_ker_iff k

private theorem quotientHom_quotientLift_quotient (g : G) :
    E.quotientHom (E.quotientLift (E.quotient g)) = E.quotientHom g := by
  rw [E.quotientHom_quotientLift]
  change Multiplicative.ofAdd (Multiplicative.toAdd (E.quotientHom g)) =
    E.quotientHom g
  exact (Multiplicative.ofAdd : K ≃ Multiplicative K).symm_apply_apply _

/-- A class is in the pairing radical exactly when any lift of it is central. -/
theorem mem_center_iff_mem_commutatorPairingRadical (g : G) :
    g ∈ Subgroup.center G ↔ E.quotient g ∈ E.commutatorPairingRadical := by
  constructor
  · intro hg l
    have hcenter : ∀ h : G, h * g = g * h :=
      Subgroup.mem_center_iff.mp hg
    have hcomm : Commute g (E.quotientLift l) :=
      (hcenter (E.quotientLift l)).symm
    have hscalar : E.commutatorScalar g (E.quotientLift l) = 1 := by
      apply E.includeScalar_injective
      rw [E.includeScalar_commutatorScalar,
        commutatorElement_eq_one_iff_commute.mpr hcomm, map_one]
    calc
      E.commutatorPairing (E.quotient g) l =
          E.commutatorScalar (E.quotientLift (E.quotient g))
            (E.quotientLift l) := rfl
      _ = E.commutatorScalar g (E.quotientLift l) :=
        E.commutatorScalar_eq_of_quotient_eq_left
          (E.quotientHom_quotientLift_quotient g)
      _ = 1 := hscalar
  · intro hg
    rw [Subgroup.mem_center_iff]
    intro h
    have hqg := E.quotientHom_quotientLift_quotient g
    have hqh := E.quotientHom_quotientLift_quotient h
    have hpair : E.commutatorPairing (E.quotient g) (E.quotient h) = 1 :=
      ((E.mem_commutatorPairingRadical_iff (E.quotient g)).mp hg)
        (E.quotient h)
    have hscalar : E.commutatorScalar g h = 1 := by
      calc
        E.commutatorScalar g h =
            E.commutatorScalar (E.quotientLift (E.quotient g)) h :=
          E.commutatorScalar_eq_of_quotient_eq_left hqg.symm
        _ = E.commutatorScalar (E.quotientLift (E.quotient g))
              (E.quotientLift (E.quotient h)) :=
          E.commutatorScalar_eq_of_quotient_eq_right hqh.symm
        _ = E.commutatorPairing (E.quotient g) (E.quotient h) := rfl
        _ = 1 := hpair
    have hcomm : Commute g h := by
      apply commutatorElement_eq_one_iff_commute.mp
      calc
        ⁅g, h⁆ = E.includeScalar (E.commutatorScalar g h) :=
          (E.includeScalar_commutatorScalar g h).symm
        _ = E.includeScalar 1 := by rw [hscalar]
        _ = 1 := map_one E.includeScalar
    exact hcomm.eq.symm

/-- The center of the theta extension maps exactly onto the kernel of the
    additive commutator pairing.  This is the set-level form of the
    center-to-ker statement used in Mumford's theta-group argument. -/
theorem quotient_image_center_eq_commutatorPairingBihom_ker :
    E.quotient '' (Subgroup.center G : Set G) =
      ((E.commutatorPairingBihom).ker : Set K) := by
  apply Set.Subset.antisymm
  · rintro k ⟨g, hg, rfl⟩
    change E.quotient g ∈ (E.commutatorPairingBihom).ker
    rw [E.mem_commutatorPairingBihom_ker_iff]
    intro l
    exact (E.mem_center_iff_mem_commutatorPairingRadical g).mp hg l
  · intro k hk
    obtain ⟨g, hg⟩ :=
      E.quotientHom_surjective (Multiplicative.ofAdd k)
    have hq : E.quotient g = k := by
      unfold ThetaExtension.quotient
      rw [hg]
      rfl
    refine ⟨g, ?_, hq⟩
    apply (E.mem_center_iff_mem_commutatorPairingRadical g).mpr
    intro l
    have hl := (E.mem_commutatorPairingBihom_ker_iff k).mp hk l
    simpa [hq] using hl

/-- If the quotient pairing has trivial radical, the center is exactly the
    scalar subgroup in the theta extension. -/
theorem center_eq_includeScalar_range_of_commutatorPairingRadical_eq_bot
    (hrad : E.commutatorPairingRadical = ⊥) :
    Subgroup.center G = E.includeScalar.range := by
  ext g
  constructor
  · intro hg
    have hmem : E.quotient g ∈ E.commutatorPairingRadical :=
      (E.mem_center_iff_mem_commutatorPairingRadical g).mp hg
    rw [hrad] at hmem
    have hzero : E.quotient g = 0 := AddSubgroup.mem_bot.mp hmem
    have hqone : E.quotientHom g = 1 := by
      have hz := (Multiplicative.toAdd : Multiplicative K ≃ K).injective hzero
      change E.quotientHom g = (1 : Multiplicative K) at hz
      exact hz
    change g ∈ E.includeScalar.range
    rw [E.exact]
    exact (MonoidHom.mem_ker).mpr hqone
  · intro hg
    rcases hg with ⟨s, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact (E.includeScalar_commute s g).eq.symm

/-- Evaluating the pairing on quotient classes agrees with the scalar
    commutator of any representatives of those classes. -/
theorem commutatorPairing_quotient_eq_commutatorScalar (g h : G) :
    E.commutatorPairing (E.quotient g) (E.quotient h) =
      E.commutatorScalar g h := by
  have hq (x : G) :
      E.quotientHom (E.quotientLift (E.quotient x)) = E.quotientHom x := by
    rw [E.quotientHom_quotientLift]
    change Multiplicative.ofAdd (Multiplicative.toAdd (E.quotientHom x)) =
      E.quotientHom x
    exact (Multiplicative.ofAdd : K ≃ Multiplicative K).symm_apply_apply _
  calc
    E.commutatorPairing (E.quotient g) (E.quotient h) =
        E.commutatorScalar (E.quotientLift (E.quotient g))
          (E.quotientLift (E.quotient h)) := rfl
    _ = E.commutatorScalar g (E.quotientLift (E.quotient h)) :=
      E.commutatorScalar_eq_of_quotient_eq_left
        (hq g)
    _ = E.commutatorScalar g h :=
      E.commutatorScalar_eq_of_quotient_eq_right
        (hq h)

/-- The quotient pairing detects commutativity of arbitrary representatives,
    rather than only the chosen representatives used in its definition. -/
theorem commutatorPairing_quotient_eq_one_iff_commute (g h : G) :
    E.commutatorPairing (E.quotient g) (E.quotient h) = 1 ↔
      Commute g h := by
  rw [E.commutatorPairing_quotient_eq_commutatorScalar]
  constructor
  · intro hpair
    apply commutatorElement_eq_one_iff_commute.mp
    calc
      ⁅g, h⁆ = E.includeScalar (E.commutatorScalar g h) :=
        (E.includeScalar_commutatorScalar g h).symm
      _ = E.includeScalar 1 := by rw [hpair]
      _ = 1 := map_one E.includeScalar
  · intro hcomm
    apply E.includeScalar_injective
    rw [E.includeScalar_commutatorScalar,
      commutatorElement_eq_one_iff_commute.mpr hcomm, map_one]

/-! The quotient pairing also detects commutativity of the entire extension.
For a cyclic quotient, centrality of the scalar kernel then forces
commutativity. The prime-cardinality theorem below is the abstract-group part
of Mumford's theta-extension criterion; it does not model nonreduced finite
group schemes. -/

theorem isMulCommutative_iff_commutatorPairing_eq_one :
    IsMulCommutative G ↔ ∀ k l : K, E.commutatorPairing k l = 1 := by
  constructor
  · intro hG k l
    apply (E.commutatorPairing_eq_one_iff_commute k l).mpr
    exact hG.1.1 (E.quotientLift k) (E.quotientLift l)
  · intro hpair
    refine ⟨⟨fun g h => ?_⟩⟩
    exact ((E.commutatorPairing_quotient_eq_one_iff_commute g h).mp
      (hpair (E.quotient g) (E.quotient h))).eq

theorem isMulCommutative_of_isAddCyclic [IsAddCyclic K] :
    IsMulCommutative G := by
  apply MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center E.quotientHom
  intro g hg
  rw [← E.exact] at hg
  obtain ⟨s, rfl⟩ := hg
  rw [Subgroup.mem_center_iff]
  intro g
  exact (E.includeScalar_commute s g).eq.symm

theorem isMulCommutative_of_prime_card {p : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p) : IsMulCommutative G := by
  letI : IsAddCyclic K := isAddCyclic_of_prime_card hK
  exact E.isMulCommutative_of_isAddCyclic

end ThetaExtension

end Mumford
