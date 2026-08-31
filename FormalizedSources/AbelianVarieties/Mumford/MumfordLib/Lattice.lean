/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.Uniformization

/-!
# Period-lattice quotients

This file packages the additive quotient data supplied by analytic uniformization
and constructs the standard real period-lattice model of the genus torus.
-/

namespace Mumford
namespace Uniformization

noncomputable section

/-- An additive uniformization certificate with a specified period lattice.

For an analytic exponential map, `kernel_exponential` identifies the periods
with the kernel. Surjectivity then identifies the lattice quotient with the
target additive group.
-/
structure PeriodLatticeQuotient (V X : Type*) [AddCommGroup V] [AddCommGroup X] where
  periodLattice : AddSubgroup V
  exponential : V →+ X
  exponential_surjective : Function.Surjective exponential
  kernel_exponential : exponential.ker = periodLattice

namespace PeriodLatticeQuotient

/-- The first isomorphism theorem for a period-lattice quotient certificate. -/
def quotientAddEquiv {V X : Type*} [AddCommGroup V] [AddCommGroup X]
    (u : PeriodLatticeQuotient V X) : V ⧸ u.periodLattice ≃+ X :=
  (QuotientAddGroup.quotientAddEquivOfEq u.kernel_exponential.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      u.exponential u.exponential_surjective)

/-- The quotient equivalence agrees with the exponential map on representatives. -/
@[simp]
theorem quotientAddEquiv_mk {V X : Type*} [AddCommGroup V] [AddCommGroup X]
    (u : PeriodLatticeQuotient V X) (v : V) :
    u.quotientAddEquiv (QuotientAddGroup.mk' u.periodLattice v) = u.exponential v := by
  simp only [quotientAddEquiv, AddEquiv.trans_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  change QuotientAddGroup.kerLift u.exponential (v : V ⧸ u.exponential.ker) =
    u.exponential v
  rw [QuotientAddGroup.kerLift_mk]

/- Two representatives define the same quotient point exactly when their
   difference is a period. -/
theorem quotientAddEquiv_mk_eq_iff {V X : Type*} [AddCommGroup V] [AddCommGroup X]
    (u : PeriodLatticeQuotient V X) (v w : V) :
    u.quotientAddEquiv (QuotientAddGroup.mk' u.periodLattice v) =
        u.quotientAddEquiv (QuotientAddGroup.mk' u.periodLattice w) ↔
      v - w ∈ u.periodLattice := by
  rw [quotientAddEquiv_mk, quotientAddEquiv_mk]
  constructor
  · intro h
    have hz : u.exponential (v - w) = 0 := by
      rw [map_sub, h, sub_self]
    rw [← AddMonoidHom.mem_ker, u.kernel_exponential] at hz
    exact hz
  · intro h
    have hz : u.exponential (v - w) = 0 := by
      rw [← AddMonoidHom.mem_ker, u.kernel_exponential]
      exact h
    have heq : u.exponential v - u.exponential w = 0 := by
      simpa only [map_sub] using hz
    exact sub_eq_zero.mp heq

/- A quotient representative is killed by an integer precisely when the
   corresponding scalar multiple lies in the period subgroup. -/
theorem quotient_mk_mem_zsmulTorsion_iff
    {V : Type*} [AddCommGroup V] (N : AddSubgroup V) (n : ℤ) (v : V) :
    QuotientAddGroup.mk' N v ∈ zsmulTorsionSubgroup (V ⧸ N) n ↔
      n • v ∈ N := by
  change n • (QuotientAddGroup.mk' N v) = 0 ↔ _
  rw [← (QuotientAddGroup.mk' N).map_zsmul]
  change QuotientAddGroup.mk' N (n • v) = 0 ↔ _
  rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']

/-- An open quotient exponential identifies its period quotient with the
   target also at the topological level. -/
noncomputable def quotientHomeomorph
    {V X : Type*} [AddCommGroup V] [AddCommGroup X]
    [TopologicalSpace V] [TopologicalSpace X]
    (u : PeriodLatticeQuotient V X)
    (hquot : IsOpenQuotientMap u.exponential) :
    V ⧸ u.periodLattice ≃ₜ X := by
  refine
    { toEquiv := u.quotientAddEquiv.toEquiv
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · rw [(QuotientAddGroup.isQuotientMap_mk
      u.periodLattice).continuous_iff]
    change Continuous (fun v : V =>
      u.quotientAddEquiv (QuotientAddGroup.mk' u.periodLattice v))
    simpa only [quotientAddEquiv_mk] using hquot.continuous
  · apply hquot.continuous_comp_iff.mp
    change Continuous (fun v : V =>
      u.quotientAddEquiv.symm (u.exponential v))
    have hcomp :
        (fun v : V => u.quotientAddEquiv.symm (u.exponential v)) =
          (fun v : V => QuotientAddGroup.mk' u.periodLattice v) := by
      funext v
      rw [← quotientAddEquiv_mk]
      exact u.quotientAddEquiv.symm_apply_apply _
    rw [hcomp]
    exact QuotientAddGroup.continuous_mk

@[simp]
theorem quotientHomeomorph_mk
    {V X : Type*} [AddCommGroup V] [AddCommGroup X]
    [TopologicalSpace V] [TopologicalSpace X]
    (u : PeriodLatticeQuotient V X)
    (hquot : IsOpenQuotientMap u.exponential) (v : V) :
    u.quotientHomeomorph hquot
        (QuotientAddGroup.mk' u.periodLattice v) =
      u.exponential v :=
  quotientAddEquiv_mk u v

end PeriodLatticeQuotient

/-- The real vector group underlying a complex torus of dimension `g`. -/
abbrev GenusRealVector (g : ℕ) := Fin (2 * g) → ℝ

/-- The coordinatewise integer lattice in the real vector group of dimension `2 * g`. -/
def integerPeriodLattice (g : ℕ) : AddSubgroup (GenusRealVector g) :=
  AddSubgroup.pi Set.univ (fun _ => AddSubgroup.zmultiples (1 : ℝ))

/-- The additive exponential map from the real line to the unit additive circle. -/
def unitAddCircleExponential : ℝ →+ UnitAddCircle :=
  QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))

/-- The coordinatewise exponential from the real vector group to the genus torus. -/
def genusTorusExponential (g : ℕ) : GenusRealVector g →+ GenusTorus g :=
  AddMonoidHom.piMap (fun _ => unitAddCircleExponential)

/-- The coordinatewise exponential is continuous for the product topologies. -/
theorem genusTorusExponential_continuous (g : ℕ) :
    Continuous (genusTorusExponential g) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : Fin (2 * g) → ℝ =>
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) (x i))
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)

/-- The standard genus torus is connected, including the zero-dimensional case. -/
theorem genusTorus_isConnected (g : ℕ) :
    IsConnected (Set.univ : Set (GenusTorus g)) := by
  change IsConnected (Set.univ : Set (Fin (2 * g) → UnitAddCircle))
  have hpi : IsConnected ((Set.univ : Set (Fin (2 * g))).pi
      (fun _ : Fin (2 * g) => (Set.univ : Set UnitAddCircle))) := by
    rw [isConnected_univ_pi]
    intro i
    exact isConnected_univ
  simpa only [Set.pi_univ] using hpi

/-- The standard genus torus is path connected. -/
theorem genusTorus_isPathConnected (g : ℕ) : PathConnectedSpace (GenusTorus g) := by
  letI : Nonempty (GenusTorus g) := ⟨0⟩
  exact
    { nonempty := inferInstance
      joined := by
        intro x y
        exact ⟨Path.pi (fun i => PathConnectedSpace.somePath (x i) (y i))⟩ }

/-- The standard exponential is an open quotient map onto the genus torus. -/
theorem genusTorusExponential_isOpenQuotientMap (g : ℕ) :
    IsOpenQuotientMap (genusTorusExponential g) := by
  change IsOpenQuotientMap (Pi.map (fun _ : Fin (2 * g) =>
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) :
      ℝ → UnitAddCircle)))
  exact IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

/-- The coordinatewise exponential to the genus torus is surjective. -/
theorem genusTorusExponential_surjective (g : ℕ) :
    Function.Surjective (genusTorusExponential g) := by
  exact Function.Surjective.piMap
    (fun _ => QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)))

/-- The kernel of the coordinatewise exponential is exactly the integer period lattice. -/
theorem genusTorusExponential_ker (g : ℕ) :
    (genusTorusExponential g).ker = integerPeriodLattice g := by
  ext x
  rw [AddMonoidHom.mem_ker]
  simp only [integerPeriodLattice, AddSubgroup.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro hx i
    have hxi := congrFun hx i
    change unitAddCircleExponential (x i) = 0 at hxi
    rw [← AddMonoidHom.mem_ker] at hxi
    change x i ∈
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).ker at hxi
    simpa only [QuotientAddGroup.ker_mk'] using hxi
  · intro hx
    funext i
    rw [Pi.zero_apply]
    change unitAddCircleExponential (x i) = 0
    rw [← AddMonoidHom.mem_ker]
    change x i ∈
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).ker
    simpa only [QuotientAddGroup.ker_mk'] using hx i

/-- The standard real period-lattice certificate for the genus torus. -/
def standardGenusTorusPeriodLatticeQuotient (g : ℕ) :
    PeriodLatticeQuotient (GenusRealVector g) (GenusTorus g) where
  periodLattice := integerPeriodLattice g
  exponential := genusTorusExponential g
  exponential_surjective := genusTorusExponential_surjective g
  kernel_exponential := genusTorusExponential_ker g

/-- The standard additive equivalence between the real lattice quotient and the genus torus. -/
def genusRealVectorQuotientAddEquiv (g : ℕ) :
    GenusRealVector g ⧸ integerPeriodLattice g ≃+ GenusTorus g :=
  (standardGenusTorusPeriodLatticeQuotient g).quotientAddEquiv

/-- The standard quotient equivalence evaluates on a representative by the
coordinatewise additive exponential. -/
@[simp]
theorem genusRealVectorQuotientAddEquiv_mk (g : ℕ) (v : GenusRealVector g) :
    genusRealVectorQuotientAddEquiv g
        (QuotientAddGroup.mk' (integerPeriodLattice g) v) =
      genusTorusExponential g v := by
  exact PeriodLatticeQuotient.quotientAddEquiv_mk
    (standardGenusTorusPeriodLatticeQuotient g) v

/-- Integer torsion of the standard real lattice quotient is a product of
cyclic groups indexed by the `2 * g` coordinates. -/
def genusRealVectorQuotient_zsmulTorsion_addEquiv {g : ℕ} {n : ℤ} (hn : n ≠ 0) :
    zsmulTorsionSubgroup (GenusRealVector g ⧸ integerPeriodLattice g) n ≃+
      (Fin (2 * g) → ZMod n.natAbs) := by
  exact (zsmulTorsion_addEquiv_of_addEquiv (genusRealVectorQuotientAddEquiv g) n).trans
    (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)

/- The positive-natural notation is obtained from the signed classification by
transporting the canonical equality `(n : ℤ).natAbs = n`. -/
noncomputable def genusRealVectorQuotient_natCast_zsmulTorsion_addEquiv
    {g n : ℕ} (hn : 0 < n) :
    zsmulTorsionSubgroup (GenusRealVector g ⧸ integerPeriodLattice g) (n : ℤ) ≃+
      (Fin (2 * g) → ZMod n) := by
  have hne : (n : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)
  let castEquiv : (Fin (2 * g) → ZMod (n : ℤ).natAbs) ≃+
      (Fin (2 * g) → ZMod n) :=
    AddEquiv.cast (M := fun m : ℕ => Fin (2 * g) → ZMod m)
      (Int.natAbs_ofNat' n)
  exact (genusRealVectorQuotient_zsmulTorsion_addEquiv hne).trans castEquiv

/-- The natural-number real quotient torsion equivalence is the signed one
followed by the canonical `natAbs` cast. -/
theorem genusRealVectorQuotient_natCast_zsmulTorsion_addEquiv_eq_trans_cast
    {g n : ℕ} (hn : 0 < n) :
    genusRealVectorQuotient_natCast_zsmulTorsion_addEquiv hn =
      (genusRealVectorQuotient_zsmulTorsion_addEquiv
        (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn))).trans
        (AddEquiv.cast (M := fun m : ℕ => Fin (2 * g) → ZMod m)
          (Int.natAbs_ofNat' n)) := by
  rfl

@[simp]
theorem genusRealVectorQuotient_natCast_zsmulTorsion_addEquiv_apply
    {g n : ℕ} (hn : 0 < n)
    (x : zsmulTorsionSubgroup
      (GenusRealVector g ⧸ integerPeriodLattice g) (n : ℤ)) :
    (genusRealVectorQuotient_natCast_zsmulTorsion_addEquiv hn) x =
      (AddEquiv.cast (M := fun m : ℕ => Fin (2 * g) → ZMod m)
          (Int.natAbs_ofNat' n))
        ((genusRealVectorQuotient_zsmulTorsion_addEquiv
          (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn))) x) := by
  rfl

/-- The standard real lattice quotient has the expected finite torsion order. -/
theorem genusRealVectorQuotient_zsmulTorsion_card {g : ℕ} {n : ℤ} (hn : n ≠ 0) :
    Nat.card (zsmulTorsionSubgroup (GenusRealVector g ⧸ integerPeriodLattice g) n) =
      n.natAbs ^ (2 * g) := by
  calc
    Nat.card (zsmulTorsionSubgroup (GenusRealVector g ⧸ integerPeriodLattice g) n) =
        Nat.card (zsmulTorsionSubgroup (GenusTorus g) n) :=
      zsmulTorsion_card_eq_of_addEquiv (genusRealVectorQuotientAddEquiv g) n
    _ = n.natAbs ^ (2 * g) := genusTorus_zsmulTorsion_card g hn

/-- The standard real quotient has the expected positive-natural torsion
order. -/
theorem genusRealVectorQuotient_natCast_zsmulTorsion_card
    {g n : ℕ} (hn : 0 < n) :
    Nat.card (zsmulTorsionSubgroup
      (GenusRealVector g ⧸ integerPeriodLattice g) (n : ℤ)) =
      n ^ (2 * g) := by
  have hne : (n : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)
  simpa using (genusRealVectorQuotient_zsmulTorsion_card (g := g) hne)

/-- Every nonzero integer acts surjectively on the standard real lattice
quotient. -/
theorem genusRealVectorQuotient_exists_division {g : ℕ}
    (x : GenusRealVector g ⧸ integerPeriodLattice g) {n : ℤ} (hn : n ≠ 0) :
    ∃ y, n • y = x := by
  obtain ⟨z, hz⟩ := genusTorus_exists_division g (genusRealVectorQuotientAddEquiv g x) hn
  refine ⟨(genusRealVectorQuotientAddEquiv g).symm z, ?_⟩
  apply (genusRealVectorQuotientAddEquiv g).injective
  simpa only [map_zsmul, AddEquiv.apply_symm_apply] using hz

/-- The integer torsion of the standard real lattice quotient is finite. -/
theorem genusRealVectorQuotient_zsmulTorsion_finite {g : ℕ} {n : ℤ} (hn : n ≠ 0) :
    Finite (zsmulTorsionSubgroup (GenusRealVector g ⧸ integerPeriodLattice g) n) := by
  let u : GenusTorusUniformization
      (GenusRealVector g ⧸ integerPeriodLattice g) g :=
    ⟨genusRealVectorQuotientAddEquiv g⟩
  exact zsmulTorsion_finite_of_uniformization u hn

/-- Positive-natural torsion in the standard real quotient is finite. -/
theorem genusRealVectorQuotient_natCast_zsmulTorsion_finite
    {g n : ℕ} (hn : 0 < n) :
    Finite (zsmulTorsionSubgroup
      (GenusRealVector g ⧸ integerPeriodLattice g) (n : ℤ)) := by
  have hne : (n : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)
  exact genusRealVectorQuotient_zsmulTorsion_finite (g := g) hne

/-- The standard real exponential transported to a chosen uniformized group. -/
def exponential_to {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) : GenusRealVector g →+ X :=
  u.equiv.symm.toAddMonoidHom.comp (genusTorusExponential g)

/-- The transported exponential to a chosen uniformized group is surjective. -/
theorem exponential_to_surjective {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) : Function.Surjective (exponential_to u) := by
  intro x
  obtain ⟨y, hy⟩ := genusTorusExponential_surjective g (u.equiv x)
  refine ⟨y, ?_⟩
  change u.equiv.symm (genusTorusExponential g y) = x
  rw [hy, u.equiv.symm_apply_apply]

/-- The transported exponential has the same coordinatewise integer kernel. -/
theorem exponential_to_ker {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) :
    (exponential_to u).ker = integerPeriodLattice g := by
  ext x
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro hx
    change u.equiv.symm (genusTorusExponential g x) = 0 at hx
    have hx' : genusTorusExponential g x = 0 := by
      apply u.equiv.symm.injective
      simpa only [map_zero] using hx
    have hx'' : x ∈ (genusTorusExponential g).ker := (AddMonoidHom.mem_ker).mpr hx'
    rw [genusTorusExponential_ker g] at hx''
    exact hx''
  · intro hx
    have hx' : x ∈ (genusTorusExponential g).ker := by
      rw [genusTorusExponential_ker g]
      exact hx
    have hx'' : genusTorusExponential g x = 0 := (AddMonoidHom.mem_ker).mp hx'
    change u.equiv.symm (genusTorusExponential g x) = 0
    rw [hx'', map_zero]

/-- The period-lattice quotient certificate induced by a genus-torus uniformization. -/
def uniformizedPeriodLatticeQuotient {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) :
    PeriodLatticeQuotient (GenusRealVector g) X where
  periodLattice := integerPeriodLattice g
  exponential := exponential_to u
  exponential_surjective := exponential_to_surjective u
  kernel_exponential := exponential_to_ker u

/-- A genus-torus uniformization identifies the standard real lattice quotient with its group. -/
def uniformizedQuotientAddEquiv {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) :
    GenusRealVector g ⧸ integerPeriodLattice g ≃+ X :=
  (uniformizedPeriodLatticeQuotient u).quotientAddEquiv

/-- The transported quotient equivalence evaluates on representatives by the
transported exponential map. -/
@[simp]
theorem uniformizedQuotientAddEquiv_mk {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) (v : GenusRealVector g) :
    uniformizedQuotientAddEquiv u
        (QuotientAddGroup.mk' (integerPeriodLattice g) v) =
      exponential_to u v := by
  exact PeriodLatticeQuotient.quotientAddEquiv_mk
    (uniformizedPeriodLatticeQuotient u) v

/-- The quotient model for a chosen uniformization factors through the standard
torus model and the chosen additive equivalence. -/
theorem uniformizedQuotientAddEquiv_eq_trans {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) :
    uniformizedQuotientAddEquiv u =
      (genusRealVectorQuotientAddEquiv g).trans u.equiv.symm := by
  apply AddEquiv.ext
  intro q
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (integerPeriodLattice g) q
  rfl

/-- Torsion transport through a quotient and then a chosen uniformization
agrees with the direct quotient classification. -/
theorem uniformizedQuotient_zsmulTorsion_addEquiv_eq_direct
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) {n : ℤ} (hn : n ≠ 0) :
    (zsmulTorsion_addEquiv_of_addEquiv (uniformizedQuotientAddEquiv u) n).trans
        (zsmulTorsion_addEquiv_of_uniformization u hn) =
      genusRealVectorQuotient_zsmulTorsion_addEquiv (g := g) hn := by
  rw [uniformizedQuotientAddEquiv_eq_trans u]
  apply AddEquiv.ext
  intro x
  have htransport :
      (zsmulTorsion_addEquiv_of_addEquiv u.equiv n)
          ((zsmulTorsion_addEquiv_of_addEquiv
            ((genusRealVectorQuotientAddEquiv g).trans u.equiv.symm) n) x) =
        (zsmulTorsion_addEquiv_of_addEquiv
          (genusRealVectorQuotientAddEquiv g) n) x := by
    apply Subtype.ext
    simp
  rw [show ((zsmulTorsion_addEquiv_of_addEquiv
      ((genusRealVectorQuotientAddEquiv g).trans u.equiv.symm) n).trans
      (zsmulTorsion_addEquiv_of_uniformization u hn)) x =
      (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)
        ((zsmulTorsion_addEquiv_of_addEquiv u.equiv n)
          ((zsmulTorsion_addEquiv_of_addEquiv
            ((genusRealVectorQuotientAddEquiv g).trans u.equiv.symm) n) x)) by rfl]
  rw [htransport]
  rfl

end
end Uniformization
end Mumford
