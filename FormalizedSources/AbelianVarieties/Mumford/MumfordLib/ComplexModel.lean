/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.Lattice
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex

/-!
# The complex vector-space model

The analytic uniformization uses a complex vector space of dimension `g`,
while the underlying real torus has `2 * g` circle factors.  This file makes
that change of coordinates explicit and transports the period-lattice model
through it.
-/

namespace Mumford
namespace Uniformization

noncomputable section

/-- The complex vector group of dimension `g`. -/
abbrev GenusComplexVector (g : ℕ) := Fin g → ℂ

/-- Split a real pair into its two real coordinates. -/
def realPairToFinTwoLinearEquiv : (ℝ × ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  (LinearEquiv.finTwoArrow ℝ ℝ).symm

/-- Uncurry a two-level real coordinate family. -/
def uncurryGenusLinearEquiv (g : ℕ) :
    (Fin g → Fin 2 → ℝ) ≃ₗ[ℝ] (Fin g × Fin 2 → ℝ) :=
  { toEquiv := (Equiv.curry (Fin g) (Fin 2) ℝ).symm
    map_add' := by
      intro f h
      rfl
    map_smul' := by
      intro r f
      rfl }

/-- Reindex a pair of finite coordinates as a single `Fin (2 * g)` index. -/
def genusComplexIndexEquiv (g : ℕ) : Fin g × Fin 2 ≃ Fin (2 * g) :=
  (finProdFinEquiv (m := g) (n := 2)).trans
    (Equiv.cast (congrArg Fin (Nat.mul_comm g 2)))

/-- Reindex real coordinates along `genusComplexIndexEquiv`. -/
def reindexGenusRealLinearEquiv (g : ℕ) :
    (Fin g × Fin 2 → ℝ) ≃ₗ[ℝ] GenusRealVector g :=
  { toEquiv :=
      Equiv.piCongrLeft (fun _ : Fin (2 * g) => ℝ) (genusComplexIndexEquiv g)
    map_add' := by
      intro f h
      funext i
      dsimp [Equiv.piCongrLeft, Equiv.piCongrLeft']
      simp
    map_smul' := by
      intro r f
      funext i
      dsimp [Equiv.piCongrLeft, Equiv.piCongrLeft']
      simp }

/-- The canonical additive equivalence from complex `g`-coordinates to real
`2g`-coordinates. -/
def genusComplexVectorRealification (g : ℕ) :
    GenusComplexVector g ≃ₗ[ℝ] GenusRealVector g :=
  (LinearEquiv.piCongrRight (fun _ => Complex.equivRealProdLm)).trans
    ((LinearEquiv.piCongrRight (fun _ => realPairToFinTwoLinearEquiv)).trans
      ((uncurryGenusLinearEquiv g).trans (reindexGenusRealLinearEquiv g)))

/- The realification is continuous for the standard finite-dimensional
   topologies. -/
theorem genusComplexVectorRealification_continuous (g : ℕ) :
    Continuous (genusComplexVectorRealification g) :=
  (genusComplexVectorRealification g).toLinearMap.continuous_of_finiteDimensional

/-- The complex-to-real coordinate change evaluated on a paired index. -/
@[simp]
theorem genusComplexVectorRealification_at_index (g : ℕ)
    (z : GenusComplexVector g) (i : Fin g) (j : Fin 2) :
    genusComplexVectorRealification g z (genusComplexIndexEquiv g (i, j)) =
      (realPairToFinTwoLinearEquiv (Complex.equivRealProdLm (z i))) j := by
  have hrr (f : Fin g × Fin 2 → ℝ) :
      reindexGenusRealLinearEquiv g f (genusComplexIndexEquiv g (i, j)) = f (i, j) := by
    change
      (Equiv.piCongrLeft (fun _ : Fin (2 * g) => ℝ)
        (genusComplexIndexEquiv g)) f (genusComplexIndexEquiv g (i, j)) = f (i, j)
    exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (2 * g) => ℝ)
      (genusComplexIndexEquiv g) f (i, j)
  change reindexGenusRealLinearEquiv g
      ((uncurryGenusLinearEquiv g)
        ((LinearEquiv.piCongrRight (fun _ => realPairToFinTwoLinearEquiv))
          ((LinearEquiv.piCongrRight (fun _ => Complex.equivRealProdLm)) z)))
      (genusComplexIndexEquiv g (i, j)) = _
  rw [hrr]
  rfl

@[simp]
theorem genusComplexVectorRealification_real (g : ℕ)
    (z : GenusComplexVector g) (i : Fin g) :
    genusComplexVectorRealification g z (genusComplexIndexEquiv g (i, 0)) =
      (z i).re := by
  rw [genusComplexVectorRealification_at_index]
  simp [realPairToFinTwoLinearEquiv]

@[simp]
theorem genusComplexVectorRealification_imag (g : ℕ)
    (z : GenusComplexVector g) (i : Fin g) :
    genusComplexVectorRealification g z (genusComplexIndexEquiv g (i, 1)) =
      (z i).im := by
  rw [genusComplexVectorRealification_at_index]
  simp [realPairToFinTwoLinearEquiv]

/-- The inverse realification reconstructs each complex coordinate from its
real and imaginary coordinates in the `Fin (2 * g)` model. -/
@[simp]
theorem genusComplexVectorRealification_symm_apply (g : ℕ)
    (v : GenusRealVector g) (i : Fin g) :
    (genusComplexVectorRealification g).symm v i =
      Complex.equivRealProdLm.symm
        (v (genusComplexIndexEquiv g (i, 0)),
          v (genusComplexIndexEquiv g (i, 1))) := by
  apply (Complex.equivRealProdLm).injective
  rw [Complex.equivRealProdLm_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The period lattice in complex coordinates, obtained by pulling back the
standard integer lattice along realification. -/
def complexPeriodLattice (g : ℕ) : AddSubgroup (GenusComplexVector g) :=
  AddSubgroup.comap (genusComplexVectorRealification g).toAddMonoidHom
    (integerPeriodLattice g)

/-- The coordinatewise exponential after changing complex coordinates to real
coordinates. -/
def complexGenusTorusExponential (g : ℕ) :
    GenusComplexVector g →+ GenusTorus g :=
  (genusTorusExponential g).comp
    (genusComplexVectorRealification g).toAddMonoidHom

/- The realified complex-coordinate exponential is continuous. -/
theorem complexGenusTorusExponential_continuous (g : ℕ) :
    Continuous (complexGenusTorusExponential g) := by
  exact (genusTorusExponential_continuous g).comp
    (genusComplexVectorRealification_continuous g)

/-- The realified exponential is surjective. -/
theorem complexGenusTorusExponential_surjective (g : ℕ) :
    Function.Surjective (complexGenusTorusExponential g) := by
  intro y
  obtain ⟨v, hv⟩ := genusTorusExponential_surjective g y
  obtain ⟨z, hz⟩ := (genusComplexVectorRealification g).surjective v
  refine ⟨z, ?_⟩
  change genusTorusExponential g (genusComplexVectorRealification g z) = y
  rw [hz, hv]

/-- The pulled-back integer lattice is exactly the kernel of the realified
exponential. -/
theorem complexGenusTorusExponential_ker (g : ℕ) :
    (complexGenusTorusExponential g).ker = complexPeriodLattice g := by
  ext z
  change genusTorusExponential g (genusComplexVectorRealification g z) = 0 ↔
    genusComplexVectorRealification g z ∈ integerPeriodLattice g
  rw [← AddMonoidHom.mem_ker, genusTorusExponential_ker]

/-- A complex-coordinate period-lattice quotient certificate. -/
def standardComplexGenusPeriodLatticeQuotient (g : ℕ) :
    PeriodLatticeQuotient (GenusComplexVector g) (GenusTorus g) where
  periodLattice := complexPeriodLattice g
  exponential := complexGenusTorusExponential g
  exponential_surjective := complexGenusTorusExponential_surjective g
  kernel_exponential := complexGenusTorusExponential_ker g

/-- The complex-coordinate quotient is equivalent to the standard genus torus. -/
def complexGenusQuotientAddEquiv (g : ℕ) :
    GenusComplexVector g ⧸ complexPeriodLattice g ≃+ GenusTorus g :=
  (standardComplexGenusPeriodLatticeQuotient g).quotientAddEquiv

@[simp]
theorem complexGenusQuotientAddEquiv_mk (g : ℕ) (z : GenusComplexVector g) :
    complexGenusQuotientAddEquiv g
        (QuotientAddGroup.mk' (complexPeriodLattice g) z) =
      complexGenusTorusExponential g z := by
  exact PeriodLatticeQuotient.quotientAddEquiv_mk
    (standardComplexGenusPeriodLatticeQuotient g) z

/- Two complex representatives define the same quotient point exactly when
   their difference is a complex period. -/
theorem complexGenusQuotientAddEquiv_mk_eq_iff (g : ℕ)
    (z w : GenusComplexVector g) :
    complexGenusQuotientAddEquiv g
        (QuotientAddGroup.mk' (complexPeriodLattice g) z) =
      complexGenusQuotientAddEquiv g
        (QuotientAddGroup.mk' (complexPeriodLattice g) w) ↔
      z - w ∈ complexPeriodLattice g := by
  exact PeriodLatticeQuotient.quotientAddEquiv_mk_eq_iff
    (standardComplexGenusPeriodLatticeQuotient g) z w

/- The realification carries the complex period quotient to the standard real
   period quotient. -/
def complexQuotientToRealQuotientAddHom (g : ℕ) :
    (GenusComplexVector g ⧸ complexPeriodLattice g) →+
      (GenusRealVector g ⧸ integerPeriodLattice g) :=
  QuotientAddGroup.map (complexPeriodLattice g) (integerPeriodLattice g)
    (genusComplexVectorRealification g).toAddMonoidHom (by
      intro z hz
      exact AddSubgroup.mem_comap.mp hz)

def realQuotientToComplexQuotientAddHom (g : ℕ) :
    (GenusRealVector g ⧸ integerPeriodLattice g) →+
      (GenusComplexVector g ⧸ complexPeriodLattice g) :=
  QuotientAddGroup.map (integerPeriodLattice g) (complexPeriodLattice g)
    (genusComplexVectorRealification g).symm.toAddMonoidHom (by
      intro v hv
      change genusComplexVectorRealification g
          ((genusComplexVectorRealification g).symm v) ∈ integerPeriodLattice g
      simpa only [LinearEquiv.apply_symm_apply] using hv)

/- The quotient map induced by realification is continuous. -/
theorem complexQuotientToRealQuotientAddHom_continuous (g : ℕ) :
    Continuous (complexQuotientToRealQuotientAddHom g) := by
  rw [(QuotientAddGroup.isQuotientMap_mk
    (complexPeriodLattice g)).continuous_iff]
  change Continuous (fun z : GenusComplexVector g =>
    QuotientAddGroup.mk' (integerPeriodLattice g)
      (genusComplexVectorRealification g z))
  exact QuotientAddGroup.continuous_mk.comp
    (genusComplexVectorRealification_continuous g)

/- The inverse quotient map induced by the inverse realification is continuous. -/
theorem realQuotientToComplexQuotientAddHom_continuous (g : ℕ) :
    Continuous (realQuotientToComplexQuotientAddHom g) := by
  rw [(QuotientAddGroup.isQuotientMap_mk
    (integerPeriodLattice g)).continuous_iff]
  change Continuous (fun v : GenusRealVector g =>
    QuotientAddGroup.mk' (complexPeriodLattice g)
      ((genusComplexVectorRealification g).symm v))
  exact QuotientAddGroup.continuous_mk.comp
    ((genusComplexVectorRealification g).symm.toLinearMap.continuous_of_finiteDimensional)

theorem realQuotientToComplexQuotientAddHom_comp (g : ℕ) :
    (realQuotientToComplexQuotientAddHom g).comp
        (complexQuotientToRealQuotientAddHom g) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro q
  refine QuotientAddGroup.induction_on q ?_
  intro z
  simp [complexQuotientToRealQuotientAddHom,
    realQuotientToComplexQuotientAddHom]

theorem complexQuotientToRealQuotientAddHom_comp (g : ℕ) :
    (complexQuotientToRealQuotientAddHom g).comp
        (realQuotientToComplexQuotientAddHom g) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro q
  refine QuotientAddGroup.induction_on q ?_
  intro v
  simp [complexQuotientToRealQuotientAddHom,
    realQuotientToComplexQuotientAddHom]

/-- The additive equivalence between the complex and real period quotients. -/
def complexQuotientToRealQuotientAddEquiv (g : ℕ) :
    (GenusComplexVector g ⧸ complexPeriodLattice g) ≃+
      (GenusRealVector g ⧸ integerPeriodLattice g) :=
  AddMonoidHom.toAddEquiv (complexQuotientToRealQuotientAddHom g)
    (realQuotientToComplexQuotientAddHom g)
    (realQuotientToComplexQuotientAddHom_comp g)
    (complexQuotientToRealQuotientAddHom_comp g)

/-- The complex and real period quotients are homeomorphic as additive groups. -/
noncomputable def complexQuotientToRealQuotientHomeomorph (g : ℕ) :
    (GenusComplexVector g ⧸ complexPeriodLattice g) ≃ₜ
      (GenusRealVector g ⧸ integerPeriodLattice g) :=
  { complexQuotientToRealQuotientAddEquiv g with
    continuous_toFun := complexQuotientToRealQuotientAddHom_continuous g
    continuous_invFun := realQuotientToComplexQuotientAddHom_continuous g }

@[simp]
theorem complexQuotientToRealQuotientAddEquiv_mk (g : ℕ)
    (z : GenusComplexVector g) :
    complexQuotientToRealQuotientAddEquiv g
        (QuotientAddGroup.mk' (complexPeriodLattice g) z) =
      QuotientAddGroup.mk' (integerPeriodLattice g)
        (genusComplexVectorRealification g z) := by
  change complexQuotientToRealQuotientAddHom g
      (QuotientAddGroup.mk' (complexPeriodLattice g) z) = _
  simp [complexQuotientToRealQuotientAddHom]

@[simp]
theorem realQuotientToComplexQuotientAddEquiv_mk (g : ℕ)
    (v : GenusRealVector g) :
    (complexQuotientToRealQuotientAddEquiv g).symm
        (QuotientAddGroup.mk' (integerPeriodLattice g) v) =
      QuotientAddGroup.mk' (complexPeriodLattice g)
        ((genusComplexVectorRealification g).symm v) := by
  change realQuotientToComplexQuotientAddHom g
      (QuotientAddGroup.mk' (integerPeriodLattice g) v) = _
  simp [realQuotientToComplexQuotientAddHom]

/- The converse representative criterion is useful when a real period
   calculation is transported back to complex coordinates. -/
theorem realQuotientToComplexQuotientAddEquiv_mk_eq_iff (g : ℕ)
    (v w : GenusRealVector g) :
    (complexQuotientToRealQuotientAddEquiv g).symm
        (QuotientAddGroup.mk' (integerPeriodLattice g) v) =
      (complexQuotientToRealQuotientAddEquiv g).symm
        (QuotientAddGroup.mk' (integerPeriodLattice g) w) ↔
      v - w ∈ integerPeriodLattice g := by
  constructor
  · intro h
    have h' : QuotientAddGroup.mk' (integerPeriodLattice g) v =
        QuotientAddGroup.mk' (integerPeriodLattice g) w := by
      simpa only [AddEquiv.apply_symm_apply] using
        congrArg (complexQuotientToRealQuotientAddEquiv g) h
    have hreal :
        genusRealVectorQuotientAddEquiv g
            (QuotientAddGroup.mk' (integerPeriodLattice g) v) =
          genusRealVectorQuotientAddEquiv g
            (QuotientAddGroup.mk' (integerPeriodLattice g) w) :=
      congrArg (genusRealVectorQuotientAddEquiv g) h'
    exact (PeriodLatticeQuotient.quotientAddEquiv_mk_eq_iff
      (standardGenusTorusPeriodLatticeQuotient g) v w).mp hreal
  · intro h
    have hreal :
        genusRealVectorQuotientAddEquiv g
            (QuotientAddGroup.mk' (integerPeriodLattice g) v) =
          genusRealVectorQuotientAddEquiv g
            (QuotientAddGroup.mk' (integerPeriodLattice g) w) :=
      (PeriodLatticeQuotient.quotientAddEquiv_mk_eq_iff
        (standardGenusTorusPeriodLatticeQuotient g) v w).mpr h
    have h' : QuotientAddGroup.mk' (integerPeriodLattice g) v =
        QuotientAddGroup.mk' (integerPeriodLattice g) w :=
      (genusRealVectorQuotientAddEquiv g).injective hreal
    exact congrArg (complexQuotientToRealQuotientAddEquiv g).symm h'

/- The quotient equivalence intertwines the two exponential models. -/
theorem complexQuotientToRealQuotientAddEquiv_trans_genusRealVectorQuotient
    (g : ℕ) :
    (complexQuotientToRealQuotientAddEquiv g).trans
        (genusRealVectorQuotientAddEquiv g) =
      complexGenusQuotientAddEquiv g := by
  apply AddEquiv.ext
  intro q
  refine QuotientAddGroup.induction_on q ?_
  intro z
  change genusRealVectorQuotientAddEquiv g
      (complexQuotientToRealQuotientAddEquiv g
        (QuotientAddGroup.mk' (complexPeriodLattice g) z)) =
    complexGenusQuotientAddEquiv g
      (QuotientAddGroup.mk' (complexPeriodLattice g) z)
  rw [complexQuotientToRealQuotientAddEquiv_mk,
    genusRealVectorQuotientAddEquiv_mk,
    complexGenusQuotientAddEquiv_mk]
  rfl

/-- The complex-coordinate quotient has the expected signed-integer torsion
classification. -/
def complexGenusQuotient_zsmulTorsion_addEquiv {g : ℕ} {n : ℤ} (hn : n ≠ 0) :
    zsmulTorsionSubgroup
        (GenusComplexVector g ⧸ complexPeriodLattice g) n ≃+
      (Fin (2 * g) → ZMod n.natAbs) :=
  (zsmulTorsion_addEquiv_of_addEquiv (complexGenusQuotientAddEquiv g) n).trans
    (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)

@[simp]
theorem complexGenusQuotient_zsmulTorsion_addEquiv_apply
    {g : ℕ} {n : ℤ} (hn : n ≠ 0)
    (x : zsmulTorsionSubgroup
      (GenusComplexVector g ⧸ complexPeriodLattice g) n) :
    ((complexGenusQuotient_zsmulTorsion_addEquiv hn) x :
        Fin (2 * g) → ZMod n.natAbs) =
      (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)
        ((zsmulTorsion_addEquiv_of_addEquiv
          (complexGenusQuotientAddEquiv g) n) x) := by
  rfl

/- The positive-natural notation is obtained from the signed classification by
transporting the canonical equality `(n : ℤ).natAbs = n`. -/
noncomputable def complexGenusQuotient_natCast_zsmulTorsion_addEquiv
    {g n : ℕ} (hn : 0 < n) :
    zsmulTorsionSubgroup
        (GenusComplexVector g ⧸ complexPeriodLattice g) (n : ℤ) ≃+
      (Fin (2 * g) → ZMod n) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  let castEquiv : (Fin (2 * g) → ZMod (n : ℤ).natAbs) ≃+
      (Fin (2 * g) → ZMod n) :=
    AddEquiv.cast (M := fun m : ℕ => Fin (2 * g) → ZMod m)
      (Int.natAbs_ofNat' n)
  exact (complexGenusQuotient_zsmulTorsion_addEquiv hne).trans castEquiv

theorem complexGenusQuotient_natCast_zsmulTorsion_addEquiv_eq_trans_cast
    {g n : ℕ} (hn : 0 < n) :
    complexGenusQuotient_natCast_zsmulTorsion_addEquiv hn =
      (complexGenusQuotient_zsmulTorsion_addEquiv
        (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn))).trans
        (AddEquiv.cast (M := fun m : ℕ => Fin (2 * g) → ZMod m)
          (Int.natAbs_ofNat' n)) := by
  rfl

@[simp]
theorem complexGenusQuotient_natCast_zsmulTorsion_addEquiv_apply
    {g n : ℕ} (hn : 0 < n)
    (x : zsmulTorsionSubgroup
      (GenusComplexVector g ⧸ complexPeriodLattice g) (n : ℤ)) :
    (complexGenusQuotient_natCast_zsmulTorsion_addEquiv hn) x =
      (AddEquiv.cast (M := fun m : ℕ => Fin (2 * g) → ZMod m)
          (Int.natAbs_ofNat' n))
        ((complexGenusQuotient_zsmulTorsion_addEquiv
          (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn))) x) := by
  rfl

/-- The complex-coordinate quotient has torsion order `|n| ^ (2 * g)`. -/
theorem complexGenusQuotient_zsmulTorsion_card {g : ℕ} {n : ℤ} (hn : n ≠ 0) :
    Nat.card
        (zsmulTorsionSubgroup
          (GenusComplexVector g ⧸ complexPeriodLattice g) n) =
      n.natAbs ^ (2 * g) := by
  calc
    Nat.card
        (zsmulTorsionSubgroup
          (GenusComplexVector g ⧸ complexPeriodLattice g) n) =
        Nat.card (zsmulTorsionSubgroup (GenusTorus g) n) :=
      zsmulTorsion_card_eq_of_addEquiv (complexGenusQuotientAddEquiv g) n
    _ = n.natAbs ^ (2 * g) := genusTorus_zsmulTorsion_card g hn

/-- The nonzero-integer torsion of the complex period quotient is finite. -/
theorem complexGenusQuotient_zsmulTorsion_finite {g : ℕ} {n : ℤ} (hn : n ≠ 0) :
    Finite
      (zsmulTorsionSubgroup
        (GenusComplexVector g ⧸ complexPeriodLattice g) n) := by
  letI : NeZero n.natAbs := ⟨Int.natAbs_pos.mpr hn |>.ne'⟩
  exact (complexGenusQuotient_zsmulTorsion_addEquiv hn).toEquiv.finite_iff.mpr
    inferInstance

/-- Positive-natural torsion in the complex period quotient has the expected
cardinality. -/
theorem complexGenusQuotient_natCast_zsmulTorsion_card
    {g n : ℕ} (hn : 0 < n) :
    Nat.card
        (zsmulTorsionSubgroup
          (GenusComplexVector g ⧸ complexPeriodLattice g) (n : ℤ)) =
      n ^ (2 * g) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  simpa using complexGenusQuotient_zsmulTorsion_card (g := g) hne

/-- Positive-natural torsion in the complex period quotient is finite. -/
theorem complexGenusQuotient_natCast_zsmulTorsion_finite
    {g n : ℕ} (hn : 0 < n) :
    Finite
      (zsmulTorsionSubgroup
        (GenusComplexVector g ⧸ complexPeriodLattice g) (n : ℤ)) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  exact complexGenusQuotient_zsmulTorsion_finite (g := g) hne

end
end Uniformization
end Mumford
