/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.ComplexModel
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Complex uniformization interface

The analytic uniformization theorem supplies an additive equivalence from a
complex vector-space quotient by a period lattice to the underlying complex
torus.  Mathlib does not currently provide the analytic Lie-group theorem, so
this module records that witness explicitly and exposes the algebraic
consequences that follow from it.
-/

namespace Mumford
namespace Uniformization

noncomputable section

/-- A chosen additive uniformization by a complex period-lattice quotient.

This is the algebraic interface to the analytic uniformization theorem; the
existence of such a witness is intentionally a hypothesis rather than an
unproved global declaration. -/
structure ComplexTorusUniformization (X : Type*) [AddCommGroup X] (g : ℕ) where
  equiv : X ≃+ (GenusComplexVector g ⧸ complexPeriodLattice g)

/-- Package an additive exponential with the canonical period kernel as a
period-lattice quotient certificate. -/
def complexPeriodLatticeQuotientOfExponential
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (exponential : GenusComplexVector g →+ X)
    (hsurj : Function.Surjective exponential)
    (hker : exponential.ker = complexPeriodLattice g) :
    PeriodLatticeQuotient (GenusComplexVector g) X where
  periodLattice := complexPeriodLattice g
  exponential := exponential
  exponential_surjective := hsurj
  kernel_exponential := hker

/- A continuous surjective exponential into a locally compact Hausdorff
   additive group is open by the topological-group open mapping theorem. -/
theorem isOpenQuotientMap_of_continuous_surjective_of_locallyCompact
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [ContinuousAdd X] {g : ℕ}
    (exponential : GenusComplexVector g →+ X)
    (hsurj : Function.Surjective exponential)
    (hcont : Continuous exponential) :
    IsOpenQuotientMap exponential := by
  rw [isOpenQuotientMap_iff]
  exact ⟨hsurj, hcont,
    AddMonoidHom.isOpenMap_of_sigmaCompact exponential hsurj hcont⟩

/- The standard complex-coordinate exponential satisfies the hypotheses of the
   open-mapping theorem, so its period quotient carries the canonical topology. -/
theorem complexGenusTorusExponential_isOpenQuotientMap (g : ℕ) :
    IsOpenQuotientMap (complexGenusTorusExponential g) := by
  exact isOpenQuotientMap_of_continuous_surjective_of_locallyCompact
    (complexGenusTorusExponential g)
    (complexGenusTorusExponential_surjective g)
    (complexGenusTorusExponential_continuous g)

/-- A surjective additive exponential with the canonical period kernel induces
the chosen complex uniformization witness. -/
def ComplexTorusUniformization.ofExponential
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (exponential : GenusComplexVector g →+ X)
    (hsurj : Function.Surjective exponential)
    (hker : exponential.ker = complexPeriodLattice g) :
    ComplexTorusUniformization X g where
  equiv :=
    (complexPeriodLatticeQuotientOfExponential exponential hsurj hker).quotientAddEquiv.symm

/-- An open quotient exponential supplies the topological form of the complex
uniformization witness.  The open-quotient hypothesis is the analytic input;
the additive and kernel data are inherited from `ofExponential`. -/
noncomputable def ComplexTorusUniformization.ofExponential_toHomeomorph
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (exponential : GenusComplexVector g →+ X)
    (hsurj : Function.Surjective exponential)
    (hker : exponential.ker = complexPeriodLattice g)
    (hquot : IsOpenQuotientMap exponential) :
    X ≃ₜ (GenusComplexVector g ⧸ complexPeriodLattice g) :=
  (complexPeriodLatticeQuotientOfExponential exponential hsurj hker)
    |>.quotientHomeomorph hquot |>.symm

/- The open-mapping variant exposes the usual locally compact Hausdorff target
   assumptions directly, so callers need not manufacture an open-quotient
   certificate separately. -/
noncomputable def ComplexTorusUniformization.ofExponential_toHomeomorph_of_locallyCompact
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [ContinuousAdd X] {g : ℕ}
    (exponential : GenusComplexVector g →+ X)
    (hsurj : Function.Surjective exponential)
    (hker : exponential.ker = complexPeriodLattice g)
    (hcont : Continuous exponential) :
    X ≃ₜ (GenusComplexVector g ⧸ complexPeriodLattice g) :=
  ComplexTorusUniformization.ofExponential_toHomeomorph exponential hsurj hker
    (isOpenQuotientMap_of_continuous_surjective_of_locallyCompact
      exponential hsurj hcont)

@[simp]
theorem ComplexTorusUniformization.ofExponential_toHomeomorph_of_locallyCompact_apply
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [ContinuousAdd X] {g : ℕ}
    (exponential : GenusComplexVector g →+ X)
    (hsurj : Function.Surjective exponential)
    (hker : exponential.ker = complexPeriodLattice g)
    (hcont : Continuous exponential) (x : X) :
    ComplexTorusUniformization.ofExponential_toHomeomorph_of_locallyCompact
        exponential hsurj hker hcont x =
      (ComplexTorusUniformization.ofExponential exponential hsurj hker).equiv x :=
  rfl

@[simp]
theorem ComplexTorusUniformization.ofExponential_toHomeomorph_apply
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (exponential : GenusComplexVector g →+ X)
    (hsurj : Function.Surjective exponential)
    (hker : exponential.ker = complexPeriodLattice g)
    (hquot : IsOpenQuotientMap exponential) (x : X) :
    ComplexTorusUniformization.ofExponential_toHomeomorph
        exponential hsurj hker hquot x =
      (ComplexTorusUniformization.ofExponential exponential hsurj hker).equiv x :=
  rfl

@[simp]
theorem ComplexTorusUniformization.ofExponential_equiv_symm_mk
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (exponential : GenusComplexVector g →+ X)
    (hsurj : Function.Surjective exponential)
    (hker : exponential.ker = complexPeriodLattice g)
    (z : GenusComplexVector g) :
    (ComplexTorusUniformization.ofExponential exponential hsurj hker).equiv.symm
        (QuotientAddGroup.mk' (complexPeriodLattice g) z) =
      exponential z := by
  change
    (complexPeriodLatticeQuotientOfExponential exponential hsurj hker).quotientAddEquiv
        (QuotientAddGroup.mk' (complexPeriodLattice g) z) =
      exponential z
  exact PeriodLatticeQuotient.quotientAddEquiv_mk
    (complexPeriodLatticeQuotientOfExponential exponential hsurj hker) z

/- The complex period quotient is homeomorphic to the standard real torus via
   its own exponential, independently of the intermediate realification map. -/
noncomputable def complexGenusQuotientHomeomorph (g : ℕ) :
    (GenusComplexVector g ⧸ complexPeriodLattice g) ≃ₜ GenusTorus g :=
  (standardComplexGenusPeriodLatticeQuotient g).quotientHomeomorph
    (complexGenusTorusExponential_isOpenQuotientMap g)

@[simp]
theorem complexGenusQuotientHomeomorph_apply (g : ℕ)
    (q : GenusComplexVector g ⧸ complexPeriodLattice g) :
    complexGenusQuotientHomeomorph g q = complexGenusQuotientAddEquiv g q :=
  rfl

@[simp]
theorem complexGenusQuotientHomeomorph_mk (g : ℕ)
    (z : GenusComplexVector g) :
    complexGenusQuotientHomeomorph g
        (QuotientAddGroup.mk' (complexPeriodLattice g) z) =
      complexGenusTorusExponential g z := by
  exact PeriodLatticeQuotient.quotientHomeomorph_mk
    (standardComplexGenusPeriodLatticeQuotient g)
    (complexGenusTorusExponential_isOpenQuotientMap g) z

/-- Two complex uniformization witnesses agree when their quotient maps agree
on representatives. -/
@[ext]
theorem ComplexTorusUniformization.ext
    {X : Type*} [AddCommGroup X] {g : ℕ}
    {u v : ComplexTorusUniformization X g}
    (h : ∀ z : GenusComplexVector g,
      u.equiv.symm (QuotientAddGroup.mk' (complexPeriodLattice g) z) =
        v.equiv.symm (QuotientAddGroup.mk' (complexPeriodLattice g) z)) :
    u = v := by
  have hinv : u.equiv.symm = v.equiv.symm := by
    apply AddEquiv.ext
    intro q
    refine QuotientAddGroup.induction_on q ?_
    intro z
    exact h z
  have hequiv : u.equiv = v.equiv := by
    simpa only [AddEquiv.symm_symm] using congrArg AddEquiv.symm hinv
  cases u
  cases v
  simpa only [ComplexTorusUniformization.mk.injEq] using hequiv

/-- The quotient witness induced by an exponential is unique among witnesses
whose inverse map has the same representative formula. -/
theorem ComplexTorusUniformization.eq_of_exponential_compatibility
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (exponential : GenusComplexVector g →+ X)
    (hsurj : Function.Surjective exponential)
    (hker : exponential.ker = complexPeriodLattice g)
    (hcompat : ∀ z : GenusComplexVector g,
      u.equiv.symm (QuotientAddGroup.mk' (complexPeriodLattice g) z) =
        exponential z) :
    u = ComplexTorusUniformization.ofExponential exponential hsurj hker := by
  apply ComplexTorusUniformization.ext
  intro z
  rw [ComplexTorusUniformization.ofExponential_equiv_symm_mk]
  exact hcompat z

/- Recover the exponential map from a chosen quotient uniformization. -/
def ComplexTorusUniformization.exponential
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) :
    GenusComplexVector g →+ X :=
  u.equiv.symm.toAddMonoidHom.comp
    (QuotientAddGroup.mk' (complexPeriodLattice g))

@[simp]
theorem ComplexTorusUniformization.exponential_apply
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) (z : GenusComplexVector g) :
    u.exponential z =
      u.equiv.symm (QuotientAddGroup.mk' (complexPeriodLattice g) z) :=
  rfl

theorem ComplexTorusUniformization.exponential_surjective
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) :
    Function.Surjective u.exponential := by
  intro x
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective
    (complexPeriodLattice g) (u.equiv x)
  refine ⟨z, ?_⟩
  change u.equiv.symm (QuotientAddGroup.mk' (complexPeriodLattice g) z) = x
  rw [hz, u.equiv.symm_apply_apply]

theorem ComplexTorusUniformization.exponential_ker
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) :
    u.exponential.ker = complexPeriodLattice g := by
  ext z
  rw [AddMonoidHom.mem_ker]
  change u.equiv.symm (QuotientAddGroup.mk' (complexPeriodLattice g) z) = 0 ↔
    z ∈ complexPeriodLattice g
  constructor
  · intro hz
    have hz' : QuotientAddGroup.mk' (complexPeriodLattice g) z = 0 := by
      apply u.equiv.symm.injective
      simpa only [map_zero] using hz
    rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk'] at hz'
    exact hz'
  · intro hz
    have hz' : QuotientAddGroup.mk' (complexPeriodLattice g) z = 0 := by
      rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
      exact hz
    rw [hz', map_zero]

/- Reconstructing a witness from its recovered exponential is definitionally
   compatible with the original representative formula. -/
theorem ComplexTorusUniformization.ofExponential_exponential
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) :
    ComplexTorusUniformization.ofExponential
        u.exponential u.exponential_surjective u.exponential_ker = u := by
  symm
  exact ComplexTorusUniformization.eq_of_exponential_compatibility u
    u.exponential u.exponential_surjective u.exponential_ker
    (fun z => rfl)

/- Package the recovered map back into a period-lattice quotient certificate. -/
def ComplexTorusUniformization.toPeriodLatticeQuotient
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) :
    PeriodLatticeQuotient (GenusComplexVector g) X :=
  complexPeriodLatticeQuotientOfExponential
    u.exponential u.exponential_surjective u.exponential_ker

theorem ComplexTorusUniformization.toPeriodLatticeQuotient_quotientAddEquiv
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) :
    u.toPeriodLatticeQuotient.quotientAddEquiv = u.equiv.symm := by
  apply AddEquiv.ext
  intro q
  refine QuotientAddGroup.induction_on q ?_
  intro z
  rfl

/-- Forget the complex coordinates and obtain the real genus-torus model. -/
def ComplexTorusUniformization.toGenusTorusUniformization
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) : GenusTorusUniformization X g :=
  { equiv := u.equiv.trans (complexGenusQuotientAddEquiv g) }

/-- Repackage a real genus-torus uniformization as a complex period-quotient
uniformization. -/
def GenusTorusUniformization.toComplexTorusUniformization
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) : ComplexTorusUniformization X g :=
  { equiv := u.equiv.trans (complexGenusQuotientAddEquiv g).symm }

@[simp]
theorem ComplexTorusUniformization.toGenusTorusUniformization_apply
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) (x : X) :
    u.toGenusTorusUniformization.equiv x =
      complexGenusQuotientAddEquiv g (u.equiv x) :=
  rfl

@[simp]
theorem GenusTorusUniformization.toComplexTorusUniformization_apply
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) (x : X) :
    u.toComplexTorusUniformization.equiv x =
      (complexGenusQuotientAddEquiv g).symm (u.equiv x) :=
  rfl

theorem GenusTorusUniformization.toComplexTorusUniformization_toGenusTorusUniformization
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : GenusTorusUniformization X g) :
    u.toComplexTorusUniformization.toGenusTorusUniformization = u := by
  apply congrArg (fun e => GenusTorusUniformization.mk e)
  apply AddEquiv.ext
  intro x
  simp

theorem ComplexTorusUniformization.toGenusTorusUniformization_toComplexTorusUniformization
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) :
    u.toGenusTorusUniformization.toComplexTorusUniformization = u := by
  apply congrArg (fun e => ComplexTorusUniformization.mk e)
  apply AddEquiv.ext
  intro x
  simp

/-- The complex and real witness interfaces carry exactly the same data. -/
def genusTorusUniformizationEquivComplexTorusUniformization
    {X : Type*} [AddCommGroup X] {g : ℕ} :
    GenusTorusUniformization X g ≃ ComplexTorusUniformization X g where
  toFun := GenusTorusUniformization.toComplexTorusUniformization
  invFun := ComplexTorusUniformization.toGenusTorusUniformization
  left_inv := GenusTorusUniformization.toComplexTorusUniformization_toGenusTorusUniformization
  right_inv := ComplexTorusUniformization.toGenusTorusUniformization_toComplexTorusUniformization

theorem complexTorusUniformization_nonempty_iff_genusTorusUniformization_nonempty
    {X : Type*} [AddCommGroup X] {g : ℕ} :
    Nonempty (ComplexTorusUniformization X g) ↔
      Nonempty (GenusTorusUniformization X g) := by
  constructor
  · rintro ⟨u⟩
    exact ⟨u.toGenusTorusUniformization⟩
  · rintro ⟨u⟩
    exact ⟨u.toComplexTorusUniformization⟩

/- The open quotient exponential identifies the real period quotient with the
   product torus also at the topological level. -/
noncomputable def genusRealVectorQuotientHomeomorph (g : ℕ) :
    (GenusRealVector g ⧸ integerPeriodLattice g) ≃ₜ GenusTorus g :=
  (standardGenusTorusPeriodLatticeQuotient g).quotientHomeomorph
    (genusTorusExponential_isOpenQuotientMap g)

@[simp]
theorem genusRealVectorQuotientHomeomorph_apply (g : ℕ)
    (q : GenusRealVector g ⧸ integerPeriodLattice g) :
    genusRealVectorQuotientHomeomorph g q = genusRealVectorQuotientAddEquiv g q :=
  rfl

/- The complex quotient homeomorphism agrees with the composite obtained by
   realifying first and then applying the standard real quotient model. -/
theorem complexGenusQuotientHomeomorph_eq_trans (g : ℕ) :
    (complexQuotientToRealQuotientHomeomorph g).trans
        (genusRealVectorQuotientHomeomorph g) =
      complexGenusQuotientHomeomorph g := by
  apply Homeomorph.ext
  intro q
  refine QuotientAddGroup.induction_on q ?_
  intro z
  change genusRealVectorQuotientHomeomorph g
      (complexQuotientToRealQuotientHomeomorph g
        (QuotientAddGroup.mk' (complexPeriodLattice g) z)) =
    complexGenusQuotientHomeomorph g
      (QuotientAddGroup.mk' (complexPeriodLattice g) z)
  rw [complexGenusQuotientHomeomorph_mk]
  rw [genusRealVectorQuotientHomeomorph_apply]
  change genusRealVectorQuotientAddEquiv g
      (complexQuotientToRealQuotientAddEquiv g
        (QuotientAddGroup.mk' (complexPeriodLattice g) z)) =
    complexGenusTorusExponential g z
  rw [complexQuotientToRealQuotientAddEquiv_mk,
    genusRealVectorQuotientAddEquiv_mk,
    complexGenusTorusExponential]
  rfl

/- The analytic witness can be upgraded to a homeomorphism once continuity of
   its chosen equivalence and inverse has been supplied.  Keeping these as
   explicit hypotheses records the genuine analytic boundary. -/
noncomputable def ComplexTorusUniformization.toHomeomorph
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    X ≃ₜ (GenusComplexVector g ⧸ complexPeriodLattice g) :=
  { toEquiv := u.equiv.toEquiv
    continuous_toFun := hcont
    continuous_invFun := hcont_symm }

@[simp]
theorem ComplexTorusUniformization.toHomeomorph_apply
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) (x : X) :
    u.toHomeomorph hcont hcont_symm x = u.equiv x :=
  rfl

theorem ComplexTorusUniformization.exponential_continuous
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont_symm : Continuous u.equiv.symm) :
    Continuous u.exponential := by
  change Continuous (u.equiv.symm ∘
    (QuotientAddGroup.mk' (complexPeriodLattice g)))
  exact hcont_symm.comp QuotientAddGroup.continuous_mk

theorem ComplexTorusUniformization.exponential_isOpenQuotientMap
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    IsOpenQuotientMap u.exponential := by
  rw [isOpenQuotientMap_iff]
  refine ⟨u.exponential_surjective,
    u.exponential_continuous hcont_symm, ?_⟩
  change IsOpenMap (u.equiv.symm ∘
    (QuotientAddGroup.mk' (complexPeriodLattice g)))
  exact (u.toHomeomorph hcont hcont_symm).symm.isOpenMap.comp
    QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap

theorem ComplexTorusUniformization.ofExponential_toHomeomorph_exponential
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) :
    ComplexTorusUniformization.ofExponential_toHomeomorph
        u.exponential u.exponential_surjective u.exponential_ker
        (u.exponential_isOpenQuotientMap hcont hcont_symm) =
      u.toHomeomorph hcont hcont_symm := by
  apply Homeomorph.ext
  intro x
  rw [ComplexTorusUniformization.ofExponential_toHomeomorph_apply]
  rw [ComplexTorusUniformization.ofExponential_exponential]
  rfl

/- Combining the preceding maps gives a topological real-torus model for a
   topological complex uniformization witness. -/
noncomputable def ComplexTorusUniformization.toGenusTorusHomeomorph
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) : X ≃ₜ GenusTorus g :=
  (u.toHomeomorph hcont hcont_symm).trans
    ((complexQuotientToRealQuotientHomeomorph g).trans
      (genusRealVectorQuotientHomeomorph g))

@[simp]
theorem ComplexTorusUniformization.toGenusTorusHomeomorph_apply
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] {g : ℕ}
    (u : ComplexTorusUniformization X g)
    (hcont : Continuous u.equiv)
    (hcont_symm : Continuous u.equiv.symm) (x : X) :
    u.toGenusTorusHomeomorph hcont hcont_symm x =
      u.toGenusTorusUniformization.equiv x := by
  change genusRealVectorQuotientHomeomorph g
      (complexQuotientToRealQuotientHomeomorph g (u.equiv x)) =
    complexGenusQuotientAddEquiv g (u.equiv x)
  change genusRealVectorQuotientAddEquiv g
      (complexQuotientToRealQuotientAddEquiv g (u.equiv x)) =
    complexGenusQuotientAddEquiv g (u.equiv x)
  rw [← AddEquiv.trans_apply]
  rw [complexQuotientToRealQuotientAddEquiv_trans_genusRealVectorQuotient]


/-- Division by every nonzero integer transported through complex
uniformization. -/
theorem complexUniformization_exists_division
    {X : Type*} [AddCommGroup X] {g : ℕ}
    (u : ComplexTorusUniformization X g) (x : X) {n : ℤ} (hn : n ≠ 0) :
    ∃ y : X, n • y = x := by
  exact exists_division_of_uniformization
    u.toGenusTorusUniformization x hn

/-- Signed-integer torsion in a complex period-lattice quotient is the
expected product of cyclic groups. -/
def complexUniformization_zsmulTorsion_addEquiv
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
  (u : ComplexTorusUniformization X g) (hn : n ≠ 0) :
    zsmulTorsionSubgroup X n ≃+
      (Fin (2 * g) → ZMod n.natAbs) :=
  (zsmulTorsion_addEquiv_of_addEquiv
      u.toGenusTorusUniformization.equiv n).trans
    (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)

/- The complex torsion classification factors through the complex quotient
   equivalence before applying the coordinatewise cyclic classification. -/
theorem complexUniformization_zsmulTorsion_addEquiv_eq_trans
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (u : ComplexTorusUniformization X g) (hn : n ≠ 0) :
    complexUniformization_zsmulTorsion_addEquiv u hn =
        (zsmulTorsion_addEquiv_of_addEquiv u.equiv n).trans
        (complexGenusQuotient_zsmulTorsion_addEquiv hn) := by
  simp only [complexUniformization_zsmulTorsion_addEquiv,
    ComplexTorusUniformization.toGenusTorusUniformization,
    complexGenusQuotient_zsmulTorsion_addEquiv]
  rw [zsmulTorsion_addEquiv_of_addEquiv_trans]
  apply AddEquiv.ext
  intro x
  rfl

/- The complex torsion classification can also be computed through the real
   period quotient. -/
theorem complexUniformization_zsmulTorsion_addEquiv_eq_real
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (u : ComplexTorusUniformization X g) (hn : n ≠ 0) :
    complexUniformization_zsmulTorsion_addEquiv u hn =
      (zsmulTorsion_addEquiv_of_addEquiv u.equiv n).trans
        ((zsmulTorsion_addEquiv_of_addEquiv
          (complexQuotientToRealQuotientAddEquiv g) n).trans
          (genusRealVectorQuotient_zsmulTorsion_addEquiv hn)) := by
  rw [complexUniformization_zsmulTorsion_addEquiv_eq_trans u hn]
  have htor :
      zsmulTorsion_addEquiv_of_addEquiv (complexGenusQuotientAddEquiv g) n =
        (zsmulTorsion_addEquiv_of_addEquiv
          (complexQuotientToRealQuotientAddEquiv g) n).trans
          (zsmulTorsion_addEquiv_of_addEquiv
            (genusRealVectorQuotientAddEquiv g) n) := by
    rw [← complexQuotientToRealQuotientAddEquiv_trans_genusRealVectorQuotient]
    exact zsmulTorsion_addEquiv_of_addEquiv_trans _ _ n
  change
    (zsmulTorsion_addEquiv_of_addEquiv u.equiv n).trans
        ((zsmulTorsion_addEquiv_of_addEquiv
          (complexGenusQuotientAddEquiv g) n).trans
          (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)) =
      (zsmulTorsion_addEquiv_of_addEquiv u.equiv n).trans
        ((zsmulTorsion_addEquiv_of_addEquiv
          (complexQuotientToRealQuotientAddEquiv g) n).trans
          ((zsmulTorsion_addEquiv_of_addEquiv
            (genusRealVectorQuotientAddEquiv g) n).trans
            (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)))
  rw [htor]
  rfl

@[simp]
theorem complexUniformization_zsmulTorsion_addEquiv_apply
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (u : ComplexTorusUniformization X g) (hn : n ≠ 0)
    (x : zsmulTorsionSubgroup X n) :
    ((complexUniformization_zsmulTorsion_addEquiv u hn) x : Fin (2 * g) → ZMod n.natAbs) =
      (productTorus_zsmul_torsion_addEquiv_pi_zmod hn)
        ((zsmulTorsion_addEquiv_of_addEquiv
          u.toGenusTorusUniformization.equiv n) x) := by
  rfl

/- The positive-natural notation is obtained from the signed classification by
transporting the canonical equality `(n : ℤ).natAbs = n`. -/
noncomputable def complexUniformization_natCast_zsmulTorsion_addEquiv
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : ComplexTorusUniformization X g) (hn : 0 < n) :
    zsmulTorsionSubgroup X (n : ℤ) ≃+ (Fin (2 * g) → ZMod n) := by
  have hne : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  let castEquiv : (Fin (2 * g) → ZMod (n : ℤ).natAbs) ≃+
      (Fin (2 * g) → ZMod n) :=
    AddEquiv.cast (M := fun m : ℕ => Fin (2 * g) → ZMod m)
      (Int.natAbs_ofNat' n)
  exact (complexUniformization_zsmulTorsion_addEquiv u hne).trans castEquiv

/-- The natural-number torsion equivalence is the signed equivalence followed
by the canonical `natAbs` cast. -/
theorem complexUniformization_natCast_zsmulTorsion_addEquiv_eq_trans_cast
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : ComplexTorusUniformization X g) (hn : 0 < n) :
    complexUniformization_natCast_zsmulTorsion_addEquiv u hn =
      (complexUniformization_zsmulTorsion_addEquiv u
        (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn))).trans
        (AddEquiv.cast (M := fun m : ℕ => Fin (2 * g) → ZMod m)
          (Int.natAbs_ofNat' n)) := by
  rfl

@[simp]
theorem complexUniformization_natCast_zsmulTorsion_addEquiv_apply
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : ComplexTorusUniformization X g) (hn : 0 < n)
    (x : zsmulTorsionSubgroup X (n : ℤ)) :
    (complexUniformization_natCast_zsmulTorsion_addEquiv u hn) x =
      (AddEquiv.cast (M := fun m : ℕ => Fin (2 * g) → ZMod m)
          (Int.natAbs_ofNat' n))
        ((complexUniformization_zsmulTorsion_addEquiv u
          (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn))) x) := by
  rfl

/-- Cardinality of signed-integer torsion under a complex uniformization. -/
theorem complexUniformization_zsmulTorsion_card
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (u : ComplexTorusUniformization X g) (hn : n ≠ 0) :
    Nat.card (zsmulTorsionSubgroup X n) = n.natAbs ^ (2 * g) := by
  exact zsmulTorsion_card_of_uniformization u.toGenusTorusUniformization hn

/-- Finiteness of every nonzero signed-integer torsion subgroup under a
complex uniformization. -/
theorem complexUniformization_zsmulTorsion_finite
    {X : Type*} [AddCommGroup X] {g : ℕ} {n : ℤ}
    (u : ComplexTorusUniformization X g) (hn : n ≠ 0) :
    Finite (zsmulTorsionSubgroup X n) := by
  exact zsmulTorsion_finite_of_uniformization u.toGenusTorusUniformization hn

/-- Positive-natural torsion cardinality in the complex model. -/
theorem complexUniformization_natCast_zsmulTorsion_card
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : ComplexTorusUniformization X g) (hn : 0 < n) :
    Nat.card (zsmulTorsionSubgroup X (n : ℤ)) = n ^ (2 * g) := by
  exact natCast_zsmulTorsion_card_of_uniformization
    u.toGenusTorusUniformization hn

/-- Positive-natural torsion is finite in the complex model. -/
theorem complexUniformization_natCast_zsmulTorsion_finite
    {X : Type*} [AddCommGroup X] {g n : ℕ}
    (u : ComplexTorusUniformization X g) (hn : 0 < n) :
    Finite (zsmulTorsionSubgroup X (n : ℤ)) := by
  exact complexUniformization_zsmulTorsion_finite u
    (by exact_mod_cast (Nat.ne_of_gt hn))

end
end Uniformization
end Mumford
