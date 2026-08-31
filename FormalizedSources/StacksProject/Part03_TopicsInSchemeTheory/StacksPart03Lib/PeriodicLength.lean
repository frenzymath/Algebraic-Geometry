/-
Copyright (c) 2026 The StacksPart03Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart03Lib Contributors
-/

import Mathlib.RingTheory.Length
import StacksPart03Lib.Cohomology

/-!
# Finite-length cohomology of two-periodic complexes

For a two-periodic complex, the even and odd cohomology modules are the
kernel/range quotients.  Mathlib's `IsFiniteLength` and `Module.length` give a
source-faithful, axiom-free finite-length package, while retaining `ℕ∞` so
that no finiteness hypothesis is hidden in the definitions.
-/

namespace StacksPart03

variable {R M N : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

namespace TwoPeriodicComplex

/-- The even cohomology module `ker(d₀) / range(d₁)`. -/
abbrev evenCohomology (C : TwoPeriodicComplex R M N) :=
  C.HZero

/-- The odd cohomology module `ker(d₁) / range(d₀)`. -/
abbrev oddCohomology (C : TwoPeriodicComplex R M N) :=
  C.HOne

/-- Both cohomology modules have finite length. -/
def HasFiniteLength (C : TwoPeriodicComplex R M N) : Prop :=
  IsFiniteLength R C.evenCohomology ∧ IsFiniteLength R C.oddCohomology

/-- Length of the even cohomology module. -/
noncomputable def evenLength (C : TwoPeriodicComplex R M N) : ℕ∞ :=
  Module.length R C.evenCohomology

/-- Length of the odd cohomology module. -/
noncomputable def oddLength (C : TwoPeriodicComplex R M N) : ℕ∞ :=
  Module.length R C.oddCohomology

theorem HasFiniteLength.evenLength_ne_top (C : TwoPeriodicComplex R M N)
    (hC : C.HasFiniteLength) : C.evenLength ≠ ⊤ :=
  Module.length_ne_top_iff.mpr hC.1

theorem HasFiniteLength.oddLength_ne_top (C : TwoPeriodicComplex R M N)
    (hC : C.HasFiniteLength) : C.oddLength ≠ ⊤ :=
  Module.length_ne_top_iff.mpr hC.2

/-- The alternating (even minus odd) cohomology length in `ℕ∞`.

Subtraction is the canonical truncated subtraction on `ℕ∞`; under
`HasFiniteLength` this is the usual difference of finite natural lengths. -/
noncomputable def lengthDifference (C : TwoPeriodicComplex R M N) : ℕ∞ :=
  C.evenLength - C.oddLength

theorem lengthDifference_eq_zero_iff_le (C : TwoPeriodicComplex R M N) :
    C.lengthDifference = 0 ↔ C.evenLength ≤ C.oddLength := by
  exact tsub_eq_zero_iff_le

theorem hasFiniteLength_iff (C : TwoPeriodicComplex R M N) :
    C.HasFiniteLength ↔
      IsFiniteLength R C.evenCohomology ∧ IsFiniteLength R C.oddCohomology :=
  Iff.rfl

/-- Finite-length ambient modules give finite-length periodic cohomology. -/
theorem hasFiniteLength_of_finite_ambient (C : TwoPeriodicComplex R M N)
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N) : C.HasFiniteLength := by
  constructor
  · apply IsFiniteLength.of_surjective ?_ (Submodule.mkQ_surjective _)
    apply IsFiniteLength.of_injective hM
    exact Submodule.subtype_injective _
  · apply IsFiniteLength.of_surjective ?_ (Submodule.mkQ_surjective _)
    apply IsFiniteLength.of_injective hN
    exact Submodule.subtype_injective _

/-! ## Integer lengths and multiplicity -/

/-- The integer represented by a finite module length.

The finiteness witness prevents the `⊤` value of `ℕ∞` from being silently
interpreted as an integer. -/
noncomputable def finiteLengthInt (R P : Type*) [Ring R]
    [AddCommGroup P] [Module R P] (_hP : IsFiniteLength R P) : ℤ :=
  Int.ofNat (Module.length R P).toNat

/-- Additivity of finite integer lengths along a short exact sequence. -/
theorem finiteLengthInt_eq_add_of_exact
    {P Q S : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup S]
    [Module R P] [Module R Q] [Module R S]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] S)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g)
    (hP : IsFiniteLength R P) (hQ : IsFiniteLength R Q)
    (hS : IsFiniteLength R S) :
    finiteLengthInt R Q hQ =
      finiteLengthInt R P hP + finiteLengthInt R S hS := by
  have hPtop : Module.length R P ≠ ⊤ := Module.length_ne_top_iff.mpr hP
  have hStop : Module.length R S ≠ ⊤ := Module.length_ne_top_iff.mpr hS
  have hlen := Module.length_eq_add_of_exact f g hf hg hfg
  have hNat := congrArg ENat.toNat hlen
  rw [ENat.toNat_add hPtop hStop] at hNat
  simpa [finiteLengthInt] using congrArg Int.ofNat hNat

/-- A linear equivalence preserves finite integer length. -/
theorem finiteLengthInt_eq_of_linearEquiv
    {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    [Module R P] [Module R Q] (e : P ≃ₗ[R] Q)
    (hP : IsFiniteLength R P) (hQ : IsFiniteLength R Q) :
    finiteLengthInt R P hP = finiteLengthInt R Q hQ := by
  change Int.ofNat (Module.length R P).toNat = Int.ofNat (Module.length R Q).toNat
  rw [e.length_eq]

private theorem rangeRestrict_surjective
    {P Q : Type*} [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]
    (f : P →ₗ[R] Q) : Function.Surjective f.rangeRestrict := by
  intro y
  obtain ⟨x, hx⟩ := y.property
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- The additive periodic multiplicity, as an integer difference of lengths. -/
noncomputable def multiplicity (C : TwoPeriodicComplex R M N)
    (hC : C.HasFiniteLength) : ℤ :=
  finiteLengthInt R C.evenCohomology hC.1 -
    finiteLengthInt R C.oddCohomology hC.2

/-- For finite ambient modules, periodic multiplicity is the ambient length
difference (the finite-periodic-length lemma). -/
theorem multiplicity_eq_ambient_length_sub
    (C : TwoPeriodicComplex R M N)
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N) :
    C.multiplicity (C.hasFiniteLength_of_finite_ambient hM hN) =
      finiteLengthInt R M hM - finiteLengthInt R N hN := by
  let hC := C.hasFiniteLength_of_finite_ambient hM hN
  have hK0 : IsFiniteLength R C.d₀.ker :=
    IsFiniteLength.of_injective hM (Submodule.subtype_injective _)
  have hK1 : IsFiniteLength R C.d₁.ker :=
    IsFiniteLength.of_injective hN (Submodule.subtype_injective _)
  have hR0 : IsFiniteLength R C.d₀.range :=
    IsFiniteLength.of_surjective hM (rangeRestrict_surjective C.d₀)
  have hR1 : IsFiniteLength R C.d₁.range :=
    IsFiniteLength.of_surjective hN (rangeRestrict_surjective C.d₁)
  let B0 := (LinearMap.range C.d₀).comap C.d₁.ker.subtype
  let B1 := (LinearMap.range C.d₁).comap C.d₀.ker.subtype
  have hB0 : IsFiniteLength R B0 := by
    let e := Submodule.comapSubtypeEquivOfLe C.range_d₀_le_ker_d₁
    exact IsFiniteLength.of_injective hR0 e.injective
  have hB1 : IsFiniteLength R B1 := by
    let e := Submodule.comapSubtypeEquivOfLe C.range_d₁_le_ker_d₀
    exact IsFiniteLength.of_injective hR1 e.injective
  have hM_eq : finiteLengthInt R M hM =
      finiteLengthInt R C.d₀.ker hK0 + finiteLengthInt R C.d₀.range hR0 :=
    finiteLengthInt_eq_add_of_exact C.d₀.ker.subtype C.d₀.rangeRestrict
      (Submodule.subtype_injective _) (rangeRestrict_surjective C.d₀) (by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
          Submodule.range_subtype]) hK0 hM hR0
  have hN_eq : finiteLengthInt R N hN =
      finiteLengthInt R C.d₁.ker hK1 + finiteLengthInt R C.d₁.range hR1 :=
    finiteLengthInt_eq_add_of_exact C.d₁.ker.subtype C.d₁.rangeRestrict
      (Submodule.subtype_injective _) (rangeRestrict_surjective C.d₁) (by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
          Submodule.range_subtype]) hK1 hN hR1
  have hK0_eq : finiteLengthInt R C.d₀.ker hK0 =
      finiteLengthInt R B1 hB1 + finiteLengthInt R C.HZero hC.1 :=
    finiteLengthInt_eq_add_of_exact B1.subtype B1.mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _) hB1 hK0 hC.1
  have hK1_eq : finiteLengthInt R C.d₁.ker hK1 =
      finiteLengthInt R B0 hB0 + finiteLengthInt R C.HOne hC.2 :=
    finiteLengthInt_eq_add_of_exact B0.subtype B0.mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _) hB0 hK1 hC.2
  have hB0_eq : finiteLengthInt R B0 hB0 = finiteLengthInt R C.d₀.range hR0 :=
    finiteLengthInt_eq_of_linearEquiv
      (Submodule.comapSubtypeEquivOfLe C.range_d₀_le_ker_d₁) hB0 hR0
  have hB1_eq : finiteLengthInt R B1 hB1 = finiteLengthInt R C.d₁.range hR1 :=
    finiteLengthInt_eq_of_linearEquiv
      (Submodule.comapSubtypeEquivOfLe C.range_d₁_le_ker_d₀) hB1 hR1
  change finiteLengthInt R C.HZero hC.1 - finiteLengthInt R C.HOne hC.2 =
    finiteLengthInt R M hM - finiteLengthInt R N hN
  linarith [hM_eq, hN_eq, hK0_eq, hK1_eq, hB0_eq, hB1_eq]

/-- A finite `(2, 1)`-periodic complex has zero additive multiplicity. -/
theorem multiplicity_eq_zero_of_finite_ambient
    (C : TwoOnePeriodicComplex R M) (hM : IsFiniteLength R M) :
    C.multiplicity (C.hasFiniteLength_of_finite_ambient hM hM) = 0 := by
  simpa using C.multiplicity_eq_ambient_length_sub hM hM

/-- Exact periodic complexes have finite-length (indeed zero) cohomology. -/
theorem hasFiniteLength_of_isExact (C : TwoPeriodicComplex R M N)
    (hC : C.IsExact) : C.HasFiniteLength := by
  constructor
  · letI : Subsingleton C.evenCohomology := C.hZero_subsingleton_iff.mpr hC.1.symm
    exact IsFiniteLength.of_subsingleton
  · letI : Subsingleton C.oddCohomology := C.hOne_subsingleton_iff.mpr hC.2.symm
    exact IsFiniteLength.of_subsingleton

theorem evenLength_eq_zero_iff (C : TwoPeriodicComplex R M N) :
    C.evenLength = 0 ↔ Subsingleton C.evenCohomology := by
  exact Module.length_eq_zero_iff

theorem oddLength_eq_zero_iff (C : TwoPeriodicComplex R M N) :
    C.oddLength = 0 ↔ Subsingleton C.oddCohomology := by
  exact Module.length_eq_zero_iff

/-- Exactness identifies the even cohomology quotient with the zero module. -/
theorem exact_evenCohomology_subsingleton (C : TwoPeriodicComplex R M N)
    (hC : C.IsExact) : Subsingleton C.evenCohomology := by
  exact C.hZero_subsingleton_iff.mpr hC.1.symm

/-- Exactness identifies the odd cohomology quotient with the zero module. -/
theorem exact_oddCohomology_subsingleton (C : TwoPeriodicComplex R M N)
    (hC : C.IsExact) : Subsingleton C.oddCohomology := by
  exact C.hOne_subsingleton_iff.mpr hC.2.symm

@[simp]
theorem exact_evenLength_eq_zero (C : TwoPeriodicComplex R M N)
    (hC : C.IsExact) : C.evenLength = 0 := by
  exact C.evenLength_eq_zero_iff.mpr (C.exact_evenCohomology_subsingleton hC)

@[simp]
theorem exact_oddLength_eq_zero (C : TwoPeriodicComplex R M N)
    (hC : C.IsExact) : C.oddLength = 0 := by
  exact C.oddLength_eq_zero_iff.mpr (C.exact_oddCohomology_subsingleton hC)

@[simp]
theorem exact_lengthDifference_eq_zero (C : TwoPeriodicComplex R M N)
    (hC : C.IsExact) : C.lengthDifference = 0 := by
  simp [lengthDifference, C.exact_evenLength_eq_zero hC, C.exact_oddLength_eq_zero hC]

end TwoPeriodicComplex

end StacksPart03
