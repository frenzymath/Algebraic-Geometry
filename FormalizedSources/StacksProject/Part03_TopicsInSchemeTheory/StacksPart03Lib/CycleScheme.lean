/-
Copyright (c) 2026 The StacksPart03Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart03Lib Contributors
-/

import StacksPart03Lib.Cycles
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sober

/-!
# The scheme-facing pointwise cycle bridge

For a scheme, Mathlib supplies sobriety and the `T₀` separation property. Thus
irreducible closed subsets are in bijection with their generic points. This
file packages that correspondence around the locally-finite pointwise carrier
from `Cycles.lean`.

The bridge intentionally records only the coefficient and support layer. It
does not identify an irreducible closed subset with a scheme-theoretic closed
subscheme, and therefore makes no claim about lengths or multiplicities.
-/

namespace StacksPart03

open Set
open AlgebraicGeometry

universe u

/-! ## Irreducible closed carriers -/

/-- The topological carrier of an integral component of a scheme.

This is the point-set part of an integral closed subscheme: nilpotent
structure and generic multiplicities are deliberately kept for a later layer.
-/
abbrev IntegralCarrier (X : Scheme.{u}) :=
  TopologicalSpace.IrreducibleCloseds X

namespace IntegralCarrier

variable {X : Scheme.{u}}

/-- The generic point attached to an irreducible closed carrier. -/
noncomputable abbrev genericPoint (Z : IntegralCarrier X) : X :=
  Z.isIrreducible.genericPoint

/-- The generic point lies on its carrier. -/
theorem genericPoint_mem (Z : IntegralCarrier X) :
    genericPoint Z ∈ (Z : Set X) := by
  exact Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed |>.mem

/-- The carrier is the closure of its generic point. -/
@[simp]
theorem closure_genericPoint (Z : IntegralCarrier X) :
    closure ({genericPoint Z} : Set X) = (Z : Set X) := by
  exact Z.isIrreducible.closure_genericPoint Z.isClosed

/-- Generic points distinguish irreducible closed carriers. -/
theorem genericPoint_injective :
    Function.Injective (fun Z : IntegralCarrier X => genericPoint Z) := by
  intro Z W hZW
  apply TopologicalSpace.IrreducibleCloseds.ext
  rw [← Z.closure_genericPoint, ← W.closure_genericPoint]
  simp [hZW]

/-- The canonical order equivalence between carriers and scheme points. -/
noncomputable abbrev pointEquiv (X : Scheme.{u}) :
    IntegralCarrier X ≃o ↥X :=
  irreducibleSetEquivPoints

@[simp]
theorem genericPoint_pointEquiv_symm (x : X) :
    genericPoint ((pointEquiv X).symm x) = x := by
  change ((pointEquiv X).symm x).isIrreducible.genericPoint = x
  exact (pointEquiv X).apply_symm_apply x

@[simp]
theorem carrier_pointEquiv_symm (x : X) :
    ((pointEquiv X).symm x : Set X) = closure ({x} : Set X) := by
  exact coe_irreducibleEquivPoints_symm_apply x

end IntegralCarrier

/-! ## Coefficients and support -/

namespace PointCycle

variable {X : Scheme.{u}}

/-- The coefficient of a pointwise cycle at an irreducible closed carrier. -/
noncomputable def coefficient (c : PointCycle (↥X)) (Z : IntegralCarrier X) : ℤ :=
  c (IntegralCarrier.pointEquiv X Z)

/-- The carrier support of a pointwise cycle. -/
abbrev carrierSupport (c : PointCycle (↥X)) : Set (IntegralCarrier X) :=
  Function.support (coefficient c)

@[simp]
theorem mem_carrierSupport_iff (c : PointCycle (↥X)) (Z : IntegralCarrier X) :
    Z ∈ c.carrierSupport ↔ IntegralCarrier.pointEquiv X Z ∈ c.support :=
  Iff.rfl

/-- Carrier support and point support correspond under the generic-point map. -/
theorem image_carrierSupport (c : PointCycle (↥X)) :
    IntegralCarrier.pointEquiv X '' c.carrierSupport = c.support := by
  ext x
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    exact hZ
  · intro hx
    refine ⟨(IntegralCarrier.pointEquiv X).symm x, ?_, ?_⟩
    · simpa [PointCycle.carrierSupport, PointCycle.coefficient] using hx
    · simp

/-- The dimension assigned to an irreducible carrier by a pointwise dimension
function. -/
noncomputable def deltaDimension (δ : (↥X) → ℤ) (Z : IntegralCarrier X) : ℤ :=
  δ (IntegralCarrier.pointEquiv X Z)

theorem isKCycle_iff_carrierDimension
    {δ : (↥X) → ℤ} {k : ℤ} {c : PointCycle (↥X)} :
    IsKCycle δ k c ↔
      ∀ Z : IntegralCarrier X, Z ∈ c.carrierSupport →
        deltaDimension δ Z = k := by
  constructor
  · intro hc Z hZ
    exact hc hZ
  · intro h x hx
    let Z : IntegralCarrier X := (IntegralCarrier.pointEquiv X).symm x
    have hZ : Z ∈ c.carrierSupport := by
      simpa [Z, PointCycle.carrierSupport, PointCycle.coefficient] using hx
    simpa [Z, PointCycle.deltaDimension] using h Z hZ

theorem isEffective_iff_carrier
    {c : PointCycle (↥X)} :
    IsEffective c ↔ ∀ Z : IntegralCarrier X, 0 ≤ c.coefficient Z := by
  constructor
  · intro hc Z
    exact hc _
  · intro h x
    let Z : IntegralCarrier X := (IntegralCarrier.pointEquiv X).symm x
    simpa [Z, PointCycle.coefficient] using h Z

/-- Carriers meeting a subset `U` and occurring with nonzero coefficient. -/
def carriersMeeting (c : PointCycle (↥X)) (U : Set X) : Set (IntegralCarrier X) :=
  {Z | Z ∈ c.carrierSupport ∧ ((Z : Set X) ∩ U).Nonempty}

/-- Only finitely many supported carriers meet a compact open subset. -/
theorem finite_carriersMeeting_of_isCompact_of_isOpen
    (c : PointCycle (↥X)) {U : Set X} (hU : IsOpen U) (hK : IsCompact U) :
    (c.carriersMeeting U).Finite := by
  have hfinite : (U ∩ c.support).Finite :=
    c.finite_inter_support_of_isCompact hK
  refine Set.Finite.of_finite_image (f := IntegralCarrier.pointEquiv X) ?_
    (IntegralCarrier.pointEquiv X).injective.injOn
  apply hfinite.subset
  rintro x ⟨Z, hZ, rfl⟩
  refine ⟨?_, hZ.1⟩
  exact (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem_open_set_iff hU |>.2 hZ.2

/-- On a compact scheme, the complete carrier support is finite. -/
theorem finite_carrierSupport_of_isCompact
    (c : PointCycle (↥X)) (hX : IsCompact (Set.univ : Set X)) :
    c.carrierSupport.Finite := by
  have hfinite : c.support.Finite := by
    simpa using c.finite_inter_support_of_isCompact hX
  rw [← c.image_carrierSupport] at hfinite
  exact Set.Finite.of_finite_image hfinite (IntegralCarrier.pointEquiv X).injective.injOn

end PointCycle

/-! ## Restriction to an open part -/

namespace PointCycle

variable {X : Scheme.{u}}

/-- Pointwise cycles supported inside a subset `U`.

This is Mathlib's locally-finite-within-domain carrier, so restriction does
not require a quasi-compactness assumption. -/
abbrev OpenPointCycle (X : Scheme.{u}) (U : Set X) :=
  Function.locallyFinsuppWithin U ℤ

/-- Restrict a pointwise cycle by zero outside `U`. -/
noncomputable def restrict (c : PointCycle (↥X)) (U : Set X) : OpenPointCycle X U :=
  Function.locallyFinsuppWithin.restrict c (subset_univ U)

open Classical in
@[simp] theorem restrict_apply (c : PointCycle (↥X)) (U : Set X) (x : X) :
    c.restrict U x = if x ∈ U then c x else 0 := by
  rfl

@[simp]
theorem restrict_support (c : PointCycle (↥X)) (U : Set X) :
    (c.restrict U).support = U ∩ c.support := by
  classical
  ext x
  simp [PointCycle.restrict, Function.locallyFinsuppWithin.restrict_apply,
    Set.mem_inter_iff]

theorem restrict_add (c d : PointCycle (↥X)) (U : Set X) :
    (c + d).restrict U = c.restrict U + d.restrict U := by
  classical
  ext x
  by_cases hx : x ∈ U <;>
    simp [PointCycle.restrict, Function.locallyFinsuppWithin.restrict_apply, hx]

theorem restrict_restrict (c : PointCycle (↥X)) {U V : Set X} (hVU : V ⊆ U) :
    Function.locallyFinsuppWithin.restrict (c.restrict U) hVU = c.restrict V := by
  classical
  ext x
  by_cases hxV : x ∈ V
  · have hxU : x ∈ U := hVU hxV
    simp [PointCycle.restrict, Function.locallyFinsuppWithin.restrict_apply, hxV, hxU]
  · simp [PointCycle.restrict, hxV]

/-- The homogeneous predicate for a cycle supported in a subset. -/
 def IsKCycleWithin (δ : (↥X) → ℤ) (k : ℤ) {U : Set X}
    (c : OpenPointCycle X U) : Prop :=
  ∀ ⦃x : X⦄, c x ≠ 0 → δ x = k

/-- The effective predicate for a cycle supported in a subset. -/
def IsEffectiveWithin {U : Set X} (c : OpenPointCycle X U) : Prop :=
  ∀ x : X, 0 ≤ c x

theorem isKCycleWithin_restrict
    {δ : (↥X) → ℤ} {k : ℤ} {c : PointCycle (↥X)}
    (hc : IsKCycle δ k c) (U : Set X) :
    IsKCycleWithin δ k (c.restrict U) := by
  classical
  intro x hx
  have hcx : c x ≠ 0 := by
    intro hzero
    apply hx
    simp [PointCycle.restrict_apply, hzero]
  exact hc hcx

theorem isEffectiveWithin_restrict
    {c : PointCycle (↥X)} (hc : IsEffective c) (U : Set X) :
    IsEffectiveWithin (c.restrict U) := by
  intro x
  by_cases hx : x ∈ U
  · simpa [hx] using hc x
  · simp [hx]

end PointCycle

end StacksPart03
