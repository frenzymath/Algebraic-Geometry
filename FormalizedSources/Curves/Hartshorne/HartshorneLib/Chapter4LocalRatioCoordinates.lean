/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorSectionCoordinates

/-!
# Hartshorne IV.3.1: local ratios of divisor sections

This file records the local algebra behind the usual projective-coordinate
construction.  A denominator is required to be nonzero in the function field;
all regularity and gluing information is supplied as certificate data rather
than inferred from a divisor section.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
variable {D : CurveDivisor k X}

/-! ### Nonempty opens and generic-point values -/

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
/-- On an integral scheme, every nonempty open contains the generic point.

The statement is kept local to this API so that users can construct a local
ratio from the nonemptiness certificate carried by `LocalRatioOpen` without
supplying a second topological proof.
-/
lemma localRatio_genericPoint_mem_of_nonempty {U : X.left.Opens}
    (hU : (U : Set X.left).Nonempty) :
    genericPoint X.left ∈ U :=
  ((genericPoint_spec X.left).mem_open_set_iff (U := (↑U : Set X.left)) U.isOpen).mpr
    (by simpa using hU)

/-- An open together with the certificates needed for taking a generic-point
germ.  The generic-point field is explicit to make later restriction data
independent of proof-term elaboration. -/
structure LocalRatioOpen (X : Over (Spec (CommRingCat.of k))) [IsIntegral X.left] where
  U : X.left.Opens
  nonempty : (U : Set X.left).Nonempty
  generic_mem : genericPoint X.left ∈ U

namespace LocalRatioOpen

/-- Construct a local-ratio open from its nonemptiness proof. -/
def of_nonempty (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) :
    LocalRatioOpen X :=
  ⟨U, hU, localRatio_genericPoint_mem_of_nonempty hU⟩

@[simp] theorem coe_U (W : LocalRatioOpen X) :
    ((W.U : X.left.Opens) : Set X.left) = (W.U : Set X.left) :=
  rfl

end LocalRatioOpen

/-- The generic-point value of a regular structure-sheaf section on a local
ratio open. -/
noncomputable def localStructureValue (W : LocalRatioOpen X)
    (s : Γ(X.left, W.U)) : X.left.functionField :=
  (X.left.presheaf.germ W.U (genericPoint X.left) W.generic_mem).hom s

@[simp] lemma localStructureValue_eq_germ (W : LocalRatioOpen X)
    (s : Γ(X.left, W.U)) :
    localStructureValue W s =
      (X.left.presheaf.germ W.U (genericPoint X.left) W.generic_mem).hom s :=
  rfl

/-! ### A numerator, denominator, and their function-field ratio -/

/-- Two sections of `𝒪(D)` on a nonempty open, with an explicitly nonzero
denominator value. -/
structure LocalDivisorSectionRatio (D : CurveDivisor k X) where
  chart : LocalRatioOpen X
  numerator : divisorSections D chart.U
  denominator : divisorSections D chart.U
  denominator_value_ne_zero :
    (denominator : X.left.functionField) ≠ 0

namespace LocalDivisorSectionRatio

/-- The numerator value in the function field. -/
def numeratorValue (r : LocalDivisorSectionRatio D) : X.left.functionField :=
  (r.numerator : X.left.functionField)

/-- The denominator value in the function field. -/
def denominatorValue (r : LocalDivisorSectionRatio D) : X.left.functionField :=
  (r.denominator : X.left.functionField)

/-- The local affine coordinate obtained by dividing numerator by denominator. -/
noncomputable def ratio (r : LocalDivisorSectionRatio D) : X.left.functionField :=
  r.numeratorValue / r.denominatorValue

@[simp] theorem numeratorValue_eq_divisorVal (r : LocalDivisorSectionRatio D) :
    r.numeratorValue = divisorVal (D := D) (W := r.chart.U) r.numerator :=
  rfl

@[simp] theorem denominatorValue_eq_divisorVal (r : LocalDivisorSectionRatio D) :
    r.denominatorValue = divisorVal (D := D) (W := r.chart.U) r.denominator :=
  rfl

@[simp] theorem denominatorValue_ne_zero (r : LocalDivisorSectionRatio D) :
    r.denominatorValue ≠ 0 :=
  r.denominator_value_ne_zero

@[simp] theorem ratio_mul_denominator (r : LocalDivisorSectionRatio D) :
    r.ratio * r.denominatorValue = r.numeratorValue := by
  exact div_mul_cancel₀ _ r.denominator_value_ne_zero

@[simp] theorem denominator_mul_ratio (r : LocalDivisorSectionRatio D) :
    r.denominatorValue * r.ratio = r.numeratorValue := by
  rw [mul_comm]
  exact r.ratio_mul_denominator

/-- Two local ratios are equal exactly when their cross-products agree. -/
theorem ratio_eq_iff (r s : LocalDivisorSectionRatio D) :
    r.ratio = s.ratio ↔
      r.numeratorValue * s.denominatorValue =
        s.numeratorValue * r.denominatorValue := by
  rw [ratio, ratio]
  exact div_eq_div_iff r.denominator_value_ne_zero s.denominator_value_ne_zero

/-- Restrict a local ratio to a smaller nonempty open. -/
def restrict (r : LocalDivisorSectionRatio D) {V : X.left.Opens}
    (hVU : V ≤ r.chart.U) (hV : (V : Set X.left).Nonempty) :
    LocalDivisorSectionRatio D :=
  { chart := LocalRatioOpen.of_nonempty V hV
    numerator := divisorSectionsRes D hVU r.numerator
    denominator := divisorSectionsRes D hVU r.denominator
    denominator_value_ne_zero := by
      rw [divisorSectionsRes_coe hVU hV]
      exact r.denominator_value_ne_zero }

@[simp] theorem restrict_numeratorValue (r : LocalDivisorSectionRatio D)
    {V : X.left.Opens} (hVU : V ≤ r.chart.U)
    (hV : (V : Set X.left).Nonempty) :
    (r.restrict hVU hV).numeratorValue = r.numeratorValue := by
  change ((divisorSectionsRes D hVU r.numerator : divisorSections D V) :
    X.left.functionField) = r.numeratorValue
  exact divisorSectionsRes_coe hVU hV r.numerator

@[simp] theorem restrict_denominatorValue (r : LocalDivisorSectionRatio D)
    {V : X.left.Opens} (hVU : V ≤ r.chart.U)
    (hV : (V : Set X.left).Nonempty) :
    (r.restrict hVU hV).denominatorValue = r.denominatorValue := by
  change ((divisorSectionsRes D hVU r.denominator : divisorSections D V) :
    X.left.functionField) = r.denominatorValue
  exact divisorSectionsRes_coe hVU hV r.denominator

@[simp] theorem restrict_ratio (r : LocalDivisorSectionRatio D)
    {V : X.left.Opens} (hVU : V ≤ r.chart.U)
    (hV : (V : Set X.left).Nonempty) :
    (r.restrict hVU hV).ratio = r.ratio := by
  rw [ratio, ratio, restrict_numeratorValue, restrict_denominatorValue]

end LocalDivisorSectionRatio

/-! ### Finite coordinate families and supplied regularization -/

variable {n : ℕ}

/-- A finite family of local divisor sections with a chosen nonvanishing
denominator coordinate. -/
structure LocalRatioCoordinateData (D : CurveDivisor k X) (n : ℕ) where
  chart : LocalRatioOpen X
  sections : Fin (n + 1) → divisorSections D chart.U
  denominator_index : Fin (n + 1)
  denominator_value_ne_zero :
    (sections denominator_index : X.left.functionField) ≠ 0

namespace LocalRatioCoordinateData

/-- The ratio datum represented by one coordinate of a family. -/
def ratioAt (a : LocalRatioCoordinateData D n) (i : Fin (n + 1)) :
    LocalDivisorSectionRatio D :=
  { chart := a.chart
    numerator := a.sections i
    denominator := a.sections a.denominator_index
    denominator_value_ne_zero := a.denominator_value_ne_zero }

/-- The normalized local coordinate attached to one family member. -/
noncomputable def coordinate (a : LocalRatioCoordinateData D n)
    (i : Fin (n + 1)) : X.left.functionField :=
  (a.ratioAt i).ratio

@[simp] theorem coordinate_eq_ratio (a : LocalRatioCoordinateData D n)
    (i : Fin (n + 1)) :
    a.coordinate i = (a.ratioAt i).ratio :=
  rfl

@[simp] theorem coordinate_denominator (a : LocalRatioCoordinateData D n) :
    a.coordinate a.denominator_index = 1 := by
  change ((a.sections a.denominator_index : X.left.functionField) /
      (a.sections a.denominator_index : X.left.functionField)) = 1
  exact div_self a.denominator_value_ne_zero

@[simp] theorem at_numeratorValue (a : LocalRatioCoordinateData D n)
    (i : Fin (n + 1)) :
    (a.ratioAt i).numeratorValue = (a.sections i : X.left.functionField) :=
  rfl

@[simp] theorem at_denominatorValue (a : LocalRatioCoordinateData D n)
    (i : Fin (n + 1)) :
    (a.ratioAt i).denominatorValue =
      (a.sections a.denominator_index : X.left.functionField) :=
  rfl

end LocalRatioCoordinateData

/-- A supplied regularization of local ratios by honest structure-sheaf
sections.  The `compatibility` field records value preservation on every
smaller nonempty open; no gluing or regularity assertion is inferred. -/
structure LocalRatioRegularization
    (a : LocalRatioCoordinateData D n) where
  /-- The function-field coordinates being regularized. -/
  c : Fin (n + 1) → X.left.functionField
  /-- Each coordinate is the ratio of the corresponding divisor sections. -/
  c_eq_ratio : ∀ i, c i = a.coordinate i
  /-- Structure-sheaf sections representing the coordinates on the chart. -/
  regularized : Fin (n + 1) → Γ(X.left, a.chart.U)
  /-- The generic-point values of the regularized sections. -/
  regularized_value_eq : ∀ i,
    localStructureValue a.chart (regularized i) = c i
  /-- Explicit normalization of the distinguished coordinate. -/
  normalized : c a.denominator_index = 1
  /-- Explicit compatibility of the supplied regularizations with restriction. -/
  compatibility : ∀ {V : X.left.Opens} (hVU : V ≤ a.chart.U)
    (hV : (V : Set X.left).Nonempty) (i : Fin (n + 1)),
    localStructureValue (LocalRatioOpen.of_nonempty V hV)
      ((X.left.presheaf.map (homOfLE hVU).op).hom (regularized i)) =
      localStructureValue a.chart (regularized i)

namespace LocalRatioRegularization

variable {a : LocalRatioCoordinateData D n}

@[simp] theorem normalized_eq (r : LocalRatioRegularization a) :
    r.c a.denominator_index = 1 :=
  r.normalized

theorem regularized_value_eq_ratio (r : LocalRatioRegularization a)
    (i : Fin (n + 1)) :
    localStructureValue a.chart (r.regularized i) = a.coordinate i := by
  rw [r.regularized_value_eq i, r.c_eq_ratio i]

theorem restricted_value_eq (r : LocalRatioRegularization a)
    {V : X.left.Opens} (hVU : V ≤ a.chart.U)
    (hV : (V : Set X.left).Nonempty) (i : Fin (n + 1)) :
    localStructureValue (LocalRatioOpen.of_nonempty V hV)
      ((X.left.presheaf.map (homOfLE hVU).op).hom (r.regularized i)) =
      r.c i := by
  rw [r.compatibility hVU hV i, r.regularized_value_eq i]

end LocalRatioRegularization

end
end Hartshorne
