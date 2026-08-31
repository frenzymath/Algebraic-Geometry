/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffRepresentable
import AlgebraicJacobian.Picard.Pic0ChartLocusH0Rank
import AlgebraicJacobian.RiemannRoch.ChiCurve

/-! # Widened divisor representability for the challenge curve -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section Curve

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- The finite dominant map to `P¹` used by both the divisor representer and the Picard
coverage parameter. -/
noncomputable def divRepAffP1Map : C.left ⟶ P1 k :=
  (exists_isFinite_isDominant_toP1 (C := C)).choose

noncomputable instance divRepAffP1Map_isFinite : IsFinite (divRepAffP1Map C) :=
  (exists_isFinite_isDominant_toP1 (C := C)).choose_spec.1

noncomputable instance divRepAffP1Map_isDominant : IsDominant (divRepAffP1Map C) :=
  (exists_isFinite_isDominant_toP1 (C := C)).choose_spec.2.1

/-- The chosen map is a morphism over the base field. -/
theorem divRepAffP1Map_comp :
    divRepAffP1Map C ≫ P1.structureMap k = C.hom :=
  (exists_isFinite_isDominant_toP1 (C := C)).choose_spec.2.2

/-- The unconditional Picard coverage parameter attached to the same map used by the
divisor representer. -/
noncomputable def divRepAffAdmissibleParameter : ℕ := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : IsIntegral C.left := isIntegral_left_of_geometricallyReduced C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  exact admissibleCoverageParameter (C := C) (divRepAffP1Map_comp C) (genus C)

/-- The curve genus is at most the unconditional admissible coverage parameter. -/
theorem genus_le_divRepAffAdmissibleParameter :
    genus C ≤ divRepAffAdmissibleParameter C := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : IsIntegral C.left := isIntegral_left_of_geometricallyReduced C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  change genus C ≤
    admissibleCoverageParameter (C := C) (divRepAffP1Map_comp C) (genus C)
  by_cases hg : genus C = 0
  · omega
  · exact Nat.le_of_lt
      (genus_lt_admissibleCoverageParameter_of_ne_zero
        (C := C) (divRepAffP1Map_comp C) (genus C) hg (chi_moduleKSheaf C))

/-- A representer for the widened divisor functor at the genus of a challenge curve.  The finite
dominant map to `P1`, the cohomology finiteness instances, and the Euler-characteristic identities
are all chosen internally from the curve assumptions. -/
noncomputable def divFunctorAffGenusRepresenter :
    Σ D : Over (Spec (.of k)), (divFunctorAff C (genus C)).RepresentableBy D := by
  classical
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : IsIntegral C.left := isIntegral_left_of_geometricallyReduced C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  have hpi : divRepAffP1Map C ≫ P1.structureMap k = C.left ↘ Spec (.of k) :=
    divRepAffP1Map_comp C
  let D := divRepAffScheme_at (C := C) (pi := divRepAffP1Map C)
    (hpi := hpi) (g := genus C) (hO := h0_moduleKSheaf C)
    (gamma := genus C) (hgamma := Nat.le_refl _) (hchiGamma := chi_moduleKSheaf C)
  exact ⟨D, divFunctorAff_representableBy_at
    (C := C) (pi := divRepAffP1Map C) (hpi := hpi)
    (g := genus C) (hO := h0_moduleKSheaf C)
    (gamma := genus C) (hgamma := Nat.le_refl _) (hchiGamma := chi_moduleKSheaf C)⟩

/-- A chosen scheme representing the widened divisor functor at the curve's genus. -/
noncomputable def divRepAffGenusScheme : Over (Spec (.of k)) :=
  (divFunctorAffGenusRepresenter C).1

/-- The widened divisor functor at the genus of a challenge curve is representable, with no
additional hypotheses. -/
noncomputable def divFunctorAff_genus_representableBy :
    (divFunctorAff C (genus C)).RepresentableBy (divRepAffGenusScheme C) :=
  (divFunctorAffGenusRepresenter C).2

/-- A representer for the widened divisor functor at the unconditional Picard coverage
parameter. The curve genus controls Euler-characteristic normalization independently of the
larger divisor degree. -/
noncomputable def divFunctorAffAdmissibleRepresenter :
    Σ D : Over (Spec (.of k)),
      (divFunctorAff C (divRepAffAdmissibleParameter C)).RepresentableBy D := by
  classical
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : IsIntegral C.left := isIntegral_left_of_geometricallyReduced C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  have hpi : divRepAffP1Map C ≫ P1.structureMap k = C.left ↘ Spec (.of k) :=
    divRepAffP1Map_comp C
  let D := divRepAffScheme_at (C := C) (pi := divRepAffP1Map C)
    (hpi := hpi) (g := divRepAffAdmissibleParameter C) (hO := h0_moduleKSheaf C)
    (gamma := genus C) (hgamma := genus_le_divRepAffAdmissibleParameter C)
    (hchiGamma := chi_moduleKSheaf C)
  exact ⟨D, divFunctorAff_representableBy_at
    (C := C) (pi := divRepAffP1Map C) (hpi := hpi)
    (g := divRepAffAdmissibleParameter C) (hO := h0_moduleKSheaf C)
    (gamma := genus C) (hgamma := genus_le_divRepAffAdmissibleParameter C)
    (hchiGamma := chi_moduleKSheaf C)⟩

/-- The chosen scheme representing the widened divisor functor at the unconditional Picard
coverage parameter. -/
noncomputable def divRepAffAdmissibleScheme : Over (Spec (.of k)) :=
  (divFunctorAffAdmissibleRepresenter C).1

/-- The widened divisor functor at the unconditional Picard coverage parameter is representable
without any additional curve, divisor-degree, or rational-point hypothesis. -/
noncomputable def divFunctorAff_admissible_representableBy :
    (divFunctorAff C (divRepAffAdmissibleParameter C)).RepresentableBy
      (divRepAffAdmissibleScheme C) :=
  (divFunctorAffAdmissibleRepresenter C).2

end Curve

end AlgebraicGeometry
