/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffChallenge

/-!
# Cohomology of admissible-degree divisors

The admissible Abel parameter lies above the uniform ledger bound.  Consequently, every
divisor whose degree is at least that parameter has vanishing `H^1`.  At exact admissible
degree, the Riemann--Roch rank anchor then computes `h^0`, and hence the projective dimension
of the corresponding complete linear system.

These are field-fibre calculations only.  They do not construct a universal divisor line
bundle, prove local freeness or base change for its pushforward, or produce a relative
projective bundle or kernel scheme.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (L : Type u) [Field L] [Algebra k L]

local instance instIsIntegralRelCurveKernelFibre :
    IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

local instance instSmoothRelCurveKernelFibre :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

local instance instQuasiCompactRelCurveKernelFibre :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

local instance instModuleFiniteH0RelCurveKernelFibre :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

local instance instModuleFiniteH1RelCurveKernelFibre :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

/-- Divisors of degree at least the admissible Abel parameter have vanishing first
cohomology.  The statement is monotone in the degree, so exact admissible degree is a direct
special case rather than an additional hypothesis.

* Provenance: ADAPTED.
* TO CHECK: Milne's cited page assumes positive genus, while this fibrewise
  statement is packaged for all genera; verify the genus-zero scope. -/
theorem subsingleton_h1_of_divRepAffAdmissibleParameter_le_deg
    (D : (relCurve C L).CurveDivisor)
    (hD : (divRepAffAdmissibleParameter C : ℤ) ≤
      Scheme.CurveDivisor.deg L D) :
    Subsingleton (Sheaf.HModule ((relCurve C L).divisorSheaf L D) 1) := by
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
  apply subsingleton_h1_of_ledger_bound
    (C := C) (π := divRepAffP1Map C) (divRepAffP1Map_comp C)
      (genus C) (chi_moduleKSheaf C) L D
  exact (ledgerBound_le_admissibleCoverageParameter
    (C := C) (divRepAffP1Map_comp C) (genus C)).trans hD

/-- At exact admissible degree, Riemann--Roch computes the section rank as the admissible
parameter plus one minus the genus. -/
theorem h0_divisorSheaf_eq_divRepAffAdmissibleParameter_add_one_sub_genus
    (D : (relCurve C L).CurveDivisor)
    (hD : Scheme.CurveDivisor.deg L D =
      (divRepAffAdmissibleParameter C : ℤ)) :
    (Sheaf.h0 ((relCurve C L).divisorSheaf L D) : ℤ) =
      (divRepAffAdmissibleParameter C : ℤ) + 1 - (genus C : ℤ) := by
  have h1 :=
    subsingleton_h1_of_divRepAffAdmissibleParameter_le_deg C L D hD.ge
  have h0 := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := L) D h1
  have hchi := chi_relCurve_baseField C L (genus C) (chi_moduleKSheaf C)
  rw [hD, hchi] at h0
  omega

/-- The complete linear system of an admissible-degree divisor has projective dimension equal
to the admissible parameter minus the genus. -/
theorem h0_sub_one_eq_divRepAffAdmissibleParameter_sub_genus
    (D : (relCurve C L).CurveDivisor)
    (hD : Scheme.CurveDivisor.deg L D =
      (divRepAffAdmissibleParameter C : ℤ)) :
    Sheaf.h0 ((relCurve C L).divisorSheaf L D) - 1 =
      divRepAffAdmissibleParameter C - genus C := by
  have h0 :=
    h0_divisorSheaf_eq_divRepAffAdmissibleParameter_add_one_sub_genus C L D hD
  have hg := genus_le_divRepAffAdmissibleParameter C
  omega

end AlgebraicGeometry
