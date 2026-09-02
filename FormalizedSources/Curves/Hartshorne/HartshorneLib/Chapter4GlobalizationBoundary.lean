/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorSectionCoordinates

/-!
# Hartshorne IV.3.1: the global-section globalization boundary

The value-preserving globalization packaged in
`Chapter4DivisorSectionCoordinates` maps divisor-sheaf sections into ordinary
global structure-sheaf sections.  Properness makes the latter one-dimensional,
so this certificate can only describe a complete linear system of dimension
zero.  The genuine positive-dimensional construction must therefore use local
ratios and glue projective charts.
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

/-- A value-preserving globalization bounds the divisor-section H⁰ by the
ordinary structure-sheaf H⁰. -/
theorem globalization_h0_le_structure_h0
    (g : DivisorSectionGlobalization D) :
    CategoryTheory.Sheaf.h0 (divisorSheaf D) ≤
      CategoryTheory.Sheaf.h0 (X.left.moduleKSheaf k) := by
  let eO :=
    CategoryTheory.Sheaf.HModule.linearEquiv₀
      (isTerminalTop : IsTerminal (⊤ : X.left.Opens)) (X.left.moduleKSheaf k)
  let f := eO.symm.toLinearMap.comp g.toGlobal
  have hf : Function.Injective f := by
    intro s t h
    apply g.toGlobal_injective
    apply eO.symm.injective
    exact h
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 0) :=
    moduleFinite_moduleKSheaf_zero_of_isProper k X
  change Module.finrank k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0) ≤
    Module.finrank k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 0)
  exact LinearMap.finrank_le_finrank_of_injective (f := f) hf

/-- A value-preserving globalization cannot exist for a positive-dimensional
complete linear system on a proper integral curve. -/
theorem no_globalization_of_linearSystemDimension_pos
    (g : DivisorSectionGlobalization D)
    (hD : 0 < linearSystemDimension D) : False := by
  have hle := globalization_h0_le_structure_h0 g
  have hzero := h0_moduleKSheaf_eq_one (k := k) (X := X)
  rw [hzero] at hle
  have hdim := linearSystemDimension_eq_h0_sub_one D
  omega

end
end Hartshorne
