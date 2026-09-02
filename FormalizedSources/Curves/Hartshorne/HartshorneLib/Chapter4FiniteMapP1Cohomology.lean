/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4FiniteMapP1Existence
import HartshorneLib.Chapter4FiniteMapP1Producer

/-! # Curve cohomology from a finite map to `P1`

The finite-map producer and the curve-to-`P1` existence theorem have deliberately
separate interfaces.  This module composes them at the curve use site.  The
`Over` instance on the underlying scheme is installed locally, so no competing
global scalar structure is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k]

/-- A smooth proper integral curve has finite degree-one structure-sheaf
cohomology.  The proof factors through the explicit finite dominant map to
`P1` and the Laurent/Cech producer. -/
theorem moduleFinite_moduleKSheaf_one_of_smoothProperIntegralCurve
    (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    Module.Finite k
      (Sheaf.HModule (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 1) := by
  letI : X.left.Over (Spec (CommRingCat.of k)) := .ofHom X.hom
  obtain ⟨π, hfin, _hdom, hcomp⟩ :=
    AlgebraicGeometry.exists_isFinite_isDominant_toP1 X.hom
  letI : IsFinite π := hfin
  exact FiniteMapP1Producer.moduleFinite_hModule_one_of_isFinite_toP1 π hcomp

end Hartshorne
