/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2Chi
import HartshorneLib.Chapter4DivisorSheafZero

/-!
# The χ base case for divisor sheaves

The zero divisor sheaf is the structure sheaf.  This small bridge exposes the
corresponding Euler-characteristic equality to the cohomology ledger.
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

theorem chi_divisorSheaf_zero :
    CategoryTheory.Sheaf.chi (divisorSheaf (X := X) (0 : CurveDivisor k X)) =
      CategoryTheory.Sheaf.chi (X.left.moduleKSheaf k) :=
  CategoryTheory.Sheaf.chi_congr (divisorSheafZeroIso (X := X))

end
end Hartshorne
