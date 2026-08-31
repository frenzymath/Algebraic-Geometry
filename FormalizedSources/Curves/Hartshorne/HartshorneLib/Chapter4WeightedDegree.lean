/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4Curves
import HartshorneLib.Chapter4ResidueDegree
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Residue-weighted degree

The natural degree over an arbitrary base field weights each coefficient by the
dimension of the corresponding residue field.  Hartshorne's curve convention
uses the bare coefficient sum because the base field is algebraically closed.
This file records both versions on the existing divisor carrier and proves
their agreement in that convention.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

attribute [local instance] AlgebraicGeometry.Scheme.residueFieldOverModule

namespace CurveDivisor

/-- The residue-weighted degree of a divisor. -/
noncomputable def residueWeightedDegree (D : CurveDivisor k X) : ℤ :=
  letI : X.left.Over (Spec (CommRingCat.of k)) := .ofHom X.hom
  D.sum (fun p n => n *
    (AlgebraicGeometry.Scheme.residueDeg k X.left p.1 : ℤ))

@[simp]
theorem residueWeightedDegree_zero :
    residueWeightedDegree (k := k) (X := X) (0 : CurveDivisor k X) = 0 := by
  classical
  unfold residueWeightedDegree
  exact Finsupp.sum_zero_index

theorem residueWeightedDegree_add (D E : CurveDivisor k X) :
    residueWeightedDegree (D + E) =
      residueWeightedDegree D + residueWeightedDegree E := by
  classical
  unfold residueWeightedDegree
  refine Finsupp.sum_add_index' (fun _ => ?_) (fun _ a b => ?_)
  · simp
  · ring

theorem residueWeightedDegree_single
    (p : {x : X.left // x ≠ genericPoint X.left}) (n : ℤ) :
    residueWeightedDegree (Finsupp.single p n : CurveDivisor k X) =
      n * (AlgebraicGeometry.Scheme.residueDeg k X.left p.1 : ℤ) := by
  classical
  unfold residueWeightedDegree
  simp

/-- Over an algebraically closed base, residue weighting is invisible. -/
theorem residueWeightedDegree_eq_degree (D : CurveDivisor k X) :
    residueWeightedDegree D = degree D := by
  classical
  letI : X.left.Over (Spec (CommRingCat.of k)) := .ofHom X.hom
  letI : SmoothOfRelativeDimension 1 (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  letI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  unfold residueWeightedDegree degree
  refine Finsupp.sum_congr fun p _ => ?_
  have hp : AlgebraicGeometry.Scheme.residueDeg k X.left p.1 = 1 :=
    AlgebraicGeometry.Scheme.residueDeg_eq_one_of_isAlgClosed
      (K := k) (X := X.left) p.2
  rw [hp]
  ring

end CurveDivisor

end Hartshorne
