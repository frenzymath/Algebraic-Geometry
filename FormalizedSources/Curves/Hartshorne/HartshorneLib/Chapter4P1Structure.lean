/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4P1Charts

/-!
# The structure morphism of the projective line

The `Proj` model used by the Hartshorne library has degree-zero part canonically isomorphic
to the ground field.  This file packages that isomorphism as the structure morphism
`P1.structureMap`, which is the compatibility datum used by finite-map cohomology.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry
open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
namespace P1

variable (k : Type u) [Field k]

local notation "Astd" => homogeneousSubmodule (Fin 2) k

/-- The standard graded polynomial ring is finite type over its degree-zero part. -/
instance : Algebra.FiniteType (Astd 0) (MvPolynomial (Fin 2) k) :=
  have : IsScalarTower k (Astd 0) (MvPolynomial (Fin 2) k) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := Astd 0)
      (A := MvPolynomial (Fin 2) k) (fun r =>
      (SetLike.GradeZero.coe_algebraMap Astd r).symm
      )
  Algebra.FiniteType.of_restrictScalars_finiteType k (Astd 0)
    (MvPolynomial (Fin 2) k)

/-- The canonical structure morphism `P1 k -> Spec k`. -/
noncomputable def structureMap : P1 k ⟶ Spec (.of k) :=
  Proj.toSpecZero Astd ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Astd 0)))

instance : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (Astd 0)))) := by
  have h : IsIso (CommRingCat.ofHom (algebraMap k (Astd 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (gradeZeroAlgEquiv k).bijective
  infer_instance

/-- The projective-line structure map is proper. -/
instance : IsProper (structureMap k) := by
  have h1 : IsProper (Proj.toSpecZero Astd) := inferInstance
  have h2 : IsProper (Spec.map (CommRingCat.ofHom (algebraMap k (Astd 0)))) :=
    inferInstance
  exact IsProper.comp_iff.mpr h1

/-- The projective line as an object over `Spec k`. -/
noncomputable def asOver : Over (Spec (.of k)) := Over.mk (structureMap k)

instance : IsProper (asOver k).hom := inferInstanceAs (IsProper (structureMap k))

end P1
end AlgebraicGeometry
