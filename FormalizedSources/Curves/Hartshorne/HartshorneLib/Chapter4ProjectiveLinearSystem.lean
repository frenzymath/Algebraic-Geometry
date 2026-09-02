/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4LinearSystemDimension

/-!
# Hartshorne IV.3.1: projective-map certificates for linear systems

The numerical predicates in `Chapter4LinearSystemCriteria` deliberately do not
assert that a morphism to projective space exists.  This file supplies a small
interface for recording such a morphism when it is available.  The target is
the explicit `Proj` model of finite projective space, and the equation over
`Spec k` is a field of the certificate rather than an inferred geometric fact.

The base-point-free and very-ample certificates also carry the corresponding
dimension-drop hypotheses.  Consequently the extraction theorems below use
only the already-proved numerical equivalences; they do not claim that a
numerical predicate constructs a morphism or that an arbitrary morphism comes
from the complete linear system.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry
open MvPolynomial

namespace Hartshorne

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
variable {D : CurveDivisor k X}

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### A concrete projective target -/

/-- The `Proj` model of finite projective `n`-space over `k`. -/
noncomputable def projectiveSpace (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)

/-- The canonical map from the chosen projective-space model to `Spec k`.

The degree-zero part is used exactly as in the existing `P1.structureMap`.
No claim about an isomorphism with `k` is needed for the certificate API.
-/
noncomputable def projectiveSpaceStructureMap
    (k : Type u) [Field k] (n : ℕ) :
    projectiveSpace k n ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap k
        ((MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) 0)))

/-! ### Explicit certificates -/

/-- Data certifying a morphism from `X` to a finite projective space over `k`.

The compatibility equation is intentionally explicit.  In particular, this
structure does not assert that a map exists from a numerical linear-system
predicate; callers must provide the target dimension, map, and equation.
-/
structure ProjectiveMapCertificate (D : CurveDivisor k X) where
  /-- The dimension of the projective target. -/
  n : ℕ
  /-- The target dimension agrees with the complete linear-system dimension. -/
  target_dimension : (n : ℤ) = linearSystemDimension D
  /-- The underlying scheme morphism to the chosen projective target. -/
  map : X.left ⟶ projectiveSpace k n
  /-- The map is a morphism over `Spec k`. -/
  map_over : map ≫ projectiveSpaceStructureMap k n = X.hom

namespace ProjectiveMapCertificate

/-- Package an explicitly supplied over-`Spec k` morphism. -/
def of_map (D : CurveDivisor k X) (n : ℕ)
    (target_dimension : (n : ℤ) = linearSystemDimension D)
    (map : X.left ⟶ projectiveSpace k n)
    (map_over : map ≫ projectiveSpaceStructureMap k n = X.hom) :
    ProjectiveMapCertificate D :=
  ⟨n, target_dimension, map, map_over⟩

@[simp] theorem target_dimension_eq (c : ProjectiveMapCertificate D) :
    (c.n : ℤ) = linearSystemDimension D :=
  c.target_dimension

@[simp] theorem map_over_eq (c : ProjectiveMapCertificate D) :
    c.map ≫ projectiveSpaceStructureMap k c.n = X.hom :=
  c.map_over

end ProjectiveMapCertificate

/-- A projective-map certificate carrying the numerical base-point-free
dimension drops as an explicit hypothesis. -/
structure BasePointFreeProjectiveMapCertificate
    (D : CurveDivisor k X) extends ProjectiveMapCertificate D where
  dimension_drop :
    ∀ (x : X.left) (hx : x ≠ genericPoint X.left),
      linearSystemDimension (CurveDivisor.devissageDivisor hx D) =
        linearSystemDimension D - 1

namespace BasePointFreeProjectiveMapCertificate

/-- Build the certificate once an over-`Spec k` map and the numerical predicate
have been supplied.  This constructor does not manufacture the map. -/
def of_basePointFree
    (base : ProjectiveMapCertificate D)
    (hD : BasePointFreeLinearSystem D) :
    BasePointFreeProjectiveMapCertificate D :=
  ⟨base, (basePointFreeLinearSystem_iff_linearSystemDimension_drop D).mp hD⟩

/-- The dimension-drop component implies the existing numerical predicate. -/
theorem basePointFreeLinearSystem
    (c : BasePointFreeProjectiveMapCertificate D) :
    BasePointFreeLinearSystem D :=
  (basePointFreeLinearSystem_iff_linearSystemDimension_drop D).mpr c.dimension_drop

end BasePointFreeProjectiveMapCertificate

/-- A projective-map certificate carrying both the numerical very-ample drops
and an explicit closed-immersion hypothesis for the chosen map. -/
structure VeryAmpleProjectiveMapCertificate
    (D : CurveDivisor k X) extends ProjectiveMapCertificate D where
  /-- The supplied projective map is a closed immersion. -/
  closedImmersion : IsClosedImmersion toProjectiveMapCertificate.map
  dimension_drop :
    ∀ (x y : X.left)
      (hx : x ≠ genericPoint X.left) (hy : y ≠ genericPoint X.left),
      linearSystemDimension
          (CurveDivisor.devissageDivisor hy
            (CurveDivisor.devissageDivisor hx D)) =
        linearSystemDimension D - 2

namespace VeryAmpleProjectiveMapCertificate

/-- Build the certificate from an explicitly supplied map, closed-immersion
proof, and numerical very-ample predicate. -/
def of_veryAmple
    (base : ProjectiveMapCertificate D)
    (hclosed : IsClosedImmersion base.map)
    (hD : VeryAmpleLinearSystem D) :
    VeryAmpleProjectiveMapCertificate D :=
  ⟨base, hclosed,
    (veryAmpleLinearSystem_iff_linearSystemDimension_drop D).mp hD⟩

/-- The dimension-drop component implies the existing numerical predicate. -/
theorem veryAmpleLinearSystem
    (c : VeryAmpleProjectiveMapCertificate D) :
    VeryAmpleLinearSystem D :=
  (veryAmpleLinearSystem_iff_linearSystemDimension_drop D).mpr c.dimension_drop

@[simp] theorem closedImmersion_map
    (c : VeryAmpleProjectiveMapCertificate D) :
    IsClosedImmersion c.toProjectiveMapCertificate.map :=
  c.closedImmersion

end VeryAmpleProjectiveMapCertificate

/-! ### Unbundled extraction aliases -/

/-- A base-point-free projective-map certificate implies the numerical
base-point-free predicate. -/
theorem basePointFreeLinearSystem_of_projectiveMapCertificate
    (c : BasePointFreeProjectiveMapCertificate D) :
    BasePointFreeLinearSystem D :=
  c.basePointFreeLinearSystem

/-- A very-ample projective-map certificate implies the numerical very-ample
predicate. -/
theorem veryAmpleLinearSystem_of_projectiveMapCertificate
    (c : VeryAmpleProjectiveMapCertificate D) :
    VeryAmpleLinearSystem D :=
  c.veryAmpleLinearSystem

end
end Hartshorne
