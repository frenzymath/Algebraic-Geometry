/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4ProjectiveLinearSystem

/-!
# Hartshorne IV.3.1: producing the projective map from a section basis

`Chapter4ProjectiveLinearSystem` records a projective map together with its
target dimension.  This file packages the finite-dimensional section basis
which supplies that dimension.  It also exposes the standard `Proj` constructor
from a generating family of global sections.  The bridge from a divisor-sheaf
basis to such coordinates, and the resulting geometric properties, remains
explicit data rather than an unproved assertion.
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

/-- The degree-zero cohomology module of a curve divisor. -/
abbrev CurveDivisorSectionSpace (D : CurveDivisor k X) : Type u :=
  CategoryTheory.Sheaf.HModule
    (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D) 0

/-! ### Maps from global sections -/

/-- A finite family of global sections whose homogeneous coordinates cover `X`.

The irrelevant-ideal condition is the precise generation hypothesis used by
`Proj.fromOfGlobalSections`; it is kept explicit so that this API does not
claim base-point-freeness without a proof of generation.
-/
structure GlobalSectionsProjectiveMapData (n : ℕ) where
  sections : Fin (n + 1) → Γ(X.left, ⊤)
  irrelevant_span :
    letI : Algebra k Γ(X.left, ⊤) :=
      (X.left.overAlgebraMap k (⊤ : X.left.Opens)).toAlgebra
    (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).toIdeal.map
        (MvPolynomial.aeval sections).toRingHom = ⊤

namespace GlobalSectionsProjectiveMapData

/-- The projective morphism defined by a generating family of global sections. -/
noncomputable def map
    {n : ℕ} (data : GlobalSectionsProjectiveMapData (k := k) (X := X) n) :
    X.left ⟶ projectiveSpace k n :=
  by
    letI : Algebra k Γ(X.left, ⊤) :=
      (X.left.overAlgebraMap k (⊤ : X.left.Opens)).toAlgebra
    exact Proj.fromOfGlobalSections
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
      (MvPolynomial.aeval data.sections).toRingHom data.irrelevant_span

/-- The map from global sections is over the base field. -/
@[reassoc (attr := simp)] theorem map_over
    {n : ℕ} (data : GlobalSectionsProjectiveMapData (k := k) (X := X) n) :
    data.map ≫ projectiveSpaceStructureMap k n = X.hom := by
  letI : Algebra k Γ(X.left, ⊤) :=
    (X.left.overAlgebraMap k (⊤ : X.left.Opens)).toAlgebra
  change (Proj.fromOfGlobalSections
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
      (MvPolynomial.aeval data.sections).toRingHom data.irrelevant_span) ≫
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k
            ((MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) 0)))) = X.hom
  rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero]
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hbase :
      ((MvPolynomial.aeval data.sections).toRingHom.comp
          (algebraMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)
            (MvPolynomial (Fin (n + 1)) k))).comp
        (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)) =
      X.left.overAlgebraMap k (⊤ : X.left.Opens) := by
    letI : IsScalarTower k
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)
        (MvPolynomial (Fin (n + 1)) k) :=
      IsScalarTower.of_algebraMap_eq
        (R := k)
        (S := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)
        (A := MvPolynomial (Fin (n + 1)) k) fun r => by
          change algebraMap k (MvPolynomial (Fin (n + 1)) k) r =
            ((algebraMap k
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0) r :
                MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0) :
              MvPolynomial (Fin (n + 1)) k)
          exact (SetLike.GradeZero.coe_algebraMap _ r).symm
    ext r
    change (MvPolynomial.aeval data.sections)
        ((algebraMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)
          (MvPolynomial (Fin (n + 1)) k))
          ((algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)) r)) =
      X.left.overAlgebraMap k (⊤ : X.left.Opens) r
    have hscalar := congrArg (fun f : k →+* MvPolynomial (Fin (n + 1)) k => f r)
      (IsScalarTower.algebraMap_eq k
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)
        (MvPolynomial (Fin (n + 1)) k))
    calc
      (MvPolynomial.aeval data.sections)
          ((algebraMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)
            (MvPolynomial (Fin (n + 1)) k))
            ((algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)) r)) =
          (MvPolynomial.aeval data.sections)
            (algebraMap k (MvPolynomial (Fin (n + 1)) k) r) := by
              congr 1
      _ = algebraMap k Γ(X.left, ⊤) r := (MvPolynomial.aeval data.sections).commutes r
      _ = X.left.overAlgebraMap k (⊤ : X.left.Opens) r := by
        simp only [RingHom.algebraMap_toAlgebra]
  have hstructure :
      X.left.overAlgebraMap k (⊤ : X.left.Opens) =
        (X.hom.appTop.hom).comp
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    ext y
    simp only [Scheme.overAlgebraMap, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
    exact congrFun (congrArg (fun f => f.hom)
      (X.left.presheaf.map_id (Opposite.op (⊤ : X.left.Opens)))) _
  rw [hbase, hstructure, CommRingCat.ofHom_comp, Spec.map_comp]
  change X.left.toSpecΓ ≫ Spec.map X.hom.appTop ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv = X.hom
  rw [← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end GlobalSectionsProjectiveMapData

/-- Explicit data for a map to projective space equipped with a basis of the
complete section space indexed by the homogeneous coordinates.

The map is required to be over `Spec k`; no map is inferred merely from the
existence of the basis.
-/
structure ProjectiveMapProducer (D : CurveDivisor k X) where
  /-- The projective target has one coordinate for each basis vector minus one. -/
  n : ℕ
  /-- A basis of the degree-zero divisor-sheaf cohomology. -/
  basis : Module.Basis (Fin (n + 1)) k (CurveDivisorSectionSpace D)
  /-- The explicitly supplied scheme morphism to the projective target. -/
  map : X.left ⟶ projectiveSpace k n
  /-- Compatibility with the structure morphisms to `Spec k`. -/
  map_over : map ≫ projectiveSpaceStructureMap k n = X.hom

namespace ProjectiveMapProducer

/-- Package explicit basis and over-`Spec k` map data. -/
def of_basis (D : CurveDivisor k X) (n : ℕ)
    (basis : Module.Basis (Fin (n + 1)) k (CurveDivisorSectionSpace D))
    (map : X.left ⟶ projectiveSpace k n)
    (map_over : map ≫ projectiveSpaceStructureMap k n = X.hom) :
    ProjectiveMapProducer D :=
  ⟨n, basis, map, map_over⟩

/-- Combine a section basis with the projective map constructed from a
generating family of global sections. -/
def of_globalSections (D : CurveDivisor k X) (n : ℕ)
    (basis : Module.Basis (Fin (n + 1)) k (CurveDivisorSectionSpace D))
    (data : GlobalSectionsProjectiveMapData (k := k) (X := X) n) :
    ProjectiveMapProducer D :=
  ⟨n, basis, data.map, data.map_over⟩

@[simp] theorem map_over_eq (p : ProjectiveMapProducer D) :
    p.map ≫ projectiveSpaceStructureMap k p.n = X.hom :=
  p.map_over

/-- The basis cardinality identifies the target dimension with the complete
linear-system dimension `h⁰(D) - 1`. -/
theorem target_dimension (p : ProjectiveMapProducer D) :
    (p.n : ℤ) = linearSystemDimension D := by
  have hdimNat :
      CategoryTheory.Sheaf.h0 (divisorSheaf D) = p.n + 1 := by
    change Module.finrank k (CurveDivisorSectionSpace D) = p.n + 1
    simpa [Fintype.card_fin] using (Module.finrank_eq_card_basis p.basis)
  rw [linearSystemDimension_eq_h0_sub_one, hdimNat]
  omega

/-- Turn the basis-and-map package into the dimension-indexed projective-map
certificate. -/
def toProjectiveMapCertificate (p : ProjectiveMapProducer D) :
    ProjectiveMapCertificate D :=
  ProjectiveMapCertificate.of_map D p.n p.target_dimension p.map p.map_over

@[simp] theorem toProjectiveMapCertificate_n (p : ProjectiveMapProducer D) :
    p.toProjectiveMapCertificate.n = p.n :=
  rfl

@[simp] theorem toProjectiveMapCertificate_map (p : ProjectiveMapProducer D) :
    p.toProjectiveMapCertificate.map = p.map :=
  rfl

@[simp] theorem toProjectiveMapCertificate_map_over (p : ProjectiveMapProducer D) :
    p.toProjectiveMapCertificate.map ≫
        projectiveSpaceStructureMap k p.toProjectiveMapCertificate.n = X.hom :=
  p.map_over

/-- A numerical base-point-free predicate upgrades the produced map to the
base-point-free projective-map certificate. -/
def toBasePointFreeCertificate (p : ProjectiveMapProducer D)
    (hD : BasePointFreeLinearSystem D) :
    BasePointFreeProjectiveMapCertificate D :=
  BasePointFreeProjectiveMapCertificate.of_basePointFree
    p.toProjectiveMapCertificate hD

/-- A numerical very-ample predicate and a supplied closed-immersion proof
upgrade the produced map to a very-ample projective-map certificate. -/
def toVeryAmpleCertificate (p : ProjectiveMapProducer D)
    (hclosed : IsClosedImmersion p.map)
    (hD : VeryAmpleLinearSystem D) :
    VeryAmpleProjectiveMapCertificate D :=
  VeryAmpleProjectiveMapCertificate.of_veryAmple
    p.toProjectiveMapCertificate hclosed hD

@[simp] theorem basePointFreeLinearSystem_of_predicate
    (p : ProjectiveMapProducer D) (hD : BasePointFreeLinearSystem D) :
    BasePointFreeLinearSystem D :=
  BasePointFreeProjectiveMapCertificate.basePointFreeLinearSystem
    (p.toBasePointFreeCertificate hD)

@[simp] theorem veryAmpleLinearSystem_of_predicate
    (p : ProjectiveMapProducer D) (hclosed : IsClosedImmersion p.map)
    (hD : VeryAmpleLinearSystem D) :
    VeryAmpleLinearSystem D :=
  VeryAmpleProjectiveMapCertificate.veryAmpleLinearSystem
    (p.toVeryAmpleCertificate hclosed hD)

end ProjectiveMapProducer

end
end Hartshorne
