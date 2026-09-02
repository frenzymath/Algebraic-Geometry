/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4ProjectiveMapProducer

/-!
# Hartshorne IV.3.1: divisor sections as projective coordinates

The `Proj.fromOfGlobalSections` constructor works with sections of the
structure sheaf.  A section of `𝒪(D)` is instead a rational function, so there
is no canonical way to feed a basis of `H⁰(X, 𝒪(D))` to that constructor without
additional geometric data.  This file records that missing bridge explicitly:
a supplied globalization of the basis sections, together with the irrelevant-
ideal generation certificate, produces the existing projective-map datum.
No regularity, gluing, or base-point-freeness assertion is hidden in a
definition.  For a nontrivial complete linear system on a proper curve this
globalization is too restrictive: the genuine construction uses local ratios
of divisor sections and glues the resulting projective-coordinate maps.
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
attribute [local instance] Scheme.overModule

noncomputable local instance globalSectionsAlgebra : Algebra k Γ(X.left, ⊤) :=
  (X.left.overAlgebraMap k (⊤ : X.left.Opens)).toAlgebra

/-! ### The two section values involved in the bridge -/

/-- The rational-function value of a degree-zero divisor-sheaf cohomology class. -/
noncomputable def divisorH0Value (D : CurveDivisor k X)
    (s : CurveDivisorSectionSpace D) : X.left.functionField :=
  divisorVal
    (CategoryTheory.Sheaf.HModule.linearEquiv₀
      (isTerminalTop : IsTerminal (⊤ : X.left.Opens)) (divisorSheaf D) s)

/-- Degree-zero divisor-sheaf cohomology classes are determined by their
rational-function values. -/
theorem divisorH0Value_injective (D : CurveDivisor k X) :
    Function.Injective (divisorH0Value D) := by
  intro s t h
  apply (CategoryTheory.Sheaf.HModule.linearEquiv₀
    (isTerminalTop : IsTerminal (⊤ : X.left.Opens)) (divisorSheaf D)).injective
  apply divisorSection_ext
  exact h

/-- The rational-function value of a global structure-sheaf section. -/
noncomputable def structureH0Value (s : Γ(X.left, ⊤)) : X.left.functionField :=
  (X.left.presheaf.germ ⊤ (genericPoint X.left) trivial).hom s

/-! ### Explicit globalization of a divisor-section space -/

/--
Data realizing divisor-sheaf sections as global structure-sheaf sections.

The value equation is the regularity requirement needed to compare the two
section spaces inside the function field.  It is deliberately a field of the
data structure: it is not available for an arbitrary divisor and cannot be
replaced by typeclass inference.
-/
structure DivisorSectionGlobalization (D : CurveDivisor k X) where
  /-- The proposed global structure-sheaf section attached to a divisor section. -/
  toGlobal : CurveDivisorSectionSpace D →ₗ[k] Γ(X.left, ⊤)
  /-- The proposed section has the same rational-function value. -/
  value_eq : ∀ s,
    structureH0Value (toGlobal s) = divisorH0Value D s

namespace DivisorSectionGlobalization

@[simp] theorem toGlobal_zero (g : DivisorSectionGlobalization D) :
    g.toGlobal 0 = 0 := by
  exact g.toGlobal.map_zero

@[simp] theorem toGlobal_add (g : DivisorSectionGlobalization D)
    (s t : CurveDivisorSectionSpace D) :
    g.toGlobal (s + t) = g.toGlobal s + g.toGlobal t := by
  exact g.toGlobal.map_add s t

@[simp] theorem toGlobal_smul (g : DivisorSectionGlobalization D)
    (r : k) (s : CurveDivisorSectionSpace D) :
    g.toGlobal (r • s) = r • g.toGlobal s := by
  exact g.toGlobal.map_smul r s

/-- A value-preserving globalization is necessarily injective.  Thus the
global structure-sheaf section space must be large enough to contain the whole
divisor-section space; this exposes why local ratios are needed in the usual
positive-degree construction. -/
theorem toGlobal_injective (g : DivisorSectionGlobalization D) :
    Function.Injective g.toGlobal := by
  intro s t h
  apply divisorH0Value_injective D
  rw [← g.value_eq s, ← g.value_eq t, h]

end DivisorSectionGlobalization

/-! ### Coordinates indexed by a finite basis -/

/--
A finite divisor-section basis equipped with explicit global coordinates.

`coordinate_sections` remembers the actual divisor-sheaf sections represented by
the basis vectors.  `coordinate_value` compares their rational values with the
global structure-sheaf coordinates.  The final field is exactly the generation
hypothesis consumed by `Proj.fromOfGlobalSections`.
-/
structure DivisorSectionCoordinateData (D : CurveDivisor k X) (n : ℕ) where
  basis : Module.Basis (Fin (n + 1)) k (CurveDivisorSectionSpace D)
  globalization : DivisorSectionGlobalization D
  coordinates : Fin (n + 1) → Γ(X.left, ⊤)
  coordinates_eq_globalization :
    ∀ i, coordinates i = globalization.toGlobal (basis i)
  coordinate_sections : Fin (n + 1) → divisorSections D ⊤
  coordinate_sections_eq_basis :
    ∀ i, coordinate_sections i =
      CategoryTheory.Sheaf.HModule.linearEquiv₀
        (isTerminalTop : IsTerminal (⊤ : X.left.Opens)) (divisorSheaf D) (basis i)
  coordinate_value : ∀ i,
    structureH0Value (coordinates i) = divisorVal (coordinate_sections i)
  irrelevant_span :
    letI : Algebra k Γ(X.left, ⊤) :=
      (X.left.overAlgebraMap k (⊤ : X.left.Opens)).toAlgebra
    (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).toIdeal.map
        (MvPolynomial.aeval coordinates).toRingHom = ⊤

namespace DivisorSectionCoordinateData

/-- Assemble coordinate data from a basis and an explicit globalization.

The only remaining input is the irrelevant-ideal generation statement.  The
coordinate sections themselves are canonically the degree-zero sections
associated to the basis vectors.
-/
def of_globalization (D : CurveDivisor k X) (n : ℕ)
    (basis : Module.Basis (Fin (n + 1)) k (CurveDivisorSectionSpace D))
    (globalization : DivisorSectionGlobalization D)
    (irrelevant_span :
      letI : Algebra k Γ(X.left, ⊤) :=
        (X.left.overAlgebraMap k (⊤ : X.left.Opens)).toAlgebra
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).toIdeal.map
          (MvPolynomial.aeval (fun i => globalization.toGlobal (basis i))).toRingHom = ⊤) :
    DivisorSectionCoordinateData D n :=
  { basis := basis
    globalization := globalization
    coordinates := fun i => globalization.toGlobal (basis i)
    coordinates_eq_globalization := fun _ => rfl
    coordinate_sections := fun i =>
      CategoryTheory.Sheaf.HModule.linearEquiv₀
        (isTerminalTop : IsTerminal (⊤ : X.left.Opens)) (divisorSheaf D) (basis i)
    coordinate_sections_eq_basis := fun _ => rfl
    coordinate_value := fun i => by
      rw [globalization.value_eq]
      rfl
    irrelevant_span := irrelevant_span }

/-- The basis vector represented as an honest section on the whole curve. -/
noncomputable def basisSection
    {n : ℕ} (data : DivisorSectionCoordinateData D n) (i : Fin (n + 1)) :
    divisorSections D ⊤ :=
  CategoryTheory.Sheaf.HModule.linearEquiv₀
    (isTerminalTop : IsTerminal (⊤ : X.left.Opens)) (divisorSheaf D) (data.basis i)

@[simp] theorem coordinate_sections_eq_basisSection
    {n : ℕ} (data : DivisorSectionCoordinateData D n) (i : Fin (n + 1)) :
    data.coordinate_sections i = data.basisSection i :=
  data.coordinate_sections_eq_basis i

/-- The value of a coordinate is the value of the corresponding divisor section. -/
theorem coordinate_value_eq_divisorH0Value
    {n : ℕ} (data : DivisorSectionCoordinateData D n) (i : Fin (n + 1)) :
    structureH0Value (data.coordinates i) =
      divisorH0Value D (data.basis i) := by
  rw [data.coordinates_eq_globalization i, data.globalization.value_eq]

/-- A value-preserving globalization carries the chosen divisor-section basis
to a linearly independent family of global coordinates. -/
theorem coordinates_linearIndependent
    {n : ℕ} (data : DivisorSectionCoordinateData D n) :
    LinearIndependent k data.coordinates := by
  have hker : data.globalization.toGlobal.ker = ⊥ :=
    LinearMap.ker_eq_bot_of_injective data.globalization.toGlobal_injective
  have hli :
      LinearIndependent k
        (data.globalization.toGlobal ∘ data.basis) :=
    (Module.Basis.linearIndependent data.basis).map'
      data.globalization.toGlobal hker
  have hcoord :
      (data.globalization.toGlobal ∘ data.basis) = data.coordinates := by
    funext i
    simpa only [Function.comp_apply] using
      (data.coordinates_eq_globalization i).symm
  rw [← hcoord]
  exact hli

/-- Every coordinate in a value-preserving globalization is nonzero. -/
theorem coordinates_ne_zero
    {n : ℕ} (data : DivisorSectionCoordinateData D n) (i : Fin (n + 1)) :
    data.coordinates i ≠ 0 :=
  (data.coordinates_linearIndependent).ne_zero i

/-- Forget the divisor-section bookkeeping and expose the existing global-section
`Proj` input. -/
def toGlobalSectionsProjectiveMapData
    {n : ℕ} (data : DivisorSectionCoordinateData D n) :
    GlobalSectionsProjectiveMapData (k := k) (X := X) n :=
  ⟨data.coordinates, data.irrelevant_span⟩

@[simp] theorem toGlobalSectionsProjectiveMapData_sections
    {n : ℕ} (data : DivisorSectionCoordinateData D n) :
    data.toGlobalSectionsProjectiveMapData.sections = data.coordinates :=
  rfl

@[simp] theorem toGlobalSectionsProjectiveMapData_irrelevant_span
    {n : ℕ} (data : DivisorSectionCoordinateData D n) :
    data.toGlobalSectionsProjectiveMapData.irrelevant_span = data.irrelevant_span :=
  rfl

/-- Build the projective-map producer from a divisor-section coordinate datum. -/
def toProjectiveMapProducer
    {n : ℕ} (data : DivisorSectionCoordinateData D n) :
    ProjectiveMapProducer D :=
  ProjectiveMapProducer.of_globalSections D n data.basis
    data.toGlobalSectionsProjectiveMapData

@[simp] theorem toProjectiveMapProducer_n
    {n : ℕ} (data : DivisorSectionCoordinateData D n) :
    data.toProjectiveMapProducer.n = n :=
  rfl

@[simp] theorem toProjectiveMapProducer_basis
    {n : ℕ} (data : DivisorSectionCoordinateData D n) :
    data.toProjectiveMapProducer.basis = data.basis :=
  rfl

@[simp] theorem toProjectiveMapProducer_map
    {n : ℕ} (data : DivisorSectionCoordinateData D n) :
    data.toProjectiveMapProducer.map =
      data.toGlobalSectionsProjectiveMapData.map :=
  rfl

@[simp] theorem toProjectiveMapProducer_map_over
    {n : ℕ} (data : DivisorSectionCoordinateData D n) :
    data.toProjectiveMapProducer.map ≫ projectiveSpaceStructureMap k n = X.hom :=
  data.toGlobalSectionsProjectiveMapData.map_over

end DivisorSectionCoordinateData

end
end Hartshorne
