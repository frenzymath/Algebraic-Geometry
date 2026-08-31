/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite morphisms and affine section modules

The finite-map-to-projective-line argument needs a finite module on each affine
target chart.  This file isolates the corresponding scheme-theoretic input:
the finite ring map on sections supplied by `IsFinite` gives finite generation
of sections on the inverse-image chart.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

namespace FiniteMapSections

variable {X Y : Scheme.{u}}

/-- The algebra on sections induced by a morphism of schemes over an affine open.

This is kept as a named, reducible definition so callers can install exactly the
section algebra needed by `RingHom.Finite` and `Module.Finite` without introducing a
global instance that could compete with another scalar structure. -/
@[reducible]
noncomputable def sectionAlgebra (f : X ⟶ Y) (U : Y.Opens) :
    Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

/-- A finite morphism induces a finite module on sections over every affine target open. -/
theorem moduleFinite_of_isFinite (f : X ⟶ Y) [IsFinite f]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := sectionAlgebra f U
    Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := sectionAlgebra f U
  rw [← RingHom.finite_algebraMap]
  exact f.finite_app U hU

/-- A finite morphism supplies a finite spanning set for sections over an affine target open. -/
theorem exists_finset_generators_of_isFinite (f : X ⟶ Y) [IsFinite f]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := sectionAlgebra f U
    ∃ s : Finset Γ(X, f ⁻¹ᵁ U),
      Submodule.span Γ(Y, U) (s : Set Γ(X, f ⁻¹ᵁ U)) = ⊤ := by
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := sectionAlgebra f U
  letI : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    moduleFinite_of_isFinite f U hU
  exact Module.Finite.fg_top (R := Γ(Y, U)) (M := Γ(X, f ⁻¹ᵁ U))

end FiniteMapSections

end Hartshorne
