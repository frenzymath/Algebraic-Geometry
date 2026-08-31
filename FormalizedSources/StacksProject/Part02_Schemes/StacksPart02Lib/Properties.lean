/-
Copyright (c) 2026 The StacksPart02Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart02Lib Contributors
-/

import Mathlib.AlgebraicGeometry.Properties

/-!
# Topological and reducedness properties of schemes

The Mathlib scheme API provides the local-affine proofs of the basic
topological properties of a scheme, as well as the corresponding reducedness
lemmas.  This module exposes those facts under the namespace used by the
Stacks Part 02 development.
-/

namespace StacksPart02

open TopologicalSpace Topology CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Topological properties of the underlying space of a scheme. -/

/-- The underlying topological space of a scheme is `T₀`. -/
theorem scheme_t0 (X : Scheme.{u}) : T0Space X := by
  infer_instance

/-- The underlying topological space of a scheme is quasi-sober. -/
theorem scheme_quasiSober (X : Scheme.{u}) : QuasiSober X := by
  infer_instance

/-- The underlying topological space of a scheme is prespectral. -/
theorem scheme_prespectral (X : Scheme.{u}) : PrespectralSpace X := by
  infer_instance

/-- Every affine open of a scheme is quasi-compact. -/
theorem affineOpen_isCompact {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) : IsCompact (U : Set X) := by
  exact hU.isCompact

/- Reducedness properties. -/

/-- An affine scheme with reduced global sections is reduced. -/
theorem scheme_reduced_of_affine_reduced (X : Scheme.{u}) [IsAffine X]
    [_root_.IsReduced Γ(X, ⊤)] : IsReduced X := by
  exact isReduced_of_isAffine_isReduced X

/-- Reducedness of an affine scheme is equivalent to reducedness of its ring. -/
theorem affine_reduced_iff (R : CommRingCat.{u}) :
    IsReduced (Spec R) ↔ _root_.IsReduced R := by
  exact affine_isReduced_iff R

/-- Reducedness can be checked on an open cover. -/
theorem reduced_of_openCover (X : Scheme.{u}) (𝒰 : X.OpenCover)
    [∀ i, IsReduced (𝒰.X i)] : IsReduced X := by
  exact IsReduced.of_openCover X 𝒰

end StacksPart02
