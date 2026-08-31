/-
Copyright (c) 2026 The StacksPart02Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart02Lib Contributors
-/

import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affine open covers

The scheme-level affine opens form a topological basis and cover the whole
underlying space.  These wrappers expose the corresponding Mathlib facts under
the namespace used by the Stacks Part 02 development.
-/

namespace StacksPart02

open AlgebraicGeometry TopologicalSpace

universe u

/-- Affine opens form a basis for the topology of a scheme. -/
theorem scheme_affine_opens_is_basis (X : Scheme.{u}) :
    Opens.IsBasis X.affineOpens := by
  exact Scheme.isBasis_affineOpens X

/-- The affine opens cover the underlying space of a scheme. -/
theorem scheme_affine_opens_iSup_eq_top (X : Scheme.{u}) :
    ⨆ i : X.affineOpens, (i : X.Opens) = ⊤ := by
  exact AlgebraicGeometry.iSup_affineOpens_eq_top X

/-- A standard open in an affine scheme is affine (Stacks, Tag 01I3). -/
theorem scheme_standardOpen_isAffineOpen
    (X : Scheme.{u}) [IsAffine X] (f : Γ(X, ⊤)) :
    IsAffineOpen (X.basicOpen f) := by
  exact (isAffineOpen_top X).basicOpen f

/- A standard open of an affine scheme is affine (Stacks, Tag 01I3). -/
theorem scheme_standardOpen_isAffine
    (X : Scheme.{u}) [IsAffine X] (f : Γ(X, ⊤)) :
    IsAffine (X.basicOpen f) := by
  infer_instance

/-- Two affine opens have a common affine standard-open neighbourhood
(Stacks, Tag 01IW). -/
theorem scheme_standardOpen_two_affines
    (X : Scheme.{u}) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (x : X) (hx : x ∈ U ⊓ V) :
    ∃ (f : Γ(X, U)) (g : Γ(X, V)),
      X.basicOpen f = X.basicOpen g ∧
        x ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f) := by
  obtain ⟨f, g, hfg, hxf⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter hU hV x hx
  exact ⟨f, g, hfg, hxf, hU.basicOpen f⟩

end StacksPart02
