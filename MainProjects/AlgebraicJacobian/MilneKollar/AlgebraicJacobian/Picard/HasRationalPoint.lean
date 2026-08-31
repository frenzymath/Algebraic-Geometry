/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Rational points of schemes over fields

This module isolates the lightweight predicate that a scheme over a field has a
section. Keeping it below the Picard representability development lets geometric
base-change modules use the predicate without importing the FGA seam.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **`C` has a `k`-rational point**: the structural morphism `C.hom` admits a
section `sigma : Spec k ⟶ C.left`. For the smooth proper geometrically integral
curves of this project this is the pointing already threaded through the
Albanese statements.

This is a predicate only. In particular, this module provides no instance that
would manufacture a rational point for an arbitrary curve. -/
class HasRationalPoint {k : Type u} [Field k] (C : Over (Spec (.of k))) : Prop where
  nonempty_section :
    Nonempty {sigma : Spec (.of k) ⟶ C.left // sigma ≫ C.hom = 𝟙 (Spec (.of k))}

end AlgebraicGeometry.Scheme
