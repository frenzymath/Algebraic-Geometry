/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2LineBundles

/-!
# Pullback transport for line bundles

The pullback functor sends module isomorphisms to module isomorphisms.  This
small API packages the resulting invariance of the local-triviality predicate,
and provides the common use case where a line bundle is replaced by an
isomorphic module before pulling back.
-/

set_option autoImplicit false

open CategoryTheory

namespace Hartshorne

universe u

open AlgebraicGeometry

/-- Pullback preserves the line-bundle property across an isomorphism of
scheme modules on the target. -/
theorem isLineBundle_pullback_iff_of_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (e : M ≅ N) :
    IsLineBundle ((Scheme.Modules.pullback f).obj M) ↔
      IsLineBundle ((Scheme.Modules.pullback f).obj N) := by
  exact isLineBundle_iff_of_iso ((Scheme.Modules.pullback f).mapIso e)

/-- Pulling back an isomorphic replacement of a line bundle again gives a
line bundle. -/
theorem IsLineBundle.pullback_of_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (hM : IsLineBundle M) (e : M ≅ N) :
    IsLineBundle ((Scheme.Modules.pullback f).obj N) := by
  exact (hM.pullback f).of_iso ((Scheme.Modules.pullback f).mapIso e)

end Hartshorne
