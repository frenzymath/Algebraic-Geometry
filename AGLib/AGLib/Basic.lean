/-
Copyright (c) 2026 Frenzymath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frenzymath
-/
import Mathlib.AlgebraicGeometry.Scheme

/-!
# AGLib basics

Entry module for the unified algebraic geometry library.

## Implementation notes

Declarations promoted here should be source-independent APIs: mathlib-level
generality, stable names, and module docs. Prefer extracting and generalizing
stable material from `FormalizedSources/` and flagship routes over re-proving
it from scratch. Cite the upstream module in the docstring when extracting.
-/

/--
Marker that the AGLib package elaborates against the workspace mathlib pin.

This is a bootstrap placeholder so `lake build AGLib` is green before the first
real extractions land. Replace or delete it once a nontrivial public definition
exists.
-/
def AGLib.bootstrap : True := trivial
