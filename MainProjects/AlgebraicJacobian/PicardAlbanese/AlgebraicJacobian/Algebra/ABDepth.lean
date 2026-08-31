/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Depth and projective dimension of a module

First file of the Auslander–Buchsbaum package `Algebra/AB*.lean` (ported, split
along its section structure, from the sorry-free commutative-algebra layer of the
old in-tree Albanese draft; every file is re-kernel-verified in this tree).

* `RingTheory.Module.depth` — the `I`-depth of an `R`-module `M`: the supremum in
  `ℕ∞` of lengths of `M`-regular sequences contained in `I`, with the convention
  `depth = ⊤` when `I • M = M` (Stacks tag 00LI).
* `Module.projectiveDimension` — the projective dimension of an `R`-module,
  re-exporting the categorical `CategoryTheory.projectiveDimension` of
  `ModuleCat.of R M`.

Mathlib at the project's pin has `IsRegularLocalRing`, the categorical
`CategoryTheory.projectiveDimension`, and the regular-sequence predicate
`RingTheory.Sequence.IsRegular`, but not the numeric depth function — that is the
gap `RingTheory.Module.depth` fills.

The package continues with the Ext-index characterisation of depth
(`ABDepthExt`), the short-exact-sequence depth calculus (`ABDepthSES`), the
syzygy substrate (`ABSyzygy`), the Auslander–Buchsbaum formula (`ABFormula`), and
the Cohen–Macaulay / regular-local chapter (`ABRegularQuotient`,
`ABRegularDomain`, `ABRegularCM`).

## References

Stacks Project tags 00LI (definition-depth), 00LW (lemma-depth-ext), 00LX
(lemma-depth-in-ses), 090V (proposition-Auslander–Buchsbaum), 00N8
(definition-local-ring-CM), 00NQ (lemma-regular-ring-CM), 00NP
(lemma-regular-domain). Matsumura, *Commutative Ring Theory*, Theorem 19.1.
Auslander–Buchsbaum, "Homological dimension in local rings", 1957.
-/

set_option autoImplicit false

universe u v

open CategoryTheory

namespace RingTheory

namespace Module

/-! ## Depth of a module

The `I`-depth of an `R`-module `M` is the supremum in `{0, 1, 2, …, ∞}` of the
lengths of `M`-regular sequences contained in `I` (provided `IM ≠ M`; if
`IM = M` we set `depth_I(M) = ∞`). Mathlib at the pin exposes the
regular-sequence predicate `RingTheory.Sequence.IsRegular`
(`Mathlib.RingTheory.Regular.RegularSequence`) but not the resulting numeric
depth function — that is the gap this declaration fills (Stacks tag 00LI). -/

/-- The **`I`-depth** of an `R`-module `M`: the supremum (in `ℕ∞`) of lengths of
`M`-regular sequences contained in the ideal `I`.

When `IM = M` (the "trivial-quotient" case, e.g. `M = 0` or `I = R`) the
supremum is taken to be `⊤` by convention. When `(R, 𝔪)` is local one usually
calls `depth (IsLocalRing.maximalIdeal R) M` simply *the depth* of `M`
(Stacks tag 00LI). 






 * Provenance: REFERENCE.
-/
noncomputable def depth {R : Type u} [CommRing R] (_I : Ideal R)
    (_M : Type v) [AddCommGroup _M] [Module R _M] : ℕ∞ :=
  open Classical in
  if _I • (⊤ : Submodule R _M) = ⊤ then (⊤ : ℕ∞)
  else sSup { n : ℕ∞ | ∃ rs : List R, (rs.length : ℕ∞) = n ∧
    (∀ r ∈ rs, r ∈ _I) ∧ RingTheory.Sequence.IsRegular _M rs }

end Module

end RingTheory

/-! ## Projective dimension

Mathlib at the pin exposes the categorical
`CategoryTheory.projectiveDimension : C → WithBot ℕ∞` on an abelian category
with enough projectives (`Mathlib.CategoryTheory.Abelian.Projective.Dimension`).
For `R`-modules this specialises to `ModuleCat.of R M`; downstream consumers use
the wrapper `Module.projectiveDimension` directly on an `R`-module without
threading `ModuleCat.of`. -/

namespace Module

/-- The **projective dimension** of an `R`-module `M`, defined as the
categorical projective dimension of `ModuleCat.of R M`.

The categorical definition is the infimum (in `WithBot ℕ∞`) of `n : ℕ` such
that all `Ext^i(M, -)` vanish for `i > n`, equivalently the smallest length of
a projective resolution of `M`. 






 * Provenance: CUSTOM.
-/
noncomputable def projectiveDimension (R : Type u) [Ring R]
    (_M : Type u) [AddCommGroup _M] [Module R _M] : WithBot ℕ∞ :=
  CategoryTheory.projectiveDimension (ModuleCat.of R _M)

end Module
