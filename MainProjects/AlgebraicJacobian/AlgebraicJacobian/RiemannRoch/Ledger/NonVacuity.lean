/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.GenusBridge
import AlgebraicJacobian.RiemannRoch.Ledger.ResidueOneAlgClosed
import AlgebraicJacobian.Picard.RigidPushforwardP1Witness

/-!
# The ported ledger is not vacuous: it fires at `ℙ¹_k`

Every headline of `Ledger/` quantifies over a curve bundle `C : Over (Spec (.of k))` with
`[IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]`, and
the two `Module.Finite` cohomology binders of the conditional ledger are discharged from those
three by instance synthesis.  A clean `#print axioms` line says nothing about whether *any*
object satisfies the three, and this workspace has twice shipped results whose binders turned
out to be unsatisfiable at a curve (`Adelic/ChartFinitenessRefuted.lean`, inbox `I-0534`,
`I-0563`).  So the acceptance test belongs next to the results, in Lean.

`Adelic.p1Over k` — this project's own `ℙ¹_k` — satisfies all three
(`Adelic.isProper_p1Over_hom`, `instSmoothOfRelativeDimensionOneP1Over`, and geometric
integrality from `Picard/RigidPushforwardP1Constants.lean`), and it is not a fresh construction:
`Picard/RigidPushforwardP1Witness.lean` already uses it as the non-vacuity witness for the
rigid-pushforward gate.

`chi_divisorSheaf_p1Over` below is the Riemann–Roch identity of `Ledger/GenusBridge.lean`
*elaborated at that object*, with no `Module.Finite`, no gate, and no abstract binder on the
right-hand side: every hypothesis is found.  Its `#print axioms` is
`[propext, Classical.choice, Quot.sound]`.

## What this does and does not establish

It establishes that the ledger's hypothesis bundle is **inhabited by a real curve of this
project**, so the statements have content and the synthesis path from the three geometric
binders to the two finiteness instances actually runs.

It does *not* establish that the ledger is interesting at `ℙ¹` specifically — genus zero is the
degenerate case, and a result that were *only* true there would still pass this test.  The test
rules out emptiness, not weakness.  What rules out weakness is that the binders here are the
same three the challenge's `genus` and `Jacobian` carry, so any curve those speak about is also
a curve the ledger speaks about.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **The ledger's Riemann–Roch identity at `ℙ¹_k`** — the non-vacuity probe.

Stated at `Adelic.p1Over k`, a concrete object of this project, with *no* finiteness hypothesis
and no abstract curve binder: `IsProper`, `SmoothOfRelativeDimension 1`,
`GeometricallyIrreducible`, and both `Module.Finite` cohomology instances are all synthesised
here.  So `chi_divisorSheaf_genus` is a statement with content, not a theorem about an empty
class of objects. -/
theorem chi_divisorSheaf_p1Over (k : Type u) [Field k]
    (D : (Adelic.p1Over k).left.CurveDivisor) :
    letI : (Adelic.p1Over k).left.Over (Spec (CommRingCat.of k)) :=
      .ofHom (Adelic.p1Over k).hom
    haveI : SmoothOfRelativeDimension 1
        ((Adelic.p1Over k).left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Adelic.p1Over k).hom)
    Sheaf.chi ((Adelic.p1Over k).left.divisorSheaf k D)
      = 1 - genus (Adelic.p1Over k) + Scheme.CurveDivisor.deg k D :=
  chi_divisorSheaf_genus (Adelic.p1Over k) D

/-- **The Riemann inequality at `ℙ¹_k`**, same discharge, same reason for existing. -/
theorem riemann_inequality_p1Over (k : Type u) [Field k]
    (D : (Adelic.p1Over k).left.CurveDivisor) :
    letI : (Adelic.p1Over k).left.Over (Spec (CommRingCat.of k)) :=
      .ofHom (Adelic.p1Over k).hom
    haveI : SmoothOfRelativeDimension 1
        ((Adelic.p1Over k).left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Adelic.p1Over k).hom)
    Scheme.CurveDivisor.deg k D + 1 - genus (Adelic.p1Over k)
      ≤ (Sheaf.h0 ((Adelic.p1Over k).left.divisorSheaf k D) : ℤ) :=
  riemann_inequality_genus (Adelic.p1Over k) D

/-- **`H¹(ℙ¹_k, 𝒪)` is finite-dimensional**, on this project's own `Scheme.HModule` carrier —
so `genus (p1Over k)` is the dimension of an honestly finite-dimensional space rather than a
`finrank` defaulting to zero.  Without this the two theorems above would be satisfied by
`genus = 0` for a reason having nothing to do with `ℙ¹` being rational. -/
theorem moduleFinite_genus_carrier_p1Over (k : Type u) [Field k] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf (Adelic.p1Over k)) 1) :=
  moduleFinite_genus_carrier (Adelic.p1Over k)

end AlgebraicGeometry
