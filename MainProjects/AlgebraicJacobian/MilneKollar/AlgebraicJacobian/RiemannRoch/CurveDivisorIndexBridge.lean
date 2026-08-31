/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.CurveCoheight

/-!
# The divisor-level index bridge to the sibling χ-ledger (AJC.rr.principal)

`RiemannRoch/CurveCoheight.lean` (ajc-rr) compares the two *point* index sets used for
divisors on a curve:

```
X.PrimeDivisor  ≃  {x : X // x ≠ genericPoint X}
```

the right-hand side being the index set of the sibling project's `CurveDivisor`
(`Algebraic-Jacobian-Challenge-Rebuild`, `RiemannRoch/Divisor.lean`), whose χ-ledger proves
`deg (div g) = 0` sorry-free. This file lifts that comparison from points to **divisors and
their degree**, which is the form the open leaf
`Scheme.WeilDivisor.principal_degree_zero` consumes:

* `Scheme.WeilDivisor.addEquivNonGeneric` — `Div(X) ≃+ ({x // x ≠ η} →₀ ℤ)`, additively;
* `Scheme.WeilDivisor.degree_eq_sum_nonGeneric` — degree is the coefficient sum on **either**
  index set, so the transport does not move degrees.

## What this is and is not

This is the *first* of the two carrier mismatches that `WeilDivisor.lean` lists as the cost of
porting the sibling's χ-ledger conclusion. It is now closed, and the transport is additive, so
it carries the degree homomorphism rather than only the underlying sets.

It is **not** the port. The remaining mismatch is the residue-degree weighting of the
sibling's `deg` (discharged over `k̄` by `Adelic.residueDeg_eq_one_of_isAlgClosed_curve`, which
sits downstream of `WeilDivisor.lean` — see the discussion at `principal_degree_zero`), and the
χ-machinery itself still has to arrive. ajc-rr's staging audit (inbox I-0495, 2026-07-28)
measured that port as near-mechanical: 22 cone files compile against AJC dependencies with
byte-identical bodies.

The coheight bound `∀ z, coheight z ≤ 1` is carried as a hypothesis exactly as in
`CurveCoheight.lean`, and for the same reason: it *is* the curve hypothesis, so assuming it
loses nothing, while proving it bottoms out in standard-smooth material that sits downstream
of this file. Discharge it with `Adelic.coheight_le_one_of_curve` where that is in scope.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme.WeilDivisor

variable {X : Scheme.{u}} [IrreducibleSpace X]

/-- **The divisor-level index comparison, additively.** `Finsupp.domCongr` of ajc-rr's
point-level `PrimeDivisor.equivNonGeneric`; additive because relabelling the index set of a
finitely-supported function commutes with pointwise addition.

Additivity is what makes this usable for a *degree* statement: `degree` is an
`AddMonoidHom` (`degree_hom`), and a bare `Equiv` of divisor groups would not respect it. -/
noncomputable def addEquivNonGeneric (hdim : ∀ z : X, Order.coheight z ≤ 1) :
    X.WeilDivisor ≃+ ({x : X // x ≠ genericPoint X} →₀ ℤ) :=
  Finsupp.domCongr (Scheme.PrimeDivisor.equivNonGeneric hdim)

/-- **Degree is the coefficient sum on either index set** — the transport moves no degrees.

`degree` sums the bare coefficients (`Σ_Y D Y`), and relabelling along a bijection leaves a
finite sum unchanged (`Finsupp.sum_mapDomain_index`, whose two side conditions are `rfl` here
because the summand `fun _ n => n` ignores the index). So the sibling's degree-zero conclusion
transports along `addEquivNonGeneric` without a correction term.

This is the statement that makes the index mismatch *closed* rather than merely stated: an
index equivalence that did not respect degree would not help the leaf. -/
theorem degree_eq_sum_nonGeneric (hdim : ∀ z : X, Order.coheight z ≤ 1)
    (D : X.WeilDivisor) :
    degree D = (addEquivNonGeneric hdim D).sum (fun _ n => n) := by
  change (D : X.PrimeDivisor →₀ ℤ).sum (fun _ n => n)
    = (Finsupp.equivMapDomain (Scheme.PrimeDivisor.equivNonGeneric hdim)
        (D : X.PrimeDivisor →₀ ℤ)).sum (fun _ n => n)
  rw [Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

/-- The transported form of the degree-zero conclusion: a divisor whose relabelled
coefficient sum vanishes has degree zero. The shape in which the sibling's `deg_divOf` will be
consumed once its χ-machinery is ported. -/
theorem degree_eq_zero_of_sum_nonGeneric_eq_zero (hdim : ∀ z : X, Order.coheight z ≤ 1)
    {D : X.WeilDivisor}
    (h : (addEquivNonGeneric hdim D).sum (fun _ n => n) = 0) :
    degree D = 0 :=
  (degree_eq_sum_nonGeneric hdim D).trans h

end Scheme.WeilDivisor

end AlgebraicGeometry
