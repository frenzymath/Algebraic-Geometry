/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.WeilDivisor

/-!
# Producing prime divisors from non-generic points, at any import level

`WeilDivisor.lean` records that the divisor index-set comparison splits into a *consuming*
direction (`PrimeDivisor.point_ne_genericPoint`, elementary, proved there) and a *producing*
direction (non-generic ⟹ `coheight = 1`), whose substantive half `coheight ≤ 1` is
`Adelic.coheight_le_one_of_curve` and lives strictly **downstream**.  So a consumer at
`WeilDivisor` level cannot produce prime divisors, and the concurrently-running `ajc-pic0av`
lane reported exactly that as the block on its χ-ledger port (AJC team thread `I-0493`).

**What this file does, and what it deliberately does not do.**  It does not re-prove
`coheight ≤ 1`: that rests on a ~180-line standard-smooth/Kähler-differential argument in
`Adelic/FiniteMapToP1.lean`, and duplicating it upstream would be worse than the problem.
Instead it takes the bound as an explicit **hypothesis** and packages everything else, so the
producer is available at *every* import level and the geometric input can be discharged wherever
it happens to be in scope:

* `Scheme.PrimeDivisor.ofNonGeneric` — from `Order.coheight z ≤ 1` and `z ≠ genericPoint X`,
  build the `PrimeDivisor`.  Its `coheight = 1` field is `le_antisymm` of the hypothesis and the
  elementary `one_le_coheight_of_ne_genericPoint` already in `WeilDivisor.lean`.
* `Scheme.PrimeDivisor.equivNonGeneric` — the resulting **equivalence of index sets**
  `X.PrimeDivisor ≃ {x // x ≠ genericPoint X}`, given the coheight bound at every point.  This
  is the sibling project's `CurveDivisor` index set, so this is the first of the two carrier
  mismatches `WeilDivisor.lean:1304-1311` lists as the cost of porting the sorry-free χ-ledger.

The hypothesis form is the honest one here rather than a workaround: `coheight ≤ 1` is a genuine
curve hypothesis (it fails on any space of dimension `> 1`), so a producer that *assumes* it is
not weaker than one that proves it for a specific curve — it is the same content, reusable, and
it inverts no imports.  A consumer with `Adelic` in scope discharges it with
`Adelic.coheight_le_one_of_curve`; one without can carry it as a binder.

## Provenance

Rederived in AJC's own abstractions; nothing is ported.  The mathematics is the two-line
`le_antisymm` that `WeilDivisor.lean` describes but cannot state at its own import level, plus
the `Equiv` packaging.  Requested by `ajc-pic0av`; landed in `ajc-rr`'s file scope because
`WeilDivisor.lean` belongs to that lane and must not be edited here.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.PrimeDivisor

variable {X : Scheme.{u}} [IrreducibleSpace X]

/-- **The producing direction of the index-set comparison.**  A non-generic point whose coheight
is at most one *is* a prime divisor.

The coheight bound is the curve hypothesis, taken here as an argument rather than proved: see
the module docstring.  With `Adelic` in scope, discharge it by
`Adelic.coheight_le_one_of_curve C z`. -/
def ofNonGeneric {z : X} (hz : z ≠ genericPoint X) (hle : Order.coheight z ≤ 1) :
    X.PrimeDivisor where
  point := z
  coheight := le_antisymm hle (Scheme.one_le_coheight_of_ne_genericPoint hz)

@[simp] theorem ofNonGeneric_point {z : X} (hz : z ≠ genericPoint X)
    (hle : Order.coheight z ≤ 1) : (ofNonGeneric hz hle).point = z := rfl

/-- **`ofNonGeneric` and `point_ne_genericPoint` are mutually inverse**, so on a space whose
points all have coheight `≤ 1` the two divisor index sets agree:

`X.PrimeDivisor ≃ {x : X // x ≠ genericPoint X}`.

The right-hand side is the index set of the sibling project's `CurveDivisor`
(`Algebraic-Jacobian-Challenge-Rebuild`, `RiemannRoch/Divisor.lean`), whose χ-ledger proves
degree-zero-of-principal sorry-free.  This equivalence is the first of the two carrier
mismatches that `WeilDivisor.lean` lists as the cost of that port; the second is the residue-degree
weighting of `deg`, which over an algebraically closed field is discharged by
`Adelic.residueDeg_eq_one_of_isAlgClosed_curve`.

Injectivity of `point` is `PrimeDivisor.ext`; surjectivity onto the non-generic points is
`ofNonGeneric`. -/
def equivNonGeneric (hdim : ∀ z : X, Order.coheight z ≤ 1) :
    X.PrimeDivisor ≃ {x : X // x ≠ genericPoint X} where
  toFun Y := ⟨Y.point, Y.point_ne_genericPoint⟩
  invFun x := ofNonGeneric x.2 (hdim x.1)
  left_inv _ := PrimeDivisor.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem equivNonGeneric_apply_coe (hdim : ∀ z : X, Order.coheight z ≤ 1)
    (Y : X.PrimeDivisor) : ((equivNonGeneric hdim) Y : X) = Y.point := rfl

@[simp] theorem equivNonGeneric_symm_point (hdim : ∀ z : X, Order.coheight z ≤ 1)
    (x : {x : X // x ≠ genericPoint X}) :
    ((equivNonGeneric hdim).symm x).point = (x : X) := rfl

end Scheme.PrimeDivisor

end AlgebraicGeometry
