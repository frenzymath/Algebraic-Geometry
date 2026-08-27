/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.OrdCompare
import AlgebraicJacobian.RiemannRoch.WeilDivisor

/-!
# The two projects' principal divisors have the same coefficients

The ported ledger's principal divisor is `Scheme.divOf` (`Ledger/PrincipalDivisor.lean`), whose
coefficient at a closed point is `Multiplicative.toAdd (Scheme.ordZ f hx g)`, built from the
adic valuation of the maximal ideal of the DVR stalk.  This project's own principal divisor is
`Scheme.WeilDivisor.principal` (`RiemannRoch/WeilDivisor.lean`), whose coefficient at a prime
divisor is `Scheme.RationalMap.order`, built from mathlib's `Ring.ordFrac` on the same stalk.

Those are *different constructions of the same integer*, and until now the identification was
unproved — it is the second of the two gaps this lane reported against reading `deg_divOf` as
`principal_degree_zero` (the first, the residue weighting, is
`Ledger/ResidueOneAlgClosed.lean`).  This file closes it:

* `Scheme.ordZ_toAdd_eq_log_ordFrac` — the coefficient identity at a point;
* `Scheme.divOf_apply_eq_rationalMap_order` — the same, stated against
  `Scheme.RationalMap.order` as `WeilDivisor.principal` uses it.

## The proof, and why it is short

Both sides bottom out in the *same* valuation, which is not obvious from the definitions:

1. `Scheme.ord f hx` is by construction the adic valuation of `stalkHeightOne X x`, the maximal
   ideal of the stalk viewed as a height-one prime (`Scheme.ord_eq_valuation`, `rfl`).
2. `stalkHeightOne X x` is *definitionally* `IsDiscreteValuationRing.maximalIdeal` of that stalk
   — checked by `rfl`, so no transport is needed.
3. Mathlib's `Ring.ordFrac_eq_valuation_inv` says `ordFrac R = (valuation K _)⁻¹` on a DVR.  So
   `ordFrac` is the *inverse* of the valuation, and `ordZ` is the valuation composed with
   `invMonoidHom` — the same inversion, on the other side of the units equivalence.
4. `WithZero.log` of a coerced unit is `Multiplicative.toAdd`, which turns (3) into the claim.

The sign conventions therefore agree with no correction term: both are `+1` at a simple zero.
That is worth stating explicitly, because a sign error here would be invisible in any
degree-zero statement (`0 = -0`) and would corrupt every non-principal use.

## Provenance

AJC-native rederivation.  Neither project had this comparison: the ledger side is a port from
`Algebraic-Jacobian-Challenge-Rebuild`, which has no `WeilDivisor.principal` to compare against,
and this project's `WeilDivisor.lean` records the comparison as an unmeasured cost.  The
load-bearing input is mathlib's `Ring.ordFrac_eq_valuation_inv`
(`Mathlib/RingTheory/OrderOfVanishing/Noetherian.lean`), which neither project had used.

## What is still not closed

This identifies **coefficients at a point**.  It is not yet the divisor-level statement
`divOf f g = principal (g : K(X)) _` transported along
`RiemannRoch/CurveDivisorIndexBridge.addEquivNonGeneric`, because the two divisors are indexed
by `{x // x ≠ η}` and `X.PrimeDivisor` respectively and `WeilDivisor.lean` is not this lane's
file to edit.  With this lemma that transport is `Finsupp.ext` along the index equivalence plus
the coefficient identity below; the remaining work is bookkeeping, not mathematics.  See the
AJC thread (inbox `I-0493`) — `ajc-pic0av` owns that file and the `AJC.rr.principal` milestone.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-! The coefficient identity itself now lives in `Ledger/OrdCompare.lean`, which does **not**
import `WeilDivisor.lean` — see that file's docstring for why the split matters (an import
inversion blocks substituting a downstream theorem into an upstream `sorry`).  Re-exported here
under its `RationalMap.order` spelling for consumers already downstream. -/

/-- **The ledger's principal divisor has this project's coefficients** (★): at a prime divisor
`Y` of the curve, the coefficient of `Scheme.divOf f g` at `Y.point` is
`Scheme.RationalMap.order Y g` — the coefficient `Scheme.WeilDivisor.principal` uses.

This is `ordZ_toAdd_eq_log_ordFrac` with the right-hand side folded back into
`RationalMap.order`, which is by definition `WithZero.log (Ring.ordFrac _ _)`. -/
theorem Scheme.divOf_apply_eq_rationalMap_order (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] [IsLocallyNoetherian X]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (g : X.functionFieldˣ) (Y : X.PrimeDivisor) (hY : Y.point ≠ genericPoint X)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)] :
    @DFunLike.coe ({x : X // x ≠ genericPoint X} →₀ ℤ) _ _ _ (Scheme.divOf f g) ⟨Y.point, hY⟩
      = Scheme.RationalMap.order Y (g : X.functionField) := by
  rw [Scheme.divOf_apply f g hY]
  exact Scheme.ordZ_toAdd_eq_log_ordFrac f g hY

end AlgebraicGeometry
