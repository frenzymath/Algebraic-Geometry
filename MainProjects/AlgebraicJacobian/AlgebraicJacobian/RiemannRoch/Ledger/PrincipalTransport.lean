/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.PrincipalCompare
import AlgebraicJacobian.RiemannRoch.Ledger.ResidueOneAlgClosed
import AlgebraicJacobian.RiemannRoch.CurveDivisorIndexBridge

/-!
# The two principal divisors are equal, and the degree-zero statement that follows

`Ledger/PrincipalCompare.lean` identified the *coefficients* of the ported `Scheme.divOf` with
those of this project's `Scheme.WeilDivisor.principal`.  This file finishes the transport:

* `Scheme.WeilDivisor.addEquivNonGeneric_principal` (★) — the two principal divisors are
  **equal as divisors**, once `principal` is relabelled along the index-set equivalence of
  `RiemannRoch/CurveDivisorIndexBridge.lean`;
* `Scheme.WeilDivisor.degree_principal_eq_deg` — hence `degree (principal g)` is the ledger's
  weighted `deg (divOf g)` read as a bare coefficient sum;
* `Scheme.WeilDivisor.degree_principal_eq_zero_of_isAlgClosed` (★) — hence **`degree` of a
  principal divisor vanishes** over an algebraically closed base field.

The last statement is `Scheme.WeilDivisor.principal_degree_zero` (`RiemannRoch/WeilDivisor.lean`,
milestone `AJC.rr.principal`) restricted to `k = k̄`.  It is stated here, in this lane's own
path, rather than in `WeilDivisor.lean`, which belongs to another lane; whoever owns that file
can discharge the leaf from this or reprove it in place.

## The three carrier mismatches, and where each was closed

`WeilDivisor.lean` listed the cost of importing the sibling project's degree-zero conclusion.
All three pieces now exist:

| mismatch | closed by |
|---|---|
| index set `PrimeDivisor` vs `{x ≠ η}` | `CurveDivisorIndexBridge.addEquivNonGeneric` |
| residue weighting `Σ nₓ[κ(x):k]` vs `Σ nₓ` | `ResidueOneAlgClosed` (needs `k = k̄`) |
| `ordZ` vs `RationalMap.order` | `Ledger/PrincipalCompare.ordZ_toAdd_eq_log_ordFrac` |

and the χ-machinery they were the cost *of* is `Ledger/ChiLedger.deg_divOf`, unconditional at a
curve by `Ledger/ChiCurve`.

## Scope, stated plainly

`[IsAlgClosed k]` is load-bearing in the degree-zero corollary and is **not** removable by
better bookkeeping: over a general field the ledger proves the *weighted* degree vanishes, and
the unweighted degree of a principal divisor is then a different number.  The general-field
statement therefore remains open, and the honest reading of this file is "the k̄ case of
`AJC.rr.principal`, with the weighted case available over any field".

`degree_principal_eq_deg` is the general-field content: it holds with no `IsAlgClosed`, and says
the two projects compute the same divisor.  Only the final vanishing needs `k̄`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.WeilDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
  [IsNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
  [Scheme.IsRegularInCodimensionOne X] [IrreducibleSpace X]

/-- **The two projects' principal divisors are the same divisor** (★): relabelling
`Scheme.WeilDivisor.principal` along the index equivalence gives the ported `Scheme.divOf`.

`Finsupp.ext` reduces to the coefficient identity `PrincipalCompare.ordZ_toAdd_eq_log_ordFrac`;
the `Ring.KrullDimLE 1` instance that `RationalMap.order` needs at the point is supplied by
routing through `PrimeDivisor.ofNonGeneric`, which is where the coheight hypothesis is used.

No `IsAlgClosed` here: this holds over any base field. -/
theorem addEquivNonGeneric_principal (hdim : ∀ z : X, Order.coheight z ≤ 1)
    (g : X.functionFieldˣ) (hg : (g : X.functionField) ≠ 0) :
    addEquivNonGeneric hdim (principal (g : X.functionField) hg)
      = Scheme.divOf (X ↘ Spec (CommRingCat.of k)) g := by
  ext y
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk (y : X)) :=
    Scheme.IsRegularInCodimensionOne.instKrullDimLEStalk
      (Scheme.PrimeDivisor.ofNonGeneric y.2 (hdim _))
  rw [Scheme.divOf_apply _ g y.2]
  change (Finsupp.equivMapDomain (Scheme.PrimeDivisor.equivNonGeneric hdim)
      (principal (g : X.functionField) hg : X.PrimeDivisor →₀ ℤ)) y = _
  rw [Finsupp.equivMapDomain_apply, principal_apply]
  exact (Scheme.ordZ_toAdd_eq_log_ordFrac _ g y.2).symm

/-- **The degree of a principal divisor is the ledger's coefficient sum**, over any base field.

`degree` sums bare coefficients on `PrimeDivisor`; `degree_eq_sum_nonGeneric` moves that to the
relabelled index set without changing it; and `addEquivNonGeneric_principal` identifies the
relabelled divisor with `divOf`.  So the ledger's divisor and this project's carry the same
degree, with no `IsAlgClosed` assumption — the residue weighting has not entered yet. -/
theorem degree_principal_eq_deg (hdim : ∀ z : X, Order.coheight z ≤ 1)
    (g : X.functionFieldˣ) (hg : (g : X.functionField) ≠ 0) :
    degree (principal (g : X.functionField) hg)
      = (Scheme.divOf (X ↘ Spec (CommRingCat.of k)) g).sum (fun _ n => n) := by
  rw [degree_eq_sum_nonGeneric hdim, addEquivNonGeneric_principal (k := k) hdim g hg]

/-- **Principal divisors have degree zero over an algebraically closed base field** (★).

This is `Scheme.WeilDivisor.principal_degree_zero` (`RiemannRoch/WeilDivisor.lean`, milestone
`AJC.rr.principal`) in the case `k = k̄`.  The chain: the ported χ-ledger gives
`deg (divOf g) = 0` for the *residue-weighted* degree (`Ledger/ChiLedger.deg_divOf`, whose two
finiteness binders are discharged at a curve by `Ledger/ChiCurve`);
`Ledger/ResidueOneAlgClosed` collapses that weighting to a bare coefficient sum over `k̄`; and
`degree_principal_eq_deg` transports it onto `degree`.

`[IsAlgClosed k]` is load-bearing and not bookkeeping: see the module docstring. -/
theorem degree_principal_eq_zero_of_isAlgClosed [IsAlgClosed k]
    [Module.Finite k (Sheaf.HModule (X.moduleKSheaf k) 0)]
    [Module.Finite k (Sheaf.HModule (X.moduleKSheaf k) 1)]
    (hdim : ∀ z : X, Order.coheight z ≤ 1)
    (g : X.functionFieldˣ) (hg : (g : X.functionField) ≠ 0) :
    degree (principal (g : X.functionField) hg) = 0 := by
  rw [degree_principal_eq_deg (k := k) hdim g hg,
    ← Scheme.CurveDivisor.deg_eq_sum_of_isAlgClosed (K := k)]
  exact deg_divOf k g

end Scheme.WeilDivisor

/-! ## The bundled-curve form, with the finiteness binders discharged -/

/-- **Principal divisors have degree zero on a curve over `k̄`** — the bundled form, and the
one to quote.

`degree_principal_eq_zero_of_isAlgClosed` still *carries* the two `Module.Finite` cohomology
binders, because it is stated for a bare scheme over `Spec k` rather than for the bundled curve
that discharges them.  Here they are discharged, from `moduleFinite_hModule_zero` and
`moduleFinite_hModule_one` (`Ledger/ChiCurve`, `Ledger/Finiteness`), so the hypotheses are:
properness, smoothness of relative dimension one, geometric irreducibility, Noetherianness,
regularity in codimension one, the coheight bound, and `k = k̄`.

That is `Scheme.WeilDivisor.principal_degree_zero` (milestone `AJC.rr.principal`) over an
algebraically closed field.  The `[IsAlgClosed k]` binder is the only gap to the general
statement, and it is a genuine one — see `Ledger/ResidueOneAlgClosed`. -/
theorem degree_principal_eq_zero_curve {k : Type u} [Field k] [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left] [IrreducibleSpace C.left]
    (hdim : ∀ z : C.left, Order.coheight z ≤ 1)
    (g : C.left.functionFieldˣ) (hg : (g : C.left.functionField) ≠ 0) :
    Scheme.WeilDivisor.degree
      (Scheme.WeilDivisor.principal (g : C.left.functionField) hg) = 0 := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  exact Scheme.WeilDivisor.degree_principal_eq_zero_of_isAlgClosed (k := k) hdim g hg

end AlgebraicGeometry
