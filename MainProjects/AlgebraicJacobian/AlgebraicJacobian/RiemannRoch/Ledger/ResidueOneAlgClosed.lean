/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.ChiCurve

/-!
# The residue weighting collapses over an algebraically closed base field

The ported χ-ledger measures divisors with the **residue-weighted** degree
`deg D = ∑ₓ Dₓ · [κ(x) : K]` (`Ledger/Divisor.lean`), while
`AlgebraicGeometry.Scheme.WeilDivisor.degree` is the **bare coefficient sum** `∑ₓ Dₓ`.
`RiemannRoch/CurveDivisorIndexBridge.lean` closed the *index* half of that mismatch
(`addEquivNonGeneric`, additively and degree-preservingly); the *weighting* half was left open,
and it is what stops `deg_divOf` from being read as `principal_degree_zero`.

This file supplies the weighting half over an algebraically closed base field, which is the
regime the two are ever claimed to agree in:

* `Scheme.residueDeg_eq_one_of_isAlgClosed` (★) — `[κ(x) : K] = 1` at every non-generic point
  of a curve over an algebraically closed `K`;
* `Scheme.CurveDivisor.deg_eq_sum_of_isAlgClosed` — hence `deg D = ∑ₓ Dₓ`, the weighting is a
  no-op;
* `Scheme.CurveDivisor.sum_divOf_eq_zero_of_isAlgClosed` — hence principal divisors have
  **unweighted** degree zero.

## Provenance, and why this is not a port

The statement is one the sibling project `Algebraic-Jacobian-Challenge-Rebuild` does **not**
have: searching its `RiemannRoch/` finds `residueDeg _ _ = 1` only ever as a *hypothesis*
(`CoverageDrop.lean:143` `hdx`, `:218` `hPdeg`, `GraphSectionEval`, `SepPointsDense`), never as
a conclusion, so there is no producer to port.  This project's *adelic* lane has an analogous
result (`Adelic/ResidueField.residueDeg_eq_one_of_isAlgClosed_curve`), but for a **different**
`residueDeg`: that one is `finrank k (localStepTgt k P 1)`, a subquotient of the function field
cut out by valuations, whereas the ledger's is `finrank K (X.residueField x)` on mathlib's
residue field.  The two definitions are not interchangeable without a comparison nobody has
built, so this is a rederivation in the ledger's own vocabulary, not a reuse.

The argument itself is three steps and needs no geometry beyond what
`Scheme.residueDeg_finite` already provides: `κ(x)` is a finite `K`-module, a finite algebra is
integral, and an integral extension of an algebraically closed field is an isomorphism
(`IsAlgClosed.algebraMap_bijective_of_isIntegral`).  Finiteness is exactly where the curve
hypotheses enter, and they enter only there.

## Scope — read this before quoting the collapse

`IsAlgClosed K` is **essential and not incidental**.  Over a general base field the weighting is
real: a closed point with residue field a nontrivial extension contributes its degree, and the
weighted and unweighted degrees genuinely differ.  So this file does *not* remove the residue
weighting from the ledger; it identifies the one regime where a consumer may ignore it.  A
consumer that needs `principal_degree_zero` over an arbitrary field still needs either the
weighted statement or a separate argument, and this file is no evidence that such an argument is
close.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] Scheme.residueFieldOverModule

/-- **The residue degree is one over an algebraically closed base field** (★):
`[κ(x) : K] = 1` at every non-generic point of an integral curve, locally of finite type and
smooth of relative dimension one over an algebraically closed `K`.

`Scheme.residueDeg_finite` makes `κ(x)` a finite `K`-module; a finite algebra is integral; and
`IsAlgClosed.algebraMap_bijective_of_isIntegral` makes the structure map `K → κ(x)` bijective,
so `κ(x)` is one-dimensional.

The curve hypotheses are used *only* through `residueDeg_finite` — the closed-field step is pure
field theory. -/
theorem Scheme.residueDeg_eq_one_of_isAlgClosed [IsAlgClosed K]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {x : X} (hx : x ≠ genericPoint X) :
    X.residueDeg K x = 1 := by
  haveI hfin := Scheme.residueDeg_finite (K := K) hx
  letI alg : Algebra K (X.residueField x) := (X.residueOverAlgebraMap K x).toAlgebra
  haveI : Algebra.IsIntegral K (X.residueField x) := Algebra.IsIntegral.of_finite K _
  have hbij : Function.Bijective (algebraMap K (X.residueField x)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  change Module.finrank K (X.residueField x) = 1
  have e : K ≃ₗ[K] X.residueField x :=
    LinearEquiv.ofBijective (Algebra.linearMap K (X.residueField x)) hbij
  rw [← e.finrank_eq, Module.finrank_self]

namespace Scheme.CurveDivisor

/-- **Over `K̄` the residue weighting is a no-op**: `deg D = ∑ₓ Dₓ`, the bare coefficient sum.

This is the statement that lets a consumer holding the ledger's weighted `deg` speak about
`WeilDivisor.degree`, which sums coefficients unweighted
(`RiemannRoch/CurveDivisorIndexBridge.degree_eq_sum_nonGeneric` supplies the matching index
relabelling). -/
theorem deg_eq_sum_of_isAlgClosed [IsAlgClosed K]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (D : X.CurveDivisor) :
    deg K D = D.sum (fun _ n => n) := by
  classical
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Scheme.residueDeg_eq_one_of_isAlgClosed (K := K) x.2]
  push_cast
  ring

end Scheme.CurveDivisor

end AlgebraicGeometry

/-! ## The consequence: unweighted degree zero for principal divisors over `K̄` -/

namespace AlgebraicGeometry

open Scheme

/-- **Principal divisors have unweighted degree zero over an algebraically closed field** (★):
for a unit `g` of the function field of a smooth proper geometrically irreducible curve over
`k = k̄`, the *bare coefficient sum* of `div g` vanishes.

`deg_divOf` (the ported χ-ledger) gives this for the residue-*weighted* degree;
`CurveDivisor.deg_eq_sum_of_isAlgClosed` collapses the weighting.  Both `Module.Finite`
cohomology binders of the ledger are discharged here by synthesis rather than assumed
(`moduleFinite_hModule_zero`, `moduleFinite_hModule_one`).

This is the shape the open leaf `Scheme.WeilDivisor.principal_degree_zero` consumes — its
`degree` is the same bare coefficient sum, on the other index set, and
`RiemannRoch/CurveDivisorIndexBridge.degree_eq_sum_nonGeneric` relabels between them
degree-preservingly.  Two caveats before anyone closes that leaf with this:

1. `[IsAlgClosed k]` is a real restriction, not bookkeeping — see the module docstring.  The
   leaf as stated in `WeilDivisor.lean` carries no such hypothesis.
2. This says nothing about whether `Scheme.divOf` and that file's principal divisor are the
   same construction.  That comparison is unproved here and is not claimed. -/
theorem sum_divOf_eq_zero_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (g : C.left.functionFieldˣ) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
    (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) g).sum (fun _ n => n) = 0 := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  have h := deg_divOf k g
  rw [CurveDivisor.deg_eq_sum_of_isAlgClosed (K := k)] at h
  exact h

end AlgebraicGeometry
