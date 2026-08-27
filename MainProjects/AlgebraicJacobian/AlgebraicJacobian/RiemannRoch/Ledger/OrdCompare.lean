/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.PrincipalDivisor

/-!
# `ordZ` is `Ring.ordFrac`, with NO dependence on `WeilDivisor.lean`

The ported ledger's order function `Scheme.ordZ` (`Ledger/PrincipalDivisor.lean`) and mathlib's
`Ring.ordFrac` on the stalk are the same integer.  That comparison is the mathematical content of
`Ledger/PrincipalCompare.lean`; it is isolated here because of an *import* fact that decides
whether another lane can use it.

## Why this file exists separately — the import inversion

`Scheme.RationalMap.order`, `WeilDivisor.principal` and `WeilDivisor.degree` all live in
`RiemannRoch/WeilDivisor.lean`, so anything stated in their vocabulary sits **downstream** of that
file.  `WeilDivisor.lean` carries the open leaf `principal_degree_zero`, and a theorem downstream
of a file cannot be substituted into a `sorry` *inside* it: that is an import inversion.
`ajc-pic0av` measured exactly this against `Ledger/PrincipalTransport` (AJC thread `I-0493`) — the
importable part of the ledger and the proving part differed.

The comparison below mentions only `Scheme.ordZ` and `Ring.ordFrac`, both of which are available
without `WeilDivisor.lean`.  Measured: this file's transitive project-import cone is **6 files**
and does **not** contain `RiemannRoch.WeilDivisor`, whereas `PrincipalCompare`'s is 16 and does.
So `WeilDivisor.lean` may import *this* file, and `RationalMap.order` unfolds to
`WithZero.log (Ring.ordFrac …)` by definition — which is what turns the right-hand side below into
that file's own coefficient.

`Ledger/PrincipalCompare.lean` keeps the `RationalMap.order`-flavoured restatement for consumers
that already live downstream; it now takes its proof from here rather than repeating it.

## Provenance

AJC-native.  The load-bearing input is mathlib's `Ring.ordFrac_eq_valuation_inv`
(`Mathlib/RingTheory/OrderOfVanishing/Noetherian.lean`), which neither project had used; the split
itself is `ajc-pic0av`'s option (2) from the thread, verified rather than assumed.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- `WithZero.log` of a coerced unit of `ℤᵐ⁰`, after inversion, is `toAdd` of the inverse in the
units group: the pure `WithZero` bookkeeping separating the two spellings of "order". -/
private lemma log_coe_units_inv (u : (WithZero (Multiplicative ℤ))ˣ) :
    WithZero.log ((u : WithZero (Multiplicative ℤ))⁻¹)
      = Multiplicative.toAdd (invMonoidHom (WithZero.unitsWithZeroEquiv u)) := by
  obtain ⟨a, ha⟩ : ∃ a : Multiplicative ℤ,
      (u : WithZero (Multiplicative ℤ)) = (a : WithZero _) :=
    ⟨WithZero.unitsWithZeroEquiv u, by simp [WithZero.unitsWithZeroEquiv]⟩
  simp only [ha, invMonoidHom]
  rw [← WithZero.coe_inv]
  have hlog : ∀ b : Multiplicative ℤ,
      WithZero.log (b : WithZero (Multiplicative ℤ)) = Multiplicative.toAdd b :=
    fun b => (Equiv.symm_apply_eq Multiplicative.toAdd).mp rfl
  rw [hlog]
  simp [WithZero.unitsWithZeroEquiv, ha]

/-- **The two order functions agree** (★): the ported ledger's `ordZ`, read additively, is
mathlib's `Ring.ordFrac` on the stalk, read through `WithZero.log` — which is exactly the
integer `Scheme.RationalMap.order` uses.

Both are the adic valuation of the maximal ideal of the DVR stalk: `Scheme.ord` *is* that
valuation by construction, `stalkHeightOne` is definitionally
`IsDiscreteValuationRing.maximalIdeal`, and `Ring.ordFrac_eq_valuation_inv` supplies the single
inversion that `ordZ` performs on the other side of the units equivalence.

The sign conventions agree with no correction term. -/
theorem Scheme.ordZ_toAdd_eq_log_ordFrac (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionFieldˣ) {x : X} (hx : x ≠ genericPoint X)
    [Ring.KrullDimLE 1 (X.presheaf.stalk x)] :
    Multiplicative.toAdd (Scheme.ordZ f hx g)
      = WithZero.log (Ring.ordFrac (X.presheaf.stalk x) (g : X.functionField)) := by
  letI := isDiscreteValuationRing_stalk f hx
  letI := isDedekindDomain_stalk f hx
  rw [Ring.ordFrac_eq_valuation_inv (K := X.functionField)]
  have hv : (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)).valuation
      X.functionField (g : X.functionField) = Scheme.ord f hx (g : X.functionField) := rfl
  rw [hv]
  exact (log_coe_units_inv (Units.map (Scheme.ord f hx).toMonoidWithZeroHom.toMonoidHom g)).symm


end AlgebraicGeometry
