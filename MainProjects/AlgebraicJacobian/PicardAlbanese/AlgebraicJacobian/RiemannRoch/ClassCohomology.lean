/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Chi
import AlgebraicJacobian.RiemannRoch.MulEquiv
import AlgebraicJacobian.Picard.DivisorClassMeromorphic

/-!
# `h⁰` and `h¹` of a Čech Picard class are well-defined

For the curve bundle `X` — integral, smooth of relative dimension one and quasi-compact over a
field `K` — the sheaf cohomology of a divisor sheaf depends only on the Čech Picard *class* of
the divisor, **separately in each degree**. If two Weil divisors `D`, `D'` have equal class
(`CurveDivisor.picClass K D = CurveDivisor.picClass K D'`) then `D − D' = div g` for a rational
function `g` (extraction `(X)`, `CurveDivisor.exists_divOf_of_picClass_eq`), and multiplication
by `g` is an isomorphism of divisor sheaves `𝒪(D) ≅ 𝒪(D − div g) = 𝒪(D')`
(`Scheme.mulEquivDivisorSheaf`). Transporting the ledger invariants of `RiemannRoch/Chi.lean`
along this isomorphism gives the degreewise statements below.

This is the **W6-lite** brick of the Wave-4 FLV worksheet (`informal/w4-flv-worksheet.md` §3.1):
it collapses to a few lines on the landed `h0_congr`/`h1_congr`/`mapEquiv` API and the landed
multiplication isomorphism, and it closes the FLV-facing form of the degree-lane AMENDMENT debt
(`informal/deg-d2-meromorphic-worksheet.md` §"AMENDMENT 2026-07-15"). Every declaration is the
carbon copy, in a fixed cohomological degree, of the landed Euler-characteristic twin
`AlgebraicGeometry.chi_divisorSheaf_eq_of_picClass_eq` (`RiemannRoch/Degree.lean`), and it
carries the same (finiteness-free) hypothesis budget as that twin.

## Main declarations

* `AlgebraicGeometry.h0_divisorSheaf_eq_of_picClass_eq`: `𝒪(D) = 𝒪(D') → h⁰(𝒪(D)) = h⁰(𝒪(D'))`.
* `AlgebraicGeometry.h1_divisorSheaf_eq_of_picClass_eq`: `𝒪(D) = 𝒪(D') → h¹(𝒪(D)) = h¹(𝒪(D'))`.
* `AlgebraicGeometry.subsingleton_hModule_one_of_picClass_eq`: the vanishing of `H¹` transports
  from `D` to any `D'` of the same class — the `Subsingleton` form the FLV consumers need (it is
  what `HModule.mapEquiv` transports, and it is strictly stronger than `h¹ = 0`).
* `AlgebraicGeometry.moduleFinite_hModule_divisorSheaf_zero_of_picClass_eq` /
  `..._one_of_picClass_eq`: finite-dimensionality of `H⁰`/`H¹` transports between divisors of
  equal class (`Module.Finite.equiv` along the same isomorphism).

## Packaging decision (recorded per the W6-lite charter)

The FLV consumers (`informal/w4-flv-worksheet.md` §2.5 step 4, and the §1.2 rank corollary) use
witness-independence *directly* as the equalities/transports above, always on `h⁰`/`h¹` of a
concrete witness `divisorSheaf K D`. They never need a choice-based `h0OfClass`/`h1OfClass`
package. Introducing such packaged definitions would add a `Classical.choice`-of-witness
indirection with no current consumer, so — mirroring the deliberate scope of §3.1, which lists
exactly the `h¹`-eq lemma, the `Subsingleton` transport and the `h⁰` twin — the packaged
"cohomology of a class" definitions are **not** introduced here; the eq-lemmas and transports are
the honest, choice-free interface FLV consumes. (The analogous `classDeg` package in
`Degree.lean` earns its keep only because it is itself the E-i..E-iii interface object; there is
no such downstream demand for an `h⁰`/`h¹` package.)
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **The multiplication isomorphism identifying divisor sheaves of equal class.** For Weil
divisors `D`, `D'` with `CurveDivisor.picClass K D = CurveDivisor.picClass K D'`, the extraction
lemma writes `D − D' = div g`, and multiplication by `g` realizes an isomorphism of sheaves of
`K`-modules `𝒪(D) ≅ 𝒪(D')`. This is the single geometric input shared by every degreewise
statement below (compare the identically-built `hiso` inside
`chi_divisorSheaf_eq_of_picClass_eq`). -/
private noncomputable def picClassDivisorSheafIso {D D' : X.CurveDivisor}
    (h : CurveDivisor.picClass K D = CurveDivisor.picClass K D') :
    X.divisorSheaf K D ≅ X.divisorSheaf K D' := by
  have hg := (CurveDivisor.exists_divOf_of_picClass_eq K h).choose_spec
  have hiso := mulEquivDivisorSheaf K (CurveDivisor.exists_divOf_of_picClass_eq K h).choose D
  rw [show D - Scheme.divOf (X ↘ Spec (CommRingCat.of K))
    (CurveDivisor.exists_divOf_of_picClass_eq K h).choose = D' by rw [← hg]; abel] at hiso
  exact hiso

/-! ## `h⁰` and `h¹` of a class are well-defined -/

/-- **`h⁰` is a Čech Picard class invariant**: Weil divisors of equal class have the same
`h⁰(𝒪(D))`. Carbon copy of `chi_divisorSheaf_eq_of_picClass_eq` with `Sheaf.h0_congr` in place of
`Sheaf.chi_congr`; needs no finiteness hypotheses. -/
theorem h0_divisorSheaf_eq_of_picClass_eq {D D' : X.CurveDivisor}
    (h : CurveDivisor.picClass K D = CurveDivisor.picClass K D') :
    Sheaf.h0 (X.divisorSheaf K D) = Sheaf.h0 (X.divisorSheaf K D') :=
  Sheaf.h0_congr (picClassDivisorSheafIso K h)

/-- **`h¹` is a Čech Picard class invariant**: Weil divisors of equal class have the same
`h¹(𝒪(D))`. Carbon copy of `chi_divisorSheaf_eq_of_picClass_eq` with `Sheaf.h1_congr` in place of
`Sheaf.chi_congr`; needs no finiteness hypotheses. This is the witness-independence that makes the
FLV outer quantifier `∀ D, picClass D = λθⁿ → …` well-posed. -/
theorem h1_divisorSheaf_eq_of_picClass_eq {D D' : X.CurveDivisor}
    (h : CurveDivisor.picClass K D = CurveDivisor.picClass K D') :
    Sheaf.h1 (X.divisorSheaf K D) = Sheaf.h1 (X.divisorSheaf K D') :=
  Sheaf.h1_congr (picClassDivisorSheafIso K h)

/-! ## The `Subsingleton` transport (the strong FLV form) -/

/-- **Vanishing of `H¹` is a class invariant**: if the degree-one cohomology of `𝒪(D)` is a
subsingleton (the strong vanishing form), so is that of `𝒪(D')` for any `D'` of the same class.
This is the form the FLV consumers transport (`Subsingleton`, not `h¹ = 0`, since it survives
sheaf isomorphisms and surjections and does not require finite-dimensionality): the isomorphism
`𝒪(D) ≅ 𝒪(D')` induces the `K`-linear equivalence `H¹(𝒪(D)) ≃ₗ[K] H¹(𝒪(D'))`
(`HModule.mapEquiv`), and `Subsingleton` transports across an equivalence. -/
theorem subsingleton_hModule_one_of_picClass_eq {D D' : X.CurveDivisor}
    (h : CurveDivisor.picClass K D = CurveDivisor.picClass K D')
    (hsub : Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1)) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K D') 1) :=
  (Sheaf.HModule.mapEquiv (picClassDivisorSheafIso K h) 1).toEquiv.subsingleton_congr.mp hsub

/-! ## Finite-dimensionality transports -/

/-- **Finiteness of `H⁰` is a class invariant**: if `H⁰(𝒪(D))` is a finite-dimensional
`K`-module, so is `H⁰(𝒪(D'))` for any `D'` of the same class, transported along the class
isomorphism by `Module.Finite.equiv`. -/
theorem moduleFinite_hModule_divisorSheaf_zero_of_picClass_eq {D D' : X.CurveDivisor}
    [Module.Finite K (Sheaf.HModule (X.divisorSheaf K D) 0)]
    (h : CurveDivisor.picClass K D = CurveDivisor.picClass K D') :
    Module.Finite K (Sheaf.HModule (X.divisorSheaf K D') 0) :=
  Module.Finite.equiv (Sheaf.HModule.mapEquiv (picClassDivisorSheafIso K h) 0)

/-- **Finiteness of `H¹` is a class invariant**: if `H¹(𝒪(D))` is a finite-dimensional
`K`-module, so is `H¹(𝒪(D'))` for any `D'` of the same class, transported along the class
isomorphism by `Module.Finite.equiv`. -/
theorem moduleFinite_hModule_divisorSheaf_one_of_picClass_eq {D D' : X.CurveDivisor}
    [Module.Finite K (Sheaf.HModule (X.divisorSheaf K D) 1)]
    (h : CurveDivisor.picClass K D = CurveDivisor.picClass K D') :
    Module.Finite K (Sheaf.HModule (X.divisorSheaf K D') 1) :=
  Module.Finite.equiv (Sheaf.HModule.mapEquiv (picClassDivisorSheafIso K h) 1)

end AlgebraicGeometry
