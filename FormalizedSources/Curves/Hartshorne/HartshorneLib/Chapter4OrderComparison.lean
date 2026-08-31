/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4PrincipalDivisors
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Hartshorne II.6: comparing the two order conventions

The curve divisor construction uses the integer-valued order obtained by
inverting the adic valuation of a DVR stalk.  Mathlib's `Ring.ordFrac` uses the
same valuation with the inverse built into its definition.  This file records
the resulting coefficient comparison explicitly; it is the bridge needed when
transporting a product-formula statement into `CurveDivisor` notation.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits
open AlgebraicGeometry

namespace Hartshorne

variable {K : Type u} [Field K] {X : Scheme.{u}}

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

/-- The integer order used by principal divisors is Mathlib's fractional order
after applying `WithZero.log` to the corresponding valuation. -/
theorem orderZAt_toAdd_eq_log_ordFrac (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionFieldˣ) {x : X} (hx : x ≠ genericPoint X)
    [Ring.KrullDimLE 1 (X.presheaf.stalk x)] :
    Multiplicative.toAdd (orderZAt f hx g) =
      WithZero.log (Ring.ordFrac (X.presheaf.stalk x) (g : X.functionField)) := by
  letI := smoothCurve_stalk_isDiscreteValuationRing f hx
  letI := smoothCurve_stalk_isDedekindDomain f hx
  rw [Ring.ordFrac_eq_valuation_inv (K := X.functionField)]
  have hv : (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)).valuation
      X.functionField (g : X.functionField) = orderAt f hx (g : X.functionField) := rfl
  rw [hv]
  exact (log_coe_units_inv
    (Units.map (orderAt f hx).toMonoidWithZeroHom.toMonoidHom g)).symm

end Hartshorne
