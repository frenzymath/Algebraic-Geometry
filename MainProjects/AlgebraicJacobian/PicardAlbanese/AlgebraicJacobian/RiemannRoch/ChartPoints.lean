/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Points of an affine chart and primes of its section ring

For an integral scheme `X` and an affine open `V`, the non-generic points of `V` correspond
to the nonzero primes of the section ring `Γ(X, V)` through
`IsAffineOpen.fromSpec`/`IsAffineOpen.primeIdealOf`.  This file records the four public
lemmas of that correspondence — the points ↔ primes leg of the chart colength dictionary
(`informal/deg-d5b-worksheet.md` §4 SB-3), split out of
`AlgebraicJacobian.RiemannRoch.ChartColength` for the 500-line discipline:

* `AlgebraicGeometry.IsAffineOpen.primeIdealOf_ne_bot` — the prime of a non-generic point
  of the chart is nonzero;
* `AlgebraicGeometry.IsAffineOpen.fromSpec_base_mem` — `fromSpec` lands in `V`;
* `AlgebraicGeometry.IsAffineOpen.primeIdealOf_fromSpec_base` — `primeIdealOf` is a left
  inverse of `fromSpec` on points;
* `AlgebraicGeometry.IsAffineOpen.fromSpec_base_ne_genericPoint` — the point of a nonzero
  prime is closed (non-generic).
-/

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

section PointsPrimes

variable {X : Scheme.{u}} [IsIntegral X] {V : X.Opens} (hV : IsAffineOpen V)

/-- **Nonzero prime at a closed point.** On an integral scheme, the prime of `Γ(X, V)` cut
out by a non-generic point of the affine open `V` is not `⊥`.  (Public form of the
re-derivations in `StalksDVR`/`ResidueDegree`.) -/
theorem IsAffineOpen.primeIdealOf_ne_bot {x : X} (hx : x ∈ V) (hxg : x ≠ genericPoint X) :
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≠ ⊥ := by
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  intro h
  apply hxg
  have h1 : hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  have hgen : (genericPoint (Spec Γ(X, V)) : Spec Γ(X, V)) = hV.primeIdealOf ⟨x, hx⟩ := by
    rw [genericPoint_eq_bot_of_affine]
    exact (PrimeSpectrum.ext h).symm
  rw [← h1, ← hgen, genericPoint_eq_of_isOpenImmersion hV.fromSpec]

omit [IsIntegral X] in
/-- The image of a point of `Spec Γ(X, V)` under `fromSpec` lies in `V`. -/
theorem IsAffineOpen.fromSpec_base_mem (y : Spec Γ(X, V)) : hV.fromSpec.base y ∈ V := by
  have h : hV.fromSpec.base y ∈ Set.range hV.fromSpec := ⟨y, rfl⟩
  rwa [hV.range_fromSpec] at h

omit [IsIntegral X] in
/-- `primeIdealOf` is a left inverse of `fromSpec` on points: the prime of the point of a
prime is the prime. -/
theorem IsAffineOpen.primeIdealOf_fromSpec_base (y : Spec Γ(X, V)) :
    hV.primeIdealOf ⟨hV.fromSpec.base y, hV.fromSpec_base_mem y⟩ = y :=
  hV.fromSpec.isOpenEmbedding.injective
    (hV.fromSpec_primeIdealOf ⟨hV.fromSpec.base y, hV.fromSpec_base_mem y⟩)

/-- The point of a *nonzero* prime of the chart is closed (non-generic). -/
theorem IsAffineOpen.fromSpec_base_ne_genericPoint {y : Spec Γ(X, V)}
    (hy : y.asIdeal ≠ ⊥) : hV.fromSpec.base y ≠ genericPoint X := by
  haveI : Nonempty V := ⟨⟨_, hV.fromSpec_base_mem y⟩⟩
  intro h
  apply hy
  have hgen : y = genericPoint (Spec Γ(X, V)) :=
    hV.fromSpec.isOpenEmbedding.injective
      (by rw [genericPoint_eq_of_isOpenImmersion hV.fromSpec, h])
  rw [hgen, genericPoint_eq_bot_of_affine]
  rfl

end PointsPrimes

end AlgebraicGeometry
