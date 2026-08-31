/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.RiemannRoch.Adelic.ChiLedger
import AlgebraicJacobian.Picard.SectionRingUniversal

/-!
# Discharge of the adelic `IsConstantField` gate (campaign P-cluster opener)

The χ-ledger of `RiemannRoch/Adelic/ChiLedger.lean` runs over a base field of
constants `k ↪ K(X)` packaged by the gate class `Adelic.IsConstantField k X`:
*every nonzero constant has order `0` at every prime divisor*.  The W1-F audit
dossier (run 0020) flagged this gate as instance-free and absent from the
campaign gate table.  This file discharges it for the situation the campaign
actually uses: a curve `C : Over (Spec k)` with the `k`-algebra structure on the
function field induced by the structure morphism.

## Statement audit (BLOCKING house rule; verdict recorded before proving)

* The gate `IsConstantField k X` asserts only the **easy direction** of the
  field-of-constants dialectic: nonzero constants are everywhere units, i.e.
  `ord_P (c) = 0` for `c ∈ k^×`.  With the algebra structure factoring through
  `k → Γ(C, 𝒪_C) → 𝒪_{C,P} → K(C)`, this is TRUE at full generality: a nonzero
  `c` is a unit in the field `k`, ring maps preserve units, so its image in the
  DVR stalk `𝒪_{C,P}` is a unit, and `Ring.ordFrac` of a stalk unit is `1`
  (Mathlib `Ring.ordFrac_of_isUnit`), i.e. `ord_P = 0`.  **No properness, no
  geometric integrality, no `B0` input is needed** — only `[IsIntegral C.left]`
  (for the function-field formalism) plus the standing `(*)`-hypotheses
  `[IsLocallyNoetherian]`, `[IsRegularInCodimensionOne]` of the `order` API.
* The W1-F dossier proposed discharging the gate "via B0's
  `globalSectionsAlgEquivBase`".  Correction (this file): `B0`/
  `HasTrivialConstants` is the content of the **converse** direction — that
  every everywhere-regular function is a constant, `Γ(C, 𝒪_C) = k` — which the
  gate does *not* assert.  `B0` enters only as the natural home of the ring map
  `constMap C : k → Γ(C, 𝒪_C)` used to *define* the algebra structure
  (`functionFieldAlgebra` below); that map exists for every `C : Over (Spec k)`.
* Instance-diamond audit: Mathlib has **no** `Algebra k X.functionField`
  instance for a plain field `k` (only `Algebra Γ(X, U) X.functionField` and
  `Algebra (𝒪_{X,x}) X.functionField`), so `functionFieldAlgebra` creates no
  diamond.  It is `scoped` (house pattern of
  `Scheme.globalSectionsAlgebra`, `Picard/SectionRingUniversal.lean`) — the
  χ-ledger consumer opens `AlgebraicGeometry.Scheme` to activate it together
  with the gate instance.

## Main declarations

* `Scheme.RationalMap.order_algebraMap_eq_zero_of_isUnit` — reusable brick: the
  order of (the image in `K(X)` of) a stalk unit at a prime divisor is `0`.
* `Scheme.functionFieldAlgebra` — the `k`-algebra structure on `K(C)` induced by
  the structure morphism, through `constMap` and the germ at the generic point.
* `Scheme.instIsConstantField` — the gate discharge.

Campaign reference: wave-2 P-cluster opener (task A) of
`informal/pic-representability-campaign.md`; W1-F dossier §7 gate inventory.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- **Order of a stalk unit is zero.**  For a prime divisor `Y` of a scheme `X`
satisfying the standing `(*)`-hypotheses, and a *unit* `u` of the DVR stalk
`𝒪_{X,Y}`, the order of vanishing of its image in the function field is `0`:
units have neither zeros nor poles along `Y`.  Wrapper around Mathlib's
`Ring.ordFrac_of_isUnit` through the definition
`order Y f = WithZero.log (Ring.ordFrac 𝒪_{X,Y} f)`. -/
theorem Scheme.RationalMap.order_algebraMap_eq_zero_of_isUnit
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X] (Y : X.PrimeDivisor)
    {u : X.presheaf.stalk Y.point} (hu : IsUnit u) :
    Scheme.RationalMap.order Y
      (algebraMap (X.presheaf.stalk Y.point) X.functionField u) = 0 := by
  unfold Scheme.RationalMap.order
  rw [Ring.ordFrac_of_isUnit hu, WithZero.log_one]

namespace Scheme

variable {k : Type u} [Field k]

/-- The total open `⊤` of an irreducible (e.g. integral) scheme is nonempty —
instance form, so that instance heads mentioning the Mathlib
`Algebra Γ(X, ⊤) X.functionField` (which carries a `[Nonempty ⊤]` binder) can
synthesize.  Scoped to avoid polluting general `Nonempty` searches. -/
scoped instance nonempty_top_opens (X : Scheme.{u}) [IrreducibleSpace X] :
    Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The `k`-algebra structure on the function field `K(C)` of an integral
`k`-scheme `C`, induced by the structure morphism: the composite
`k → Γ(C, 𝒪_C) → K(C)` of `constMap C` (`Picard/SectionRingUniversal.lean`)
with the germ at the generic point.  Scoped, mirroring
`globalSectionsAlgebra`. -/
noncomputable scoped instance functionFieldAlgebra
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left] :
    Algebra k C.left.functionField :=
  RingHom.toAlgebra ((C.left.germToFunctionField ⊤).hom.comp (constMap C).hom)

/-- The `k`-algebra map to the function field factors through the global
sections: `algebraMap k K(C) = germToFunctionField ∘ constMap` — definitional
unfolding of `functionFieldAlgebra`, stated against the Mathlib
`Algebra Γ(C, ⊤) K(C)` instance. -/
lemma algebraMap_functionField_eq (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] :
    algebraMap k C.left.functionField
      = (algebraMap ↥Γ(C.left, ⊤) C.left.functionField).comp (constMap C).hom :=
  rfl

/-- The tower `k → Γ(C, 𝒪_C) → K(C)` of the structure-morphism algebra
structures. -/
scoped instance isScalarTower_globalSections_functionField
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left] :
    IsScalarTower k ↥Γ(C.left, ⊤) C.left.functionField :=
  IsScalarTower.of_algebraMap_eq' (algebraMap_functionField_eq C)

/-- **The structure field satisfies the adelic `IsConstantField` interface.**
For an integral
`k`-scheme `C` satisfying the `(*)`-hypotheses, with the structure-morphism
algebra structure on `K(C)`, every nonzero constant `c ∈ k` has order `0` at
every prime divisor: `c` is a unit in the field `k`, hence its image in each
DVR stalk is a unit, and units have order `0`
(`order_algebraMap_eq_zero_of_isUnit`).

Audit verdict (see module docstring): TRUE at this generality — no properness,
no `B0`/`HasTrivialConstants` input; this is the easy direction of the
field-of-constants dialectic. -/
theorem isConstantField_functionField (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] [IsLocallyNoetherian C.left]
    [Scheme.IsRegularInCodimensionOne C.left] :
    Adelic.IsConstantField k C.left where
  order_algebraMap_eq_zero P c hc := by
    letI : Algebra ↥Γ(C.left, ⊤) (C.left.presheaf.stalk P.point) :=
      C.left.presheaf.algebra_section_stalk
        (⟨P.point, trivial⟩ : (⊤ : C.left.Opens))
    haveI : IsScalarTower ↥Γ(C.left, ⊤) (C.left.presheaf.stalk P.point)
        C.left.functionField :=
      functionField_isScalarTower C.left ⊤ ⟨P.point, trivial⟩
    have h1 : algebraMap k C.left.functionField c
        = algebraMap ↥Γ(C.left, ⊤) C.left.functionField ((constMap C).hom c) := rfl
    have hu : IsUnit (algebraMap ↥Γ(C.left, ⊤) (C.left.presheaf.stalk P.point)
        ((constMap C).hom c)) :=
      ((isUnit_iff_ne_zero.mpr hc).map (constMap C).hom).map _
    rw [h1, IsScalarTower.algebraMap_apply ↥Γ(C.left, ⊤)
      (C.left.presheaf.stalk P.point) C.left.functionField]
    exact Scheme.RationalMap.order_algebraMap_eq_zero_of_isUnit P hu

/-- Scoped instance form of `isConstantField_functionField`. -/
scoped instance instIsConstantField (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] [IsLocallyNoetherian C.left]
    [Scheme.IsRegularInCodimensionOne C.left] :
    Adelic.IsConstantField k C.left :=
  isConstantField_functionField C

end Scheme

end AlgebraicGeometry
