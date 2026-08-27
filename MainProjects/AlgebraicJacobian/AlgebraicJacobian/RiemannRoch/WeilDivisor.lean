/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import AlgebraicJacobian.Genus
import AlgebraicJacobian.Albanese.CoheightBridge
import AlgebraicJacobian.RiemannRoch.Adelic.FiniteMapToP1
import AlgebraicJacobian.RiemannRoch.Ledger.OrdCompare
import AlgebraicJacobian.RiemannRoch.Ledger.ResidueOneAlgClosed

/-!
# Weil divisors on a smooth proper curve (RR.1)

This file develops the scheme-level Weil-divisor API needed by the
Riemann--Roch part of the project. It contains:

* prime divisors and finite formal sums of prime divisors;
* restriction of prime divisors and orders of vanishing to open subschemes;
* finite support and principal divisors on Noetherian integral schemes regular
  in codimension one;
* coefficient degree, positive parts, and linear equivalence; and
* the degree-zero theorem for principal divisors on complete nonsingular curves.

Mathlib's adjacent APIs for meromorphic divisors, ring Picard groups, and
rational maps do not provide this scheme-level formal-sum construction.

## References

Blueprint: `blueprint/src/chapters/RiemannRoch_WeilDivisor.tex`.
Hartshorne, *Algebraic Geometry*, II §6 (pp. 130–137 + IV.1 pp. 294–296).
Stacks Project, tags 02RW (divisors), 02ME (order at a point), 0BE0 (degree),
0BE3 (principal divisors have degree zero on a complete nonsingular curve).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## §1. Codim-1 cycle group / Weil divisor group

Hartshorne's condition `(*)` (II §6, p. 130) is: `X` is a Noetherian integral
separated scheme that is regular in codimension one. Under `(*)`, prime divisors
are closed integral subschemes of codimension one, and the local ring at the
generic point of a prime divisor is a DVR with quotient field the function field
`K(X)`.

A prime divisor is encoded by its **generic point** together with the
codimension-one witness `Order.coheight point = 1`: the data field `point : X`
selects the generic point of the closed integral subscheme, and the predicate
field `coheight` enforces codimension one in the specialisation preorder
(Hartshorne II §6 p. 130; blueprint pin `def:prime_divisor`). Integrality of the
closure is automatic, so no separate integrality witness is needed.
-/

/-- A **prime divisor** on a scheme `X`: a closed integral subscheme of codimension
one, encoded (for a scheme satisfying Hartshorne's condition `(*)`) by its generic
point. On a curve, prime divisors correspond bijectively to closed points.

The codimension-one witness is the predicate `Order.coheight point = 1` on the
specialisation preorder of `X.carrier` (Mathlib's convention is
`x ≤ y ↔ y ⤳ x`, so the generic point is the unique maximal element and a
generic point of a codim-1 closed integral subscheme has a length-one chain
above it). The closure `{point}̄` is automatically irreducible (so the reduced
induced subscheme structure is automatically integral); hence no separate
integrality field is needed.

Blueprint reference: `def:prime_divisor` / `def:codim1_cycles` (Hartshorne II §6
p. 130; Stacks 02RW). -/
structure Scheme.PrimeDivisor (X : Scheme.{u}) where
  /-- The generic point of the closed integral subscheme. -/
  point : X
  /-- Codimension-1 witness: `point` has coheight `1` in the specialisation
  preorder on `X.carrier`. -/
  coheight : Order.coheight point = 1

/-- The **Weil divisor group** of a scheme `X` satisfying Hartshorne's condition
`(*)`: the free abelian group on the set of prime divisors of `X`,
`Div(X) = ⨁_{Y prime divisor of X} ℤ · Y`. An element `D = Σ nᵢ · Yᵢ` with finitely
many nonzero coefficients is a **Weil divisor**; if all `nᵢ ≥ 0` it is **effective**.

Blueprint reference: `def:codim1_cycles` (Hartshorne II §6 p. 130). -/
def Scheme.WeilDivisor (X : Scheme.{u}) : Type u := X.PrimeDivisor →₀ ℤ

namespace Scheme.WeilDivisor

noncomputable instance (X : Scheme.{u}) : AddCommGroup X.WeilDivisor :=
  inferInstanceAs (AddCommGroup (X.PrimeDivisor →₀ ℤ))

instance (X : Scheme.{u}) : Inhabited X.WeilDivisor :=
  inferInstanceAs (Inhabited (X.PrimeDivisor →₀ ℤ))

end Scheme.WeilDivisor

/-! ## Prime divisors are non-generic points

Two structural facts about the index set of `Scheme.WeilDivisor`, recorded here because they
are the **index-set half of the bridge to the χ-ledger route** for
`principal_degree_zero` (see the discussion at that theorem).

This project indexes divisors by `Scheme.PrimeDivisor X` — a point together with a proof that
its coheight is `1`. The sibling project `Algebraic-Jacobian-Challenge-Rebuild` indexes them
by `{x : X // x ≠ genericPoint X}` (`RiemannRoch/Divisor.lean`), and its χ-ledger closes
degree-zero-of-principal sorry-free on that carrier. That route is now *taken*: the χ-ledger
is ported into `RiemannRoch/Ledger/` and `principal_degree_zero` below is proved through it.
The index comparison splits cleanly and **both directions are available here**:

* **coheight 1 ⟹ non-generic** is `Scheme.PrimeDivisor.point_ne_genericPoint` below.
  Unconditional and elementary.
* **non-generic ⟹ coheight 1** is *not* elementary: it needs the curve hypothesis, since it
  fails as soon as the space has dimension `> 1`. Its two halves are
  `1 ≤ coheight` (elementary, `one_le_coheight_of_ne_genericPoint` below) and
  `coheight ≤ 1`, the substantive half, which is `Adelic.coheight_le_one_of_curve`.

⚠ CORRECTED (run 0067 r4). This paragraph used to say `coheight ≤ 1` "lives *downstream* of
this file", and concluded that "the direction needed to *produce* prime divisors is the one
that is still out of scope here". **Both clauses are false**, and the same file refuted them
1100 lines below while this header still asserted them — caught by a fresh-context reviewer.
`Adelic.coheight_le_one_of_curve` sits in a three-file import cone
(`Albanese.CoheightBridge`, `Picard.ProjectiveSpace`, `Adelic.P1BaseCase`), all of which this
module already reached through `Genus`; it was never downstream of `WeilDivisor.lean`, and it
is now imported here directly. So the *producing* direction is in scope: see the index
equivalence built inline in the proof of `principal_degree_zero`, whose `invFun` is exactly it
(`le_antisymm` of the bound against `one_le_coheight_of_ne_genericPoint`).

The general lesson, recorded because this lane made the same error three times in three
different files: downstreamness is a property of a **file**, not of a theorem, so a
"lives downstream" note must be re-measured whenever the importing file's own imports change. -/

/-- **A prime divisor is not the generic point.** If it were, it would be a maximum in the
specialisation order and its coheight would be `0`, contradicting `coheight = 1`.

Unconditional apart from irreducibility (which is what gives a generic point at all). -/
theorem Scheme.PrimeDivisor.point_ne_genericPoint {X : Scheme.{u}} [IrreducibleSpace X]
    (Y : X.PrimeDivisor) : Y.point ≠ genericPoint X := by
  intro h
  have hmax : IsMax Y.point := by
    intro z _
    rw [h]
    exact genericPoint_specializes z
  have h0 : Order.coheight Y.point = 0 := Order.coheight_eq_zero.mpr hmax
  rw [Y.coheight] at h0
  simp at h0

/-- **A non-generic point has coheight at least one.** The elementary half of the converse of
`Scheme.PrimeDivisor.point_ne_genericPoint`: a point that is not the generic point is not
maximal in the specialisation order (the generic point strictly dominates it), and coheight
`0` is equivalent to maximality.

The *other* half — `coheight ≤ 1`, which is what upgrades this to `coheight = 1` and so
produces a `Scheme.PrimeDivisor` — is genuinely about curves and is not available at this
point in the import graph; see `Adelic.coheight_le_one_of_curve`. -/
theorem Scheme.one_le_coheight_of_ne_genericPoint {X : Scheme.{u}} [IrreducibleSpace X]
    {x : X} (hx : x ≠ genericPoint X) : 1 ≤ Order.coheight x := by
  have hnotmax : ¬ IsMax x := fun hmax =>
    hx ((genericPoint_specializes x).antisymm (hmax (genericPoint_specializes x))).symm.eq
  exact Order.one_le_iff_ne_zero.mpr fun h => hnotmax (Order.coheight_eq_zero.mp h)

/-! ## Prime divisors and open immersions

The project-local lemma `Order.coheight_eq_of_isOpenEmbedding` lets us package
the following standard operations:
- `Scheme.PrimeDivisor.restrictToOpen` — given a prime divisor `Y` of `X` and
  `Y.point ∈ U`, the corresponding prime divisor of the open subscheme `U`.
- `Scheme.PrimeDivisor.ofOpen` — push a prime divisor of an open subscheme `U`
  back to a prime divisor of the ambient scheme `X`.
- `Scheme.PrimeDivisor.equivOpen` — the bijection
  `{ Y : X.PrimeDivisor // Y.point ∈ U } ≃ U.toScheme.PrimeDivisor`.
- `Scheme.PrimeDivisor.stalkIso` — the stalk identification along the
  open immersion `U.ι : U.toScheme ⟶ X`, a thin wrapper around Mathlib's
  `AlgebraicGeometry.Scheme.Opens.stalkIso`.

References: Stacks 02IZ (open-immersion stalks) and Stacks 005X (coheight and
Krull dimension on Noetherian schemes).
-/

namespace Scheme.PrimeDivisor

variable {X : Scheme.{u}}

/-- **Extensionality for `Scheme.PrimeDivisor`.** Two prime divisors with
the same underlying point are equal (the coheight witness is a `Prop`-valued
field, so it carries no data). Useful for the round-trip lemmas of the
`equivOpen` bijection below. -/
@[ext]
lemma ext {Y Y' : X.PrimeDivisor} (h : Y.point = Y'.point) : Y = Y' := by
  cases Y; cases Y'
  congr

/-- **PrimeDivisor restriction along an open immersion.** Given a prime
divisor `Y` of `X` whose generic point lies in an open `U ⊆ X`, the
corresponding prime divisor of the open subscheme `U.toScheme`. The
codimension-one witness transports via `Order.coheight_eq_of_isOpenEmbedding`. -/
def restrictToOpen (U : X.Opens) (Y : X.PrimeDivisor)
    (hYU : Y.point ∈ U) : U.toScheme.PrimeDivisor where
  point := ⟨Y.point, hYU⟩
  coheight := by
    rw [← Y.coheight]
    exact (Order.coheight_eq_of_isOpenEmbedding U.isOpen Y.point hYU).symm

/-- **PrimeDivisor extension from an open subscheme.** A prime divisor of an
open subscheme `U.toScheme` lifts to a prime divisor of the ambient `X` along
the open immersion `U.ι`. Codimension-one is preserved via the same
`Order.coheight_eq_of_isOpenEmbedding` bridge, this time in the forward
direction. -/
def ofOpen (U : X.Opens) (YU : U.toScheme.PrimeDivisor) :
    X.PrimeDivisor where
  point := YU.point.1
  coheight := by
    rw [Order.coheight_eq_of_isOpenEmbedding U.isOpen YU.point.1 YU.point.2]
    exact YU.coheight

@[simp]
lemma restrictToOpen_point (U : X.Opens) (Y : X.PrimeDivisor)
    (hYU : Y.point ∈ U) :
    (restrictToOpen U Y hYU).point = ⟨Y.point, hYU⟩ := rfl

@[simp]
lemma ofOpen_point (U : X.Opens) (YU : U.toScheme.PrimeDivisor) :
    (ofOpen U YU).point = YU.point.1 := rfl

/-- **Bijection between prime divisors of `X` lying inside `U` and prime
divisors of `U.toScheme`.** The forward map is
`Y ↦ Scheme.PrimeDivisor.restrictToOpen U Y.val Y.property`; the inverse is
`Scheme.PrimeDivisor.ofOpen U`. Both maps are coheight-preserving by
`Order.coheight_eq_of_isOpenEmbedding`. -/
def equivOpen (U : X.Opens) :
    { Y : X.PrimeDivisor // Y.point ∈ U } ≃ U.toScheme.PrimeDivisor where
  toFun Y := restrictToOpen U Y.1 Y.2
  invFun YU := ⟨ofOpen U YU, YU.point.2⟩
  left_inv := by
    rintro ⟨Y, hY⟩
    rfl
  right_inv := by
    intro YU
    rfl

/-- **Stalk identification along an open immersion at a prime divisor.** A
thin wrapper around Mathlib's `AlgebraicGeometry.Scheme.Opens.stalkIso`
specialised to the underlying carrier of a prime divisor `Y` lifted from
the open subscheme. Stacks 02IZ stalk side. -/
noncomputable def stalkIso (U : X.Opens) (Y : X.PrimeDivisor)
    (hYU : Y.point ∈ U) :
    U.toScheme.presheaf.stalk (restrictToOpen U Y hYU).point ≅
      X.presheaf.stalk Y.point :=
  AlgebraicGeometry.Scheme.Opens.stalkIso U ⟨Y.point, hYU⟩

end Scheme.PrimeDivisor

end AlgebraicGeometry

/-! ## Naturality of `Ring.ordFrac`

The order functions `Ring.ord`, `Ring.ordMonoidWithZeroHom`, and
`Ring.ordFrac` are invariant under a ring isomorphism and a compatible
fraction-field isomorphism.

This is the algebraic substrate for the scheme-level
`Scheme.RationalMap.order` naturality across the
`Scheme.PrimeDivisor.stalkIso` open-immersion bridge (used by the
function-field-iso naturality `order_eq_order_restrict`).

References: Stacks 02ME, 02IZ, and 02MD.
-/

namespace Ring

/-- **`Ring.ord` naturality under a ring isomorphism.**
`ord R x = ord S (e x)`. The length of `R/(x)` as `R`-module equals the
length of `S/(e x)` as `S`-module: the `R`-linear equivalence
`R/(x) ≃ₗ[R] S/(e x)` (with the `S`-side equipped with `R`-module structure
via `e`) transports length across rings using `Module.length_eq_of_surjective`.

Project-local because Mathlib `b80f227` ships no `ord` naturality lemma. -/
lemma ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : R) : Ring.ord R x = Ring.ord S (e x) := by
  have heq : Ideal.span ({e x} : Set S) = Ideal.map (e : R →+* S) (Ideal.span {x}) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  letI alg : Algebra R S := e.toRingHom.toAlgebra
  haveI : IsScalarTower R S (S ⧸ Ideal.span ({e x} : Set S)) := by
    refine ⟨fun r s m => ?_⟩
    change (algebraMap R S r * s) • m = (algebraMap R S r) • (s • m)
    rw [mul_smul]
  let φ_ring : (R ⧸ Ideal.span ({x} : Set R)) ≃+* (S ⧸ Ideal.span ({e x} : Set S)) :=
    Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e heq
  let φ : (R ⧸ Ideal.span ({x} : Set R)) ≃ₗ[R] (S ⧸ Ideal.span ({e x} : Set S)) := by
    refine { φ_ring.toAddEquiv with map_smul' := ?_ }
    intro r m
    induction m using Quotient.inductionOn with
    | h y =>
      change Ideal.Quotient.mk _ (e (r * y)) = e r • Ideal.Quotient.mk _ (e y)
      rw [map_mul]; rfl
  unfold Ring.ord
  rw [φ.length_eq]
  exact Module.length_eq_of_surjective (S := R) (R := S) (M := S ⧸ Ideal.span {e x})
    e.surjective

/-- **`nonZeroDivisors` is preserved by a ring isomorphism.** Direct from
Mathlib's `MulEquivClass.map_nonZeroDivisors`. Project-local convenience
wrapper to phrase the result as an `Iff` instead of a `Submonoid.map` equality. -/
lemma nonZeroDivisors_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (r : R) :
    r ∈ nonZeroDivisors R ↔ e r ∈ nonZeroDivisors S := by
  rw [← MulEquivClass.map_nonZeroDivisors (e : R ≃* S)]
  refine ⟨fun h => ⟨r, h, rfl⟩, fun h => ?_⟩
  obtain ⟨r', hr', heq⟩ := h
  have : r = r' := e.injective heq.symm
  rw [this]; exact hr'

/-- **`Ring.ordMonoidWithZeroHom` naturality under a ring isomorphism.**
`ordMonoidWithZeroHom S (e r) = ordMonoidWithZeroHom R r`. Reduces to
`ord_ringEquiv` after splitting on `r ∈ nonZeroDivisors R`. -/
lemma ordMonoidWithZeroHom_ringEquiv {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [Nontrivial S] (e : R ≃+* S) (r : R) :
    Ring.ordMonoidWithZeroHom S (e r) = Ring.ordMonoidWithZeroHom R r := by
  unfold Ring.ordMonoidWithZeroHom
  simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  by_cases hr : r ∈ nonZeroDivisors R
  · have her : e r ∈ nonZeroDivisors S := (nonZeroDivisors_ringEquiv e r).mp hr
    simp [hr, her, ord_ringEquiv e r]
  · have her : e r ∉ nonZeroDivisors S := fun h =>
      hr ((nonZeroDivisors_ringEquiv e r).mpr h)
    simp [hr, her]

/-- **`Ring.ordFrac` naturality under compatible isomorphisms.**

Given a ring iso `e : R ≃+* S` between Noetherian Krull-dim-`≤ 1` integral
domains and a compatible fraction-field iso `e_K : K_R ≃+* K_S` (compatibility
`e_K (algebraMap R K_R r) = algebraMap S K_S (e r)` for `r : R`), the
order-of-vanishing function on the fraction fields is invariant:
`ordFrac S (e_K x) = ordFrac R x` for any `x : K_R`.

Proof: `x = 0` is the junk-zero branch. For `x ≠ 0`, write `x = mk' K_R a b`
with `a, b ∈ nonZeroDivisors R` via `IsLocalization.surj`. Then
`e_K x = mk' K_S (e a) (e b)` via the compatibility hypothesis, and both
sides reduce via Mathlib's `ordFrac_eq_div` to a quotient of
`ordMonoidWithZeroHom`-values, which agree by `ordMonoidWithZeroHom_ringEquiv`. -/
lemma ordFrac_ringEquiv {R S : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    {K_R K_S : Type*} [Field K_R] [Field K_S]
    [Algebra R K_R] [IsFractionRing R K_R]
    [Algebra S K_S] [IsFractionRing S K_S]
    (e : R ≃+* S) (e_K : K_R ≃+* K_S)
    (h_compat : ∀ r : R, e_K (algebraMap R K_R r) = algebraMap S K_S (e r))
    (x : K_R) :
    Ring.ordFrac S (e_K x) = Ring.ordFrac R x := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero, map_zero, map_zero]
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hb_nzd : (b : R) ∈ nonZeroDivisors R := b.2
  have hb_ne : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_nzd
  have h_inj_R : Function.Injective (algebraMap R K_R) := IsFractionRing.injective R K_R
  have hb_K_ne : algebraMap R K_R (b : R) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K_R), h_inj_R.eq_iff]
    exact hb_ne
  have ha_ne : a ≠ 0 := by
    intro ha
    subst ha
    rw [map_zero] at hab
    rcases mul_eq_zero.mp hab with hx' | hb_ne'
    · exact hx hx'
    · exact hb_K_ne hb_ne'
  have ha_nzd : a ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero ha_ne
  have he_b_nzd : e b ∈ nonZeroDivisors S := (nonZeroDivisors_ringEquiv e b).mp hb_nzd
  have he_a_nzd : e a ∈ nonZeroDivisors S := (nonZeroDivisors_ringEquiv e a).mp ha_nzd
  have hx_mk : x = IsLocalization.mk' K_R a ⟨b, hb_nzd⟩ := by
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, hab]
  have he_K_x : e_K x = IsLocalization.mk' K_S (e a) ⟨e b, he_b_nzd⟩ := by
    rw [eq_comm]
    refine (IsLocalization.mk'_eq_iff_eq_mul).mpr ?_
    rw [← h_compat a, ← h_compat b, ← map_mul]
    exact congrArg e_K hab.symm
  rw [he_K_x, hx_mk]
  rw [Ring.ordFrac_eq_div S ⟨e a, he_a_nzd⟩ ⟨e b, he_b_nzd⟩]
  rw [Ring.ordFrac_eq_div R ⟨a, ha_nzd⟩ ⟨b, hb_nzd⟩]
  congr 1
  · exact ordMonoidWithZeroHom_ringEquiv e a
  · exact ordMonoidWithZeroHom_ringEquiv e b

end Ring

namespace AlgebraicGeometry

/-! ## Function fields of open subschemes

There is a canonical isomorphism `U.toScheme.functionField ≅ X.functionField` for
integral `X` and nonempty open `U ⊆ X`, obtained by composing Mathlib's
`Scheme.Opens.stalkIso U (genericPoint U.toScheme)` with the transport across
the genericPoint equality `(U.ι (genericPoint U.toScheme)) = genericPoint X`
delivered by `genericPoint_eq_of_isOpenImmersion`.

This iso is the bridge that lets `Ring.ordFrac_ringEquiv` apply at the
scheme level (with `e_K = Scheme.Opens.functionFieldIso U` and `e =
Scheme.PrimeDivisor.stalkIso U Y hYU` for a prime divisor `Y` of `X` with
`Y.point ∈ U`).

Reference: Mathlib `AlgebraicGeometry.FunctionField.genericPoint_eq_of_isOpenImmersion`
+ `Scheme.PrimeDivisor.stalkIso`. -/

/-- **Function field isomorphism along an open immersion.** For an integral
scheme `X` and a nonempty open subscheme `U ⊆ X`, the function fields of
`U.toScheme` and `X` are canonically isomorphic. -/
noncomputable def Scheme.Opens.functionFieldIso {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    (U.toScheme).functionField ≅ X.functionField :=
  (Scheme.Opens.stalkIso U (genericPoint U.toScheme)).trans
    (X.presheaf.stalkCongr (by
      have heq : ((genericPoint U.toScheme : U.toScheme.carrier).val : X.carrier) =
          genericPoint X :=
        genericPoint_eq_of_isOpenImmersion U.ι
      rw [heq]
      exact Inseparable.refl _))

/-! ## §2. Order of a rational function at a prime divisor

For a scheme `X` satisfying `(*)`, every prime divisor `Y` carries a discrete
valuation `v_Y` on the function field `K(X)`. The order of a nonzero rational
function `f ∈ K(X)^×` along `Y` is the integer `ord_Y(f) := v_Y(f)`. -/

namespace Scheme.RationalMap

/-- **Order of a nonzero rational function `f ∈ K(X)^×` along a prime divisor `Y`.**

For `X` satisfying Hartshorne's `(*)`, the local ring `O_{X,η}` at the generic
point `η` of `Y` is a discrete valuation ring with quotient field the function
field `K(X)`, and `ord_Y(f) = v_Y(f) ∈ ℤ` is the value of the associated normalised
discrete valuation on `f`.

On a smooth proper curve `C` over `k̄`, every closed point `P ∈ C` is a prime
divisor and `ord_P(f) = v_P(f)` is the standard DVR valuation at `P`.

Blueprint reference: `def:order_at_point` (Hartshorne II §6 pp. 130–131; Stacks 02ME).

The definition uses Mathlib's `Ring.ordFrac` (the canonical
`K →*₀ ℤᵐ⁰` monoid-with-zero hom from
`Mathlib.RingTheory.OrderOfVanishing.Basic`, Stacks `02MD`) on the stalk
`X.presheaf.stalk Y.point`, then projects through `WithZero.log : ℤᵐ⁰ → ℤ`
(the canonical projection with junk-on-zero, `Mathlib.Algebra.GroupWithZero.WithZero`).
On `f = 0` this gives `order Y 0 = 0`. -/
noncomputable def order {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    (f : X.functionField) : ℤ :=
  WithZero.log (Ring.ordFrac (X.presheaf.stalk Y.point) f)

end Scheme.RationalMap

/-! ### Regular-in-codimension-one bridge class

Hartshorne's condition `(*)` includes "regular in codimension one", i.e.\ every
prime divisor `Y` of `X` has a DVR stalk `O_{X,Y.point}`. Mathlib has no direct
typeclass for this; we package it as the project-bespoke class
`Scheme.IsRegularInCodimensionOne`, with an instance synthesising the per-`Y`
Krull-dim-≤-1 condition required by `Scheme.RationalMap.order`. -/

/-- Project-bespoke class encoding Hartshorne's "regular in codimension one"
clause of `(*)`: every prime divisor `Y` of `X` has a DVR stalk
`O_{X,Y.point}`. The `[IsIntegral X]` precondition makes
`IsDomain (X.presheaf.stalk Y.point)` available so that the
`IsDiscreteValuationRing` predicate is well-formed
(`AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegral`). -/
class Scheme.IsRegularInCodimensionOne (X : Scheme.{u}) [IsIntegral X] : Prop where
  /-- The defining content: every prime divisor's stalk is a discrete valuation
  ring. (This is the precise content of Hartshorne's `(*)`; the weaker
  `Ring.KrullDimLE 1` derives via the `IsDiscreteValuationRing` ⟹
  `IsPrincipalIdealRing` ⟹ `Ring.KrullDimLE 1` chain via the bridge
  instance below.) -/
  out : ∀ Y : Scheme.PrimeDivisor X, IsDiscreteValuationRing (X.presheaf.stalk Y.point)

/-- Bridge instance: from `[Scheme.IsRegularInCodimensionOne X]`, typeclass
synthesis can derive `IsDiscreteValuationRing (X.presheaf.stalk Y.point)` for
every prime divisor `Y`. -/
instance Scheme.IsRegularInCodimensionOne.instIsDiscreteValuationRingStalk
    {X : Scheme.{u}} [IsIntegral X] [Scheme.IsRegularInCodimensionOne X]
    (Y : Scheme.PrimeDivisor X) :
    IsDiscreteValuationRing (X.presheaf.stalk Y.point) :=
  Scheme.IsRegularInCodimensionOne.out Y

/-- **Open-immersion descent for `IsRegularInCodimensionOne`.** The codim-1
regularity hypothesis transports along the open immersion `U.ι : U.toScheme ⟶ X`:
prime divisors of `U.toScheme`
push to prime divisors of `X` via `Scheme.PrimeDivisor.ofOpen`, and Mathlib's
`Scheme.Opens.stalkIso` gives the ring iso between stalks. We then transport
the `IsDiscreteValuationRing` property via
`IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`.

Reference: Stacks 02IZ (open-immersion stalks). -/
instance Scheme.IsRegularInCodimensionOne.instOpen
    {X : Scheme.{u}} [IsIntegral X] [Scheme.IsRegularInCodimensionOne X]
    (U : X.Opens) [IsIntegral U.toScheme] :
    Scheme.IsRegularInCodimensionOne U.toScheme := by
  refine ⟨fun YU => ?_⟩
  haveI hY : IsDiscreteValuationRing (X.presheaf.stalk YU.point.1) :=
    Scheme.IsRegularInCodimensionOne.out (Scheme.PrimeDivisor.ofOpen U YU)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (AlgebraicGeometry.Scheme.Opens.stalkIso U YU.point).symm.commRingCatIsoToRingEquiv

/-- Bridge instance: from `[Scheme.IsRegularInCodimensionOne X]`, typeclass
synthesis can derive `Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)` for every
prime divisor `Y`, via the `IsDiscreteValuationRing` ⟹ `IsPrincipalIdealRing`
⟹ `Ring.KrullDimLE 1` chain (Mathlib's `IsDiscreteValuationRing.toIsPrincipalIdealRing`
+ `IsPrincipalIdealRing.krullDimLE_one`). -/
instance Scheme.IsRegularInCodimensionOne.instKrullDimLEStalk
    {X : Scheme.{u}} [IsIntegral X] [Scheme.IsRegularInCodimensionOne X]
    (Y : Scheme.PrimeDivisor X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk Y.point) :=
  haveI : IsDiscreteValuationRing (X.presheaf.stalk Y.point) :=
    Scheme.IsRegularInCodimensionOne.out Y
  haveI : IsPrincipalIdealRing (X.presheaf.stalk Y.point) :=
    IsDiscreteValuationRing.toIsPrincipalIdealRing
  IsPrincipalIdealRing.krullDimLE_one _

/-- **Naturality of `Ring.ordFrac` across an open-immersion stalk isomorphism.**

This theorem combines the
`Scheme.PrimeDivisor.stalkIso U Y hYU` ring iso with a user-supplied
function-field iso `e_K` (typically the `Scheme.Opens.functionFieldIso U`)
and a compatibility hypothesis `h_compat` into the algebraic naturality
`Ring.ordFrac_ringEquiv`. -/
theorem Scheme.PrimeDivisor.ordFrac_stalkIso_naturality
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]
    (U : X.Opens) [Nonempty U] [IsIntegral U.toScheme]
    [Scheme.IsRegularInCodimensionOne U.toScheme]
    (Y : X.PrimeDivisor) (hYU : Y.point ∈ U)
    (e_K : U.toScheme.functionField ≃+* X.functionField)
    (h_compat : ∀ r : U.toScheme.presheaf.stalk
        (Scheme.PrimeDivisor.restrictToOpen U Y hYU).point,
      e_K (algebraMap _ U.toScheme.functionField r) =
        algebraMap _ X.functionField
          ((Scheme.PrimeDivisor.stalkIso U Y hYU).commRingCatIsoToRingEquiv r))
    (f : U.toScheme.functionField) :
    Ring.ordFrac (X.presheaf.stalk Y.point) (e_K f) =
      Ring.ordFrac (U.toScheme.presheaf.stalk
        (Scheme.PrimeDivisor.restrictToOpen U Y hYU).point) f :=
  Ring.ordFrac_ringEquiv
    (Scheme.PrimeDivisor.stalkIso U Y hYU).commRingCatIsoToRingEquiv
    e_K h_compat f

/-! ## Order under restriction to an open subscheme

We discharge the compatibility hypothesis of
`Scheme.PrimeDivisor.ordFrac_stalkIso_naturality`
with `e_K := Scheme.Opens.functionFieldIso U`, producing the user-facing
naturality `Scheme.PrimeDivisor.order_eq_order_restrict`:
`order Y (functionFieldIso U f) = order (restrictToOpen U Y hYU) f`.

The key is morphism-level commutativity in `CommRingCat`: the two ways of mapping the
stalk of `U.toScheme` at `Y` into `X.functionField` — first specialise to the
generic point of `U` then apply `functionFieldIso`, vs. first apply the
open-immersion `stalkIso` then specialise to the generic point of `X` —
agree. The proof is a germ-chase via `TopCat.Presheaf.stalk_hom_ext`,
`germ_stalkSpecializes`, and `Scheme.Opens.germ_stalkIso_hom`.

Reference: Stacks 02IZ (open-immersion stalks) + Mathlib's
`TopCat.Presheaf.germ_stalkSpecializes` + `Scheme.Opens.germ_stalkIso_hom`.
-/

/-- **Morphism-level compatibility for the function-field iso.** For an integral
scheme `X`, a nonempty integral open `U`, and a prime divisor `Y` of `X` with
`Y.point ∈ U`, the square
```
  stalk_U Y  --stalkSpec_U-->  functionField U
      |                              |
   stalkIso                     functionFieldIso
      v                              v
  stalk_X Y  --stalkSpec_X-->  functionField X
```
commutes in `CommRingCat`, where the horizontal maps are the canonical
`stalkSpecializes` maps to the respective generic points (i.e. the algebra
maps `O_{·,Y} → K(·)`). -/
theorem Scheme.PrimeDivisor.functionFieldIso_compat {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] [IsIntegral U.toScheme]
    (Y : X.PrimeDivisor) (hYU : Y.point ∈ U) :
    U.toScheme.presheaf.stalkSpecializes
        ((genericPoint_spec U.toScheme).specializes (Set.mem_univ
          (Scheme.PrimeDivisor.restrictToOpen U Y hYU).point)) ≫
        (Scheme.Opens.functionFieldIso U).hom =
      (Scheme.PrimeDivisor.stalkIso U Y hYU).hom ≫
        X.presheaf.stalkSpecializes
          ((genericPoint_spec X).specializes (Set.mem_univ Y.point)) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hxV
  have hcongr : ∀ {a b : X} (e : Inseparable a b),
      (X.presheaf.stalkCongr e).hom = X.presheaf.stalkSpecializes e.ge := by
    intros; rfl
  simp only [Scheme.PrimeDivisor.stalkIso, Scheme.Opens.functionFieldIso, Iso.trans_hom,
    restrictToOpen_point, hcongr]
  simp only [TopCat.Presheaf.germ_stalkSpecializes_assoc,
    Scheme.Opens.germ_stalkIso_hom_assoc]
  exact (TopCat.Presheaf.germ_stalkSpecializes _ _ _).trans
    (TopCat.Presheaf.germ_stalkSpecializes _ _ _).symm

/-- **Naturality of `Scheme.RationalMap.order` across the function-field iso.** For an
integral locally-Noetherian scheme `X` regular in codimension one, a nonempty
integral open `U`, a prime divisor `Y` of `X` with `Y.point ∈ U`, and a
rational function `f` of `U.toScheme`, the order of the transported function
`functionFieldIso U f` along `Y` equals the order of `f` along the restricted
prime divisor `restrictToOpen U Y hYU`. -/
theorem Scheme.PrimeDivisor.order_eq_order_restrict {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    (U : X.Opens) [Nonempty U] [IsIntegral U.toScheme]
    (Y : X.PrimeDivisor) (hYU : Y.point ∈ U)
    (f : U.toScheme.functionField) :
    Scheme.RationalMap.order Y
        ((Scheme.Opens.functionFieldIso U).commRingCatIsoToRingEquiv f) =
      Scheme.RationalMap.order (Scheme.PrimeDivisor.restrictToOpen U Y hYU) f := by
  have hcompat : ∀ r : U.toScheme.presheaf.stalk
      (Scheme.PrimeDivisor.restrictToOpen U Y hYU).point,
      (Scheme.Opens.functionFieldIso U).commRingCatIsoToRingEquiv
          (algebraMap _ U.toScheme.functionField r) =
        algebraMap _ X.functionField
          ((Scheme.PrimeDivisor.stalkIso U Y hYU).commRingCatIsoToRingEquiv r) := by
    intro r
    have hM := Scheme.PrimeDivisor.functionFieldIso_compat U Y hYU
    have happ := congrArg (fun φ => (CommRingCat.Hom.hom φ) r) hM
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at happ
    exact happ
  unfold Scheme.RationalMap.order
  rw [Scheme.PrimeDivisor.ordFrac_stalkIso_naturality U Y hYU
      (Scheme.Opens.functionFieldIso U).commRingCatIsoToRingEquiv hcompat f]

/-! ### Order-on-curve algebraic identities

These are per-prime-divisor algebraic identities on
`Scheme.RationalMap.order` — direct consequences of `Ring.ordFrac` being
a `K →*₀ ℤᵐ⁰` monoid-with-zero hom composed with `WithZero.log : ℤᵐ⁰ → ℤ`
(which is additive on nonzero arguments, junk-zero on `0`).

The lemmas:

- `Scheme.RationalMap.order_zero`: `ord_Y 0 = 0` (junk convention).
- `Scheme.RationalMap.order_mul_of_ne_zero`: `ord_Y (f·g) = ord_Y f +
  ord_Y g` when both `f, g ≠ 0`.
- `Scheme.RationalMap.order_units_inv`: `ord_Y u⁻¹ = -ord_Y u` for a
  unit `u : K(X)ˣ`.

Blueprint reference: `def:order_at_point` §2 (Hartshorne II §6 valuation
identities `v_Y(fg) = v_Y(f)+v_Y(g)`, `v_Y(f⁻¹) = -v_Y(f)`, `v_Y(1) = 0`). -/

/-- `ord_Y 0 = 0` by the junk-on-zero convention.

Direct from `Ring.ordFrac _` being a monoid-with-zero hom (`map_zero`)
and `WithZero.log_zero`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_zero
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)] :
    Scheme.RationalMap.order Y (0 : X.functionField) = 0 := by
  unfold Scheme.RationalMap.order
  rw [map_zero, WithZero.log_zero]

/-- `ord_Y (f · g) = ord_Y f + ord_Y g` when `f, g ≠ 0`.

Direct from `Ring.ordFrac _` being a monoid-with-zero hom (`map_mul`)
and `WithZero.log_mul` (which requires both factors nonzero). -/
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_mul_of_ne_zero
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    Scheme.RationalMap.order Y (f * g) =
      Scheme.RationalMap.order Y f + Scheme.RationalMap.order Y g := by
  unfold Scheme.RationalMap.order
  rw [map_mul]
  exact WithZero.log_mul ((map_ne_zero _).mpr hf) ((map_ne_zero _).mpr hg)

/-- `ord_Y f⁻¹ = -ord_Y f` for any `f : K(X)`.

The `f = 0` case is junk-vacuous (`f⁻¹ = 0` in a `GroupWithZero`, both sides
are zero). For `f ≠ 0` this is the DVR-valuation identity `v(f⁻¹) = -v(f)`.

Direct from `Ring.ordFrac _` being a monoid-with-zero hom (`map_inv₀`)
and `WithZero.log_inv` (which holds for all `WithZero (Multiplicative G)`
elements including zero, by the junk-on-zero convention). -/
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_inv
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    (f : X.functionField) :
    Scheme.RationalMap.order Y f⁻¹ = -Scheme.RationalMap.order Y f := by
  unfold Scheme.RationalMap.order
  rw [map_inv₀, WithZero.log_inv]

/-- `ord_Y u⁻¹ = -ord_Y u` for a unit `u : K(X)ˣ`.

A specialisation of `order_inv` to the unit form
`((u⁻¹ : K(X)ˣ) : K(X)) = (u : K(X))⁻¹`, useful at call sites that thread
`Units` (e.g. the `principal_hom : K(X)ˣ →* Multiplicative Div(X)` body). -/
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_units_inv
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    (u : (X.functionField)ˣ) :
    Scheme.RationalMap.order Y ((u⁻¹ : (X.functionField)ˣ) : X.functionField) =
      -Scheme.RationalMap.order Y (u : X.functionField) := by
  rw [show ((u⁻¹ : (X.functionField)ˣ) : X.functionField) =
        (u : X.functionField)⁻¹ from by simp]
  exact Scheme.RationalMap.order_inv Y _

/-- **`ord_Y (-f) = ord_Y f`** for any rational function `f`.

The argument: `(-f)^2 = f^2`, so taking `ordFrac` (a monoid-with-zero hom) and
then `WithZero.log_pow` gives `2 • ord_Y (-f) = 2 • ord_Y f` in `ℤ`. The free
action `(· • ·) : ℕ → ℤ → ℤ` cancels `2 ≠ 0`, giving the equality.

This sign-flip identity is useful in divisor-of-function calculations. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_neg
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    (f : X.functionField) :
    Scheme.RationalMap.order Y (-f) = Scheme.RationalMap.order Y f := by
  unfold Scheme.RationalMap.order
  have h : ((-f) ^ 2) = (f ^ 2) := by ring
  have h1 : (Ring.ordFrac (X.presheaf.stalk Y.point) (-f)) ^ 2 =
      (Ring.ordFrac (X.presheaf.stalk Y.point) f) ^ 2 := by
    rw [← map_pow, ← map_pow, h]
  have h2 : ((Ring.ordFrac (X.presheaf.stalk Y.point) (-f)) ^ 2).log =
      ((Ring.ordFrac (X.presheaf.stalk Y.point) f) ^ 2).log := by rw [h1]
  rw [WithZero.log_pow, WithZero.log_pow] at h2
  exact (smul_right_injective ℤ (by norm_num : (2 : ℕ) ≠ 0)) h2

/-- **`ord_Y (f^n) = n · ord_Y f`** for a nonzero rational function `f` and
natural number exponent `n`.

By induction on `n` from `order_mul_of_ne_zero` + `order_one`. The `f = 0`
hypothesis is necessary because the multiplicativity of `order` requires both
factors nonzero (otherwise `WithZero.log_mul` does not apply).

This is the order-theoretic input for the divisor identity
`div(f^n) = n · div(f)`. -/
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_pow_of_ne_zero
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    {f : X.functionField} (hf : f ≠ 0) (n : ℕ) :
    Scheme.RationalMap.order Y (f ^ n) = n * Scheme.RationalMap.order Y f := by
  induction n with
  | zero => simp [Scheme.RationalMap.order]
  | succ k ih =>
    rw [pow_succ, Scheme.RationalMap.order_mul_of_ne_zero Y (pow_ne_zero k hf) hf, ih]
    push_cast
    ring

/-! ### Finite support of the order function

The affine-chart minimal-primes core proving `rationalMap_order_finite_support`
under the `[IsNoetherian X]` hypothesis. The merely locally Noetherian statement
is false: the line with infinitely many origins is integral, locally Noetherian
and regular in codimension one, yet `t` has order one at infinitely many origins.
Global Noetherianness supplies the required quasi-compactness (Stacks 02RV).

The argument: a finite affine cover (from quasi-compactness) reduces to the
per-chart statement, where a codim-1 point of `X` inside an affine chart `U`
corresponds to a **height-one prime** `p` of `R := Γ(X, U)` (via
`ringKrullDim_stalk_eq_coheight` + `AtPrime.ringKrullDim_eq_height`); writing
`f = a/b` in `K = Frac R`, a point where `ord_Y f ≠ 0` must have `a ∈ p` or
`b ∈ p`, and a height-one prime containing a nonzero element is a minimal prime
over it (`Ideal.finite_minimalPrimes_of_isNoetherianRing`). -/

/-- **Height-one prime containing a nonzero element is minimal over it.** In a
domain `R`, a height-one prime `p` with `a ∈ p` (`a ≠ 0`) is a minimal prime of
the principal ideal `(a)`. Pure ring-theory substrate for the affine-chart
finiteness core. -/
private lemma mem_minimalPrimes_of_height_one {R : Type*} [CommRing R] [IsDomain R]
    {p : Ideal R} [p.IsPrime] (hp1 : p.height = 1) {a : R} (ha : a ≠ 0)
    (hap : a ∈ p) : p ∈ (Ideal.span {a}).minimalPrimes := by
  have hle : Ideal.span {a} ≤ p := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hap)
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hle
  haveI hqprime : q.IsPrime := hq.1.1
  have haq : a ∈ q := hq.1.2 (Ideal.subset_span (Set.mem_singleton a))
  have hqbot : q ≠ ⊥ := by
    intro h; rw [h] at haq; exact ha (by simpa using haq)
  have hqeqp : q = p := by
    rcases eq_or_lt_of_le hqp with h | h
    · exact h
    · exfalso
      haveI : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
      have hbotlt : (⊥ : Ideal R) < q := bot_lt_iff_ne_bot.mpr hqbot
      have hh1 : (⊥ : Ideal R).height + 1 ≤ q.height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hbotlt
      have hh2 : q.height + 1 ≤ p.height :=
        Ideal.height_add_one_le_of_lt_of_isPrime h
      rw [Ideal.height_bot, zero_add] at hh1
      have hqle : q.height ≤ 1 := hp1 ▸ Ideal.height_mono hqp
      have hqeq1 : q.height = 1 := le_antisymm hqle hh1
      rw [hqeq1, hp1] at hh2
      exact absurd hh2 (by decide)
  rw [← hqeqp]; exact hq

section FiniteSupport

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]

/-- **Atomic vanishing.** A chart section `r : Γ(X, U)` that does not vanish at
the codim-1 point `Y.point` (i.e. `r ∉ p_Y`, the prime of `R = Γ(X, U)` at `Y`)
has order zero along `Y`: `ord_Y (r) = 0`. The stalk `O_{X,Y}` is the localization
`R_{p_Y}` (`isLocalization_stalk`), `r` maps to a unit there, and `Ring.ordFrac`
of a unit is `1`. -/
private lemma order_algebraMap_eq_zero_of_notMem_primeIdealOf
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (Y : X.PrimeDivisor) (hYU : Y.point ∈ U)
    (r : Γ(X, U)) (hr : r ∉ (hU.primeIdealOf ⟨Y.point, hYU⟩).asIdeal) :
    Scheme.RationalMap.order Y (algebraMap Γ(X, U) X.functionField r) = 0 := by
  letI algSt : Algebra Γ(X, U) (X.presheaf.stalk Y.point) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨Y.point, hYU⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk Y.point)
      (hU.primeIdealOf ⟨Y.point, hYU⟩).asIdeal := hU.isLocalization_stalk ⟨Y.point, hYU⟩
  haveI hst : IsScalarTower Γ(X, U) (X.presheaf.stalk Y.point) X.functionField :=
    functionField_isScalarTower X U ⟨Y.point, hYU⟩
  have hunit : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk Y.point) r) :=
    IsLocalization.map_units (X.presheaf.stalk Y.point)
      (⟨r, hr⟩ : (hU.primeIdealOf ⟨Y.point, hYU⟩).asIdeal.primeCompl)
  have hne : algebraMap Γ(X, U) (X.presheaf.stalk Y.point) r ≠ 0 := hunit.ne_zero
  have hnzd : algebraMap Γ(X, U) (X.presheaf.stalk Y.point) r ∈
      nonZeroDivisors (X.presheaf.stalk Y.point) := mem_nonZeroDivisors_of_ne_zero hne
  unfold Scheme.RationalMap.order
  rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk Y.point) X.functionField r,
      Ring.ordFrac_eq_ord (X.presheaf.stalk Y.point) hne,
      Ring.ordMonoidWithZeroHom_eq_coe (X.presheaf.stalk Y.point) hnzd (n := 0)
        (by rw [Ring.ord_of_isUnit hunit]; simp)]
  simp

omit [IsIntegral X] [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X] in
/-- **Height of the chart prime is one.** For a prime divisor `Y` with generic
point in an affine chart `U`, the corresponding prime `p_Y := primeIdealOf` of
`R = Γ(X, U)` has height one. Combines `ringKrullDim_stalk_eq_coheight`
(codim-1 witness) with `IsLocalization.AtPrime.ringKrullDim_eq_height`. -/
private lemma primeIdealOf_height_eq_one {U : X.Opens} (hU : IsAffineOpen U)
    (Y : X.PrimeDivisor) (hYU : Y.point ∈ U) :
    (hU.primeIdealOf ⟨Y.point, hYU⟩).asIdeal.height = 1 := by
  letI algSt : Algebra Γ(X, U) (X.presheaf.stalk Y.point) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨Y.point, hYU⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk Y.point)
      (hU.primeIdealOf ⟨Y.point, hYU⟩).asIdeal := hU.isLocalization_stalk ⟨Y.point, hYU⟩
  have h1 := Scheme.ringKrullDim_stalk_eq_coheight X Y.point
  have h2 := IsLocalization.AtPrime.ringKrullDim_eq_height
      (hU.primeIdealOf ⟨Y.point, hYU⟩).asIdeal (X.presheaf.stalk Y.point)
  rw [Y.coheight] at h1
  rw [h1] at h2
  exact_mod_cast h2.symm

/-- **Per-chart finiteness.** On a single affine chart `U`, the set of prime
divisors meeting `U` at which a nonzero rational function `f` has nonzero order is
finite. Writing `f = a/b`, such a prime `p_Y` (height one) contains `a` or `b`,
hence lies in the finite union of minimal primes over `(a)` and `(b)`. -/
private lemma finite_chart_support {U : X.Opens} (hU : IsAffineOpen U)
    {f : X.functionField} (hf : f ≠ 0) :
    {Y : X.PrimeDivisor | Y.point ∈ U ∧ Scheme.RationalMap.order Y f ≠ 0}.Finite := by
  classical
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  by_cases hUe : Nonempty U
  swap
  · apply Set.Finite.subset Set.finite_empty
    rintro Y ⟨hYU, -⟩
    exact absurd ⟨⟨Y.point, hYU⟩⟩ hUe
  haveI := hUe
  haveI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, U)) f
  have hinj : Function.Injective (algebraMap Γ(X, U) X.functionField) :=
    IsFractionRing.injective _ _
  have hbne : (b : Γ(X, U)) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have halgb : algebraMap Γ(X, U) X.functionField (b : Γ(X, U)) ≠ 0 := fun h =>
    hbne (hinj (by rw [h, map_zero]))
  have hane : a ≠ 0 := by
    rintro rfl; rw [map_zero] at hab; exact (mul_ne_zero hf halgb) hab
  have halga : algebraMap Γ(X, U) X.functionField a ≠ 0 := fun h =>
    hane (hinj (by rw [h, map_zero]))
  have hfeq : f = algebraMap Γ(X, U) X.functionField a *
      (algebraMap Γ(X, U) X.functionField (b : Γ(X, U)))⁻¹ := by
    rw [← hab, mul_inv_cancel_right₀ halgb]
  -- the finite bounding set of primes
  have hBfin :
      ({q : PrimeSpectrum Γ(X, U) | q.asIdeal ∈ (Ideal.span {a}).minimalPrimes} ∪
        {q : PrimeSpectrum Γ(X, U) |
          q.asIdeal ∈ (Ideal.span {(b : Γ(X, U))}).minimalPrimes}).Finite := by
    refine Set.Finite.union ?_ ?_
    · exact (Ideal.finite_minimalPrimes_of_isNoetherianRing Γ(X, U)
        (Ideal.span {a})).preimage (Set.injOn_of_injective (fun _ _ h => PrimeSpectrum.ext h))
    · exact (Ideal.finite_minimalPrimes_of_isNoetherianRing Γ(X, U)
        (Ideal.span {(b : Γ(X, U))})).preimage
        (Set.injOn_of_injective (fun _ _ h => PrimeSpectrum.ext h))
  -- total map with junk value into PrimeSpectrum
  let junk : PrimeSpectrum Γ(X, U) := ⟨⊥, Ideal.isPrime_bot⟩
  let Φ : X.PrimeDivisor → PrimeSpectrum Γ(X, U) :=
    fun Y => if h : Y.point ∈ U then hU.primeIdealOf ⟨Y.point, h⟩ else junk
  apply Set.Finite.of_finite_image (f := Φ)
  · refine hBfin.subset ?_
    rintro q ⟨Y, ⟨hYU, hord⟩, rfl⟩
    simp only [Φ, dif_pos hYU]
    have hheight := primeIdealOf_height_eq_one hU Y hYU
    haveI : (hU.primeIdealOf ⟨Y.point, hYU⟩).asIdeal.IsPrime :=
      (hU.primeIdealOf ⟨Y.point, hYU⟩).isPrime
    have hmem : a ∈ (hU.primeIdealOf ⟨Y.point, hYU⟩).asIdeal ∨
        (b : Γ(X, U)) ∈ (hU.primeIdealOf ⟨Y.point, hYU⟩).asIdeal := by
      by_contra hcon
      rw [not_or] at hcon
      apply hord
      rw [hfeq,
        Scheme.RationalMap.order_mul_of_ne_zero Y halga (inv_ne_zero halgb),
        Scheme.RationalMap.order_inv,
        order_algebraMap_eq_zero_of_notMem_primeIdealOf hU Y hYU a hcon.1,
        order_algebraMap_eq_zero_of_notMem_primeIdealOf hU Y hYU (b : Γ(X, U)) hcon.2]
      ring
    rcases hmem with hmem | hmem
    · exact Or.inl (mem_minimalPrimes_of_height_one hheight hane hmem)
    · exact Or.inr (mem_minimalPrimes_of_height_one hheight hbne hmem)
  · rintro Y ⟨hYU, -⟩ Y' ⟨hY'U, -⟩ hΦ
    simp only [Φ, dif_pos hYU, dif_pos hY'U] at hΦ
    have := congrArg hU.fromSpec hΦ
    rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
    exact Scheme.PrimeDivisor.ext this

end FiniteSupport

/-- **Hartshorne II.6.1**: for a nonzero rational function `f` on a Noetherian
integral scheme `X` satisfying `(*)`, the order function `Y ↦ ord_Y(f)` is
nonzero at only finitely many prime divisors `Y`. This is the well-definedness
side condition for `Scheme.WeilDivisor.principal`.

The proof uses a finite affine cover and the fact that only finitely many
height-one primes can divide the numerator or denominator on each chart.

The statement is generic in `f` (no `f ≠ 0` hypothesis is threaded): on
`f = 0` the function `Y ↦ ord_Y(0) = WithZero.log 0 = 0` has empty support,
which is finite, so the conclusion holds vacuously. -/
theorem rationalMap_order_finite_support {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    (f : X.functionField) :
    (Function.support (fun Y : X.PrimeDivisor =>
      Scheme.RationalMap.order Y f)).Finite := by
  -- Case 1 (f = 0): the order function evaluates to
  -- `WithZero.log (Ring.ordFrac _ 0) = WithZero.log 0 = 0` at every
  -- prime divisor, so the support is empty (finite vacuously).
  by_cases hf : f = 0
  · subst hf
    convert Set.finite_empty
    ext Y
    simp only [Function.mem_support, ne_eq, Set.mem_empty_iff_false, iff_false,
      Decidable.not_not, Scheme.RationalMap.order_zero]
  -- Case 2 (f ≠ 0): Stacks 02RV. Global Noetherian = quasi-compact gives a
  -- FINITE affine cover `X = ⋃ᵢ Uᵢ`; every prime divisor's generic point lies in
  -- some `Uᵢ`, so the support is contained in the finite union of the per-chart
  -- supports, each finite by `finite_chart_support` (the affine-chart
  -- minimal-primes core).  Without `[CompactSpace X]` (equivalently
  -- `[IsNoetherian X]`) this fails: the line with infinitely many origins is a
  -- non-quasi-compact counterexample.
  · haveI : CompactSpace X := inferInstance
    set 𝒰 := X.affineCover.finiteSubcover with h𝒰
    refine Set.Finite.subset (Set.finite_iUnion fun i : 𝒰.I₀ =>
      finite_chart_support (isAffineOpen_opensRange (𝒰.f i)) hf) ?_
    intro Y hY
    refine Set.mem_iUnion.mpr ⟨𝒰.idx Y.point, ?_, hY⟩
    exact 𝒰.covers Y.point

namespace Scheme.WeilDivisor

variable {X : Scheme.{u}}

/-! ## §3. Divisor of a closed point on a curve

On a smooth proper curve `C` over a field, every closed point `P ∈ C` is a prime
divisor (it is closed, integral, of codimension one in the one-dimensional integral
scheme `C`). The associated Weil divisor is `[P] = 1 · P ∈ Div(C)`. -/

/-- **The Weil divisor associated to a closed point `P` on a curve.** The element
`[P] := 1 · P ∈ Div(C)`, i.e. the prime divisor `P` with multiplicity one.

For a smooth proper curve every closed point is automatically a prime divisor (it
is a codimension-one integral closed subscheme of the one-dimensional integral
scheme `C`); conversely every prime divisor on a curve is of this form, so an
arbitrary divisor on `C` is a finite formal `ℤ`-linear combination
`Σ nᵢ · [Pᵢ]` of closed points.

Blueprint reference: `def:divisor_closed_point` (Hartshorne II §6 p. 137).

The definition is zero outside its intended codimension-one scope. It
case-splits on `Order.coheight P = 1` (the codimension-one witness of
`PrimeDivisor`). On the branch where the equality holds — automatic for a
closed point on a one-dimensional integral scheme — we promote `P` to a
`PrimeDivisor` via the witness and return `Finsupp.single ⟨P, h⟩ 1`, i.e.
the prime divisor `P` with multiplicity one. On the off-branch (junk regime)
we return the zero divisor; see `ofClosedPoint_eq_single` for the equation in
the codimension-one regime. -/
noncomputable def ofClosedPoint {C : Scheme.{u}} (P : C)
    (_hP : IsClosed ({P} : Set C)) : C.WeilDivisor :=
  if h : Order.coheight P = 1 then Finsupp.single ⟨P, h⟩ 1 else 0

/-- In the hypothesised regime where the closed point `P` has coheight one
(the codim-1 condition automatic for a closed point of a one-dimensional
integral scheme), `ofClosedPoint P hP` is the prime divisor `P` with
multiplicity one. -/
lemma ofClosedPoint_eq_single {C : Scheme.{u}} (P : C)
    (hP : IsClosed ({P} : Set C)) (h : Order.coheight P = 1) :
    ofClosedPoint P hP = Finsupp.single ⟨P, h⟩ 1 := by
  simp [ofClosedPoint, h]

/-- Off-branch: outside the codim-1 regime, `ofClosedPoint` is junk-defined as
the zero divisor. (Only relevant when the user supplies a "closed point" that
does not have coheight one in the ambient scheme — e.g. a generic point or a
codim-≥2 point on a higher-dimensional scheme.) -/
lemma ofClosedPoint_eq_zero {C : Scheme.{u}} (P : C)
    (hP : IsClosed ({P} : Set C)) (h : Order.coheight P ≠ 1) :
    ofClosedPoint P hP = 0 := by
  simp [ofClosedPoint, h]

/-! ## §4. Degree of a divisor over an algebraically closed base -/

/-- **Degree of a Weil divisor on a smooth proper curve over `k̄`.**

Over an algebraically closed field `k̄`, every closed point of a smooth proper
curve `C` has residue field `k̄`, so each prime divisor `[P]` contributes degree
one to the sum, and `deg(D) := Σᵢ nᵢ` is the sum of the integer coefficients of
the formal sum `D = Σ nᵢ · [Pᵢ]`.

(Over a general field `k` one weights by the residue-field degrees
`Σᵢ nᵢ · [κ(Pᵢ) : k]` to recover the geometric degree; the project's RR bridge
needs only the `k̄` specialisation.)

Blueprint reference: `def:divisor_degree` (Hartshorne II §6 p. 137; Stacks 0BE0).

Implementation: `Finsupp.sum D (fun _ n => n)` is the sum of all coefficients of
the finitely supported function representing `D`. -/
noncomputable def degree (D : X.WeilDivisor) : ℤ :=
  (D : X.PrimeDivisor →₀ ℤ).sum (fun _ n => n)

/-- **The degree map is a group homomorphism `Div(C) → ℤ`.**

`deg(D₁ + D₂) = deg(D₁) + deg(D₂)`, `deg(-D) = -deg(D)`, `deg(0) = 0`. Bundled
as an `AddMonoidHom` for downstream use (the linear-equivalence quotient
`Cl(C) := Div(C) / im(div)` will inherit a `deg : Cl(C) → ℤ` from this).

Blueprint reference: `thm:divisor_degree_hom` (immediate from `def:divisor_degree`).

Implementation: built from `Finsupp.liftAddHom (fun _ ↦ AddMonoidHom.id ℤ)`, the
generic Mathlib packaging that lifts a family of `AddMonoidHom`s indexed by the
support into a single `AddMonoidHom` on the finsupp. Unfolds to
`D.sum (fun _ z ↦ z) = degree D` (see `degree_hom_apply` below). -/
noncomputable def degree_hom : X.WeilDivisor →+ ℤ :=
  Finsupp.liftAddHom (fun _ ↦ AddMonoidHom.id ℤ)

@[simp]
lemma degree_hom_apply (D : X.WeilDivisor) : degree_hom D = degree D :=
  Finsupp.liftAddHom_apply (α := X.PrimeDivisor) (M := ℤ) (N := ℤ)
    (fun _ ↦ AddMonoidHom.id ℤ) D

/-- **Degree of the zero divisor is zero.** A direct consequence of
`degree_hom` being an `AddMonoidHom`. -/
@[simp]
lemma degree_zero : degree (0 : X.WeilDivisor) = 0 := by
  rw [← degree_hom_apply]; exact map_zero _

/-- **Degree is additive.** A direct consequence of `degree_hom` being an
`AddMonoidHom`. -/
lemma degree_add (D₁ D₂ : X.WeilDivisor) :
    degree (D₁ + D₂) = degree D₁ + degree D₂ := by
  rw [← degree_hom_apply, ← degree_hom_apply, ← degree_hom_apply]
  exact map_add _ _ _

/-- **Degree of the negation.** `deg(-D) = -deg D`. A direct consequence of
`degree_hom` being an `AddMonoidHom`. -/
@[simp]
lemma degree_neg (D : X.WeilDivisor) :
    degree (-D) = -degree D := by
  rw [← degree_hom_apply, ← degree_hom_apply]
  exact map_neg _ _

/-- **Degree is subtractive.** `deg(D₁ - D₂) = deg D₁ - deg D₂`. A direct
consequence of `degree_hom` being an `AddMonoidHom`. -/
lemma degree_sub (D₁ D₂ : X.WeilDivisor) :
    degree (D₁ - D₂) = degree D₁ - degree D₂ := by
  rw [← degree_hom_apply, ← degree_hom_apply, ← degree_hom_apply]
  exact map_sub _ _ _

/-! ## §5. Principal divisors -/

/-- **The principal divisor of a nonzero rational function `f ∈ K(X)^×`.**

By Hartshorne's Lemma 6.1, `ord_Y(f) = 0` for all but finitely many prime
divisors `Y`, so the formal sum
`div(f) := Σ_{Y prime divisor} ord_Y(f) · Y ∈ Div(X)`
has finite support and is a well-defined Weil divisor.

On a smooth proper curve `C` over `k̄`, this specialises to
`div(f) = Σ_{P closed point} ord_P(f) · [P]`.

Blueprint reference: `def:principal_divisor` (Hartshorne II §6 Lemma 6.1 +
following definition, p. 131).

The construction uses `Finsupp.ofSupportFinite` with the finite-support
witness `rationalMap_order_finite_support` (Hartshorne 6.1 / Stacks 02RV),
which is proved under `[IsNoetherian X]` via a finite affine cover and the
height-one/minimal-primes bound on each chart. -/
noncomputable def principal [IsIntegral X] [IsNoetherian X]
    [Scheme.IsRegularInCodimensionOne X] (f : X.functionField)
    (_hf : f ≠ 0) : X.WeilDivisor :=
  Finsupp.ofSupportFinite
    (fun Y : X.PrimeDivisor => Scheme.RationalMap.order Y f)
    (rationalMap_order_finite_support f)

/-- **The coefficient of `principal f hf` at a prime divisor `Y` is the order of
`f` along `Y`.** This is the basic structural unfolding of the
`Finsupp.ofSupportFinite` packaging in `principal`; one-line via
`Finsupp.ofSupportFinite_coe` from `Mathlib.Data.Finsupp.Defs`. -/
lemma principal_apply [IsIntegral X] [IsNoetherian X]
    [Scheme.IsRegularInCodimensionOne X] (f : X.functionField) (hf : f ≠ 0)
    (Y : X.PrimeDivisor) :
    (show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y =
      Scheme.RationalMap.order Y f := by
  change (Finsupp.ofSupportFinite
      (fun Y : X.PrimeDivisor => Scheme.RationalMap.order Y f)
      (rationalMap_order_finite_support f)) Y = _
  rw [Finsupp.ofSupportFinite_coe]

/-- **`Scheme.RationalMap.order Y 1 = 0`** — the order of the constant
function `1` is `0` at every prime divisor. Direct from
`map_one` of `Ring.ordFrac` + `WithZero.log_one`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_one
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)] :
    Scheme.RationalMap.order Y (1 : X.functionField) = 0 := by
  unfold Scheme.RationalMap.order
  rw [map_one, WithZero.log_one]

/-- **The principal divisor of the constant function `1` is the zero
divisor.** A direct consequence of `Scheme.RationalMap.order_one`. -/
@[simp]
lemma principal_one [IsIntegral X] [IsNoetherian X]
    [Scheme.IsRegularInCodimensionOne X] :
    principal (1 : X.functionField) one_ne_zero = 0 := by
  change (_ : X.PrimeDivisor →₀ ℤ) = (0 : X.PrimeDivisor →₀ ℤ)
  apply Finsupp.ext
  intro Y
  rw [principal_apply]
  exact Scheme.RationalMap.order_one Y

/-- **The principal-divisor map is a group homomorphism `K(X)^× → Div(X)`.**

Concretely `div(fg) = div(f) + div(g)`, `div(f⁻¹) = -div(f)`, `div(1) = 0`. Bundled
as a `MonoidHom` from the multiplicative units of `K(X)` to `Multiplicative (Div(X))`
(equivalently: an additive map `(K(X)^×, ·) → (Div(X), +)`).

Blueprint reference: `thm:principal_hom` (Hartshorne II §6 p. 131).

The homomorphism laws close coordinate-wise from the DVR identities
`v_Y(fg) = v_Y(f) + v_Y(g)` and `v_Y(1) = 0`. The per-`Y` identities live in
`Scheme.RationalMap.order` via `Ring.ordFrac` (a `K →*₀ ℤᵐ⁰` monoid-with-zero
hom) and `WithZero.log_mul` / `WithZero.log_one`. -/
noncomputable def principal_hom [IsIntegral X] [IsNoetherian X]
    [Scheme.IsRegularInCodimensionOne X] :
    (X.functionField)ˣ →* Multiplicative X.WeilDivisor where
  toFun u :=
    Multiplicative.ofAdd (principal (↑u : X.functionField) (Units.ne_zero u))
  map_one' := by
    -- Goal: Multiplicative.ofAdd (principal ↑1 _) = 1.
    -- Use `← ofAdd_zero` to rewrite RHS as `Multiplicative.ofAdd 0`,
    -- then `congr 1` reduces to `principal ↑1 _ = 0` (Finsupp equality),
    -- and `Finsupp.ext` peels to the per-`Y` coordinate identity, which
    -- closes by unfolding `order` to `WithZero.log (Ring.ordFrac _ 1) = 0`
    -- via `map_one` and `WithZero.log_one`.
    rw [← ofAdd_zero]
    congr 1
    apply Finsupp.ext
    intro Y
    change Scheme.RationalMap.order Y
        (((1 : (X.functionField)ˣ) : X.functionField)) = 0
    rw [Units.val_one]
    unfold Scheme.RationalMap.order
    rw [map_one, WithZero.log_one]
  map_mul' u v := by
    -- Goal: Multiplicative.ofAdd (principal ↑(u*v) _) =
    --       Multiplicative.ofAdd (principal ↑u _) * Multiplicative.ofAdd (principal ↑v _).
    -- Use `← ofAdd_add` to rewrite RHS, then `congr 1` reduces to
    -- `principal ↑(u*v) _ = principal ↑u _ + principal ↑v _` (Finsupp
    -- equality), and `Finsupp.ext` peels to the per-`Y` coordinate
    -- identity `order Y (uv) = order Y u + order Y v`, which closes by
    -- `Ring.ordFrac (uv) = Ring.ordFrac u * Ring.ordFrac v` (`map_mul`)
    -- and `WithZero.log_mul` (the nonzero hypotheses come from
    -- `Units.ne_zero` and `map_ne_zero`).
    rw [← ofAdd_add]
    congr 1
    apply Finsupp.ext
    intro Y
    change Scheme.RationalMap.order Y ((↑(u * v) : X.functionField))
      = Scheme.RationalMap.order Y (↑u : X.functionField)
      + Scheme.RationalMap.order Y (↑v : X.functionField)
    rw [Units.val_mul]
    unfold Scheme.RationalMap.order
    rw [map_mul]
    exact WithZero.log_mul
      ((map_ne_zero _).mpr (Units.ne_zero u))
      ((map_ne_zero _).mpr (Units.ne_zero v))

/-- **Principal divisors on a complete nonsingular curve have degree zero**
(Hartshorne Corollary II.6.10, Stacks 0BE3).

For every nonzero rational function `f ∈ K(C)^×` on a smooth proper curve `C`
over an algebraically closed field `k̄`,
`deg(div(f)) = 0 ∈ ℤ`.

Blueprint reference: `thm:principal_deg_zero` (Hartshorne II.6 Cor. 6.10 p. 138).

**PROVED (run 0067) via the χ-ledger, not via Hartshorne's `φ : C → ℙ¹` argument.**
Hartshorne 6.10 splits on whether `f` is constant and, in the non-constant case,
exhibits `K(C)` as a finite extension of `k̄(f) ≅ k̄(t)` to get a finite
`φ : C → ℙ¹_{k̄}` with `div(f) = φ^*([0] - [∞])`. That route needs two geometric
sub-lemmas this project does not have (the finite morphism induced by a
non-constant rational function, and multiplicativity of degree under finite
pullback).

The route taken instead needs neither, and needs **no case split**: the ported
χ-ledger `χ(𝒪(D)) = χ(𝒪_C) + deg D` (`Ledger/ChiLedger.chi_divisorSheaf`, a
dévissage induction over closed points with skyscraper quotients) yields
`deg (div g) = 0` by transporting `χ` along the multiplication isomorphism
`𝒪(0) ≅ 𝒪(-div g)` and cancelling. Three carrier comparisons connect that to the
statement here, and each is discharged rather than assumed:

* the **order functions** agree — `Ledger/OrdCompare.ordZ_toAdd_eq_log_ordFrac`
  identifies the ledger's `ordZ`, read additively, with the `Ring.ordFrac`-based
  `Scheme.RationalMap.order` used by `principal`, *with no sign correction*;
* the **index sets** agree — `X.PrimeDivisor ≃ {x // x ≠ genericPoint X}`, built
  inline below from `PrimeDivisor.point_ne_genericPoint` and
  `one_le_coheight_of_ne_genericPoint` against `Adelic.coheight_le_one_of_curve`;
* the **degree weightings** agree over `k̄` — `Ledger/ResidueOneAlgClosed` collapses
  the ledger's residue-weighted `Σ nₓ·[κ(x):k]` to the bare coefficient sum that
  `degree` computes. This is where `[IsAlgClosed kbar]` is load-bearing; over a
  general field the two degrees are genuinely different numbers.

Since the argument is uniform in `f`, the constant case is not special: a constant
`f` simply has every coefficient zero, and the same chain returns `0`. -/
theorem principal_degree_zero {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (C : Over (Spec (.of kbar))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsIntegral C.left] [IsNoetherian C.left]
    [Scheme.IsRegularInCodimensionOne C.left]
    (f : C.left.functionField) (hf : f ≠ 0) :
    degree (principal f hf) = 0 := by
  -- The coheight bound at every point of the curve.  This is the ONE input that had been
  -- recorded across this lane as "strictly downstream and unavailable here": it is not.
  -- `Adelic.coheight_le_one_of_curve` sits in an import cone of three files besides itself
  -- (`Albanese.CoheightBridge`, `Picard.ProjectiveSpace`, `Adelic.P1BaseCase`), all of which
  -- this module already reaches through `Genus`.
  have hdim : ∀ z : C.left, Order.coheight z ≤ 1 :=
    fun z => AlgebraicGeometry.Adelic.coheight_le_one_of_curve C z
  letI : C.left.Over (Spec (CommRingCat.of kbar)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of kbar)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of kbar)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (CommRingCat.of kbar)) :=
    inferInstanceAs (QuasiCompact C.hom)
  -- `f` is a unit of the function field: a nonzero element of a field.  The ledger's principal
  -- divisor is indexed by units, this file's by nonzero elements.
  have hgu : IsUnit f := isUnit_iff_ne_zero.mpr hf
  set g : C.left.functionFieldˣ := hgu.unit with hgdef
  have hgval : (g : C.left.functionField) = f := rfl
  -- THE LEDGER INPUT, over `k̄`: the bare coefficient sum of the ported `divOf` vanishes.
  -- `Ledger/ResidueOneAlgClosed.sum_divOf_eq_zero_of_isAlgClosed` composes
  -- `ChiLedger.deg_divOf` (weighted degree zero, from the χ-ledger) with the residue-weight
  -- collapse over `k̄`, and discharges both `Module.Finite` cohomology binders at the curve.
  have hledger : (Scheme.divOf (C.left ↘ Spec (CommRingCat.of kbar)) g).sum
      (fun _ n => n) = 0 :=
    AlgebraicGeometry.sum_divOf_eq_zero_of_isAlgClosed C g
  -- THE INDEX COMPARISON, inline.  `RiemannRoch/CurveCoheight.PrimeDivisor.equivNonGeneric`
  -- is this equivalence, but that file imports *this* one, so it is used here in the two-line
  -- form it packages: `point_ne_genericPoint` one way, and `le_antisymm` of the coheight bound
  -- against `one_le_coheight_of_ne_genericPoint` the other.
  let e : C.left.PrimeDivisor ≃ {x : C.left // x ≠ genericPoint C.left} :=
    { toFun := fun Y => ⟨Y.point, Y.point_ne_genericPoint⟩
      invFun := fun x => ⟨x.1, le_antisymm (hdim _)
        (Scheme.one_le_coheight_of_ne_genericPoint x.2)⟩
      left_inv := fun Y => by ext; rfl
      right_inv := fun x => by ext; rfl }
  -- The relabelled `principal f hf` IS the ledger's `divOf g`, coefficient by coefficient.
  -- `Ring.KrullDimLE 1` at the stalk comes from regularity in codimension one, read at the
  -- prime divisor that `e.symm` produces — which is where the coheight bound is consumed.
  have hEq : Finsupp.equivMapDomain e (principal f hf : C.left.PrimeDivisor →₀ ℤ)
      = Scheme.divOf (C.left ↘ Spec (CommRingCat.of kbar)) g := by
    ext y
    haveI : Ring.KrullDimLE 1 (C.left.presheaf.stalk (y : C.left)) :=
      Scheme.IsRegularInCodimensionOne.instKrullDimLEStalk (e.symm y)
    rw [Scheme.divOf_apply _ g y.2, Finsupp.equivMapDomain_apply]
    change Scheme.RationalMap.order (e.symm y) f = _
    exact (Scheme.ordZ_toAdd_eq_log_ordFrac _ g y.2).symm
  -- `degree` is the coefficient sum on EITHER index set: relabelling along a bijection leaves a
  -- finite sum unchanged, and the summand `fun _ n => n` ignores the index, so both side
  -- conditions of `Finsupp.sum_mapDomain_index` are `rfl`.  No correction term.
  have hdeg : degree (principal f hf)
      = (Finsupp.equivMapDomain e (principal f hf : C.left.PrimeDivisor →₀ ℤ)).sum
        (fun _ n => n) := by
    rw [Finsupp.equivMapDomain_eq_mapDomain,
      Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    rfl
  rw [hdeg, hEq, hledger]

/-! ## §6. Positive part of a Weil divisor

The carrier
`X.WeilDivisor = X.PrimeDivisor →₀ ℤ` is a finitely supported integer-valued
function on prime divisors; the *positive part* `(D)_0` is obtained by
replacing each coefficient `n_Y` with `max(n_Y, 0)`. Equivalently this is
the lattice join `D ⊔ 0` in the pointwise lattice structure (the
`semilatticeSup` instance on `Finsupp` is noncomputable). The complementary
*negative part* `(D)_∞ := (-D)_0` then gives the canonical decomposition
`D = (D)_0 - (D)_∞` into a difference of effective divisors.

Blueprint reference: `def:WeilDivisor_positivePart` in
`RiemannRoch_WeilDivisor.tex`.
-/

/-- **Positive part of a Weil divisor**.

`positivePart D` is the divisor obtained from `D` by replacing each
coefficient `n_Y` with `max(n_Y, 0)` (equivalently `D ⊔ 0` in the
pointwise lattice structure on `Finsupp`). For `D = div(f)` on a smooth
proper curve `C`, this recovers the divisor-of-zeros `(f)_0` — the
formal sum of the zeros of `f` with their multiplicities.

The complementary `negativePart D := positivePart (-D)` then gives
`D = positivePart D - negativePart D` as a difference of effective
divisors.

Implementation: `Finsupp.mapRange (fun n : ℤ => n ⊔ 0) (by simp)`, the
generic Mathlib packaging that maps a finsupp's coefficients through a
zero-preserving function. (The `D ⊔ 0` lattice form is equivalent but
requires the noncomputable `Finsupp.semilatticeSup` synthesis on
`PrimeDivisor →₀ ℤ`; the explicit `mapRange` form is more transparent
to typeclass synthesis.)

Blueprint reference: `def:WeilDivisor_positivePart` (project-bespoke;
chapter `RiemannRoch_WeilDivisor.tex` §6, Hartshorne II.6.10 phrasing). -/
noncomputable def positivePart (D : X.WeilDivisor) : X.WeilDivisor :=
  Finsupp.mapRange (fun n : ℤ => n ⊔ 0) (by simp) D

/-- The positive part of the zero divisor is zero. -/
@[simp]
lemma positivePart_zero : positivePart (0 : X.WeilDivisor) = 0 := by
  change Finsupp.mapRange (fun n : ℤ => n ⊔ 0) (by simp)
    (0 : X.PrimeDivisor →₀ ℤ) = (0 : X.PrimeDivisor →₀ ℤ)
  exact Finsupp.mapRange_zero

/-- **Degree of positive part as a sum of capped coefficients.** A purely
symbolic Mathlib manipulation: unfolding `positivePart`
(= `Finsupp.mapRange (max · 0)`) and `degree` (= `Finsupp.sum (fun _ n => n)`)
identifies `degree (positivePart D)` with the sum of `max (D Y) 0` over
the support of `D`.

The proof uses `Finsupp.sum_mapRange_index` from
`Mathlib.Algebra.BigOperators.Finsupp.Basic`. -/
lemma degree_positivePart_eq_sum_max (D : X.WeilDivisor) :
    degree (positivePart D) = D.sum (fun _ n => max n 0) := by
  unfold positivePart degree
  exact Finsupp.sum_mapRange_index (h := fun _ b => b) (by intro _; rfl)

/-- **Positive part of a `Finsupp.single`.** Pointwise extraction of the
mapRange definition of `positivePart`: for a one-point-supported Weil divisor
`Finsupp.single Y n`, the positive part is `Finsupp.single Y (max n 0)`.
A direct consequence of `Finsupp.mapRange_single` (with `max 0 0 = 0` as
the zero-preservation witness). -/
@[simp]
lemma positivePart_single (Y : X.PrimeDivisor) (n : ℤ) :
    positivePart (Finsupp.single Y n : X.WeilDivisor) =
      Finsupp.single Y (max n 0) := by
  change Finsupp.mapRange (fun n : ℤ => n ⊔ 0) (by simp)
      (Finsupp.single Y n) = _
  rw [Finsupp.mapRange_single]

/-- **Degree of a `Finsupp.single` Weil divisor.** The degree of the
one-point-supported Weil divisor `Finsupp.single Y n` is `n`. A direct
consequence of `Finsupp.sum_single_index`. -/
@[simp]
lemma degree_single (Y : X.PrimeDivisor) (n : ℤ) :
    degree (Finsupp.single Y n : X.WeilDivisor) = n := by
  unfold degree
  change (Finsupp.single Y n : X.PrimeDivisor →₀ ℤ).sum (fun _ n => n) = n
  exact Finsupp.sum_single_index rfl

/-- **Sum-over-prime-divisors lower bound via a single contributing point.**
If `f` has order `1` at some prime divisor `Y₀`, then the degree of the positive
part of `principal f hf` is at least `1`. -/
lemma one_le_degree_positivePart_principal_of_order_one
    [IsIntegral X] [IsNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]
    (f : X.functionField) (hf : f ≠ 0) (Y₀ : X.PrimeDivisor)
    (h₀ : Scheme.RationalMap.order Y₀ f = 1) :
    1 ≤ degree (positivePart (principal f hf)) := by
  classical
  rw [degree_positivePart_eq_sum_max]
  -- The sum is over a finset; isolate the Y₀ contribution.
  have hY₀_supp :
      Y₀ ∈ (show (X.PrimeDivisor →₀ ℤ) from principal f hf).support := by
    rw [Finsupp.mem_support_iff]
    rw [principal_apply]
    rw [h₀]
    exact one_ne_zero
  -- For the sum to be ≥ 1, isolate the Y₀ term (= 1) and the rest (≥ 0).
  have h_split :
      (show (X.PrimeDivisor →₀ ℤ) from principal f hf).sum
          (fun _ n => max n 0) =
        max ((show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y₀) 0 +
          ((show (X.PrimeDivisor →₀ ℤ) from principal f hf).support.erase Y₀).sum
            (fun Y => max
              ((show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y) 0) := by
    rw [show (show (X.PrimeDivisor →₀ ℤ) from principal f hf).sum
            (fun _ n => max n 0) =
          (show (X.PrimeDivisor →₀ ℤ) from principal f hf).support.sum
            (fun Y => max
              ((show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y) 0)
        from rfl]
    rw [Finset.sum_erase_eq_sub hY₀_supp]
    ring
  rw [h_split]
  -- The Y₀ term equals max 1 0 = 1.
  have hY₀_val :
      (show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y₀ = 1 := by
    rw [principal_apply]; exact h₀
  rw [hY₀_val]
  -- The remainder is a sum of non-negative integers, hence ≥ 0.
  have h_nonneg :
      0 ≤ ((show (X.PrimeDivisor →₀ ℤ) from principal f hf).support.erase Y₀).sum
        (fun Y => max
          ((show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y) 0) :=
    Finset.sum_nonneg (fun Y _ => le_max_right _ _)
  -- Conclude: 1 = max 1 0 ≤ max 1 0 + 0 ≤ LHS + remainder.
  have : (max (1 : ℤ) 0) = 1 := by norm_num
  rw [this]
  linarith

/-- **Generic Finsupp identity**: the sum of clipped non-negative parts equals
the sum of the coefficients over the positive-coefficient sub-support.

For a finsupp `D : α →₀ ℤ`, `D.sum (max · 0)` agrees with the unclipped sum
`∑ D` restricted to the finset `{a ∈ supp D | 0 < D a}`. Negative-coefficient
points contribute `0` to the max and drop out; positive-coefficient points
contribute `D a` to both sides; the (vacuously zero) `D a = 0` case is excluded
by the `supp` filter on both sides. -/
lemma _root_.Finsupp.sum_max_zero_eq_sum_filter_pos {α : Type*}
    (D : α →₀ ℤ) :
    D.sum (fun _ n => max n 0) =
      ∑ a ∈ D.support.filter (fun a => 0 < D a), D a := by
  classical
  rw [Finsupp.sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hpos : 0 < D a
  · simp [hpos]
    omega
  · simp [hpos]
    omega

/-! ## §7. Linear equivalence and the divisor class group -/

/-- **Linear equivalence of Weil divisors.**

Two Weil divisors `D, D' ∈ Div(X)` are linearly equivalent, written `D ~ D'`, if
and only if there exists a nonzero rational function `f ∈ K(X)^×` with
`D - D' = div(f) ∈ Div(X)`.

`~` is an equivalence relation (reflexivity from `div(1) = 0`, symmetry from
`div(f⁻¹) = -div(f)`, transitivity from `div(fg) = div(f) + div(g)`, all via
`thm:principal_hom`). The quotient `Cl(X) := Div(X) / im(div)` is the
**divisor class group** of `X`.

On a smooth proper curve `C` over `k̄`, `thm:principal_deg_zero` shows the
degree map descends to `deg : Cl(C) → ℤ`.

Blueprint reference: `def:linear_equivalence` (Hartshorne II §6 p. 131). -/
def LinearEquivalence [IsIntegral X] [IsNoetherian X]
    [Scheme.IsRegularInCodimensionOne X] (D D' : X.WeilDivisor) : Prop :=
  ∃ (f : X.functionField) (hf : f ≠ 0), D - D' = principal f hf

end Scheme.WeilDivisor

end AlgebraicGeometry
