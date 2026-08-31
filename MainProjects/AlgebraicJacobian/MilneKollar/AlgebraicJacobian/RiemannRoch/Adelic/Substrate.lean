/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.RiemannRoch.WeilDivisor

/-!
# Adelic Riemann–Roch lane — Tier-0 substrate (nodes N1–N4)

This file implements the Tier-0 substrate of the adelic Riemann–Roch lane
(design document §3, nodes N1–N4), built directly on top of the project's
`AlgebraicJacobian.RiemannRoch.WeilDivisor` substrate (`PrimeDivisor`,
`RationalMap.order`, `IsRegularInCodimensionOne`, `WeilDivisor`).

* **N2 `pointValuation`** — for a prime divisor `P` of a scheme `X` regular in
  codimension one, the DVR stalk `O_{X,P}` carries the height-one-spectrum adic
  valuation `v_P` on the function field `K(X)`; we identify the project's
  `Scheme.RationalMap.order P` with `-log ∘ v_P` (`order_eq_neg_log_pointValuation`).
* **N3 `sectionOfDivisor`** — the Riemann–Roch section subgroup
  `Γ(U, 𝒪_X(D)) = { f ∈ K(X) : ∀ P ∈ U, ord_P f ≥ -D(P) }` as an
  `AddSubgroup K(X)`, together with the elementary order laws (monotonicity in
  `D`, the `min`/`⊔`-intersection identities, `1 ∈ L(0)`).
* **N1 `HasDedekindChart`** — the gate class packaging "every nonempty affine
  chart `Γ(X, U)` is a Dedekind domain" (design §4), with the Dedekind-from-DVR
  bridge `isDedekindDomain_of_forall_isLocalization_dvr`.
* **N4** — the affine-chart finiteness building block: on a Dedekind chart the
  set of height-one places at which a rational function is non-integral is finite
  (`IsDedekindDomain.HeightOneSpectrum.Support.finite`).

## The `RationalMap.order` ultrametric

The one genuinely new analytic input is that `Scheme.RationalMap.order P` obeys
the ultrametric inequality `ord_P (f + g) ≥ min (ord_P f) (ord_P g)`, which makes
`sectionOfDivisor` closed under addition. It is derived from mathlib's
`Ring.ordFrac_eq_valuation_inv` (the DVR order-of-vanishing is the inverse of the
maximal-ideal adic valuation) plus `Valuation.map_add` and the monotonicity of
`WithZero.log` on nonzero elements.

## References

Design document `adelic-rr-lane-design.md` §§1–4; Stichtenoth,
*Algebraic Function Fields and Codes*, ch. 1; Hartshorne, *Algebraic Geometry*
II §6; Stacks 02RV, 02MD, 02IZ.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits IsDedekindDomain
open scoped WithZero

namespace AlgebraicGeometry
namespace Adelic

/-! ## §N2. The point valuation of a prime divisor -/

section PointValuation

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]

/-- **N2 — the point valuation `v_P`.** For a prime divisor `P` of a scheme `X`
that is regular in codimension one, the DVR stalk `O_{X,P.point}` has a maximal
ideal in its height-one spectrum, and the associated adic valuation of the
function field `K(X)` is the discrete valuation `v_P : K(X) → ℤᵐ⁰` at `P`. -/
noncomputable def pointValuation (P : X.PrimeDivisor) :
    Valuation X.functionField ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk P.point)).valuation
    X.functionField

/-- **N2 identification.** The project's `Scheme.RationalMap.order P` equals
`-log ∘ v_P`, i.e. the additive normalisation of the point valuation `v_P`. This
is the bridge between the `Ring.ordFrac`-based `order` and mathlib's
height-one-spectrum adic valuation. -/
theorem order_eq_neg_log_pointValuation (P : X.PrimeDivisor)
    (f : X.functionField) :
    Scheme.RationalMap.order P f = -(WithZero.log (pointValuation P f)) := by
  unfold Scheme.RationalMap.order pointValuation
  rw [Ring.ordFrac_eq_valuation_inv, WithZero.log_inv]

/-- **The `order` ultrametric.** For nonzero `f, g` with `f + g ≠ 0`, the order of
the sum is at least the minimum of the orders. This is the valuation-theoretic
triangle inequality `v_P(f + g) ≥ min (v_P f) (v_P g)` for the additive
normalisation `ord_P = -log ∘ v_P`; it is what makes `sectionOfDivisor` closed
under addition. -/
theorem order_add_ge_min (P : X.PrimeDivisor) {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (Scheme.RationalMap.order P f) (Scheme.RationalMap.order P g) ≤
      Scheme.RationalMap.order P (f + g) := by
  simp only [order_eq_neg_log_pointValuation]
  set v := pointValuation P with hv
  have hvf : v f ≠ 0 := by simpa [hv] using (Valuation.zero_iff v).not.mpr hf
  have hvg : v g ≠ 0 := by simpa [hv] using (Valuation.zero_iff v).not.mpr hg
  have hvfg : v (f + g) ≠ 0 := by simpa [hv] using (Valuation.zero_iff v).not.mpr hfg
  have hadd : v (f + g) ≤ max (v f) (v g) := v.map_add f g
  rcases le_total (v f) (v g) with h | h
  · have hle : v (f + g) ≤ v g := hadd.trans (by rw [max_eq_right h])
    have hlog : WithZero.log (v (f + g)) ≤ WithZero.log (v g) :=
      (WithZero.log_le_log hvfg hvg).mpr hle
    calc min (-(WithZero.log (v f))) (-(WithZero.log (v g)))
        ≤ -(WithZero.log (v g)) := min_le_right _ _
      _ ≤ -(WithZero.log (v (f + g))) := by linarith
  · have hle : v (f + g) ≤ v f := hadd.trans (by rw [max_eq_left h])
    have hlog : WithZero.log (v (f + g)) ≤ WithZero.log (v f) :=
      (WithZero.log_le_log hvfg hvf).mpr hle
    calc min (-(WithZero.log (v f))) (-(WithZero.log (v g)))
        ≤ -(WithZero.log (v f)) := min_le_left _ _
      _ ≤ -(WithZero.log (v (f + g))) := by linarith

end PointValuation

/-! ## §N3. Riemann–Roch section subgroups `Γ(U, 𝒪_X(D))` -/

section Sections

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]

/-- **N3 — the Riemann–Roch section subgroup `Γ(U, 𝒪_X(D))`.** For an open
`U ⊆ X` and a Weil divisor `D`, the set of rational functions `f ∈ K(X)` whose
order along every prime divisor `P` meeting `U` is at least `-D(P)`:
`Γ(U, 𝒪_X(D)) = { f : f = 0 ∨ ∀ P ∈ U, ord_P f ≥ -D(P) }`.

The `f = 0` disjunct encodes the convention `ord_P 0 = +∞` (the project's junk
convention gives `ord_P 0 = 0`, so the zero function must be admitted separately).
Closure under addition is the `order` ultrametric `order_add_ge_min`. -/
def sectionOfDivisor (U : X.Opens) (D : X.WeilDivisor) :
    AddSubgroup X.functionField where
  carrier := { f | f = 0 ∨ ∀ P : X.PrimeDivisor, P.point ∈ U →
    -((show X.PrimeDivisor →₀ ℤ from D) P) ≤ Scheme.RationalMap.order P f }
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    rcases eq_or_ne f 0 with rfl | hfne
    · simpa using hg
    rcases eq_or_ne g 0 with rfl | hgne
    · simpa using hf
    rcases eq_or_ne (f + g) 0 with h0 | h0
    · exact Or.inl h0
    refine Or.inr fun P hP => ?_
    have hcf := (hf.resolve_left hfne) P hP
    have hcg := (hg.resolve_left hgne) P hP
    calc -((show X.PrimeDivisor →₀ ℤ from D) P)
        ≤ min (Scheme.RationalMap.order P f) (Scheme.RationalMap.order P g) :=
          le_min hcf hcg
      _ ≤ Scheme.RationalMap.order P (f + g) := order_add_ge_min P hfne hgne h0
  neg_mem' := by
    intro f hf
    rcases hf with rfl | hf
    · exact Or.inl (by simp)
    · refine Or.inr fun P hP => ?_
      rw [Scheme.RationalMap.order_neg]
      exact hf P hP

/-- Membership in `Γ(U, 𝒪_X(D))`. -/
theorem mem_sectionOfDivisor {U : X.Opens} {D : X.WeilDivisor}
    {f : X.functionField} :
    f ∈ sectionOfDivisor U D ↔ f = 0 ∨ ∀ P : X.PrimeDivisor, P.point ∈ U →
      -((show X.PrimeDivisor →₀ ℤ from D) P) ≤ Scheme.RationalMap.order P f :=
  Iff.rfl

/-- Membership for a nonzero function: only the order condition remains. -/
theorem mem_sectionOfDivisor_of_ne_zero {U : X.Opens} {D : X.WeilDivisor}
    {f : X.functionField} (hf : f ≠ 0) :
    f ∈ sectionOfDivisor U D ↔ ∀ P : X.PrimeDivisor, P.point ∈ U →
      -((show X.PrimeDivisor →₀ ℤ from D) P) ≤ Scheme.RationalMap.order P f := by
  rw [mem_sectionOfDivisor, or_iff_right hf]

/-- **Monotonicity in the divisor.** If `D ≤ D'` pointwise then
`Γ(U, 𝒪(D)) ⊆ Γ(U, 𝒪(D'))`. -/
theorem sectionOfDivisor_mono (U : X.Opens) {D D' : X.WeilDivisor}
    (h : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P ≤
      (show X.PrimeDivisor →₀ ℤ from D') P) :
    sectionOfDivisor U D ≤ sectionOfDivisor U D' := by
  intro f hf
  rcases hf with rfl | hf
  · exact Or.inl rfl
  exact Or.inr fun P hP => (neg_le_neg (h P)).trans (hf P hP)

/-- **`1 ∈ Γ(U, 𝒪(0))`** — the seed of `L(0) ⊇ k`. -/
theorem one_mem_sectionOfDivisor_zero (U : X.Opens) :
    (1 : X.functionField) ∈ sectionOfDivisor U (0 : X.WeilDivisor) := by
  refine Or.inr fun P hP => ?_
  rw [Scheme.RationalMap.order_one]
  change -((0 : X.PrimeDivisor →₀ ℤ) P) ≤ 0
  simp

/-- **Intersection over opens.** A section over `U₁ ⊔ U₂` is exactly a section
over `U₁` intersected with a section over `U₂`. -/
theorem sectionOfDivisor_sup (U₁ U₂ : X.Opens) (D : X.WeilDivisor) :
    sectionOfDivisor (U₁ ⊔ U₂) D =
      sectionOfDivisor U₁ D ⊓ sectionOfDivisor U₂ D := by
  ext f
  rw [AddSubgroup.mem_inf, mem_sectionOfDivisor, mem_sectionOfDivisor,
    mem_sectionOfDivisor]
  constructor
  · rintro (rfl | h)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr fun P hP => h P (TopologicalSpace.Opens.mem_sup.mpr (Or.inl hP)),
        Or.inr fun P hP => h P (TopologicalSpace.Opens.mem_sup.mpr (Or.inr hP))⟩
  · rintro ⟨h1, h2⟩
    rcases eq_or_ne f 0 with rfl | hfne
    · exact Or.inl rfl
    refine Or.inr fun P hP => ?_
    rcases (TopologicalSpace.Opens.mem_sup).mp hP with hP1 | hP2
    · exact (h1.resolve_left hfne) P hP1
    · exact (h2.resolve_left hfne) P hP2

/-- **Intersection of divisor conditions is the `min` divisor.** If `E` is the
pointwise minimum of `D` and `D'`, then `Γ(U, 𝒪(D)) ⊓ Γ(U, 𝒪(D')) = Γ(U, 𝒪(E))`,
i.e. `L(D) ∩ L(D') = L(min D D')`. -/
theorem sectionOfDivisor_inf_divisor (U : X.Opens) {D D' E : X.WeilDivisor}
    (hE : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from E) P =
      min ((show X.PrimeDivisor →₀ ℤ from D) P)
        ((show X.PrimeDivisor →₀ ℤ from D') P)) :
    sectionOfDivisor U D ⊓ sectionOfDivisor U D' = sectionOfDivisor U E := by
  ext f
  rw [AddSubgroup.mem_inf, mem_sectionOfDivisor, mem_sectionOfDivisor,
    mem_sectionOfDivisor]
  constructor
  · rintro ⟨h1, h2⟩
    rcases eq_or_ne f 0 with rfl | hfne
    · exact Or.inl rfl
    refine Or.inr fun P hP => ?_
    rw [hE P]
    rcases le_total ((show X.PrimeDivisor →₀ ℤ from D) P)
        ((show X.PrimeDivisor →₀ ℤ from D') P) with hle | hle
    · rw [min_eq_left hle]; exact (h1.resolve_left hfne) P hP
    · rw [min_eq_right hle]; exact (h2.resolve_left hfne) P hP
  · rintro (rfl | h)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr fun P hP =>
          ((by rw [hE P]; exact neg_le_neg (min_le_left _ _)) :
            _ ≤ -((show X.PrimeDivisor →₀ ℤ from E) P)).trans (h P hP),
        Or.inr fun P hP =>
          ((by rw [hE P]; exact neg_le_neg (min_le_right _ _)) :
            _ ≤ -((show X.PrimeDivisor →₀ ℤ from E) P)).trans (h P hP)⟩

/-- **The Riemann–Roch space `L(D)`.** Global sections of `𝒪_X(D)`: the section
over all of `X`. On a 2-affine cover `U₀ ⊔ U₁ = ⊤` this is
`Γ(U₀, 𝒪(D)) ⊓ Γ(U₁, 𝒪(D))`, the kernel of the Čech difference map. -/
def linearSystem (D : X.WeilDivisor) : AddSubgroup X.functionField :=
  sectionOfDivisor ⊤ D

/-- On a 2-affine cover `U₀ ⊔ U₁ = ⊤`, `L(D)` is the intersection of the two
chart sections. -/
theorem linearSystem_eq_inf {U₀ U₁ : X.Opens} (hcov : U₀ ⊔ U₁ = ⊤)
    (D : X.WeilDivisor) :
    linearSystem D = sectionOfDivisor U₀ D ⊓ sectionOfDivisor U₁ D := by
  rw [linearSystem, ← hcov, sectionOfDivisor_sup]

end Sections

/-! ## §N1. Dedekind coordinate rings of affine charts -/

section Chart

variable {X : Scheme.{u}}

/-- **N1 (unconditional half) — the affine chart is a fraction-ring chart.** For a
nonempty affine open `U` of an integral scheme, the coordinate ring `Γ(X, U)` has
`K(X)` as its fraction field. Thin wrapper around mathlib's
`functionField_isFractionRing_of_isAffineOpen`. -/
theorem chartRing_isFractionRing [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : IsFractionRing Γ(X, U) X.functionField :=
  functionField_isFractionRing_of_isAffineOpen X U hU

/-- **N1 (unconditional half) — the affine chart is Noetherian.** For a nonempty
affine open `U` of a locally Noetherian scheme, `Γ(X, U)` is a Noetherian ring. -/
theorem chartRing_isNoetherianRing [IsLocallyNoetherian X] {U : X.Opens}
    (hU : IsAffineOpen U) : IsNoetherianRing Γ(X, U) :=
  IsLocallyNoetherian.component_noetherian ⟨U, hU⟩

/-- **N1 — the Dedekind-from-DVR bridge** (pure ring theory, `IsDedekindDomainDvr`).
A Noetherian integral domain whose localization at every nonzero prime is a
discrete valuation ring is a Dedekind domain. This is exactly the criterion under
which a smooth (equivalently: regular, on a curve) affine chart `Γ(X, U)` is
Dedekind; the missing input is that every nonzero prime of the chart is
height-one, i.e. that `X` is a curve. -/
theorem isDedekindDomain_of_forall_localization_dvr {R : Type*} [CommRing R]
    [IsDomain R] [IsNoetherianRing R]
    (h : ∀ (P : Ideal R) [P.IsPrime], P ≠ ⊥ →
      IsDiscreteValuationRing (Localization.AtPrime P)) :
    IsDedekindDomain R := by
  haveI : IsDedekindDomainDvr R := by
    refine { is_dvr_at_nonzero_prime := fun P hP hPp => ?_ }
    haveI := hPp
    exact h P hP
  infer_instance

/-- **N1 (gate) — `HasDedekindChart`.** Packages "every nonempty affine chart of
`X` has a Dedekind coordinate ring". On a smooth (or normal) curve this holds
because each chart is a one-dimensional regular Noetherian domain; where mathlib's
`smooth ⇒ regular chart` bridge is unavailable we supply this as a `HasPicScheme`-
style gate class (no global instance — an honest hypothesis), to be discharged
later via `isDedekindDomain_of_forall_localization_dvr` (design §4). -/
class HasDedekindChart (X : Scheme.{u}) [IsIntegral X] : Prop where
  /-- Every nonempty affine chart is a Dedekind domain. -/
  isDedekindDomain : ∀ (U : X.Opens), IsAffineOpen U → [Nonempty U] →
    IsDedekindDomain Γ(X, U)

/-- Access the Dedekind-chart hypothesis for a specific nonempty affine open. -/
theorem isDedekindDomain_chart [IsIntegral X] [HasDedekindChart X] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] : IsDedekindDomain Γ(X, U) :=
  HasDedekindChart.isDedekindDomain U hU

end Chart

/-! ## §N4. Finiteness of the places of a rational function on a chart

The scheme-level statement `rationalMap_order_finite_support` in
`RiemannRoch/WeilDivisor.lean` (that `P ↦ ord_P f` has finite support) is **false**
as pinned there with only `[IsLocallyNoetherian X]`: the "line with infinitely many
origins" is integral, locally Noetherian and regular in codimension one, yet `t`
has order one at each of its infinitely many origins.  Finiteness needs `X`
globally Noetherian (`[IsNoetherian X]`, i.e. quasi-compact), matching Stacks 02RV.

What *is* unconditionally true, and is the reusable core of the affine-chart
argument, is the following: on a single Dedekind chart, a nonzero rational function
is non-integral (valuation `≠ 1`) at only finitely many height-one places. -/

section Finiteness

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **N4 (chart core).** For a nonzero element `k` of the fraction field of a
Dedekind domain `R`, only finitely many height-one places `v` have `v(k) ≠ 1`
(i.e. only finitely many places where `k` is a zero or a pole). This is the
finite-support statement for the principal divisor on a single affine chart,
obtained from mathlib's `HeightOneSpectrum.Support.finite` applied to `k` and to
`k⁻¹`. -/
theorem finite_places_ne_one {k : K} (hk : k ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K k ≠ 1}.Finite := by
  have h1 := HeightOneSpectrum.Support.finite R k
  have h2 := HeightOneSpectrum.Support.finite R k⁻¹
  refine (h1.union h2).subset fun v hv => ?_
  simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq] at hv ⊢
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · right
    rw [Set.mem_setOf_eq, map_inv₀]
    have hv0 : v.valuation K k ≠ 0 := by
      simpa using (Valuation.zero_iff (v.valuation K)).not.mpr hk
    exact one_lt_inv₀ (lt_of_le_of_ne zero_le (Ne.symm hv0)) |>.mpr hlt
  · exact Or.inl hgt

end Finiteness

end Adelic
end AlgebraicGeometry
