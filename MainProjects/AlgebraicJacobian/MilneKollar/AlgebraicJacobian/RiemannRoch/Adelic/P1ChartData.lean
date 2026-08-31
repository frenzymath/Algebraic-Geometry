/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.FinitenessP1

/-!
# The `ℙ¹` chart-ring computation: discharging `P1HasLaurentChartData` (node `N11b`)

**STATUS: COMPLETE — registered in `AlgebraicJacobian.lean`.**  The gate instance
`instP1HasLaurentChartData` is proved with clean axioms
`[propext, Classical.choice, Quot.sound]`.

This file computes the standard-chart Laurent data of the concrete
projective line `ℙ¹ = ℙ(ULift (Fin 2); Spec k)` (the `Proj`-pullback model of
`Picard/ProjectiveSpace.lean`), the datum consumed by the adelic keystone
`Adelic.LaurentChartData.module_finite_H1Cok` (`FinitenessP1.lean`), and thereby to
discharge the gate `Adelic.P1HasLaurentChartData`.

**Landed so far (LSP-verified, clean axioms):**
* `p1CoordAway i j` — the coordinate fraction `Xⱼ/Xᵢ ∈ Away 𝒫 Xᵢ`;
* `p1XSection`, `p1YSection` — the chart coordinates `x = X₁/X₀ ∈ Γ(V₀)`,
  `y = X₀/X₁ ∈ Γ(V₁)`, pulled back along `toProjInt`;
* `p1Monomial a b` and `p1Monomial_eq_coordPow` — **the per-monomial span heart**:
  the degree-`(a+b)` monomial fraction `X₀^a X₁^b / X₀^(a+b)` equals `(X₁/X₀)^b`;
* `span_p1CoordAway_pow_top` — **the full chart-ring span core (`ℤ`-span, route
  step 1)**: `⊤ ≤ Submodule.span (𝒜 0) {(X₁/X₀)^m}` in `(ℤ[X₀,X₁]_{X₀})₀`.  Every
  degree-zero away element `p/X₀^N` (`Away.mk_surjective`) expands over the monomial
  support of the homogeneous numerator `p ∈ 𝒜 N`; each occurring exponent vector `d`
  has `d₀ + d₁ = N` (homogeneity, `IsHomogeneous.coeff_eq_zero`), so the per-monomial
  helper `awayMk_monomial_mem_span` (built on `p1Monomial_eq_coordPow` and the
  two-variable monomial expansion `monomial_eq_C_mul_pow`) rewrites each summand as a
  constant `𝒜 0`-scalar times `(X₁/X₀)^{d₁}`, landing the whole fraction in the span.

**Landed (route step 2, the char-free base change — `span_pow_p1XSection_scaffold`):**
`Γ(V₀) = k[x]`.  The chart open `V₀ = p1Chart ⟨0⟩ = toProjInt ⁻¹ᵁ D₊(X₀)` is the pullback
of the affine `D₊(X₀) ⊆ Proj ℤ[X₀,X₁]` over the terminal scheme, hence (Route B, no
flatness) its section ring is the ring pushout of the affine fibre product
(`isIso_pushoutSection_of_isAffineOpen`), whose two structural maps ring-generate it
(`closure_range_union_range_eq_top_of_isPushout`); the `Proj`-side generators are carried
into the `k`-span of the powers of `x` by the `ℤ`-span core (`span_p1CoordAway_pow_top`,
transported by an inlined `span_induction`), the `Spec k`-side generators are `k`-multiples
of `1`.  **Elaboration note:** the composite ring hom is given an *explicit source type with
an ascribed `X`-index* — otherwise `RingHom.comp` defers the index and unifies the `D₊(X₀)`
basic-open predicates through the concrete `ℙ¹` pullback into `MvPolynomial`, which is
astronomically slow.

**Landed (route steps 3–4):** the symmetric `y`-chart span `Γ(V₁) = k[y]`, the overlap
identities `V₀ ⊓ V₁ = D(x) = D(y)` and `x·y = 1` (through the *hoisted* overlap
polynomial `p1XY = X₀X₁` — one shared elaborated copy, see its docstring for the
`binop%`/`OfNat`-instance elaboration trap), and the final
`p1LaurentChartData`/`instP1HasLaurentChartData` assembly.

## The reduction (route map for a future wave)

The geometric substrate — the two affine charts `Vᵢ = D₊(Xᵢ)` (pulled back to the
model), their affineness, and the covering property — is already assembled as
`Adelic.p1CoverSquare` (`FinitenessP1.lean`).  What remains is the chart-ring content
of `Adelic.LaurentChartData`:

1. **Coordinate sections.**  `x = X₁/X₀ ∈ Γ(V₀)`, `y = X₀/X₁ ∈ Γ(V₁)`, defined as
   pullbacks along `ProjectiveSpace.toProjInt` of the away-section fractions:
   `x := (toProjInt.app D₊(X₀)).hom ((Proj.awayToSection 𝒜 (X ⟨0⟩)).hom (p1CoordAway ⟨0⟩ ⟨1⟩))`,
   and symmetrically `y` at `⟨1⟩`.  (`p1CoordAway i j = Xⱼ/Xᵢ ∈ Away 𝒜 (Xᵢ)` below.)

2. **Overlap identities** `V₀ ⊓ V₁ = D(x) = D(y)` and `x · y = 1`.  On the overlap
   `D₊(X₀X₁)` the pullbacks of `x, y` restrict, by naturality of `Scheme.Hom.app`
   and `Proj.awayMap_awayToSection`, to the images of `awayFraction ⟨1⟩ ⟨0⟩ = X₁/X₀`
   and `awayFraction ⟨0⟩ ⟨1⟩ = X₀/X₁` in `Away 𝒜 (X₀X₁)`, whose product is `1`
   (`ProjTwist.awayFraction_mul_inv`).  The basic-open identities follow from
   `Scheme.preimage_basicOpen` together with the `Proj`-side computation of the basic
   open of the away fraction (its non-vanishing locus inside `D₊(Xᵢ)` is `D₊(XᵢXⱼ)`).

3. **Chart spanning** `Γ(V₀) = k[x]`, `Γ(V₁) = k[y]` (the fields `span_pow_x/y`).
   The mathematical heart.  Two routes:
   * (Route A, char-restricted) Flat base change `02KE`
     (`QuotScheme.pullback_baseMap_sectionLinearEquiv_of_quasiCompact`, CLOSED) gives
     `Γ(V₀) ≃ₗ[k] k ⊗_ℤ Away 𝒜 (X₀)`.  It requires `[Flat (Spec k ↘ ⊤)]`, i.e. `k`
     flat over `ℤ`, i.e. `k` torsion-free — TRUE only in characteristic `0`.  So this
     route discharges the gate only for `[CharZero k]`.
   * (Route B, char-free — preferred) The chart preimage is the pullback
     `Spec k ×_{⊤} D₊(Xᵢ) = Spec (k ⊗_ℤ Away 𝒜 (Xᵢ))` (restrict the defining pullback
     square `ProjectiveSpace.isPullback_map`/`of_hasPullback` over the affine `D₊(Xᵢ)`;
     product of affines over the terminal `⊤ = Spec (ULift ℤ)` is `Spec` of the tensor —
     no flatness needed).  Read off `Γ(V₀) ≅ k ⊗_ℤ Away 𝒜 (X₀)` directly.
   In either case the span reduces, by `k ⊗_ℤ (−)` base change of `Submodule.span`, to
   the **`ℤ`-span core**: `Away 𝒜 (Xᵢ)` is `(𝒜 0)`-spanned by the powers of the
   coordinate fraction `p1CoordAway ⟨0⟩ ⟨1⟩`.  Proof by `HomogeneousLocalization`
   induction: an away element is `Away.mk 𝒜 hX₀ n p hp` with `p ∈ 𝒜 n` homogeneous of
   degree `n` in two variables, hence `p = Σ_{b≤n} c_b · X₀^{n-b} X₁^b`
   (`MvPolynomial.as_sum` + homogeneity forcing `d₀ + d₁ = n` on the support), so
   `p / X₀^n = Σ_b c_b · (X₁/X₀)^b` in the localization.

## Assembly

With 1–3 in hand, `Adelic.LaurentChartData (Over.mk (ℙ¹ ↘ Spec k))` is populated from
`p1CoverSquare`'s fields plus the above, and
`instance : P1HasLaurentChartData k := ⟨⟨…⟩⟩` discharges the gate (for `[CharZero k]`
via Route A, or for every field via Route B).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.Adelic

/-! ## The single-chart coordinate fractions `Xⱼ/Xᵢ ∈ (ℤ[X]_{Xᵢ})₀` -/

section CoordAway

variable (n : Type u)

/-- The coordinate fraction `Xⱼ/Xᵢ` as an element of the degree-zero away ring
`(ℤ[X]_{Xᵢ})₀ = Away 𝒫[n] Xᵢ` of the integral model (numerator `Xⱼ`, denominator
`Xᵢ`, both homogeneous of degree `1`).  On the chart `V₀` the coordinate is
`X₁/X₀ = p1CoordAway ⟨0⟩ ⟨1⟩`; on `V₁` it is `X₀/X₁ = p1CoordAway ⟨1⟩ ⟨0⟩`.

UNVERIFIED (see the module header): the `1 • 1 = 1` grading obligation is discharged
by `simpa`, but no elaboration/kernel check has been run under the current host load. -/
noncomputable def p1CoordAway (i j : n) :
    Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) :=
  Away.mk _ (ProjTwist.X_mem_deg_one n i) 1 (X j)
    (by simpa using ProjTwist.X_mem_deg_one n j)

end CoordAway

/-! ## The coordinate sections on the `ℙ¹` model

The coordinates `x, y` of `Adelic.LaurentChartData` on the concrete model
`ℙ¹ = ℙ(ULift (Fin 2); Spec k)` are the pullbacks along `ProjectiveSpace.toProjInt`
of the away-section fractions `X₁/X₀`, `X₀/X₁`.  Restriction target opens are
`p1Chart k ⟨0⟩ = toProjInt ⁻¹ᵁ D₊(X₀)` and `p1Chart k ⟨1⟩ = toProjInt ⁻¹ᵁ D₊(X₁)`
(definitionally, from `FinitenessP1.p1Chart`). -/

section CoordSection

variable (k : Type u) [Field k]

/-- The coordinate `x = X₁/X₀ ∈ Γ(V₀)` on the first chart of the `ℙ¹` model,
pulled back from the away section `X₁/X₀ ∈ Away 𝒫 X₀` along `toProjInt`. -/
noncomputable def p1XSection :
    Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩) :=
  ((ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).app
      (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩))).hom
    ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X ⟨0⟩)).hom (p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩))

/-- The coordinate `y = X₀/X₁ ∈ Γ(V₁)` on the second chart of the `ℙ¹` model,
pulled back from the away section `X₀/X₁ ∈ Away 𝒫 X₁` along `toProjInt`. -/
noncomputable def p1YSection :
    Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩) :=
  ((ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).app
      (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩))).hom
    ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X ⟨1⟩)).hom (p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩))

end CoordSection

/-! ## The chart-ring span core (the `ℤ[X₁/X₀]` computation)

The mathematical heart of `span_pow_x`: every element of the degree-zero away ring
`(ℤ[X₀,X₁]_{X₀})₀` is a `(𝒜 0)`-combination of the powers of the coordinate fraction
`X₁/X₀`.  The key algebraic step is that a degree-`(a+b)` monomial fraction
`X₀^a X₁^b / X₀^(a+b)` equals `(X₁/X₀)^b`. -/

section SpanCore

/-- The pure monomial identity `(x₀¹)ᵇ (x₀ᵃ x₁ᵇ) = x₀^(a+b) x₁ᵇ`, proved in a generic
commutative monoid so the certificate never touches the expensive `MvPolynomial`
`ring` normalisation. -/
private lemma pow_mul_pow_identity {A : Type*} [CommMonoid A] (x0 x1 : A) (a b : ℕ) :
    (x0 ^ 1) ^ b * (x0 ^ a * x1 ^ b) = x0 ^ (a + b) * x1 ^ b := by
  rw [pow_one, ← mul_assoc, ← pow_add, Nat.add_comm b a]

/-- The degree-`(a+b)` monomial fraction `X₀^a X₁^b / X₀^(a+b)` as an element of the
degree-zero away ring `(ℤ[X]_{X₀})₀`.  (Isolating the `Away.mk` inside a definition,
with the homogeneity obligation discharged by a `by`-block rather than a pre-typed
term, keeps the concrete graded-instance `isDefEq` from blowing up — cf. `p1CoordAway`.) -/
noncomputable def p1Monomial (a b : ℕ) :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩) :=
  Away.mk _ (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩) (a + b)
    (X ⟨0⟩ ^ a * X ⟨1⟩ ^ b)
    (by
      rw [add_smul]
      exact SetLike.mul_mem_graded
        (SetLike.pow_mem_graded a (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩))
        (SetLike.pow_mem_graded b (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩)))

/-- **The monomial-to-power identity.**  The degree-`(a+b)` monomial fraction
`X₀^a X₁^b / X₀^(a+b)` in `(ℤ[X]_{X₀})₀` equals `(X₁/X₀)^b`, the `b`-th power of the
coordinate fraction.  This is the per-monomial step of the chart-ring spanning
`Γ(V₀) = k[X₁/X₀]`. -/
lemma p1Monomial_eq_coordPow (a b : ℕ) :
    p1Monomial a b = p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩ ^ b := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_pow]
  simp only [p1Monomial, p1CoordAway, Away.val_mk, Localization.mk_pow]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, SubmonoidClass.coe_pow]
  exact pow_mul_pow_identity _ _ a b

/-- Two-variable monomial expansion: the monomial `X^d · c` in `ℤ[X₀, X₁]` is
`c · X₀^{d₀} · X₁^{d₁}` (`Finsupp.prod` over the two-element index reduced with
`Fin.prod_univ_two` through the `ULift (Fin 2) ≃ Fin 2` equivalence). -/
private lemma monomial_eq_C_mul_pow (d : ULift.{u} (Fin 2) →₀ ℕ) (c : ULift.{u} ℤ) :
    (monomial d c : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      = C c * (X ⟨0⟩ ^ d ⟨0⟩ * X ⟨1⟩ ^ d ⟨1⟩) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  congr 1
  rw [← Equiv.prod_comp (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))
        (fun i => X i ^ d i), Fin.prod_univ_two]
  rfl

/-- A monomial-fraction summand lies in the span of the coordinate powers: the
degree-`N` monomial fraction `(monomial d c)/X₀^N` (with `d₀ + d₁ = N`) equals the
degree-zero scalar `C c` times the coordinate power `(X₁/X₀)^{d₁}`. -/
private lemma awayMk_monomial_mem_span (N : ℕ) (d : ULift.{u} (Fin 2) →₀ ℕ) (c : ULift.{u} ℤ)
    (hN : d ⟨0⟩ + d ⟨1⟩ = N)
    (hmem : (monomial d c : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) ∈
      homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (N • 1)) :
    Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩) N (monomial d c) hmem ∈
      Submodule.span (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
        (Set.range fun m : ℕ => p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩ ^ m) := by
  have hC0 : (C c : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) ∈
      homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0 :=
    (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ c)
  have key : Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩) N (monomial d c) hmem
      = (⟨C c, hC0⟩ : homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
          • p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩ ^ (d ⟨1⟩) := by
    apply HomogeneousLocalization.val_injective
    have hfz : (HomogeneousLocalization.fromZeroRingHom
        (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (Submonoid.powers (X ⟨0⟩)) ⟨C c, hC0⟩).val
        = Localization.mk (C c) 1 := rfl
    rw [Algebra.smul_def, HomogeneousLocalization.algebraMap_eq,
        HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
        Away.val_mk, p1CoordAway, Away.val_mk, Localization.mk_pow, hfz,
        Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, SubmonoidClass.coe_pow]
    rw [monomial_eq_C_mul_pow d c, ← hN]
    ring
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d ⟨1⟩, rfl⟩)

/-- **The chart-ring span core.**  The degree-zero away ring `(ℤ[X₀,X₁]_{X₀})₀`
is spanned, over its constant subring `𝒜 0`, by the powers of the coordinate
fraction `X₁/X₀ = p1CoordAway ⟨0⟩ ⟨1⟩`: every degree-zero away element is a
`(𝒜 0)`-linear combination of `(X₁/X₀)^m`.  This is the mathematical heart of the
chart-ring spanning `Γ(V₀) = k[x]`.

The proof: every away element is `p / X₀^N` with `p` homogeneous of degree `N`
(`Away.mk_surjective`); expanding `p` over its monomial support and using that
each occurring exponent vector `d` satisfies `d₀ + d₁ = N` (homogeneity), the
per-monomial identity `awayMk_monomial_mem_span` writes each summand as a
constant times a coordinate power, so the whole fraction lands in the span. -/
theorem span_p1CoordAway_pow_top :
    (⊤ : Submodule (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
        (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩)))
      ≤ Submodule.span (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
          (Set.range fun m : ℕ => p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩ ^ m) := by
  intro w _
  obtain ⟨N, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
    (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩) w
  have hhom := (mem_homogeneousSubmodule _ _).mp ha
  -- each monomial summand of `a` is homogeneous of degree `N • 1`
  have hmonoAll : ∀ d : ULift.{u} (Fin 2) →₀ ℕ,
      (monomial d (coeff d a) : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) ∈
        homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (N • 1) := by
    intro d
    rcases eq_or_ne (coeff d a) 0 with h0 | h0
    · rw [h0, monomial_zero]; exact Submodule.zero_mem _
    · refine (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ ?_)
      by_contra hne
      exact h0 (hhom.coeff_eq_zero hne)
  -- every support exponent `d` has total degree `d₀ + d₁ = N`
  have hdegN : ∀ d ∈ a.support, d ⟨0⟩ + d ⟨1⟩ = N := by
    intro d hd
    rw [mem_support_iff] at hd
    have hdeg : Finsupp.degree d = N • 1 := by
      by_contra hne
      exact hd (hhom.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum,
        ← Equiv.sum_comp (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)) (fun i => d i),
        Fin.sum_univ_two] at hdeg
    simpa using hdeg
  -- monomial decomposition of the fraction over the support
  have hsum : Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩) N a ha
      = ∑ d ∈ a.support, Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩) N (monomial d (coeff d a))
          (hmonoAll d) := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, ← HomogeneousLocalization.algebraMap_apply, map_sum]
    simp only [HomogeneousLocalization.algebraMap_apply, Away.val_mk]
    rw [← Localization.mk_sum, ← MvPolynomial.as_sum]
  rw [hsum]
  refine Submodule.sum_mem _ (fun d hd => ?_)
  exact awayMk_monomial_mem_span N d (coeff d a) (hdegN d hd) (hmonoAll d)

/-! ### The `y`-chart mirror of the span core (`Γ(V₁) = k[y]`, `ℤ`-span step)

The symmetric statement for the *second* chart `D₊(X₁)`: the degree-zero away ring
`(ℤ[X₀,X₁]_{X₁})₀` is spanned over `𝒜 0` by the powers of the coordinate fraction
`X₀/X₁ = p1CoordAway ⟨1⟩ ⟨0⟩`.  The two charts are symmetric under swapping the roles
of `X₀` and `X₁`; the per-monomial expansion `monomial_eq_C_mul_pow` (which names both
variables) and the homogeneity bookkeeping (`d₀ + d₁ = N`, chart-independent) are shared
verbatim, and only the extracted coordinate exponent flips from `d₁` to `d₀`. -/

/-- The `y`-chart mirror of `awayMk_monomial_mem_span`: the degree-`N` monomial fraction
`(monomial d c)/X₁^N` (with `d₀ + d₁ = N`) equals the degree-zero scalar `C c` times the
coordinate power `(X₀/X₁)^{d₀}`, hence lies in the span of the powers of `X₀/X₁`. -/
private lemma awayMkY_monomial_mem_span (N : ℕ) (d : ULift.{u} (Fin 2) →₀ ℕ) (c : ULift.{u} ℤ)
    (hN : d ⟨0⟩ + d ⟨1⟩ = N)
    (hmem : (monomial d c : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) ∈
      homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (N • 1)) :
    Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩) N (monomial d c) hmem ∈
      Submodule.span (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
        (Set.range fun m : ℕ => p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩ ^ m) := by
  have hC0 : (C c : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) ∈
      homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0 :=
    (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ c)
  have key : Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩) N (monomial d c) hmem
      = (⟨C c, hC0⟩ : homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
          • p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩ ^ (d ⟨0⟩) := by
    apply HomogeneousLocalization.val_injective
    have hfz : (HomogeneousLocalization.fromZeroRingHom
        (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (Submonoid.powers (X ⟨1⟩)) ⟨C c, hC0⟩).val
        = Localization.mk (C c) 1 := rfl
    rw [Algebra.smul_def, HomogeneousLocalization.algebraMap_eq,
        HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
        Away.val_mk, p1CoordAway, Away.val_mk, Localization.mk_pow, hfz,
        Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, SubmonoidClass.coe_pow]
    rw [monomial_eq_C_mul_pow d c, ← hN]
    ring
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d ⟨0⟩, rfl⟩)

/-- **The `y`-chart span core.**  The degree-zero away ring `(ℤ[X₀,X₁]_{X₁})₀` is
spanned, over its constant subring `𝒜 0`, by the powers of the coordinate fraction
`X₀/X₁ = p1CoordAway ⟨1⟩ ⟨0⟩`.  The `X₀ ↔ X₁` mirror of `span_p1CoordAway_pow_top`. -/
theorem span_p1CoordAwayY_pow_top :
    (⊤ : Submodule (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
        (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩)))
      ≤ Submodule.span (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
          (Set.range fun m : ℕ => p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩ ^ m) := by
  intro w _
  obtain ⟨N, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
    (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩) w
  have hhom := (mem_homogeneousSubmodule _ _).mp ha
  have hmonoAll : ∀ d : ULift.{u} (Fin 2) →₀ ℕ,
      (monomial d (coeff d a) : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) ∈
        homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) (N • 1) := by
    intro d
    rcases eq_or_ne (coeff d a) 0 with h0 | h0
    · rw [h0, monomial_zero]; exact Submodule.zero_mem _
    · refine (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ ?_)
      by_contra hne
      exact h0 (hhom.coeff_eq_zero hne)
  have hdegN : ∀ d ∈ a.support, d ⟨0⟩ + d ⟨1⟩ = N := by
    intro d hd
    rw [mem_support_iff] at hd
    have hdeg : Finsupp.degree d = N • 1 := by
      by_contra hne
      exact hd (hhom.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum,
        ← Equiv.sum_comp (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)) (fun i => d i),
        Fin.sum_univ_two] at hdeg
    simpa using hdeg
  have hsum : Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩) N a ha
      = ∑ d ∈ a.support, Away.mk (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩) N (monomial d (coeff d a))
          (hmonoAll d) := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, ← HomogeneousLocalization.algebraMap_apply, map_sum]
    simp only [HomogeneousLocalization.algebraMap_apply, Away.val_mk]
    rw [← Localization.mk_sum, ← MvPolynomial.as_sum]
  rw [hsum]
  refine Submodule.sum_mem _ (fun d hd => ?_)
  exact awayMkY_monomial_mem_span N d (coeff d a) (hdegN d hd) (hmonoAll d)

end SpanCore

/-! ## Transporting the span core through a ring hom (route step 2, algebraic heart)

The char-free "push the `ℤ`-span through `k ⊗_ℤ (−)`".  For **any** ring hom `ρ`
from the degree-zero away ring `(ℤ[X₀,X₁]_{X₀})₀` into a `k`-algebra `B`, the image
`ρ a` of every away element lies in the `k`-span of the powers of `ρ (X₁/X₀)`.  The
`(𝒜 0) = ℤ`-scalars of the span core (`span_p1CoordAway_pow_top`) become `k`-scalars
because a ring hom sends integer constants of `𝒜 0` to integers of `B`, which are
`k`-multiples of `1`.  Applied to the pullback ring map `Away 𝒜 X₀ → Γ(V₀)` (whose
value at `X₁/X₀` is the chart coordinate `x`), this is exactly the transport of the
span through the tensor identification `Γ(V₀) = k ⊗_ℤ (ℤ[X₁/X₀])`. -/

section SpanTransport

variable {k : Type u} [Field k]

/-- Every element of the degree-zero part `𝒜 0` (the copy of `ℤ` given by the
constants) is an integer constant. -/
private lemma exists_intCast_eq_gradeZero
    (c : (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)) :
    ∃ m : ℤ, (m : (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)) = c := by
  obtain ⟨z, hz⟩ :=
    (ProjectiveSpace.bijective_algebraMap_gradeZero (ULift.{u} (Fin 2))).surjective c
  refine ⟨z.down, ?_⟩
  rw [← hz, ← map_intCast (algebraMap (ULift.{u} ℤ)
    (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)) z.down]
  rfl

/-- **Route step 2, algebraic core: transport of the span through a ring hom.**
For any ring hom `ρ` from the degree-zero away ring `(ℤ[X₀,X₁]_{X₀})₀` into a
`k`-algebra `B`, the image `ρ a` of every away element lies in the `k`-span of the
powers of `ρ (X₁/X₀)`. -/
lemma awayRingHom_mem_span_pow {B : Type u} [CommRing B] [Algebra k B]
    (ρ : Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩) →+* B)
    (a : Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩)) :
    ρ a ∈ Submodule.span k
      (Set.range fun m : ℕ => ρ (p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩) ^ m) := by
  have hmem : a ∈ Submodule.span (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
      (Set.range fun m : ℕ => p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩ ^ m) :=
    span_p1CoordAway_pow_top (Submodule.mem_top)
  induction hmem using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨m, rfl⟩ := hz
      exact Submodule.subset_span ⟨m, by rw [map_pow]⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu =>
      obtain ⟨m, rfl⟩ := exists_intCast_eq_gradeZero c
      rw [Int.cast_smul_eq_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul k]
      exact Submodule.smul_mem _ _ hu

end SpanTransport

/-! ## Base change spans (route step 2, general algebra) -/

section BaseChangeSpan

/-- **Base change is spanned by the image.**  If `N` is the base change of the
`R`-module `M` to `S` (`IsBaseChange S f` for `f : M →ₗ[R] N`), then `N` is
spanned over `S` by the image of `f` — because `N ≃ S ⊗[R] M` and every pure
tensor `s ⊗ m = s • f m` lies in the `S`-span of the range. -/
theorem isBaseChange_span_range_eq_top {R S M N : Type*} [CommSemiring R]
    [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Algebra R S] [Module S N] [IsScalarTower R S N] {f : M →ₗ[R] N}
    (hf : IsBaseChange S f) :
    Submodule.span S (Set.range f) = ⊤ := by
  rw [eq_top_iff]
  rintro n -
  obtain ⟨t, rfl⟩ := hf.equiv.surjective n
  refine TensorProduct.induction_on t (by simp) (fun s m => ?_)
    (fun x y hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
  rw [hf.equiv_tmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

open scoped Pointwise in
/-- The `k`-span of the powers of a single element `x` is closed under
multiplication (`xᵃ · xᵇ = xᵃ⁺ᵇ` is again a power), hence a subring — the fact
that makes it the target of a `Subring.closure` induction. -/
theorem mul_mem_span_range_pow {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : A) {a b : A}
    (ha : a ∈ Submodule.span k (Set.range fun n : ℕ => x ^ n))
    (hb : b ∈ Submodule.span k (Set.range fun n : ℕ => x ^ n)) :
    a * b ∈ Submodule.span k (Set.range fun n : ℕ => x ^ n) := by
  have hSS : (Set.range fun n : ℕ => x ^ n) * (Set.range fun n : ℕ => x ^ n)
      ⊆ Set.range fun n : ℕ => x ^ n := by
    rw [Set.mul_subset_iff]
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact ⟨p + q, by simp only [pow_add]⟩
  have hmul := Submodule.mul_mem_mul ha hb
  rw [Submodule.span_mul_span] at hmul
  exact Submodule.span_mono hSS hmul

end BaseChangeSpan

section BaseChange

variable (k : Type u) [Field k]

open ProjectiveSpace HomogeneousLocalization

/-- The `algebraSection` `k`-module structure on `Γ(V₀)` (registered locally so
the span statement uses the same module structure as `LaurentChartData.span_pow_x`
will at the assembly site). -/
noncomputable local instance instAlgebraΓV0 :
    Algebra k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩) :=
  Scheme.toModuleKSheaf.algebraSection
    (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
    (op (p1Chart k ⟨0⟩))

/-- The affine-chart map `awayToSection : (ℤ[X]_{X₀})₀ → Γ(D₊(X₀))` is surjective:
it is the isomorphism `basicOpenIsoAway` (`X₀` is homogeneous of degree `1 > 0`). -/
private lemma awayToSection_X0_surjective :
    Function.Surjective ⇑(Proj.awayToSection
      (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩)) := by
  haveI : IsIso (Proj.awayToSection
      (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩)) := by
    rw [← Proj.basicOpenIsoAway_hom (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      (X ⟨0⟩) (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩) one_pos]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso _).2

/-- **`V₀`-generators of type (1): the `Proj`-side.**  The `toProjInt`-pullback of a
section `s ∈ Γ(D₊(X₀))` lies in the `k`-span of the powers of `x = p1XSection`.
Writing `s = awayToSection a` (the affine chart iso, `awayToSection_X0_surjective`)
and reducing `appLE` to `app` (the chart open is `toProjInt ⁻¹ᵁ D₊(X₀)`), the pullback
is `ρ a` for the ring hom `ρ = appLE ∘ awayToSection`; every `a` is a `(𝒜 0)`-combination
of the coordinate powers (`span_p1CoordAway_pow_top`), and `ρ` carries those to the powers
of `x`, the `(𝒜 0) = ℤ`-scalars becoming `k`-scalars (`exists_intCast_eq_gradeZero`). -/
private lemma mem_span_appLE_toProjInt
    (s : Γ(Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)),
        Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩))) :
    (Scheme.Hom.appLE (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
        (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩))
        (p1Chart k ⟨0⟩) (le_refl _)).hom s
      ∈ Submodule.span k (Set.range fun n : ℕ => p1XSection k ^ n) := by
  have hbridge : Scheme.Hom.appLE (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
        (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩))
        (p1Chart k ⟨0⟩) (le_refl _)
      = (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).app
          (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩)) :=
    Scheme.Hom.appLE_eq_app _
  obtain ⟨a, rfl⟩ := awayToSection_X0_surjective s
  -- `ρ = appLE ∘ awayToSection`, with an *explicit source type* (`let` for transparency)
  let ρ : Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X (⟨0⟩ : ULift.{u} (Fin 2))) →+*
      Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩) :=
    (Scheme.Hom.appLE (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
        (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X (⟨0⟩ : ULift.{u} (Fin 2))))
        (p1Chart k ⟨0⟩) (le_refl _)).hom.comp
      (Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X (⟨0⟩ : ULift.{u} (Fin 2)))).hom
  -- `ρ (X₁/X₀) = x = p1XSection`: rewrite `appLE = app` (`hbridge`), the rest is `rfl`.
  have hval : ρ (p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩) = p1XSection k := by
    change ((Scheme.Hom.appLE (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
          (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            (X (⟨0⟩ : ULift.{u} (Fin 2))))
          (p1Chart k ⟨0⟩) (le_refl _)).hom.comp
        (Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X (⟨0⟩ : ULift.{u} (Fin 2)))).hom)
        (p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩) = p1XSection k
    rw [hbridge]; rfl
  -- every away element is a `(𝒜 0)`-combination of coordinate powers (the `ℤ`-span core)
  have hmem : a ∈ Submodule.span (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
      (Set.range fun m : ℕ => p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩ ^ m) :=
    span_p1CoordAway_pow_top Submodule.mem_top
  change ρ a ∈ Submodule.span k (Set.range fun n : ℕ => p1XSection k ^ n)
  induction hmem using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨m, rfl⟩ := hz
      rw [map_pow, hval]
      exact Submodule.subset_span ⟨m, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu =>
      obtain ⟨m, rfl⟩ := exists_intCast_eq_gradeZero c
      rw [Int.cast_smul_eq_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul k]
      exact Submodule.smul_mem _ _ hu

/-- **`V₀`-generators of type (2): the `Spec k`-side.**  The structure-morphism
pullback of a section `t ∈ Γ(Spec k, ⊤)` is the `k`-scalar `ΓSpecIso t` times `1`
(the structure-morphism algebra map factors as `iY.appLE ∘ ΓSpecIso.inv`), hence lies
in the span (which contains `1 = x⁰`). -/
private lemma mem_span_appLE_over
    (t : Γ(Spec (CommRingCat.of k), (⊤ : (Spec (CommRingCat.of k)).Opens))) :
    (Scheme.Hom.appLE (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
        ⊤ (p1Chart k ⟨0⟩) le_top).hom t
      ∈ Submodule.span k (Set.range fun n : ℕ => p1XSection k ^ n) := by
  -- `kToSection = ΓSpecIso.inv ≫ iY.appLE` (morphism level, `app ⊤` shared as subterm)
  have hcomp : Scheme.toModuleKSheaf.kToSection
        (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
        (op (p1Chart k ⟨0⟩))
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          Scheme.Hom.appLE
            (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
            ⊤ (p1Chart k ⟨0⟩) le_top := rfl
  have hkTo : ∀ c : k,
      algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩) c
      = (Scheme.Hom.appLE (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
          ⊤ (p1Chart k ⟨0⟩) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) := by
    intro c
    have e1 : algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩) c
        = (Scheme.toModuleKSheaf.kToSection
            (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
            (op (p1Chart k ⟨0⟩))).hom c := rfl
    rw [e1, hcomp]
    rfl
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom t) = t :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply t
  have h1 : (Scheme.Hom.appLE
        (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
        ⊤ (p1Chart k ⟨0⟩) le_top).hom t
      = algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩)
          ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom t) := by
    rw [hkTo, hinv]
  rw [h1, Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, pow_zero _⟩)

/-- **Route step 2 (the char-free base change): `Γ(V₀) = k[x]`.**  The first chart
`V₀ = p1Chart ⟨0⟩ = toProjInt ⁻¹ᵁ D₊(X₀)` of the `ℙ¹` model is the pullback of the
affine `D₊(X₀) ⊆ Proj ℤ[X₀,X₁]` along `Spec k → ⊤_Scheme`; as a fibre product of
affines its section ring is the ring pushout `Γ(D₊(X₀)) ⊗_ℤ k`
(`isIso_pushoutSection_of_isAffineOpen`), whose two structural maps ring-generate it
(`closure_range_union_range_eq_top_of_isPushout`).  The `Proj`-side generators land
in the `k`-span of the powers of `x = X₁/X₀` (`mem_span_appLE_toProjInt`); the
`Spec k`-side generators are `k`-multiples of `1` (`mem_span_appLE_over`).  Hence
`Γ(V₀)` is `k`-spanned by the powers of `x = p1XSection`. -/
theorem span_pow_p1XSection_scaffold :
    (⊤ : Submodule k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩)) ≤
      Submodule.span k (Set.range fun n : ℕ => p1XSection k ^ n) := by
  -- the defining pullback square of `ℙ¹`, in the `Scheme.Hom.pushoutSection` orientation
  have H : IsPullback
      (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
      (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
      (terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))))
      (terminal.from (Spec (CommRingCat.of k))) :=
    (IsPullback.of_hasPullback (terminal.from (Spec (CommRingCat.of k)))
      (terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))))).flip
  have hUY : p1Chart k ⟨0⟩
      = toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)) ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩)
        ⊓ (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ := by
    simp only [Scheme.Hom.preimage_top, inf_top_eq]
    rfl
  have hUST : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤
      terminal.from (Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ := (Scheme.Hom.preimage_top _).ge
  have hUSX : Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩) ≤
      terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))) ⁻¹ᵁ ⊤ :=
    le_top
  have hUS : IsAffineOpen (⊤ : (⊤_ Scheme.{u}).Opens) := isAffineOpen_top _
  have hUT : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  have hUX : IsAffineOpen
      (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩)) :=
    Proj.isAffineOpen_basicOpen _ _
      (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩) one_pos
  have hIso : IsIso (pushoutSection H hUST hUSX hUY) :=
    isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX
  have hpoCat := (isIso_pushoutSection_iff H hUST hUSX hUY).mp hIso
  have hclos := CommRingCat.closure_range_union_range_eq_top_of_isPushout hpoCat
  -- ### The two generating families ring-generate `Γ(V₀)`, so every section lies in the span.
  intro b hbtop
  clear hbtop
  have hb : b ∈ Subring.closure _ := hclos.ge (Subring.mem_top b)
  induction hb using Subring.closure_induction with
  | mem x hx =>
      rcases hx with ⟨s, rfl⟩ | ⟨t, rfl⟩
      · exact mem_span_appLE_toProjInt k s
      · exact mem_span_appLE_over k t
  | zero => exact Submodule.zero_mem _
  | one => exact Submodule.subset_span ⟨0, pow_zero _⟩
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | neg x _ hx => exact Submodule.neg_mem _ hx
  | mul x y _ _ hx hy => exact mul_mem_span_range_pow _ hx hy

/-! ### The `y`-chart mirror of the base change (`Γ(V₁) = k[y]`)

The `X₀ ↔ X₁` mirror of `span_pow_p1XSection_scaffold`, over the second chart
`V₁ = p1Chart ⟨1⟩ = toProjInt ⁻¹ᵁ D₊(X₁)` with coordinate `y = X₀/X₁ = p1YSection`.
Every step is the swap of the corresponding `x`-chart step, transporting the `y`-chart
span core `span_p1CoordAwayY_pow_top`. -/

/-- The `algebraSection` `k`-module structure on `Γ(V₁)` (mirror of `instAlgebraΓV0`). -/
noncomputable local instance instAlgebraΓV1 :
    Algebra k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩) :=
  Scheme.toModuleKSheaf.algebraSection
    (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
    (op (p1Chart k ⟨1⟩))

/-- The affine-chart map `awayToSection : (ℤ[X]_{X₁})₀ → Γ(D₊(X₁))` is surjective
(`X₁` is homogeneous of degree `1 > 0`); mirror of `awayToSection_X0_surjective`. -/
private lemma awayToSection_X1_surjective :
    Function.Surjective ⇑(Proj.awayToSection
      (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩)) := by
  haveI : IsIso (Proj.awayToSection
      (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩)) := by
    rw [← Proj.basicOpenIsoAway_hom (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      (X ⟨1⟩) (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩) one_pos]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso _).2

/-- **`V₁`-generators of type (1): the `Proj`-side (mirror).**  The `toProjInt`-pullback
of a section `s ∈ Γ(D₊(X₁))` lies in the `k`-span of the powers of `y = p1YSection`. -/
private lemma mem_span_appLE_toProjInt_y
    (s : Γ(Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)),
        Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩))) :
    (Scheme.Hom.appLE (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
        (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩))
        (p1Chart k ⟨1⟩) (le_refl _)).hom s
      ∈ Submodule.span k (Set.range fun n : ℕ => p1YSection k ^ n) := by
  have hbridge : Scheme.Hom.appLE (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
        (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩))
        (p1Chart k ⟨1⟩) (le_refl _)
      = (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).app
          (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩)) :=
    Scheme.Hom.appLE_eq_app _
  obtain ⟨a, rfl⟩ := awayToSection_X1_surjective s
  let ρ : Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X (⟨1⟩ : ULift.{u} (Fin 2))) →+*
      Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩) :=
    (Scheme.Hom.appLE (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
        (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X (⟨1⟩ : ULift.{u} (Fin 2))))
        (p1Chart k ⟨1⟩) (le_refl _)).hom.comp
      (Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X (⟨1⟩ : ULift.{u} (Fin 2)))).hom
  have hval : ρ (p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩) = p1YSection k := by
    change ((Scheme.Hom.appLE (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
          (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            (X (⟨1⟩ : ULift.{u} (Fin 2))))
          (p1Chart k ⟨1⟩) (le_refl _)).hom.comp
        (Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X (⟨1⟩ : ULift.{u} (Fin 2)))).hom)
        (p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩) = p1YSection k
    rw [hbridge]; rfl
  have hmem : a ∈ Submodule.span (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 0)
      (Set.range fun m : ℕ => p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩ ^ m) :=
    span_p1CoordAwayY_pow_top Submodule.mem_top
  change ρ a ∈ Submodule.span k (Set.range fun n : ℕ => p1YSection k ^ n)
  induction hmem using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨m, rfl⟩ := hz
      rw [map_pow, hval]
      exact Submodule.subset_span ⟨m, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu =>
      obtain ⟨m, rfl⟩ := exists_intCast_eq_gradeZero c
      rw [Int.cast_smul_eq_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul k]
      exact Submodule.smul_mem _ _ hu

/-- **`V₁`-generators of type (2): the `Spec k`-side (mirror).**  The structure-morphism
pullback of `t ∈ Γ(Spec k, ⊤)` is the `k`-scalar `ΓSpecIso t` times `1`, hence in the
span; mirror of `mem_span_appLE_over`. -/
private lemma mem_span_appLE_over_y
    (t : Γ(Spec (CommRingCat.of k), (⊤ : (Spec (CommRingCat.of k)).Opens))) :
    (Scheme.Hom.appLE (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
        ⊤ (p1Chart k ⟨1⟩) le_top).hom t
      ∈ Submodule.span k (Set.range fun n : ℕ => p1YSection k ^ n) := by
  have hcomp : Scheme.toModuleKSheaf.kToSection
        (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
        (op (p1Chart k ⟨1⟩))
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          Scheme.Hom.appLE
            (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
            ⊤ (p1Chart k ⟨1⟩) le_top := rfl
  have hkTo : ∀ c : k,
      algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩) c
      = (Scheme.Hom.appLE (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
          ⊤ (p1Chart k ⟨1⟩) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) := by
    intro c
    have e1 : algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩) c
        = (Scheme.toModuleKSheaf.kToSection
            (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
            (op (p1Chart k ⟨1⟩))).hom c := rfl
    rw [e1, hcomp]
    rfl
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom t) = t :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply t
  have h1 : (Scheme.Hom.appLE
        (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
        ⊤ (p1Chart k ⟨1⟩) le_top).hom t
      = algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩)
          ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom t) := by
    rw [hkTo, hinv]
  rw [h1, Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, pow_zero _⟩)

/-- **Route step 2 (`y`-chart): `Γ(V₁) = k[y]`.**  The second chart `V₁ = p1Chart ⟨1⟩`
of the `ℙ¹` model is the pullback of the affine `D₊(X₁)`; its section ring is the ring
pushout `Γ(D₊(X₁)) ⊗_ℤ k`, whose two structural maps ring-generate it.  The `Proj`-side
generators land in the `k`-span of the powers of `y = X₀/X₁` (`mem_span_appLE_toProjInt_y`);
the `Spec k`-side generators are `k`-multiples of `1` (`mem_span_appLE_over_y`).  Mirror of
`span_pow_p1XSection_scaffold`. -/
theorem span_pow_p1YSection_scaffold :
    (⊤ : Submodule k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩)) ≤
      Submodule.span k (Set.range fun n : ℕ => p1YSection k ^ n) := by
  have H : IsPullback
      (toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
      (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
      (terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))))
      (terminal.from (Spec (CommRingCat.of k))) :=
    (IsPullback.of_hasPullback (terminal.from (Spec (CommRingCat.of k)))
      (terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))))).flip
  have hUY : p1Chart k ⟨1⟩
      = toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)) ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩)
        ⊓ (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ := by
    simp only [Scheme.Hom.preimage_top, inf_top_eq]
    rfl
  have hUST : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤
      terminal.from (Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ := (Scheme.Hom.preimage_top _).ge
  have hUSX : Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩) ≤
      terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))) ⁻¹ᵁ ⊤ :=
    le_top
  have hUS : IsAffineOpen (⊤ : (⊤_ Scheme.{u}).Opens) := isAffineOpen_top _
  have hUT : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  have hUX : IsAffineOpen
      (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩)) :=
    Proj.isAffineOpen_basicOpen _ _
      (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩) one_pos
  have hIso : IsIso (pushoutSection H hUST hUSX hUY) :=
    isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX
  have hpoCat := (isIso_pushoutSection_iff H hUST hUSX hUY).mp hIso
  have hclos := CommRingCat.closure_range_union_range_eq_top_of_isPushout hpoCat
  intro b hbtop
  clear hbtop
  have hb : b ∈ Subring.closure _ := hclos.ge (Subring.mem_top b)
  induction hb using Subring.closure_induction with
  | mem x hx =>
      rcases hx with ⟨s, rfl⟩ | ⟨t, rfl⟩
      · exact mem_span_appLE_toProjInt_y k s
      · exact mem_span_appLE_over_y k t
  | zero => exact Submodule.zero_mem _
  | one => exact Submodule.subset_span ⟨0, pow_zero _⟩
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | neg x _ hx => exact Submodule.neg_mem _ hx
  | mul x y _ _ hx hy => exact mul_mem_span_range_pow _ hx hy

end BaseChange

/-! ## The overlap identities (route step 3) and the final assembly -/

section Overlap

open ProjectiveSpace HomogeneousLocalization

/-- The coordinate fraction `Xⱼ/Xᵢ = p1CoordAway i j` is exactly the localization
element `Away.isLocalizationElem` that mathlib uses to describe `Away 𝒜 (XᵢXⱼ)` as a
localization of `Away 𝒜 Xᵢ` (both are `Xⱼ/Xᵢ`, differing only by `Xⱼ^1` vs `Xⱼ`). -/
private lemma p1CoordAway_eq_isLocalizationElem (i j : ULift.{u} (Fin 2)) :
    p1CoordAway (ULift.{u} (Fin 2)) i j
      = Away.isLocalizationElem
          (𝒜 := homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) i)
          (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) j) := by
  apply HomogeneousLocalization.val_injective
  simp only [p1CoordAway, Away.isLocalizationElem, Away.val_mk, pow_one]

set_option backward.isDefEq.respectTransparency false in
-- `respectTransparency false`: the proof repeatedly crosses the `Proj`/`Scheme.Opens`
-- presheaf-carrier diamond (`X.presheaf` as `TopCat.Presheaf` vs functor); the fleet recipe.
/-- **The Proj-side basic open of the coordinate section.**  The non-vanishing locus
of the section `Xⱼ/Xᵢ = awayToSection (p1CoordAway i j)` inside the chart `D₊(Xᵢ)` is the
overlap `D₊(Xᵢ) ⊓ D₊(Xⱼ)`.  Transport the affine-chart identity: on `D₊(Xᵢ) ≅ Spec(Away)`
the section corresponds to `Xⱼ/Xᵢ`, whose basic open is `D(Xⱼ/Xᵢ) = awayι ⁻¹ D₊(Xⱼ)`
(`awayι_preimage_basicOpen`), and the image under `awayι` is `D₊(Xᵢ) ⊓ D₊(Xⱼ)`. -/
private lemma proj_basicOpen_awayToSection_coord (i j : ULift.{u} (Fin 2)) :
    Scheme.basicOpen (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)))
        ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)).hom
          (p1CoordAway (ULift.{u} (Fin 2)) i j))
      = Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)
        ⊓ Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X j) := by
  have hi : X i ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 1 :=
    ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) i
  have hj : X j ∈ homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ) 1 :=
    ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) j
  -- crux: on the affine chart `D₊(Xᵢ) ≅ Spec(Away)`, the section `awayToSection a`
  -- restricts to the Spec section corresponding to `a` (from `basicOpenToSpec_app_top`).
  have hcrux : (Proj.basicOpenIsoSpec (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X i) hi one_pos).hom.app ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (Away
          (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)))).inv.hom
          (p1CoordAway (ULift.{u} (Fin 2)) i j))
      = (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X i)).topIso.inv.hom
          ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)).hom
            (p1CoordAway (ULift.{u} (Fin 2)) i j)) := by
    rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top,
        CommRingCat.comp_apply, Iso.inv_hom_id_apply, CommRingCat.comp_apply]
    rfl
  -- step B: on the affine chart, the basic open of that section is `φ.hom ⁻¹ᵁ D(a)`.
  have hB : (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X i)).toScheme.basicOpen
        ((Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X i)).topIso.inv.hom
          ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)).hom
            (p1CoordAway (ULift.{u} (Fin 2)) i j)))
      = (Proj.basicOpenIsoSpec (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X i) hi one_pos).hom ⁻¹ᵁ
          PrimeSpectrum.basicOpen (p1CoordAway (ULift.{u} (Fin 2)) i j) := by
    have hpre := Scheme.preimage_basicOpen
      (Proj.basicOpenIsoSpec (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X i) hi one_pos).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Away
        (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)))).inv.hom
        (p1CoordAway (ULift.{u} (Fin 2)) i j))
    rw [hcrux] at hpre
    rw [← hpre]
    congr 1
    exact basicOpen_eq_of_affine
      (R := CommRingCat.of (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)))
      (p1CoordAway (ULift.{u} (Fin 2)) i j)
  -- step C: `ι = φ.hom ≫ awayι`.
  have hιfac : (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)).ι
      = (Proj.basicOpenIsoSpec (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X i) hi one_pos).hom
        ≫ Proj.awayι (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i) hi one_pos := by
    rw [← Proj.basicOpenIsoSpec_inv_ι (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      (X i) hi one_pos, Iso.hom_inv_id_assoc]
  rw [← (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X i)).ι_image_basicOpen_topIso_inv
        ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)).hom
          (p1CoordAway (ULift.{u} (Fin 2)) i j)),
      hB]
  -- `.ι ''ᵁ (φ.hom ⁻¹ᵁ W) = awayι ''ᵁ W` (rewrite `ι = φ.hom ≫ awayι` inside `conv`)
  have himg : (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)).ι ''ᵁ
        ((Proj.basicOpenIsoSpec (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X i) hi one_pos).hom ⁻¹ᵁ PrimeSpectrum.basicOpen (p1CoordAway (ULift.{u} (Fin 2)) i j))
      = Proj.awayι (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i) hi one_pos ''ᵁ
          PrimeSpectrum.basicOpen (p1CoordAway (ULift.{u} (Fin 2)) i j) := by
    simp only [hιfac, Scheme.Hom.comp_image, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  rw [himg, p1CoordAway_eq_isLocalizationElem i j,
      ← Proj.awayι_preimage_basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        hi one_pos hj one_pos,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Proj.opensRange_awayι]

/-- **The overlap-as-basic-open identity (route step 3).**  The overlap of the two chart
preimages `V_i ⊓ V_j = toProjInt ⁻¹ᵁ (D₊(Xᵢ) ⊓ D₊(Xⱼ))` is exactly the non-vanishing
locus of the coordinate section `p1CoordSection i j` on `ℙ¹`; pull back the Proj-side
identity `proj_basicOpen_awayToSection_coord` along `toProjInt`. -/
private lemma p1Chart_inf_eq_basicOpen_coordSection (k : Type u) [Field k]
    (i j : ULift.{u} (Fin 2)) :
    p1Chart k i ⊓ p1Chart k j
      = Scheme.basicOpen (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)))
          (((ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).app
              (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
                (X i))).hom
            ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
                (X i)).hom
              (p1CoordAway (ULift.{u} (Fin 2)) i j))) := by
  rw [← Scheme.preimage_basicOpen
        (ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)))
        ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X i)).hom
          (p1CoordAway (ULift.{u} (Fin 2)) i j)),
      proj_basicOpen_awayToSection_coord i j, Scheme.Hom.preimage_inf]
  rfl

/-- **The hoisted overlap polynomial `X₀ · X₁`** — a *single* elaborated copy of the
product, shared by every `D₊(X₀X₁)`/`Away 𝒜 (X₀X₁)` occurrence in the overlap
computation below.  **Elaboration note (fleet recipe):** a bare `X ⟨0⟩ * X ⟨1⟩` is
elaborated by `binop%` with the leaf indices under pending metavariables, so distinct
occurrences can pick *different* `OfNat (Fin 2)`-instance terms; any cross-occurrence
`isDefEq` then descends through `Submonoid.powers`/`MvPolynomial` and is astronomically
slow.  Referencing this one def makes all occurrences syntactically identical. -/
noncomputable def p1XY : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ) :=
  X (⟨0⟩ : ULift.{u} (Fin 2)) * X (⟨1⟩ : ULift.{u} (Fin 2))

/-- `X₀ · X₁ = X₁ · X₀`, with the hoisted copy `p1XY` on the left — the `hx`-input of
the `awayMap : Away 𝒜 X₁ → Away 𝒜 (X₀X₁)` transporting the `y`-coordinate. -/
private lemma p1XY_eq_comm :
    p1XY = X (⟨1⟩ : ULift.{u} (Fin 2)) * X (⟨0⟩ : ULift.{u} (Fin 2)) :=
  mul_comm (X (⟨0⟩ : ULift.{u} (Fin 2))) (X (⟨1⟩ : ULift.{u} (Fin 2)))

/-- The away-ring unit relation with a clean generalized binder `x` for the overlap
localiser (the two `awayMap`s land in `Away 𝒜 x` for *any* `x` presenting `X₀X₁`):
`awayMap` of the two coordinate fractions multiply to `1` in `Away 𝒜 x` (both are
`x`-fractions and mutually inverse).  `subst` recovers the concrete-product proof. -/
private lemma awayMap_coord_mul_eq_one_aux
    {x : MvPolynomial (ULift.{u} (Fin 2)) (ULift.{u} ℤ)}
    (hx₁ : x = X (⟨0⟩ : ULift.{u} (Fin 2)) * X (⟨1⟩ : ULift.{u} (Fin 2)))
    (hx₂ : x = X (⟨1⟩ : ULift.{u} (Fin 2)) * X (⟨0⟩ : ULift.{u} (Fin 2))) :
    HomogeneousLocalization.awayMap (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩)
        hx₁
        (p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩)
      * HomogeneousLocalization.awayMap (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩)
          hx₂
          (p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩) = 1 := by
  subst hx₁
  apply HomogeneousLocalization.val_injective
  simp only [p1CoordAway, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_one, HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, mul_one, MulMemClass.coe_mul]
  ring

/-- The image of the coordinate `Xⱼ/Xᵢ` under the away-restriction `Away 𝒜 Xᵢ → Away 𝒜 (X₀X₁)`
computed on the standard chart pair: `awayMap` of the two coordinate fractions multiply to `1`
in `Away 𝒜 (X₀X₁)` (both are `X₀X₁`-fractions and mutually inverse), stated through the
hoisted product `p1XY`. -/
private lemma awayMap_coord_mul_eq_one :
    HomogeneousLocalization.awayMap (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩)
        (rfl : p1XY = X (⟨0⟩ : ULift.{u} (Fin 2)) * X (⟨1⟩ : ULift.{u} (Fin 2)))
        (p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩)
      * HomogeneousLocalization.awayMap (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩)
          p1XY_eq_comm
          (p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩) = 1 :=
  awayMap_coord_mul_eq_one_aux rfl p1XY_eq_comm

/-- The overlap of the two `ℙ¹` charts is the `toProjInt`-preimage of the degree-`2`
basic open `D₊(X₀ · X₁)` (the two charts pull back `D₊(X₀)`, `D₊(X₁)`, and
`D₊(X₀) ⊓ D₊(X₁) = D₊(X₀X₁)` by `Proj.basicOpen_mul`), stated through the hoisted
product `p1XY`. -/
private lemma p1Chart_inf_eq_preimage_mul (k : Type u) [Field k] :
    p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩
      = ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)) ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) p1XY := by
  rw [show p1XY = X (⟨0⟩ : ULift.{u} (Fin 2)) * X (⟨1⟩ : ULift.{u} (Fin 2)) from rfl,
    Proj.basicOpen_mul]
  rfl

/-- **Overlap restriction of `x`.**  The restriction of the chart coordinate `x = p1XSection`
to `V₀ ⊓ V₁` is the `toProjInt`-pullback (via `appLE` over `D₊(X₀X₁)`, with the hoisted
product `p1XY` as the localiser) of the away section `X₁/X₀` transported into
`Away 𝒜 (X₀X₁)` by `awayMap`.  Morphism-level factorisation of
`awayToSection X₀ ≫ appLE D₊(X₀)` through `awayMap` and `D₊(X₀X₁)`. -/
private lemma res_p1XSection (k : Type u) [Field k] :
    ((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))).presheaf.map
        (homOfLE (inf_le_left : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩ ≤ p1Chart k ⟨0⟩)).op).hom
      (p1XSection k)
      = ((ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).appLE
          (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) p1XY)
          (p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩)
          (p1Chart_inf_eq_preimage_mul k).le).hom
        ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            p1XY).hom
          (awayMap (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩)
            (rfl : p1XY = X (⟨0⟩ : ULift.{u} (Fin 2)) * X (⟨1⟩ : ULift.{u} (Fin 2)))
            (p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩))) := by
  have Mx :
      (Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X (⟨0⟩ : ULift.{u} (Fin 2))))
        ≫ (ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).appLE
            (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
              (X (⟨0⟩ : ULift.{u} (Fin 2))))
            (p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩)
            (inf_le_left : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩ ≤ p1Chart k ⟨0⟩)
      = CommRingCat.ofHom (awayMap (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨1⟩)
            (rfl : p1XY = X (⟨0⟩ : ULift.{u} (Fin 2)) * X (⟨1⟩ : ULift.{u} (Fin 2))))
          ≫ (Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) p1XY)
          ≫ (ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).appLE
              (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) p1XY)
              (p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩)
              (p1Chart_inf_eq_preimage_mul k).le := by
    rw [Proj.awayMap_awayToSection_assoc, Scheme.Hom.map_appLE]
  exact congrArg (fun φ => φ.hom (p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩)) Mx

/-- **Overlap restriction of `y`** (mirror of `res_p1XSection`).  The restriction of
`y = p1YSection` to `V₀ ⊓ V₁` is the `appLE`-pullback of `X₀/X₁` transported into
`Away 𝒜 (X₀X₁)` by `awayMap` (using `p1XY_eq_comm` so the away localiser is the common
hoisted `p1XY`). -/
private lemma res_p1YSection (k : Type u) [Field k] :
    ((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))).presheaf.map
        (homOfLE (inf_le_right : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩ ≤ p1Chart k ⟨1⟩)).op).hom
      (p1YSection k)
      = ((ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).appLE
          (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) p1XY)
          (p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩)
          (p1Chart_inf_eq_preimage_mul k).le).hom
        ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            p1XY).hom
          (awayMap (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩)
            p1XY_eq_comm
            (p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩))) := by
  have My :
      (Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (X (⟨1⟩ : ULift.{u} (Fin 2))))
        ≫ (ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).appLE
            (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
              (X (⟨1⟩ : ULift.{u} (Fin 2))))
            (p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩)
            (inf_le_right : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩ ≤ p1Chart k ⟨1⟩)
      = CommRingCat.ofHom (awayMap (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
            (ProjTwist.X_mem_deg_one (ULift.{u} (Fin 2)) ⟨0⟩)
            p1XY_eq_comm)
          ≫ (Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) p1XY)
          ≫ (ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).appLE
              (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) p1XY)
              (p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩)
              (p1Chart_inf_eq_preimage_mul k).le := by
    rw [Proj.awayMap_awayToSection_assoc, Scheme.Hom.map_appLE]
  exact congrArg (fun φ => φ.hom (p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩)) My

/-- **The unit relation `res x · res y = 1` on the overlap (route step 3).**  Both
restrictions factor, by `res_p1XSection`/`res_p1YSection`, through the common overlap
ring map `toProjInt.appLE D₊(X₀X₁)`, whence the product is the pullback of
`awayToSection (awayMap(X₁/X₀) · awayMap(X₀/X₁))`; the away-ring identity
`awayMap_coord_mul_eq_one` collapses the argument to `1`. -/
private lemma p1_res_x_mul_res_y (k : Type u) [Field k] :
    ((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))).presheaf.map
        (homOfLE (inf_le_left : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩ ≤ p1Chart k ⟨0⟩)).op).hom
      (p1XSection k)
      * ((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))).presheaf.map
          (homOfLE (inf_le_right : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩ ≤ p1Chart k ⟨1⟩)).op).hom
        (p1YSection k)
      = 1 := by
  rw [res_p1XSection k, res_p1YSection k, ← map_mul, ← map_mul,
    awayMap_coord_mul_eq_one, map_one, map_one]

/-- **The `ℙ¹` Laurent chart datum (route step 4, assembly).**  On the standard 2-chart
geometry `p1CoverSquare` of `ℙ¹ = ℙ(ULift (Fin 2); Spec k)` (charts `V₀ = p1Chart ⟨0⟩`,
`V₁ = p1Chart ⟨1⟩`, coordinates `x = p1XSection`, `y = p1YSection`), the chart-ring
computation assembles into the `Adelic.LaurentChartData` consumed by the keystone:
the overlap is the basic open of either coordinate (`p1Chart_inf_eq_basicOpen_coordSection`),
the coordinates are mutually inverse (`p1_res_x_mul_res_y`), and each chart ring is the
`k`-span of the powers of its coordinate (`span_pow_p1XSection_scaffold`,
`span_pow_p1YSection_scaffold`). -/
noncomputable def p1LaurentChartData (k : Type u) [Field k] :
    LaurentChartData
      (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) where
  V₀ := p1Chart k ⟨0⟩
  V₁ := p1Chart k ⟨1⟩
  isAffineOpen_V₀ := isAffineOpen_p1Chart k ⟨0⟩
  isAffineOpen_V₁ := isAffineOpen_p1Chart k ⟨1⟩
  cover := p1Chart_sup_eq_top k
  x := p1XSection k
  y := p1YSection k
  inf_eq_basicOpen_x := p1Chart_inf_eq_basicOpen_coordSection k ⟨0⟩ ⟨1⟩
  inf_eq_basicOpen_y := by
    rw [inf_comm]
    exact p1Chart_inf_eq_basicOpen_coordSection k ⟨1⟩ ⟨0⟩
  res_x_mul_res_y := p1_res_x_mul_res_y k
  span_pow_x := span_pow_p1XSection_scaffold k
  span_pow_y := span_pow_p1YSection_scaffold k

/-- **Gate #1 of the genus theorem discharged.**  The concrete projective line
`ℙ(ULift (Fin 2); Spec k)` carries Laurent chart data (`p1LaurentChartData`), so the
`Adelic.P1HasLaurentChartData` gate holds for every field `k` — the char-free Route B
of the module header, closing node `N11b`. -/
noncomputable instance instP1HasLaurentChartData (k : Type u) [Field k] :
    P1HasLaurentChartData k :=
  ⟨⟨p1LaurentChartData k⟩⟩

end Overlap

end AlgebraicGeometry.Adelic
