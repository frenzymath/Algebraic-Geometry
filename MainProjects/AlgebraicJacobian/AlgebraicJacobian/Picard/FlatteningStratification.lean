/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

/-!
# Flattening stratification of a coherent sheaf (A.2.a)

This file is the **A.2.a** file-skeleton sub-build chapter for the project's
positive-genus arm of `nonempty_jacobianWitness`. It packages the
Nitsure~\S4 flattening-stratification theorem — the technical heart that
turns the absolute Quot-functor representability problem on a projective
morphism `π : X ⟶ S` with coherent input `𝓕` into a finite collection of
locally-closed strata over which `𝓕` becomes flat.

## Status (run 0010, T12 r5 — algebraic generic freeness CLOSED, axiom-clean)

**`genericFlatness` is now proved** (sorry-free), in the companion file
`AlgebraicJacobian.Picard.GenericFlatnessGeometric`: the geometric glue there
turns the algebraic statement of this file into the scheme-level one.  The
chart supply is `Scheme.Modules.exists_affine_finite_sections_nhds`
(Stacks 01PC finite-type half, proved in `Picard/QuotScheme.lean` from the
tilde–Γ adjunction); the per-pair reduction is `flat_section_pair` (a
fibre-side `Module.flat_of_isLocalized_span` over simultaneous basic opens,
then two `Module.flat_iff_of_isLocalization` base exchanges), whose per-piece
core `flat_section_chartBasic` localizes the chart freeness through the qcqs
section-localization engine (Stacks 01P0) and the mixed-base stability lemma
`Module.Flat.of_isLocalizedModule_algebra`.  That companion file, not this
one, imports the QuotScheme engine — keeping the instance environment of the
heavy dévissage proofs below unperturbed.

The `GenericFreeness` section is **sorry-free and kernel-checked**
(axioms: `propext`, `Classical.choice`, `Quot.sound` only): the dévissage
layer (splicing, torsion base case, localization transport, prime-filtration
assembly), the r3 sub-lemma layer for the domain core (integral-dimension
comparisons `ringKrullDim_le_of_isIntegral` /
`le_ringKrullDim_of_isIntegral_of_injective`, variable scaling
`exists_scaled_noether_datum`, denominator clearing
`exists_smul_isIntegralElem_of_fibre_finite`, fibre-dimension bound
`exists_nat_fibre_dim_le`), and the strong induction
`genericallyFree_quotient_prime_of_fibre_dim_le` itself, assembled into
`genericFlatnessAlgebraic` (Stacks 051R over a noetherian domain).  The r3
kernel walls (issue `I-0093`: a `Module.Free` synthesis failure and two
divergent-`whnf` timeouts, all inside the generic-rank block where the
module was the `set`-bound subalgebra subtype `↥C''` under a `letI`
algebra) were repaired in r5 by extracting that block into the standalone
lemma `exists_generic_rank_comparison`, whose clean binder context
(`D` a domain, `M` an abstract finite module) elaborates without incident;
the residual double-quotient instance stuckness in the induction is cured
by a scoped `maxSynthPendingDepth` bump.

Earlier r2 repairs of three FALSE pinned statements (quasi-compactness in
`genericFlatness`, flatness-over-the-stratum in `flatLocusStratification`,
the bundled universal property in the universal-property theorem, since r7
specialized to `n = 0` and renamed `flatLocusStratification_universal`) are
documented in the per-declaration docstrings.

This file is **sorry-free**: the geometric statements (`genericFlatness`,
`flatLocusStratification`, `flatLocusReduction`,
`flatteningStratification`, `ofCurve`) live in
`GenericFlatnessGeometric.lean` (all proved axiom-clean), and the `n = 0`
universal property `flatLocusStratification_universal` (canonical
entry-ideal strata) is proved axiom-clean in
`FlatteningStratificationUniversal.lean`.

The 4 blueprint-pinned declarations are:

1. `AlgebraicGeometry.Scheme.CoherentSheafFlat` (def, ~8 LOC) — the
   **coherent-sheaf flatness predicate** for a coherent `𝓕` on `X` over
   `S` via `f : X ⟶ S`. Affine-locally: for `U ⊆ S` and `V ⊆ f⁻¹U` both
   affine, `Γ(𝓕, V)` is a flat `Γ(S, U)`-module via the composite
   `Γ(S, U) → Γ(X, V) → End(Γ(𝓕, V))`. The corresponding Stacks tag is
   00HB (module-level) lifted to a sheaf-level predicate by the
   affine-local descent characterisation.

2. `AlgebraicGeometry.genericFlatness` (theorem, ~15 LOC) — **generic
   flatness** [Nitsure §4 Theorem]: over a noetherian integral base
   `S`, a coherent sheaf on a finite-type `X ⟶ S` is flat over a
   non-empty open `V ⊆ S`.

3. `AlgebraicGeometry.flatteningStratification` (theorem, ~25 LOC) — the
   **flattening-stratification existence theorem** [Nitsure §4]: for `S`
   noetherian and `𝓕` coherent on a proper `π : X ⟶ S`, there exists a
   finite locally-closed stratification `{S_f}` of `S` (set-theoretically
   covering, pairwise disjoint) such that `𝓕` becomes flat on each
   stratum.

4. `AlgebraicGeometry.flatteningStratification_universal` (theorem, ~15 LOC)
   — the **universal property** of the stratification [Nitsure §4 (ii)]:
   any morphism `φ : T ⟶ S` such that `𝓕` pulled back to `X ×_S T` is
   `T`-flat factors uniquely through the stratum coproduct
   `i : ⨿ S_f ⟶ S`.

Additionally, three sub-lemmas decompose the existence proof, plus a
curve-specialisation corollary feeding the Route~A consumer:

5. `AlgebraicGeometry.flatLocusStratification` (lemma, ~12 LOC) — the
   **special case `n = 0`** [Nitsure §4, n=0]: a coherent `𝓕` on `S`
   admits a finite locally-closed stratification by integer "rank"
   strata.

6. `AlgebraicGeometry.flatLocusReduction` (lemma, ~12 LOC) — the
   **Noetherian-induction reduction** [Nitsure §4 general case opening]:
   a finite reduced locally-closed stratification on which `𝓕`
   *already* becomes flat (without polynomial indexing).

7. `AlgebraicGeometry.flatLocusAssembly` (lemma, ~15 LOC) — the
   **assembly step** [Nitsure §4 via direct images]: combining the
   `n = 0` stratification iteratively on the direct images
   `E_i = π_* 𝓕(N+i)` to refine to the Hilbert-polynomial-indexed
   stratification.

8. `AlgebraicGeometry.flatteningStratification.ofCurve` (theorem, ~10 LOC)
   — the **relative-curve specialisation** for the Route~A consumer
   `C ×_k T → T`.

## Note on type expressivity

Following the project rule "Never weaken the type to dodge the proof",
each declaration carries a substantive, non-tautological type:

- `CoherentSheafFlat` reduces to module-theoretic flatness of every
  affine-local section module over the corresponding affine-base ring
  via the `appLE` ring-hom — non-empty content because flatness of a
  module is the standard non-trivial homological condition.
- `genericFlatness` requires the existence of a *non-empty* open `V`
  and substantive flatness on every affine `U ⊆ V`; both quantifiers
  are necessary (without them the statement collapses to `V = ∅`).
- `flatteningStratification` packages a *finite* indexed family of
  *locally-closed-immersions* `ι : S_f ⟶ S` that pairwise *cover*
  `|S|` *disjointly* AND on which the pullback `𝓕|_{X ×_S S_f}` becomes
  `S_f`-flat — all four conjuncts are substantive (any single
  one trivialises if dropped).
- `flatteningStratification_universal` packages the universal property
  via `∃!` (unique existence of factorisation), a substantive Yoneda
  bijection content.

## Mathlib status

Mathlib (master `b80f227`) provides `Module.Flat`,
`AlgebraicGeometry.Flat` (morphism-level), `IsImmersion`,
`IsLocallyNoetherian`, `IsIntegral`, `LocallyOfFiniteType`. It does NOT
provide: a relative projective space `ℙⁿ_S`, an `IsProjective` morphism
property, the flattening-stratification construction, or coherent-sheaf
flatness as a sheaf-level predicate.

The current file-skeleton uses `IsProper π` as the structural stand-in
for "projective `π`" (every projective morphism is proper; the
restriction is harmless in the Route~A consumer setting where `π` comes
from a smooth proper curve, which is automatically projective).
iter-177+ refinement: once Mathlib gains an `IsProjective` morphism
property, the hypothesis tightens.

## References

Blueprint: `blueprint/src/chapters/Picard_FlatteningStratification.tex`
(735 LOC, 4 pins + 4 sub-lemma/corollary names). Source: Nitsure,
"Construction of Hilbert and Quot schemes", §4 (FGA Explained Ch. 5,
arXiv:math/0504020 pp. 5–18); Stacks Project tags 00HB (module flat),
052H (flattening stratification).
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## Project-local Mathlib supplement — algebraic generic freeness (finite case)

This section builds the **module-theoretic** generic-freeness statements that
underlie the geometric `genericFlatness` (blueprint
`thm:generic_flatness_algebraic`, Nitsure~\S4 "Lemma on Generic Flatness").

The full algebraic statement — `A` a noetherian domain, `B` a *finite-type*
`A`-algebra, `M` a finite `B`-module ⟹ `∃ f ≠ 0` with `M_f` free over `A_f` —
is a deep theorem (prime-filtration dévissage + Noether normalisation +
clearing denominators). Mathlib does **not** contain it (checked against the
pinned revision; only the spreading-out lemma
`Module.FinitePresentation.exists_free_localizedModule_powers` exists).

This section proves it in full (axiom-clean, no `sorry`): the
**finite-module / finite-morphism case**
(`exists_free_localizationAway_of_finite`, via
`exists_free_localizedModule_powers` at the generic point), the **dévissage
layer** (`GenericallyFree`, `free_localizedModule_powers_mul`,
`GenericallyFree.of_linearEquiv`, `genericallyFree_of_exact`,
`genericallyFree_of_subsingleton`, `genericallyFree_of_torsion`, and the
prime-filtration frame `genericallyFree_of_forall_quotient_prime` via
`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`), and the
**Noether-normalisation domain core** `genericallyFree_quotient_prime`
(strong induction on the Krull dimension of the generic fibre; see its
docstring), assembled into `genericFlatnessAlgebraic`. -/

namespace GenericFreeness

/-- **Generic freeness, finite-module case.** For a noetherian integral domain
`A` and a finite `A`-module `M`, there is a non-zero `f ∈ A` such that the
localisation `M_f` is free over `A_f = Localization.Away f`.

This is the `d = 0` (finite-morphism) special case of the algebraic
generic-flatness theorem (`thm:generic_flatness_algebraic`, Nitsure~\S4):
inverting the generic point `Frac A`, the localised module is a finite vector
space hence free, and `Module.FinitePresentation.exists_free_localizedModule_powers`
descends that freeness to a single basic open `D(f) ⊆ Spec A`. -/
theorem exists_free_localizationAway_of_finite
    (A : Type*) (M : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ f : A, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers (nonZeroDivisors A)
      (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  exact ⟨r, nonZeroDivisors.ne_zero hr, hfree⟩

/-- **Generic flatness, finite-module case.** The flatness form of
`exists_free_localizationAway_of_finite`: for a noetherian domain `A` and a
finite `A`-module `M`, there is a non-zero `f` with `M_f` flat over `A_f`.
This is the affine-local content of `genericFlatness` for a finite morphism. -/
theorem exists_flat_localizationAway_of_finite
    (A : Type*) (M : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ f : A, f ≠ 0 ∧
      Module.Flat (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  obtain ⟨f, hf, hfree⟩ := exists_free_localizationAway_of_finite A M
  haveI := hfree
  exact ⟨f, hf, Module.Flat.of_free⟩

/-- **Generic freeness, finite-morphism case.** If `A` is a noetherian domain,
`B` a *module-finite* `A`-algebra, and `M` a finite `B`-module (with the
compatible `A`-module structure), then there is a non-zero `f ∈ A` with `M_f`
free over `A_f`. Reduces to `exists_free_localizationAway_of_finite` via
`Module.Finite.trans` (a finite module over a module-finite algebra is finite
over the base). This is generic flatness for a *finite* morphism `X → S`. -/
theorem exists_free_localizationAway_of_moduleFinite
    (A : Type*) (B : Type*) (M : Type*)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    [Module A M] [IsScalarTower A B M] :
    ∃ f : A, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  haveI : Module.Finite A M := Module.Finite.trans B M
  exact exists_free_localizationAway_of_finite A M

/-! ### The dévissage frame for full algebraic generic freeness

Grothendieck's generic-freeness lemma (blueprint
`thm:generic_flatness_algebraic`, Nitsure §4 "Lemma on Generic Flatness"):
for `A` a noetherian domain, `B` a finite-type `A`-algebra and `M` a finite
`B`-module there is `f ≠ 0` in `A` with `M_f` free over `A_f`.

Nitsure's proof has two layers: a *dévissage* (prime filtration of `M` as a
module over the noetherian ring `B`, reducing to `M = B/𝔭`, via the splicing
fact that generic freeness is stable under extensions), and a *domain core*
(`M = B/𝔭`: Noether normalisation over `Frac A` + clearing denominators +
the generic-rank exact sequence + induction on fibre dimension). This
section proves both layers completely — the splicing lemma
`genericallyFree_of_exact` (via `ModuleCat.free_shortExact` and the
localization-transport lemma `free_localizedModule_powers_mul`), the torsion
base case `genericallyFree_of_torsion` (Nitsure's `n = -1`), the domain core
`genericallyFree_quotient_prime` (Noether normalisation +
`genericallyFree_quotient_prime_of_fibre_dim_le`), and the assembly
`genericFlatnessAlgebraic` via
`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`. -/

/-- The **generic-freeness property** of an `A`-module `M`: some localization
`M_f` at a single non-zero `f ∈ A` is a free module over `A_f`. This is the
conclusion shared by every statement of this section. -/
def GenericallyFree (A : Type*) (M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] : Prop :=
  ∃ f : A, f ≠ 0 ∧
    Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

/-- Generic freeness transports along enlarging the inverted element: if `M_f`
is free over `A_f` then `M_{fg}` is free over `A_{fg}` for every `g`. The
proof is base-change associativity
`A_{fg} ⊗_{A_f} (A_f ⊗_A M) ≅ A_{fg} ⊗_A M` together with freeness of base
change (`Module.Free.tensor`); the two tensor legs are identified with the
localized modules by `IsLocalizedModule.isBaseChange`. -/
theorem free_localizedModule_powers_mul (A : Type*) (M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] (f g : A)
    (hf : Module.Free (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free (Localization.Away (f * g))
      (LocalizedModule (Submonoid.powers (f * g)) M) := by
  haveI := hf
  letI : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away f)
      (P := Localization.Away (f * g)) f g).toAlgebra
  haveI : IsScalarTower A (Localization.Away f) (Localization.Away (f * g)) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away f)
        (P := Localization.Away (f * g)) f g a).symm
  have e_f : (Localization.Away f) ⊗[A] M ≃ₗ[Localization.Away f]
      LocalizedModule (Submonoid.powers f) M :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).equiv
  have e_fg : (Localization.Away (f * g)) ⊗[A] M ≃ₗ[Localization.Away (f * g)]
      LocalizedModule (Submonoid.powers (f * g)) M :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers (f * g))
      (Localization.Away (f * g))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f * g)) M)).equiv
  have e_cancel : (Localization.Away (f * g)) ⊗[Localization.Away f]
      ((Localization.Away f) ⊗[A] M) ≃ₗ[Localization.Away (f * g)]
      (Localization.Away (f * g)) ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away f)
      (Localization.Away (f * g)) (Localization.Away (f * g)) M
  have e_congr : (Localization.Away (f * g)) ⊗[Localization.Away f]
      ((Localization.Away f) ⊗[A] M) ≃ₗ[Localization.Away (f * g)]
      (Localization.Away (f * g)) ⊗[Localization.Away f]
        (LocalizedModule (Submonoid.powers f) M) :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (Localization.Away (f * g)) (Localization.Away (f * g))) e_f
  exact Module.Free.of_equiv'
    (inferInstance : Module.Free (Localization.Away (f * g))
      ((Localization.Away (f * g)) ⊗[Localization.Away f]
        (LocalizedModule (Submonoid.powers f) M)))
    (e_congr.symm.trans (e_cancel.trans e_fg))

/-- Generic freeness is invariant under `A`-linear equivalence. -/
theorem GenericallyFree.of_linearEquiv {A : Type*} [CommRing A] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (h : GenericallyFree A M) : GenericallyFree A N := by
  obtain ⟨f, hf, hfree⟩ := h
  refine ⟨f, hf, ?_⟩
  haveI := hfree
  have e' : LocalizedModule (Submonoid.powers f) M ≃ₗ[A]
      LocalizedModule (Submonoid.powers f) N :=
    IsLocalizedModule.iso (Submonoid.powers f)
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) N) ∘ₗ e.toLinearMap)
  exact Module.Free.of_equiv' hfree
    (e'.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f))

/-- **Splicing lemma for generic freeness** — the extension step of Nitsure's
dévissage. If the outer terms of a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of `A`-modules are generically free, so is the middle
term: localize the sequence at the product of the two witnesses (exactness of
localization) and apply `ModuleCat.free_shortExact`. -/
theorem genericallyFree_of_exact {A : Type*} [CommRing A] [IsDomain A]
    {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂]
    [Module A M₂] [AddCommGroup M₃] [Module A M₃]
    (u : M₁ →ₗ[A] M₂) (v : M₂ →ₗ[A] M₃) (hu : Function.Injective u)
    (hv : Function.Surjective v) (huv : Function.Exact u v)
    (h₁ : GenericallyFree A M₁) (h₃ : GenericallyFree A M₃) :
    GenericallyFree A M₂ := by
  obtain ⟨f₁, hf₁, hfree₁⟩ := h₁
  obtain ⟨f₃, hf₃, hfree₃⟩ := h₃
  refine ⟨f₁ * f₃, mul_ne_zero hf₁ hf₃, ?_⟩
  have hfree₁' := free_localizedModule_powers_mul A M₁ f₁ f₃ hfree₁
  have hfree₃' := free_localizedModule_powers_mul A M₃ f₃ f₁ hfree₃
  rw [mul_comm f₃ f₁] at hfree₃'
  let u' : LocalizedModule (Submonoid.powers (f₁ * f₃)) M₁
      →ₗ[Localization.Away (f₁ * f₃)]
      LocalizedModule (Submonoid.powers (f₁ * f₃)) M₂ :=
    (IsLocalizedModule.map (Submonoid.powers (f₁ * f₃))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₁)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₂)
      u).extendScalarsOfIsLocalization (Submonoid.powers (f₁ * f₃))
        (Localization.Away (f₁ * f₃))
  let v' : LocalizedModule (Submonoid.powers (f₁ * f₃)) M₂
      →ₗ[Localization.Away (f₁ * f₃)]
      LocalizedModule (Submonoid.powers (f₁ * f₃)) M₃ :=
    (IsLocalizedModule.map (Submonoid.powers (f₁ * f₃))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₂)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₃)
      v).extendScalarsOfIsLocalization (Submonoid.powers (f₁ * f₃))
        (Localization.Away (f₁ * f₃))
  have hu' : Function.Injective u' :=
    IsLocalizedModule.map_injective (Submonoid.powers (f₁ * f₃))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₁)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₂) u hu
  have hv' : Function.Surjective v' :=
    IsLocalizedModule.map_surjective (Submonoid.powers (f₁ * f₃))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₂)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₃) v hv
  have huv' : Function.Exact u' v' :=
    IsLocalizedModule.map_exact (Submonoid.powers (f₁ * f₃))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₁)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₂)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₃)
      u v huv
  let C : ShortComplex (ModuleCat (Localization.Away (f₁ * f₃))) :=
    ShortComplex.mk (ModuleCat.ofHom u') (ModuleCat.ofHom v')
      (ModuleCat.hom_ext (LinearMap.ext fun x => huv'.apply_apply_eq_zero x))
  have hC : C.ShortExact :=
    { exact := C.moduleCat_exact_iff.mpr fun x hx => (huv' x).mp hx
      mono_f := (ModuleCat.mono_iff_injective _).mpr hu'
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hv' }
  haveI : Module.Free (Localization.Away (f₁ * f₃)) C.X₁ := hfree₁'
  haveI : Module.Free (Localization.Away (f₁ * f₃)) C.X₃ := hfree₃'
  exact ModuleCat.free_shortExact hC

/-- Generic freeness of a subsingleton module (with `f = 1`). This is the
degenerate input to the dévissage; the substantive Nitsure base case
(`M_K = 0`, i.e. torsion `M`) is `genericallyFree_of_torsion` below. -/
theorem genericallyFree_of_subsingleton (A M : Type*) [CommRing A]
    [Nontrivial A] [AddCommGroup M] [Module A M] [Subsingleton M] :
    GenericallyFree A M := by
  refine ⟨1, one_ne_zero, ?_⟩
  haveI : Subsingleton (LocalizedModule (Submonoid.powers (1 : A)) M) := by
    apply subsingleton_of_forall_eq 0
    intro x
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      rw [Subsingleton.elim m 0]
      exact LocalizedModule.zero_mk s
  infer_instance

/-- A finite torsion module admits a single non-zero **uniform annihilator**:
the product of annihilators of a finite generating set kills the module. -/
theorem exists_annihilator_of_torsion (A M : Type*) [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (htors : ∀ m : M, ∃ a : A, a ≠ 0 ∧ a • m = 0) :
    ∃ a : A, a ≠ 0 ∧ ∀ m : M, a • m = 0 := by
  classical
  obtain ⟨s, hs⟩ := (‹Module.Finite A M› : Module.Finite A M).fg_top
  choose a ha haz using htors
  refine ⟨∏ m ∈ s, a m, Finset.prod_ne_zero_iff.mpr fun m _ => ha m, ?_⟩
  have hker : Submodule.span A (s : Set M) ≤
      LinearMap.ker (LinearMap.lsmul A M (∏ m' ∈ s, a m')) := by
    rw [Submodule.span_le]
    intro m hm
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.lsmul_apply]
    rw [← Finset.mul_prod_erase s a hm, mul_comm, mul_smul, haz m, smul_zero]
  intro m
  have hm : m ∈ Submodule.span A (s : Set M) := by
    rw [hs]; exact Submodule.mem_top
  simpa using hker hm

/-- Generic freeness from a single non-zero uniform annihilator (no finiteness
of the module needed): the localization at the annihilator vanishes. -/
theorem genericallyFree_of_annihilator {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] {a : A} (ha : a ≠ 0)
    (hann : ∀ m : M, a • m = 0) : GenericallyFree A M := by
  refine ⟨a, ha, ?_⟩
  haveI : Subsingleton (LocalizedModule (Submonoid.powers a) M) := by
    apply subsingleton_of_forall_eq 0
    intro x
    induction x using LocalizedModule.induction_on with
    | _ m t =>
      rw [← LocalizedModule.mk_cancel_common_left
        (⟨a, Submonoid.mem_powers _⟩ : Submonoid.powers a) t m,
        Submonoid.mk_smul, hann m]
      exact LocalizedModule.zero_mk _
  infer_instance

/-- **Torsion base case** of generic freeness (Nitsure's `n = -1`, `M_K = 0`):
a finite `A`-module all of whose elements are `A`-torsion is generically free
— the product of annihilators of a finite generating set kills the module,
so the corresponding localization vanishes. -/
theorem genericallyFree_of_torsion (A M : Type*) [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (htors : ∀ m : M, ∃ a : A, a ≠ 0 ∧ a • m = 0) : GenericallyFree A M := by
  obtain ⟨a, ha, hann⟩ := exists_annihilator_of_torsion A M htors
  exact genericallyFree_of_annihilator ha hann

/-- A free module over a domain is generically free, with witness `f = 1`. -/
theorem GenericallyFree.of_free (A M : Type*) [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.Free A M] : GenericallyFree A M := by
  refine ⟨1, one_ne_zero, ?_⟩
  exact Module.Free.of_equiv'
    (inferInstance : Module.Free (Localization.Away (1 : A))
      ((Localization.Away (1 : A)) ⊗[A] M))
    (IsLocalizedModule.isBaseChange (Submonoid.powers (1 : A))
      (Localization.Away (1 : A))
      (LocalizedModule.mkLinearMap (Submonoid.powers (1 : A)) M)).equiv

/-- **Transport of generic freeness along a `g`-saturating injection**: if
`ι : M →ₗ[A] M'` is injective and every element of `M'` is carried into the
image by a power of a fixed non-zero `g`, then generic freeness of `M` gives
generic freeness of `M'` (the witness gets multiplied by `g`).  Applied to the
inclusion of a module-finite normalization subalgebra `C'' ⊆ C` whose
localizations at `g` agree. -/
theorem GenericallyFree.of_saturating_injection {A : Type*} [CommRing A]
    [IsDomain A] {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (ι : M →ₗ[A] M') (hinj : Function.Injective ι) {g : A}
    (hg : g ≠ 0) (hsat : ∀ m' : M', ∃ (N : ℕ) (m : M), g ^ N • m' = ι m)
    (h : GenericallyFree A M) : GenericallyFree A M' := by
  obtain ⟨f, hf, hfree⟩ := h
  refine ⟨f * g, mul_ne_zero hf hg, ?_⟩
  have hfree' := free_localizedModule_powers_mul A M f g hfree
  let ι' : LocalizedModule (Submonoid.powers (f * g)) M
      →ₗ[Localization.Away (f * g)] LocalizedModule (Submonoid.powers (f * g)) M' :=
    (IsLocalizedModule.map (Submonoid.powers (f * g))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f * g)) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f * g)) M')
      ι).extendScalarsOfIsLocalization (Submonoid.powers (f * g))
        (Localization.Away (f * g))
  have hmap_mk : ∀ (m : M) (t : Submonoid.powers (f * g)),
      ι' (LocalizedModule.mk m t) = LocalizedModule.mk (ι m) t := by
    intro m t
    simp only [ι', LinearMap.extendScalarsOfIsLocalization_apply']
    rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk',
      IsLocalizedModule.map_mk']
  have hι'inj : Function.Injective ι' :=
    IsLocalizedModule.map_injective (Submonoid.powers (f * g))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f * g)) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f * g)) M') ι hinj
  have hι'surj : Function.Surjective ι' := by
    intro x
    induction x using LocalizedModule.induction_on with
    | _ m' s =>
      obtain ⟨N, m, hm⟩ := hsat m'
      refine ⟨LocalizedModule.mk (f ^ N • m)
        (⟨(f * g) ^ N, pow_mem (Submonoid.mem_powers _) N⟩ * s), ?_⟩
      rw [hmap_mk, map_smul, ← hm]
      have : (f ^ N • g ^ N • m' : M') = ((f * g) ^ N) • m' := by
        rw [smul_smul, ← mul_pow]
      rw [this, ← Submonoid.mk_smul ((f * g) ^ N)
        (pow_mem (Submonoid.mem_powers (f * g)) N) m',
        LocalizedModule.mk_cancel_common_left]
  exact Module.Free.of_equiv' hfree' (LinearEquiv.ofBijective ι' ⟨hι'inj, hι'surj⟩)

/-- **Krull dimension does not grow along integral algebras** (incomparability):
for an integral `R`-algebra `S`, `dim S ≤ dim R` — the comap of a strictly
increasing chain of primes of `S` is strictly increasing in `R`. -/
theorem ringKrullDim_le_of_isIntegral (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    fun p _ hpq => by
      haveI := p.2
      exact Ideal.IsIntegral.comap_lt_comap hpq

/-- **Krull dimension does not drop along injective integral algebras**: chains
of primes of `R` lift to `S` by lying-over and going-up. -/
theorem le_ringKrullDim_of_isIntegral_of_injective (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have key : ∀ l : LTSeries (PrimeSpectrum R), ∃ l' : LTSeries (PrimeSpectrum S),
      l'.length = l.length ∧
        PrimeSpectrum.comap (algebraMap R S) l'.last = l.last := by
    intro l
    induction l using RelSeries.inductionOn' with
    | singleton p =>
      obtain ⟨Q, hQ⟩ := Algebra.IsIntegral.comap_surjective R S p
      exact ⟨RelSeries.singleton _ Q, rfl, hQ⟩
    | snoc l p hp ih =>
      obtain ⟨l', hlen, hlast⟩ := ih
      haveI := p.2
      obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal l'.last.asIdeal
          (by rw [show l'.last.asIdeal.comap (algebraMap R S) =
              (PrimeSpectrum.comap (algebraMap R S) l'.last).asIdeal from rfl,
              hlast]
              exact hp.le)
      have hp' : l.last < p := hp
      have hlt : l'.last < ⟨Q, hQprime⟩ := by
        refine lt_of_le_of_ne hQge fun h => ?_
        apply hp'.ne
        rw [← hlast, h]
        exact PrimeSpectrum.ext hQcomap
      refine ⟨l'.snoc ⟨Q, hQprime⟩ hlt, by simpa using hlen, ?_⟩
      simp only [RelSeries.last_snoc]
      exact PrimeSpectrum.ext hQcomap
  change (⨆ (p : LTSeries (PrimeSpectrum R)), (p.length : WithBot ℕ∞)) ≤
    ringKrullDim S
  refine iSup_le fun l => ?_
  obtain ⟨l', hlen, -⟩ := key l
  rw [← hlen]
  exact Order.LTSeries.length_le_krullDim l'

/-! ### The generic fibre of an algebra over a domain

For a domain `A` with fraction field `K := FractionRing A` and an `A`-algebra
`C`, the *generic fibre* is the localization
`Localization (Algebra.algebraMapSubmonoid C A⁰) = K ⊗_A C`.  Mathlib already
provides its `K`-algebra structure and the scalar tower `A → K → C_K`
(`Localization.Basic`); the lemmas below record that it is a domain when
`A ↪ C` (for a domain `C`), and that it is generated over `K` by the image of
any `A`-algebra presentation of `C`. -/

/-- For a domain `C` with `A ↪ C`, the image of `A⁰` in `C` consists of
non-zero-divisors, so the generic fibre is a domain (in particular
non-trivial). -/
theorem fibre_le_nonZeroDivisors {A C : Type*} [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [Algebra A C]
    (hinj : Function.Injective (algebraMap A C)) :
    Algebra.algebraMapSubmonoid C (nonZeroDivisors A) ≤ nonZeroDivisors C := by
  rintro - ⟨a, ha, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
  exact nonZeroDivisors.ne_zero ha (hinj (h.trans (map_zero _).symm))

theorem fibre_isDomain {A C : Type*} [CommRing A] [IsDomain A] [CommRing C]
    [IsDomain C] [Algebra A C] (hinj : Function.Injective (algebraMap A C)) :
    IsDomain
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) :=
  IsLocalization.isDomain_localization (fibre_le_nonZeroDivisors hinj)

/-- Compatibility of the generic-fibre evaluation with an `A`-algebra map from
the polynomial ring: evaluating the `K`-coefficient extension of `p` at the
fibre-images of `ψ(Xᵢ)` computes the fibre-image of `ψ p`. -/
theorem fibre_aeval_map_algebraMap {A C : Type*} [CommRing A] [IsDomain A]
    [CommRing C] [Algebra A C] {n : ℕ}
    (ψ : MvPolynomial (Fin n) A →ₐ[A] C) (p : MvPolynomial (Fin n) A) :
    MvPolynomial.aeval
      (fun i => algebraMap C
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
        (ψ (MvPolynomial.X i)))
      (MvPolynomial.map (algebraMap A (FractionRing A)) p) =
    algebraMap C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
      (ψ p) := by
  rw [MvPolynomial.aeval_map_algebraMap]
  exact DFunLike.congr_fun (MvPolynomial.aeval_unique
    ((IsScalarTower.toAlgHom A C
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))).comp
      ψ)).symm p

/-- The generic fibre is generated over `K` by the fibre-image of any
`A`-algebra presentation of `C`: the induced evaluation from the polynomial
ring over `K` is surjective. -/
theorem fibre_aeval_surjective {A C : Type*} [CommRing A] [IsDomain A]
    [CommRing C] [Algebra A C] {n : ℕ}
    (ψ : MvPolynomial (Fin n) A →ₐ[A] C) (hψ : Function.Surjective ψ) :
    Function.Surjective (MvPolynomial.aeval
      (fun i => algebraMap C
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
        (ψ (MvPolynomial.X i))) :
      MvPolynomial (Fin n) (FractionRing A) →ₐ[FractionRing A] _) := by
  intro z
  obtain ⟨⟨c, s⟩, hz⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)) z
  replace hz : IsLocalization.mk'
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) c s = z := hz
  rw [← hz]
  obtain ⟨p, rfl⟩ := hψ c
  obtain ⟨a, ha, hs⟩ := s.2
  refine ⟨(MvPolynomial.map (algebraMap A (FractionRing A)) p) *
    MvPolynomial.C (IsLocalization.mk' (FractionRing A) 1 ⟨a, ha⟩), ?_⟩
  rw [map_mul, fibre_aeval_map_algebraMap, MvPolynomial.aeval_C,
    IsLocalization.mk'_eq_mul_mk'_one (ψ p) s]
  congr 1
  rw [IsLocalization.algebraMap_mk' (S := C), map_one]
  exact congrArg (IsLocalization.mk' _ 1) (Subtype.ext hs)

/-- **Scaling the Noether normalization into `C`**: an injective finite
`K`-algebra map `φ` from a polynomial ring into the generic fibre of `C` can
be rescaled variable-by-variable (by non-zero elements of `A`, which are units
of `K`) so that the variables land in the image of `C`. -/
theorem exists_scaled_noether_datum {A C : Type*} [CommRing A] [IsDomain A]
    [CommRing C] [Algebra A C] {s : ℕ}
    (φ : MvPolynomial (Fin s) (FractionRing A) →ₐ[FractionRing A]
      Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
    (hφinj : Function.Injective φ) (hφfin : φ.toRingHom.Finite) :
    ∃ (b : Fin s → C)
      (φ' : MvPolynomial (Fin s) (FractionRing A) →ₐ[FractionRing A]
        Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))),
      Function.Injective φ' ∧ φ'.toRingHom.Finite ∧
      ∀ i, φ' (MvPolynomial.X i) = algebraMap C
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
        (b i) := by
  have hdec : ∀ i : Fin s, ∃ (b : C) (a : A), a ∈ nonZeroDivisors A ∧
      algebraMap A (FractionRing A) a • φ (MvPolynomial.X i) =
        algebraMap C
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
          b := by
    intro i
    obtain ⟨⟨bi, t⟩, ht⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)) (φ (MvPolynomial.X i))
    replace ht : IsLocalization.mk'
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) bi t =
        φ (MvPolynomial.X i) := ht
    obtain ⟨a, ha, hat⟩ := t.2
    refine ⟨bi, a, ha, ?_⟩
    rw [← ht, Algebra.smul_def, ← IsScalarTower.algebraMap_apply A (FractionRing A) _,
      IsScalarTower.algebraMap_apply A C _, hat, mul_comm]
    exact IsLocalization.mk'_spec _ bi t
  choose b a ha hab using hdec
  have hka : ∀ i, algebraMap A (FractionRing A) (a i) ≠ 0 := fun i h =>
    nonZeroDivisors.ne_zero (ha i)
      (IsFractionRing.injective A (FractionRing A) (h.trans (map_zero _).symm))
  let ρ : MvPolynomial (Fin s) (FractionRing A) →ₐ[FractionRing A]
      MvPolynomial (Fin s) (FractionRing A) :=
    MvPolynomial.aeval
      (fun i => algebraMap A (FractionRing A) (a i) • MvPolynomial.X i)
  let ρ' : MvPolynomial (Fin s) (FractionRing A) →ₐ[FractionRing A]
      MvPolynomial (Fin s) (FractionRing A) :=
    MvPolynomial.aeval
      (fun i => (algebraMap A (FractionRing A) (a i))⁻¹ • MvPolynomial.X i)
  have hρρ' : ρ.comp ρ' = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_smul, AlgHom.id_apply,
      ρ, ρ', smul_smul]
    rw [inv_mul_cancel₀ (hka i), one_smul]
  have hρ'ρ : ρ'.comp ρ = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_smul, AlgHom.id_apply,
      ρ, ρ', smul_smul]
    rw [mul_inv_cancel₀ (hka i), one_smul]
  have hρsurj : Function.Surjective ρ := fun p =>
    ⟨ρ' p, by rw [← AlgHom.comp_apply, hρρ', AlgHom.id_apply]⟩
  have hρinj : Function.Injective ρ := fun p q h => by
    have h2 := congrArg ρ' h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hρ'ρ, AlgHom.id_apply,
      AlgHom.id_apply] at h2
  refine ⟨b, φ.comp ρ, hφinj.comp hρinj,
    hφfin.comp (RingHom.Finite.of_surjective ρ.toRingHom hρsurj), fun i => ?_⟩
  rw [AlgHom.comp_apply,
    show ρ (MvPolynomial.X i) =
      algebraMap A (FractionRing A) (a i) • MvPolynomial.X i from
      MvPolynomial.aeval_X _ i,
    map_smul]
  exact hab i

/-- **Clearing denominators for integrality** [Nitsure §4, integrality step]:
if `A ↪ C` (domains), the generic fibre `F` of `C` is module-finite over
`K[X₁,…,X_s]` via `φ'`, and `φ'` sends the variables to the fibre-images of
`b : Fin s → C`, then every `c : C` becomes integral over the *unlocalized*
polynomial ring `A[X₁,…,X_s]` (acting on `C` through `X i ↦ b i`) after
multiplication by a single non-zero element of `A`.  The denominators are
cleared by `IsIntegral.exists_multiple_integral_of_isLocalization` applied to
the constant-coefficient localization `A[X] → K[X]`, and the integral
equation descends from `F` to `C` by injectivity. -/
theorem exists_smul_isIntegralElem_of_fibre_finite {A C : Type*} [CommRing A]
    [IsDomain A] [CommRing C] [IsDomain C] [Algebra A C]
    (hinj : Function.Injective (algebraMap A C)) {s : ℕ} {b : Fin s → C}
    (φ' : MvPolynomial (Fin s) (FractionRing A) →ₐ[FractionRing A]
      Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
    (hφfin : φ'.toRingHom.Finite)
    (hb : ∀ i, φ' (MvPolynomial.X i) = algebraMap C
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) (b i))
    (c : C) :
    ∃ a : A, a ≠ 0 ∧
      (MvPolynomial.aeval b :
        MvPolynomial (Fin s) A →ₐ[A] C).toRingHom.IsIntegralElem (a • c) := by
  letI : Algebra (MvPolynomial (Fin s) (FractionRing A))
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) :=
    φ'.toRingHom.toAlgebra
  haveI hFfin : Module.Finite (MvPolynomial (Fin s) (FractionRing A))
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) := hφfin
  letI : Algebra (MvPolynomial (Fin s) A)
      (MvPolynomial (Fin s) (FractionRing A)) :=
    MvPolynomial.algebraMvPolynomial
  letI : Algebra (MvPolynomial (Fin s) A)
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) :=
    (φ'.toRingHom.comp
      (MvPolynomial.map (algebraMap A (FractionRing A)))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) A)
      (MvPolynomial (Fin s) (FractionRing A))
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- the fibre is integral over `K[X]`, being module-finite
  have hint : _root_.IsIntegral (MvPolynomial (Fin s) (FractionRing A))
      (algebraMap C
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) c) :=
    (Algebra.IsIntegral.of_finite _ _).isIntegral _
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    ((nonZeroDivisors A).map (MvPolynomial.C (σ := Fin s))) _ hint
  obtain ⟨mval, hmem⟩ := m
  obtain ⟨a, haA, rfl⟩ := hmem
  refine ⟨a, nonZeroDivisors.ne_zero haA, ?_⟩
  -- the factorization square `A[X] → C → F` = `A[X] → K[X] → F`
  have hφ'eq : φ' = MvPolynomial.aeval (fun i => algebraMap C
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) (b i)) :=
    (MvPolynomial.aeval_unique φ').trans (congrArg _ (funext fun i => hb i))
  have hfact : ∀ p : MvPolynomial (Fin s) A,
      φ' (MvPolynomial.map (algebraMap A (FractionRing A)) p) =
      algebraMap C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
        (MvPolynomial.aeval b p) := by
    intro p
    rw [hφ'eq,
      show (fun i => algebraMap C
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) (b i)) =
        (fun i => algebraMap C
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
          ((MvPolynomial.aeval b : MvPolynomial (Fin s) A →ₐ[A] C)
            (MvPolynomial.X i))) from
        funext fun i => by rw [MvPolynomial.aeval_X],
      fibre_aeval_map_algebraMap]
  -- identify `m • x` with the fibre-image of `a • c`
  have heq : (⟨MvPolynomial.C a, Submonoid.mem_map_of_mem _ haA⟩ :
      ((nonZeroDivisors A).map (MvPolynomial.C (σ := Fin s)))) •
      (algebraMap C
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) c) =
      algebraMap C
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
        (a • c) := by
    rw [Submonoid.mk_smul, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [show (algebraMap (MvPolynomial (Fin s) A)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))))
        (MvPolynomial.C a) =
      φ' (MvPolynomial.map (algebraMap A (FractionRing A)) (MvPolynomial.C a))
      from rfl, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  rw [heq] at hm
  -- restate instance-free and pull the integral equation back along `C ↪ F`
  have hm' : (φ'.toRingHom.comp
      (MvPolynomial.map (algebraMap A (FractionRing A)))).IsIntegralElem
      (algebraMap C
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
        (a • c)) := hm
  obtain ⟨P, hPmonic, hPeval⟩ := hm'
  refine ⟨P, hPmonic, ?_⟩
  have hCF : Function.Injective (algebraMap C
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))) :=
    IsLocalization.injective _ (fibre_le_nonZeroDivisors hinj)
  apply hCF
  rw [map_zero, Polynomial.hom_eval₂]
  rw [show (algebraMap C
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))).comp
      (MvPolynomial.aeval b : MvPolynomial (Fin s) A →ₐ[A] C).toRingHom =
    φ'.toRingHom.comp
      (MvPolynomial.map (algebraMap A (FractionRing A))) from
    RingHom.ext fun p => (hfact p).symm]
  exact hPeval

/-- **Dévissage frame** for generic freeness: over a noetherian ring `B` (an
`A`-algebra), if every prime quotient `B ⧸ q` is generically free over the
domain `A`, then every finite `B`-module (with compatible `A`-structure) is
generically free over `A`.  Prime-filtration induction via
`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`; the subsingleton
case is `genericallyFree_of_subsingleton` and stability under extensions is
the splicing lemma `genericallyFree_of_exact`. -/
theorem genericallyFree_of_forall_quotient_prime {A : Type*} (B : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsNoetherianRing B] [Algebra A B]
    (hcore : ∀ (q : Ideal B), q.IsPrime → GenericallyFree A (B ⧸ q))
    (M : Type v) [AddCommGroup M] [Module B M] [Module.Finite B M] [Module A M]
    [IsScalarTower A B M] : GenericallyFree A M := by
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime (A := B)
    ‹Module.Finite B M›
    (motive := fun N iACG iMB _ => ∀ (iA : Module A N),
      (@IsScalarTower A B N Algebra.toSMul
        iMB.toDistribMulAction.toMulAction.toSMul
        iA.toDistribMulAction.toMulAction.toSMul) →
      @GenericallyFree A N _ iACG iA)
    ?_ ?_ ?_ ‹Module A M› ‹IsScalarTower A B M›
  · intro N _ _ _ _ iA _
    exact @genericallyFree_of_subsingleton A N _ _ _ iA ‹_›
  · intro N _ _ _ p e iA htower
    letI := iA
    haveI : IsScalarTower A B N := htower
    exact (hcore p.1 p.2).of_linearEquiv (e.restrictScalars A).symm
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ u v hu hv huv h₁ h₃ iA₂ htower₂
    letI iA₁ : Module A N₁ := Module.compHom N₁ (algebraMap A B)
    letI iA₃ : Module A N₃ := Module.compHom N₃ (algebraMap A B)
    haveI ht₁ : IsScalarTower A B N₁ :=
      ⟨fun a b n => by
        change (a • b) • n = algebraMap A B a • b • n
        rw [Algebra.smul_def, mul_smul]⟩
    haveI ht₃ : IsScalarTower A B N₃ :=
      ⟨fun a b n => by
        change (a • b) • n = algebraMap A B a • b • n
        rw [Algebra.smul_def, mul_smul]⟩
    letI := iA₂
    haveI : IsScalarTower A B N₂ := htower₂
    exact genericallyFree_of_exact (u.restrictScalars A) (v.restrictScalars A)
      hu hv huv (h₁ iA₁ ht₁) (h₃ iA₃ ht₃)

/-- Arithmetic extraction in `WithBot ℕ∞`: a quantity that is non-negative and
whose successor is bounded by `s ≤ n` is bounded by some natural `m < n`. -/
private theorem exists_nat_le_of_add_one_le {x : WithBot ℕ∞} (h0 : 0 ≤ x)
    {s n : ℕ} (h1 : x + 1 ≤ (s : WithBot ℕ∞))
    (hsn : (s : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)) :
    ∃ m : ℕ, m < n ∧ x ≤ (m : WithBot ℕ∞) := by
  have hs_n : s ≤ n := by exact_mod_cast hsn
  obtain ⟨e, rfl⟩ : ∃ e : ℕ∞, x = (e : WithBot ℕ∞) := by
    cases x with
    | bot => exact absurd h0 (by simp)
    | coe e => exact ⟨e, rfl⟩
  have h1' : e + 1 ≤ (s : ℕ∞) := by exact_mod_cast h1
  have hetop : e ≠ ⊤ := by
    intro h
    rw [h] at h1'
    simp at h1'
  lift e to ℕ using hetop
  have h1'' : e + 1 ≤ s := by exact_mod_cast h1'
  exact ⟨e, lt_of_lt_of_le (Nat.lt_of_succ_le h1'') hs_n, le_refl _⟩

/-- **The dimension drop for hypersurface quotients**: if `C'` is a domain,
`A ↪ C'`, and `C'` is presented by `s` variables with a non-zero polynomial
`d` in the kernel, then the generic fibre of `C'` has Krull dimension
strictly less than `s`.  The fibre is a surjective image of
`K[X₁,…,X_s] ⧸ (d̄)` with `d̄ ≠ 0`, and quotienting a domain by a non-zero
element drops the dimension. -/
private theorem fibre_dim_add_one_le_of_presentation {A : Type*} [CommRing A]
    [IsDomain A] {C' : Type*} [CommRing C'] [IsDomain C'] [Algebra A C']
    {s : ℕ}
    (π : MvPolynomial (Fin s) A →ₐ[A] C') (hπ : Function.Surjective π)
    {d : MvPolynomial (Fin s) A} (hd0 : d ≠ 0) (hdker : π d = 0) :
    ringKrullDim (Localization (Algebra.algebraMapSubmonoid C'
      (nonZeroDivisors A))) + 1 ≤ (s : WithBot ℕ∞) := by
  have hdbar0 : MvPolynomial.map (algebraMap A (FractionRing A)) d ≠ 0 := fun h =>
    hd0 (MvPolynomial.map_injective _
      (IsFractionRing.injective A (FractionRing A)) (by rw [h, map_zero]))
  -- the fibre evaluation kills `d̄`, hence factors through `K[X] ⧸ (d̄)`
  have hkill : ∀ p ∈ (Ideal.span {MvPolynomial.map (algebraMap A (FractionRing A)) d} :
      Ideal (MvPolynomial (Fin s) (FractionRing A))),
      (MvPolynomial.aeval (fun i => algebraMap C'
        (Localization (Algebra.algebraMapSubmonoid C' (nonZeroDivisors A)))
        (π (MvPolynomial.X i)))) p = 0 := by
    intro p hp
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul, fibre_aeval_map_algebraMap π d, hdker, map_zero, mul_zero]
  let ρ : (MvPolynomial (Fin s) (FractionRing A) ⧸
      (Ideal.span {MvPolynomial.map (algebraMap A (FractionRing A)) d})) →ₐ[FractionRing A]
      Localization (Algebra.algebraMapSubmonoid C' (nonZeroDivisors A)) :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (fun i => algebraMap C'
      (Localization (Algebra.algebraMapSubmonoid C' (nonZeroDivisors A)))
      (π (MvPolynomial.X i)))) hkill
  have hρsurj : Function.Surjective ρ := by
    have h1 := fibre_aeval_surjective π hπ
    intro z
    obtain ⟨p, hp⟩ := h1 z
    exact ⟨Ideal.Quotient.mk _ p, hp⟩
  calc ringKrullDim (Localization (Algebra.algebraMapSubmonoid C'
        (nonZeroDivisors A))) + 1
      ≤ ringKrullDim (MvPolynomial (Fin s) (FractionRing A) ⧸
          (Ideal.span {MvPolynomial.map (algebraMap A (FractionRing A)) d})) + 1 := by
        gcongr
        exact ringKrullDim_le_of_surjective ρ.toRingHom hρsurj
    _ ≤ ringKrullDim (MvPolynomial (Fin s) (FractionRing A)) :=
        ringKrullDim_quotient_succ_le_of_nonZeroDivisor
          (mem_nonZeroDivisors_of_ne_zero hdbar0)
    _ = (s : WithBot ℕ∞) := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
          ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
          Fintype.card_fin, zero_add]

/-- The generic fibre of a finite-type algebra over a noetherian domain has
finite Krull dimension, bounded by the number of variables of a Noether
normalization (using that dimension does not grow along integral maps). -/
private theorem exists_nat_fibre_dim_le {A : Type*} [CommRing A] [IsDomain A]
    (C : Type*) [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    ∃ n : ℕ, ringKrullDim (Localization (Algebra.algebraMapSubmonoid C
      (nonZeroDivisors A))) ≤ (n : WithBot ℕ∞) := by
  obtain ⟨nn, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    ‹Algebra.FiniteType A C›
  by_cases hnt : Nontrivial (Localization (Algebra.algebraMapSubmonoid C
      (nonZeroDivisors A)))
  · haveI := hnt
    haveI : Algebra.FiniteType (FractionRing A)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) :=
      Algebra.FiniteType.of_surjective _ (fibre_aeval_surjective ψ hψ)
    obtain ⟨s, φ, hφinj, hφfin⟩ := exists_finite_inj_algHom_of_fg (FractionRing A)
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
    refine ⟨s, ?_⟩
    have h1 : ringKrullDim (Localization (Algebra.algebraMapSubmonoid C
        (nonZeroDivisors A))) ≤
        ringKrullDim (MvPolynomial (Fin s) (FractionRing A)) := by
      letI := φ.toRingHom.toAlgebra
      haveI : Module.Finite (MvPolynomial (Fin s) (FractionRing A))
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A))) :=
        hφfin
      haveI := Algebra.IsIntegral.of_finite (MvPolynomial (Fin s) (FractionRing A))
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
      exact ringKrullDim_le_of_isIntegral _ _
    refine h1.trans (le_of_eq ?_)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, Fintype.card_fin,
      zero_add]
  · refine ⟨0, ?_⟩
    haveI : Subsingleton (Localization (Algebra.algebraMapSubmonoid C
        (nonZeroDivisors A))) := not_nontrivial_iff_subsingleton.mp hnt
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le


set_option maxHeartbeats 800000 in
-- the `Frac D`-basis extraction in the localized module (`Module.finBasis` +
-- `unitsSMul` denominator scaling) exceeds the default elaboration budget
/-- **Generic-rank comparison for a finite module over a domain** [Nitsure
§4, "Lemma on Generic Flatness", generic-rank step]: a finite module `M`
over a domain `D` admits an injective `D`-linear map `Φ : D^r → M` from a
finite free module whose cokernel is killed by a single non-zero `d ∈ D` —
the exact sequence `0 → D^r → M → T → 0` with `T` torsion.

Localizing at `D ∖ {0}` turns `M` into a finite-dimensional vector space
over `Frac D`; scaling a basis by denominators (`Basis.unitsSMul`) realises
it as the image of a family `cc : Fin r → M`, and `Φ` is the associated
linear-combination map.  Injectivity localizes to the linear independence of
the basis; for the cokernel, clearing the denominators of the coordinates of
`y ∈ M` (`IsLocalization.exist_integer_multiples`) puts a non-zero multiple
of `y` into the image, and `exists_annihilator_of_torsion` produces the
uniform annihilator.

Isolated as a standalone lemma (blueprint `lem:generic_rank_comparison`) so
that its localized-module instance arguments elaborate in a clean binder
context: inlined in the strong induction below (where `M := ↥C''` is a
`set`-bound subalgebra subtype under a `letI` algebra), the same block hits
a `Module.Free` synthesis failure and divergent-`whnf` instance walls
(run 0010 r3/r4, issue `I-0093`). -/
theorem exists_generic_rank_comparison (D : Type u) [CommRing D]
    [IsDomain D] (M : Type v) [AddCommGroup M] [Module D M]
    [Module.Finite D M] :
    ∃ (r : ℕ) (Φ : (Fin r → D) →ₗ[D] M), Function.Injective Φ ∧
      ∃ d : D, d ≠ 0 ∧ ∀ t : M ⧸ LinearMap.range Φ, d • t = 0 := by
  haveI hVfin : Module.Finite (FractionRing D)
      (LocalizedModule (nonZeroDivisors D) M) :=
    Module.Finite.of_isLocalizedModule (nonZeroDivisors D)
      (LocalizedModule.mkLinearMap _ _)
  -- a basis of the generic fibre of `M` consisting of images of `M`
  obtain ⟨r, cc, hccli, hccspan⟩ : ∃ (r : ℕ) (cc : Fin r → M),
      LinearIndependent (FractionRing D)
        (fun i => LocalizedModule.mkLinearMap (nonZeroDivisors D) M (cc i)) ∧
      Submodule.span (FractionRing D)
        (Set.range fun i => LocalizedModule.mkLinearMap
          (nonZeroDivisors D) M (cc i)) = ⊤ := by
    have hdec : ∀ v : LocalizedModule (nonZeroDivisors D) M,
        ∃ (m : M) (dd : nonZeroDivisors D), LocalizedModule.mk m dd = v := by
      intro v
      induction v using LocalizedModule.induction_on with
      | _ m dd => exact ⟨m, dd, rfl⟩
    choose num den hnd using hdec
    haveI : Module.Free (FractionRing D)
        (LocalizedModule (nonZeroDivisors D) M) :=
      Module.Free.of_divisionRing _ _
    let bV := Module.finBasis (FractionRing D)
      (LocalizedModule (nonZeroDivisors D) M)
    let u : Fin (Module.finrank (FractionRing D)
        (LocalizedModule (nonZeroDivisors D) M)) → (FractionRing D)ˣ := fun i =>
      (IsLocalization.map_units (FractionRing D) (den (bV i))).unit
    have hkey : ⇑(bV.unitsSMul u) = fun i => LocalizedModule.mkLinearMap
        (nonZeroDivisors D) M (num (bV i)) := by
      funext i
      rw [Module.Basis.unitsSMul_apply, Units.smul_def, IsUnit.unit_spec,
        algebraMap_smul, LocalizedModule.mkLinearMap_apply]
      have h := hnd (bV i)
      generalize hnum : num (bV i) = nn' at h ⊢
      generalize hden : den (bV i) = dd' at h ⊢
      rw [← h, LocalizedModule.smul'_mk, ← Submonoid.mk_smul dd'.1 dd'.2 nn',
        LocalizedModule.mk_cancel]
    refine ⟨_, fun i => num (bV i), ?_, ?_⟩
    · rw [← hkey]; exact (bV.unitsSMul u).linearIndependent
    · rw [← hkey]; exact (bV.unitsSMul u).span_eq
  -- the `D`-linear comparison map `D^r → M`
  let Φ : (Fin r → D) →ₗ[D] M :=
    { toFun := fun f => ∑ i, f i • cc i
      map_add' := fun f g => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun d f => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul,
          smul_eq_mul] }
  have hΦexp : ∀ f : Fin r → D,
      LocalizedModule.mkLinearMap (nonZeroDivisors D) M (Φ f) =
      ∑ i, algebraMap D (FractionRing D) (f i) •
        LocalizedModule.mkLinearMap (nonZeroDivisors D) M (cc i) := by
    intro f
    rw [show Φ f = ∑ i, f i • cc i from rfl, map_sum]
    congr 1
    funext i
    rw [map_smul, algebraMap_smul]
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have hsum : ∑ i, algebraMap D (FractionRing D) (f i) •
        LocalizedModule.mkLinearMap (nonZeroDivisors D) M (cc i) = 0 := by
      rw [← hΦexp, hf, map_zero]
    have h0 := Fintype.linearIndependent_iff.mp hccli
      (fun i => algebraMap D (FractionRing D) (f i)) hsum
    funext i
    exact IsFractionRing.injective D (FractionRing D)
      (by rw [h0 i, Pi.zero_apply, map_zero])
  -- the cokernel is torsion: clear denominators of the span coefficients
  have hTtors : ∀ t : (M ⧸ LinearMap.range Φ),
      ∃ dd : D, dd ≠ 0 ∧ dd • t = 0 := by
    intro t
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    have hy : (LocalizedModule.mkLinearMap (nonZeroDivisors D) M y) ∈
        Submodule.span (FractionRing D) (Set.range fun i =>
          LocalizedModule.mkLinearMap (nonZeroDivisors D) M (cc i)) := by
      rw [hccspan]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨l, hl⟩ := hy
    obtain ⟨dd, hdd⟩ := IsLocalization.exist_integer_multiples
      (nonZeroDivisors D) Finset.univ l
    choose uu huu using fun i => hdd i (Finset.mem_univ i)
    have hVzero : LocalizedModule.mkLinearMap (nonZeroDivisors D) M
        ((dd : D) • y - Φ uu) = 0 := by
      rw [map_sub, map_smul, hΦexp, ← hl, Finset.smul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [huu i, smul_assoc]
    obtain ⟨e, he⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors D)
      (LocalizedModule.mkLinearMap _ M)).mp hVzero
    refine ⟨(e : D) * (dd : D),
      mul_ne_zero (nonZeroDivisors.ne_zero e.2) (nonZeroDivisors.ne_zero dd.2), ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hyy : ((e : D) * (dd : D)) • y = Φ ((e : D) • uu) := by
      have h2 : (e : D) • ((dd : D) • y - Φ uu) = 0 := he
      rw [smul_sub, sub_eq_zero] at h2
      rw [mul_smul, h2, map_smul]
    rw [hyy]
    exact LinearMap.mem_range_self Φ _
  -- a single non-zero `d` annihilates the (finite) cokernel
  obtain ⟨d, hd0, hdT⟩ := exists_annihilator_of_torsion D
    (M ⧸ LinearMap.range Φ) hTtors
  exact ⟨r, Φ, hΦinj, d, hd0, hdT⟩


set_option maxHeartbeats 1600000 in
-- the ~200-line strong induction (Noether normalisation + saturation +
-- hypersurface dévissage) genuinely needs ~8× the default budget; the
-- `maxSynthPendingDepth` bump un-sticks the `Algebra A ((D ⧸ (d)) ⧸ qt)`
-- double-quotient instance chain, whose nested pending synthesis exceeds
-- the workspace default of 3 (`by_cases` at the `hcore` kernel split)
set_option maxSynthPendingDepth 8 in
/-- **Auxiliary induction for the domain core** [Nitsure §4, "Lemma on Generic
Flatness", normalisation step]: for a noetherian domain `A` and a finite-type
`A`-algebra `E` with a prime `q`, if the generic fibre of `C := E ⧸ q` has
Krull dimension at most `n`, then `C` is generically free over `A`.

Strong induction on `n`.  Either the kernel of `A → C` is non-zero (uniform
annihilator, torsion case), or `A ↪ C`: Noether-normalise the fibre
(`exists_finite_inj_algHom_of_fg`, with `s ≤ n` variables by the
integral-dimension comparison), scale the variables into `C`
(`exists_scaled_noether_datum`), clear denominators
(`exists_smul_isIntegralElem_of_fibre_finite`) to obtain a module-finite
subalgebra `C'' ⊆ C` over `D := A[X₁,…,X_s]` with `C''_g = C_g`, build the
generic-rank exact sequence `0 → D^r → C'' → T → 0` with `T` killed by some
`0 ≠ d ∈ D` (`exists_generic_rank_comparison` applied to `M := ↥C''`),
dispose of `T` by prime-filtration dévissage over `D ⧸ (d)`
(whose fibre has dimension `< s ≤ n`, so the inductive hypothesis applies),
splice, and transport along the `g`-saturating inclusion `C'' ⊆ C`. -/
theorem genericallyFree_quotient_prime_of_fibre_dim_le (n : ℕ) :
    ∀ (A E : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
      [CommRing E] [Algebra A E] [Algebra.FiniteType A E]
      (q : Ideal E), q.IsPrime →
      ringKrullDim (Localization (Algebra.algebraMapSubmonoid (E ⧸ q)
        (nonZeroDivisors A))) ≤ (n : WithBot ℕ∞) →
      GenericallyFree A (E ⧸ q) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro A E _ _ _ _ _ _ q hq hdim
  haveI := hq
  by_cases hker : ∃ a : A, a ≠ 0 ∧ algebraMap A (E ⧸ q) a = 0
  · -- kernel case: the whole quotient is annihilated by a non-zero scalar
    obtain ⟨a, ha, ha0⟩ := hker
    exact genericallyFree_of_annihilator ha fun m => by
      rw [Algebra.smul_def, ha0, zero_mul]
  -- main case: `A ↪ C`
  have hinj : Function.Injective (algebraMap A (E ⧸ q)) := by
    rw [injective_iff_map_eq_zero]
    intro a h0
    by_contra hne
    exact hker ⟨a, hne, h0⟩
  haveI hFdom : IsDomain (Localization (Algebra.algebraMapSubmonoid (E ⧸ q)
      (nonZeroDivisors A))) := fibre_isDomain hinj
  haveI : Algebra.FiniteType A (E ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A q)
      (Ideal.Quotient.mkₐ_surjective A q)
  obtain ⟨nn, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    ‹Algebra.FiniteType A (E ⧸ q)›
  haveI : Algebra.FiniteType (FractionRing A)
      (Localization (Algebra.algebraMapSubmonoid (E ⧸ q) (nonZeroDivisors A))) :=
    Algebra.FiniteType.of_surjective _ (fibre_aeval_surjective ψ hψ)
  obtain ⟨s, φ, hφinj, hφfin⟩ := exists_finite_inj_algHom_of_fg (FractionRing A)
    (Localization (Algebra.algebraMapSubmonoid (E ⧸ q) (nonZeroDivisors A)))
  -- the number of Noether variables is bounded by `n`
  have hs_le : (s : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    have h1 : ringKrullDim (MvPolynomial (Fin s) (FractionRing A)) ≤
        ringKrullDim (Localization (Algebra.algebraMapSubmonoid (E ⧸ q)
          (nonZeroDivisors A))) := by
      letI := φ.toRingHom.toAlgebra
      haveI : Module.Finite (MvPolynomial (Fin s) (FractionRing A))
          (Localization (Algebra.algebraMapSubmonoid (E ⧸ q)
            (nonZeroDivisors A))) := hφfin
      haveI := Algebra.IsIntegral.of_finite (MvPolynomial (Fin s) (FractionRing A))
        (Localization (Algebra.algebraMapSubmonoid (E ⧸ q) (nonZeroDivisors A)))
      exact le_ringKrullDim_of_isIntegral_of_injective _ _ hφinj
    have h2 : ringKrullDim (MvPolynomial (Fin s) (FractionRing A)) =
        (s : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
        Fintype.card_fin, zero_add]
    calc (s : WithBot ℕ∞) = _ := h2.symm
    _ ≤ _ := h1
    _ ≤ (n : WithBot ℕ∞) := hdim
  -- scale the Noether datum into `C` and clear denominators per generator
  obtain ⟨b, φ', hφ'inj, hφ'fin, hb⟩ := exists_scaled_noether_datum φ hφinj hφfin
  have hclear : ∀ j : Fin nn, ∃ a : A, a ≠ 0 ∧
      (MvPolynomial.aeval b :
        MvPolynomial (Fin s) A →ₐ[A] (E ⧸ q)).toRingHom.IsIntegralElem
        (a • ψ (MvPolynomial.X j)) :=
    fun j => exists_smul_isIntegralElem_of_fibre_finite hinj φ' hφ'fin hb _
  choose aa haa hint using hclear
  have hg0 : (∏ j, aa j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => haa j
  -- `C''`: the subalgebra generated over `A[X₁,…,X_s]` by the cleared
  -- generators; module-finite since the generators are integral
  letI : Algebra (MvPolynomial (Fin s) A) (E ⧸ q) :=
    (MvPolynomial.aeval b).toRingHom.toAlgebra
  haveI : IsScalarTower A (MvPolynomial (Fin s) A) (E ⧸ q) :=
    IsScalarTower.of_algebraMap_eq' ((MvPolynomial.aeval b).comp_algebraMap).symm
  set C'' : Subalgebra (MvPolynomial (Fin s) A) (E ⧸ q) :=
    Algebra.adjoin (MvPolynomial (Fin s) A)
      (Set.range fun j => aa j • ψ (MvPolynomial.X j)) with hC''def
  haveI hC''fin : Module.Finite (MvPolynomial (Fin s) A) ↥C'' := by
    have hfg : (Subalgebra.toSubmodule C'').FG := by
      apply fg_adjoin_of_finite (Set.finite_range _)
      rintro x ⟨j, rfl⟩
      exact hint j
    exact Module.Finite.iff_fg.mpr hfg
  -- saturation: a power of `g := ∏ aa j` pushes every element of `C` into `C''`
  have hsat : ∀ c : E ⧸ q, ∃ (N : ℕ) (y : ↥C''), (∏ j, aa j) ^ N • c = ↑y := by
    intro c
    obtain ⟨p, rfl⟩ := hψ c
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine ⟨0, ⟨ψ (MvPolynomial.C a), ?_⟩, by rw [pow_zero, one_smul]⟩
      have h2 : ψ (MvPolynomial.C a) =
          algebraMap (MvPolynomial (Fin s) A) (E ⧸ q) (MvPolynomial.C a) := by
        rw [show algebraMap (MvPolynomial (Fin s) A) (E ⧸ q) (MvPolynomial.C a) =
            (MvPolynomial.aeval b) (MvPolynomial.C a) from rfl,
          MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      rw [h2]
      exact Subalgebra.algebraMap_mem C'' _
    | add p1 p2 h1 h2 =>
      obtain ⟨N1, y1, hy1⟩ := h1
      obtain ⟨N2, y2, hy2⟩ := h2
      refine ⟨max N1 N2, (∏ j, aa j) ^ (max N1 N2 - N1) • y1 +
        (∏ j, aa j) ^ (max N1 N2 - N2) • y2, ?_⟩
      have hco : ((((∏ j, aa j) ^ (max N1 N2 - N1) • y1 +
          (∏ j, aa j) ^ (max N1 N2 - N2) • y2 : ↥C'')) : E ⧸ q) =
          (∏ j, aa j) ^ (max N1 N2 - N1) • (y1 : E ⧸ q) +
          (∏ j, aa j) ^ (max N1 N2 - N2) • (y2 : E ⧸ q) := rfl
      rw [map_add, smul_add, hco, ← hy1, ← hy2, smul_smul, smul_smul,
        ← pow_add, ← pow_add, Nat.sub_add_cancel (le_max_left N1 N2),
        Nat.sub_add_cancel (le_max_right N1 N2)]
    | mul_X p j hp =>
      obtain ⟨N, y, hy⟩ := hp
      refine ⟨N + 1,
        ((∏ k ∈ Finset.univ.erase j, aa k) • (⟨aa j • ψ (MvPolynomial.X j),
          Algebra.subset_adjoin ⟨j, rfl⟩⟩ : ↥C'')) * y, ?_⟩
      have hco : ((((∏ k ∈ Finset.univ.erase j, aa k) •
          (⟨aa j • ψ (MvPolynomial.X j),
            Algebra.subset_adjoin ⟨j, rfl⟩⟩ : ↥C'')) * y : ↥C'') : E ⧸ q) =
          ((∏ k ∈ Finset.univ.erase j, aa k) •
            (aa j • ψ (MvPolynomial.X j))) * (y : E ⧸ q) := rfl
      rw [map_mul, hco, ← hy, smul_smul, smul_mul_smul_comm]
      rw [show ψ p * ψ (MvPolynomial.X j) =
        ψ (MvPolynomial.X j) * ψ p from mul_comm _ _]
      congr 1
      rw [pow_succ, ← Finset.mul_prod_erase Finset.univ aa (Finset.mem_univ j)]
      ring
  -- ===== the generic-rank exact sequence over `D := A[X₁,…,X_s]` =====
  obtain ⟨r, Φ, hΦinj, d, hd0, hdT⟩ :=
    exists_generic_rank_comparison (MvPolynomial (Fin s) A) ↥C''
  -- ===== dévissage of the torsion cokernel over `E' := D ⧸ (d)` =====
  have hTBS : Module.IsTorsionBySet (MvPolynomial (Fin s) A)
      (↥C'' ⧸ LinearMap.range Φ)
      ((Ideal.span {d} : Ideal (MvPolynomial (Fin s) A)) : Set (MvPolynomial (Fin s) A)) :=
    (Module.isTorsionBySet_span_singleton_iff d).mpr hdT
  letI : Module
      (MvPolynomial (Fin s) A ⧸ (Ideal.span {d} : Ideal (MvPolynomial (Fin s) A)))
      (↥C'' ⧸ LinearMap.range Φ) := hTBS.module
  haveI : IsScalarTower A
      (MvPolynomial (Fin s) A ⧸ (Ideal.span {d} : Ideal (MvPolynomial (Fin s) A)))
      (↥C'' ⧸ LinearMap.range Φ) :=
    hTBS.isScalarTower
  haveI : Module.Finite
      (MvPolynomial (Fin s) A ⧸ (Ideal.span {d} : Ideal (MvPolynomial (Fin s) A)))
      (↥C'' ⧸ LinearMap.range Φ) :=
    Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) A) _ _
  -- every prime quotient of `E'` is generically free: kernel case or recursion
  have hcore : ∀ (qt : Ideal (MvPolynomial (Fin s) A ⧸
      (Ideal.span {d} : Ideal (MvPolynomial (Fin s) A)))), qt.IsPrime →
      GenericallyFree A ((MvPolynomial (Fin s) A ⧸
        (Ideal.span {d} : Ideal (MvPolynomial (Fin s) A))) ⧸ qt) := by
    intro qt hqt
    haveI := hqt
    by_cases hker' : ∃ a : A, a ≠ 0 ∧ algebraMap A ((MvPolynomial (Fin s) A ⧸
        (Ideal.span {d} : Ideal (MvPolynomial (Fin s) A))) ⧸ qt) a = 0
    · obtain ⟨a, ha, ha0⟩ := hker'
      exact genericallyFree_of_annihilator ha fun m => by
        rw [Algebra.smul_def, ha0, zero_mul]
    · have hinj' : Function.Injective (algebraMap A ((MvPolynomial (Fin s) A ⧸
          (Ideal.span {d} : Ideal (MvPolynomial (Fin s) A))) ⧸ qt)) := by
        rw [injective_iff_map_eq_zero]
        intro a h0
        by_contra hne
        exact hker' ⟨a, hne, h0⟩
      -- the composite presentation kills `d`, so the fibre dimension drops
      have hπd : ((Ideal.Quotient.mkₐ A qt).comp
          (Ideal.Quotient.mkₐ A (Ideal.span {d}))) d = 0 := by
        rw [AlgHom.comp_apply, show (Ideal.Quotient.mkₐ A (Ideal.span {d})) d = 0 from
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self d),
          map_zero]
      have h1 := fibre_dim_add_one_le_of_presentation
        ((Ideal.Quotient.mkₐ A qt).comp (Ideal.Quotient.mkₐ A (Ideal.span {d})))
        ((Ideal.Quotient.mkₐ_surjective A qt).comp
          (Ideal.Quotient.mkₐ_surjective A (Ideal.span {d})))
        hd0 hπd
      haveI := fibre_isDomain hinj'
      have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization
          (Algebra.algebraMapSubmonoid ((MvPolynomial (Fin s) A ⧸
            (Ideal.span {d} : Ideal (MvPolynomial (Fin s) A))) ⧸ qt)
            (nonZeroDivisors A))) :=
        ringKrullDim_nonneg_of_nontrivial
      obtain ⟨m', hm'lt, hm'le⟩ := exists_nat_le_of_add_one_le h0 h1 hs_le
      exact IH m' hm'lt A _ qt hqt hm'le
  -- assemble: the cokernel is generically free by dévissage
  have hGFT : GenericallyFree A (↥C'' ⧸ LinearMap.range Φ) :=
    genericallyFree_of_forall_quotient_prime
      (MvPolynomial (Fin s) A ⧸ (Ideal.span {d} : Ideal (MvPolynomial (Fin s) A)))
      hcore (↥C'' ⧸ LinearMap.range Φ)
  -- the free part is generically free
  have hGFfree : GenericallyFree A (Fin r → MvPolynomial (Fin s) A) :=
    GenericallyFree.of_free A _
  -- splice the exact sequence `0 → D^r → C'' → T → 0` over `A`
  have hGFC'' : GenericallyFree A ↥C'' := by
    have hinj' : Function.Injective (Φ.restrictScalars A) := by
      simpa only [LinearMap.coe_restrictScalars] using hΦinj
    have hsurj' : Function.Surjective
        (((LinearMap.range Φ).mkQ).restrictScalars A) := by
      simpa only [LinearMap.coe_restrictScalars] using
        (LinearMap.range Φ).mkQ_surjective
    have hex' : Function.Exact (Φ.restrictScalars A)
        (((LinearMap.range Φ).mkQ).restrictScalars A) := by
      have hex : Function.Exact Φ (LinearMap.range Φ).mkQ :=
        LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
      simpa only [LinearMap.coe_restrictScalars] using hex
    exact genericallyFree_of_exact (Φ.restrictScalars A)
      (((LinearMap.range Φ).mkQ).restrictScalars A) hinj' hsurj' hex' hGFfree hGFT
  -- transport along the `g`-saturating inclusion `C'' ⊆ C`
  exact hGFC''.of_saturating_injection
    ((Subalgebra.val C'').toLinearMap.restrictScalars A)
    (fun x y h => Subtype.ext h) hg0 hsat

/-- **The domain core of algebraic generic freeness** [Nitsure §4, "Lemma on
Generic Flatness", normalisation step]: for a noetherian domain `A`, a
finite-type `A`-algebra `B` and a prime `𝔭 ⊆ B`, the quotient domain `B/𝔭`
is generically free over `A`.  (A special case of Grothendieck's generic
freeness, Stacks 051R.)

Proved by presenting `B/𝔭` as a prime quotient of a polynomial ring over `A`
(this also aligns universes) and running the induction on the Krull dimension
of the generic fibre, `genericallyFree_quotient_prime_of_fibre_dim_le`; the
entry bound comes from Noether normalisation of the fibre
(`exists_nat_fibre_dim_le`). -/
theorem genericallyFree_quotient_prime (A B : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (p : Ideal B) [p.IsPrime] : GenericallyFree A (B ⧸ p) := by
  haveI : Algebra.FiniteType A (B ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A p)
      (Ideal.Quotient.mkₐ_surjective A p)
  obtain ⟨nn, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    ‹Algebra.FiniteType A (B ⧸ p)›
  haveI hkerp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  haveI : Algebra.FiniteType A (MvPolynomial (Fin nn) A ⧸ RingHom.ker ψ) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ A (RingHom.ker ψ))
      (Ideal.Quotient.mkₐ_surjective A (RingHom.ker ψ))
  obtain ⟨n, hn⟩ := exists_nat_fibre_dim_le (A := A)
    (MvPolynomial (Fin nn) A ⧸ RingHom.ker ψ)
  have haux := genericallyFree_quotient_prime_of_fibre_dim_le n A
    (MvPolynomial (Fin nn) A) (RingHom.ker ψ) hkerp hn
  exact haux.of_linearEquiv
    (Ideal.quotientKerAlgEquivOfSurjective hψ).toLinearEquiv

/-- **Algebraic generic freeness, dévissage assembly** [Nitsure §4 "Lemma on
Generic Flatness" / Stacks 051R; blueprint `thm:generic_flatness_algebraic`].

For a noetherian domain `A`, a finite-type `A`-algebra `B` and a finite
`B`-module `M` (with compatible `A`-structure), `M` is generically free over
`A`. The prime-filtration dévissage over the noetherian ring `B`
(`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`) is complete:
the subsingleton case is `genericallyFree_of_subsingleton`, prime quotients
are the domain core `genericallyFree_quotient_prime`, and stability under
extensions is the splicing lemma `genericallyFree_of_exact`. -/
theorem genericFlatnessAlgebraic (A B M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] [Module A M]
    [IsScalarTower A B M] : GenericallyFree A M := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact genericallyFree_of_forall_quotient_prime B
    (fun q hq => haveI := hq; genericallyFree_quotient_prime A B q) M

end GenericFreeness

namespace Scheme

/-! ## §1. Coherent-sheaf flatness over a base

For a morphism `f : X ⟶ S` of schemes and a coherent (more generally:
quasi-coherent) `𝓞_X`-module `𝓕`, the *coherent-sheaf flatness* predicate
`CoherentSheafFlat f 𝓕` captures Stacks 00HB lifted to the sheaf level:
for every point `x ∈ X` the stalk `𝓕_x` is a flat `𝓞_{S, f(x)}`-module
via the composite `𝓞_{S, f(x)} → 𝓞_{X, x} → End(𝓕_x)`.

Affine-locally (Stacks 00HB equivalence): on an affine open `U = Spec A
⊆ S` and an affine open `V = Spec B ⊆ f⁻¹U` with `𝓕|_V = M̃` for a
finite `B`-module `M`, the condition becomes `Module.Flat A M` with the
`A`-module structure inherited via the ring map `A → B`. The
file-internal encoding uses this affine-local form.

Blueprint reference: `def:coherent_sheaf_flat`. -/

/-- A coherent sheaf `𝓕` on `X` is **flat over `S`** for a morphism
`f : X ⟶ S` if, for every affine open `U ⊆ S` and every affine open
`V ⊆ f⁻¹U`, the `𝓞_X`-module of sections `Γ(𝓕, V)` is flat as a
`Γ(S, U)`-module, where the `Γ(S, U)`-action is the restriction of
scalars along the ring morphism `Γ(S, U) → Γ(X, V)` (the `appLE`
morphism of `f`).

This is the affine-local form of Stacks 00HB (a coherent sheaf is flat
over the base if every stalk is flat over the corresponding base
stalk); the affine-local form and stalk form are equivalent for
*quasi-coherent* sheaves on a noetherian base, which is the regime of
the flattening-stratification theorem.

iter-177+: the body of subsequent flat-locus theorems may package this
predicate as an instance-driven typeclass `Module.Flat`-style if the
sheafified-tensor infrastructure lands in Mathlib; for the iter-176
file-skeleton it is encoded as a `Prop` quantifier. -/
def CoherentSheafFlat {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Prop :=
  ∀ {U : S.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U),
    letI : Module Γ(S, U) Γ(F, V) := Module.compHom _ (f.appLE U V e).hom
    Module.Flat Γ(S, U) Γ(F, V)

end Scheme

/-! ## §2. Generic flatness (Nitsure §4) — see `GenericFlatnessGeometric.lean`

The geometric generic-flatness theorem `AlgebraicGeometry.genericFlatness`
(blueprint `thm:generic_flatness`) is stated and **proved** in the separate
file `AlgebraicJacobian.Picard.GenericFlatnessGeometric`, as the geometric
glue over the algebraic engine of this file: it consumes the qcqs
section-localization engine of `AlgebraicJacobian.Picard.QuotScheme`
(Stacks 01P0/01PC/01I8), which this file deliberately does not import so
that the instance environment of the dévissage proofs above stays fixed. -/

/-! ## §3–§6. Existence, universality, curve specialisation — moved

The geometric sections (Nitsure §4 sub-lemmas `flatLocusStratification` and
`flatLocusReduction`, the assembly `flatLocusAssembly`, the main theorem
`flatteningStratification`, its universal property, and the curve
specialisation `flatteningStratification.ofCurve`) live in
`AlgebraicJacobian.Picard.GenericFlatnessGeometric`: the proof of Lemma 6
(`flatLocusReduction`, run 0010 T12 r6) consumes `genericFlatness`, whose
geometric glue requires the QuotScheme engine that this file deliberately
does not import (see §2 above).  Blueprint `\lean{}` pointers are unchanged
— they pin fully qualified declaration names, which are preserved. -/

end AlgebraicGeometry
