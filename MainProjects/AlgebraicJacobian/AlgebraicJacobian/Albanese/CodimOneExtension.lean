/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.RiemannRoch.WeilDivisor
import AlgebraicJacobian.Albanese.CoheightBridge
import AlgebraicJacobian.Albanese.AuslanderBuchsbaum
import AlgebraicJacobian.Albanese.StandardSmoothDimension
import AlgebraicJacobian.Albanese.SmoothPrimeRegularity
import AlgebraicJacobian.Albanese.PolePurity

/-!
# Codimension-1 indeterminacy extension (A.4.a)

This file is the **A.4.a** sub-build chapter for the positive-genus arm of the
project's `nonempty_jacobianWitness`. It packages the two extension inputs to
Milne's *Abelian Varieties* §I.3 Theorem 3.2, plus the Weil-divisor
reformulation of the codim-`1` obstruction:

* **Milne Theorem 3.1** (`indeterminacy_codimGe2_of_smooth_of_complete`,
  proved): a rational map from a nonsingular variety to a complete variety
  has indeterminacy locus of codimension `≥ 2` (equivalently, it is
  codim-`1`-indeterminacy-free: `codimOneFree_of_smooth_of_complete`).
* **Extension from empty indeterminacy**
  (`existsUnique_hom_of_indeterminacyLocus_eq_empty`, proved): a rational
  map from a reduced scheme to a separated scheme with `Z(f) = ∅` is
  uniquely represented by a regular morphism. (This replaces the removed
  `extend_of_codimOneFree_of_smooth`, whose "CodimOneFree ⇒ extension"
  statement was false for general complete targets — see its docstring.)
* **Milne Lemma 3.3** (`indeterminacy_pure_codim_one_into_grpScheme`, proved
  in the *downstream* file `Albanese/Milne33.lean` — see §5): for a
  rational map from a nonsingular variety to a group variety, the
  indeterminacy locus is either empty or of pure codimension `1` (every
  point of `Z(f)` specialises from a codim-1 point of `Z(f)`).
* **Weil-divisor obstruction** (`mem_domain_iff_exists_partialMap_through_point`):
  `f` is defined at the generic point of a prime divisor `W` iff some
  `PartialMap` representative of `f` is regular at `W.point`. This is a thin
  re-shuffle of Mathlib's `RationalMap.mem_domain`; the substantive
  Hartshorne-II.6 "regular ⇔ order ≥ 0 at every DVR pullback" reformulation
  (the original Weil-divisor obstruction) is deferred to a future lemma
  that builds genuine pullback machinery (`Scheme.RationalMap.order`-along-`f`),
  outside this iter's scope.

These outputs feed Milne Theorem 3.2 in the sibling
`Albanese/Thm32RationalMapExtension.lean` (A.4.c). (The former dependence on
`cor:regular_cohen_macaulay` / Stacks 0AVF for a "Step 2 extension" is gone:
the extension needs no local-cohomology input once `Z(f) = ∅` is in hand.)

## Status (run 0069)

**This file is `sorry`-free.** Every blueprint-pinned declaration below is
proved and axiom-clean. Milne Lemma 3.3
(`indeterminacy_pure_codim_one_into_grpScheme`) was this file's single
remaining `sorry` until run 0069; it is now proved in
`Albanese/Milne33.lean` — a *downstream* module, since the proof's
difference-map / pole-purity / Hauptidealsatz-transport layers import this
file. See §5 for the pointer. In particular the DVR chain (via the sorry-free
`isRegularLocalRing_stalk_of_smooth` — Stacks 00TT at every point, proved
Serre-free in `Albanese/SmoothPrimeRegularity.lean`), Milne 3.1
(`indeterminacy_codimGe2_of_smooth_of_complete`, via Mathlib's valuative
criterion + rational-map spreading-out), and the extension-from-empty
theorem (`existsUnique_hom_of_indeterminacyLocus_eq_empty`) are complete.

The three Milne-§I.3 theorems now carry the "rational map of `k̄`-varieties"
over-ness hypothesis `f.compHom Y.hom = X.hom.toRationalMap` (Milne's ambient
assumption, needed for the valuative square's base compatibility); the
Thm 3.2 chain in `Albanese/Thm32RationalMapExtension.lean` threads it
through.

The 6 pinned declarations are:

1. `Scheme.RationalMap.indeterminacyLocus` (def, ~3 LOC) — the closed
   complement of `RationalMap.domain` as a `Set X`.
2. `Scheme.RationalMap.CodimOneFree` (def, ~3 LOC) — predicate: every
   point `η : X` with `Order.coheight η = 1` lies in `f.domain`.
3. `Scheme.localRing_dvr_of_codim_one` (theorem, ~3 LOC) — for a smooth
   integral variety, the stalk at a codim-1 point is a DVR.
4. `Scheme.RationalMap.existsUnique_hom_of_indeterminacyLocus_eq_empty`
   (theorem) — unique regular representation of a rational map with empty
   indeterminacy locus (reduced source, separated target).
5. `Scheme.RationalMap.indeterminacy_pure_codim_one_into_grpScheme`
   (theorem, ~8 LOC) — Milne Lemma 3.3.
6. `Scheme.RationalMap.mem_domain_iff_exists_partialMap_through_point`
   (theorem, ~2 LOC) — definitional re-shuffle of `RationalMap.mem_domain`
   exposing a `PartialMap` representative whose domain contains `W.point`.
   The substantive Weil-divisor `order ≥ 0` reformulation is deferred (see
   header).

## Note on type expressivity

Following the project rule "Never weaken the type to dodge the proof", each
pinned declaration carries a substantive, non-tautological type:

* `indeterminacyLocus f : Set X` returns the carrier of the closed
  complement of `f.domain` — not `∅` or `Set.univ`.
* `CodimOneFree f : Prop` is the genuine ∀-statement over codim-1 points,
  not `True`.
* `localRing_dvr_of_codim_one` produces a Mathlib `IsDiscreteValuationRing`
  instance — not a trivial proposition.
* `existsUnique_hom_of_indeterminacyLocus_eq_empty` asserts
  `∃! g, g.toRationalMap = f` — the existence of a unique regular
  representation, from the substantive `Z(f) = ∅` hypothesis.
* `indeterminacy_pure_codim_one_into_grpScheme` asserts a disjunction:
  either the locus is empty or every point of it specialises from a
  coheight-`1` point of the locus.
* `mem_domain_iff_exists_partialMap_through_point` asserts the (truthful)
  iff between definedness at `W.point` and the existence of a `PartialMap`
  representative containing `W.point` in its domain — a definitional unfold
  of `Mathlib.AlgebraicGeometry.Scheme.RationalMap.mem_domain` with the
  conjunction swapped for downstream ergonomics.

Unfolding any pinned declaration exposes the named substantive content
(the carrier set complement, the `∀ η, ...` statement, the DVR instance,
the unique regular extension, …); no `Iso.refl _` / empty-content
`proof_wanted` / `Classical.choice ⟨witness⟩` placeholders are used.

## Variety conventions

Following the project (cf. `Albanese/Thm32RationalMapExtension.lean`,
`AbelianVarietyRigidity.lean`), a **nonsingular variety over `k̄`** is an
object `X : Over (Spec (.of k̄))` carrying:

* `[Smooth X.hom]`, `[GeometricallyIrreducible X.hom]`,
* `[IsSeparated X.hom]`, `[LocallyOfFiniteType X.hom]`,
* `[IsIntegral X.left]`, `[IsReduced X.left]`.

A **complete variety** adds `[IsProper Y.hom]`. A **group variety** over
`k̄` adds a `[GrpObj Y]` instance to the variety package.

## References

Blueprint: `blueprint/src/chapters/Albanese_CodimOneExtension.tex` (~750 LOC,
6 pins). Source: Milne, *Abelian Varieties*, §I.3, Theorem 3.1 (p. 16) and
Lemma 3.3 (p. 17); Hartshorne, *Algebraic Geometry*, II.6 pp. 130–131.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

/-! ## §1. The indeterminacy locus of a rational map

The indeterminacy locus `Z(f) ⊆ X` of a rational map `f : X ⇢ Y` is the closed
complement of its domain of definition `Dom(f) := f.domain` (a Mathlib-shipped
open subset of `X`).

Blueprint pin: `def:indeterminacy_locus` (Milne §I.3 p. 16). -/

/-- **Indeterminacy locus of a rational map.** The closed complement of the
domain of definition `f.domain` (an `X.Opens`, exposed by Mathlib at
`Mathlib.AlgebraicGeometry.Birational.RationalMap`):

`Z(f) := X ∖ Dom(f) ⊆ X`.

`f` is everywhere defined (i.e. extends to a regular morphism) iff
`indeterminacyLocus f = ∅`.

Blueprint reference: `def:indeterminacy_locus` (Milne, *Abelian Varieties*,
§I.3, p. 16). -/
def indeterminacyLocus {X Y : Scheme.{u}} (f : X.RationalMap Y) : Set X :=
  (f.domain : Set X)ᶜ

/-- **Codim-1-indeterminacy-free rational map.** A rational map
`f : X ⇢ Y` is codim-1-indeterminacy-free if every codimension-one point
of `X` lies in its domain of definition. Equivalently: no prime divisor of
`X` (i.e. closure of a codim-1 generic point) is contained in
`indeterminacyLocus f`.

The codim-1 condition is encoded via `Order.coheight η = 1` on the
specialisation preorder of `X.carrier`, matching the project's standing
convention in `Scheme.PrimeDivisor` (`RiemannRoch/WeilDivisor.lean`).

Blueprint reference: `def:codim_one_indeterminacy` (Milne, *Abelian
Varieties*, Theorem 3.1, §I.3, p. 16). -/
def CodimOneFree {X Y : Scheme.{u}} (f : X.RationalMap Y) : Prop :=
  ∀ (x : X), Order.coheight x = 1 → x ∈ f.domain

end RationalMap

/-! ## §3. Smoothness yields a DVR at every codim-1 point

On a nonsingular variety `X` over `k̄`, the local ring at the generic point
of a prime divisor is a discrete valuation ring with fraction field equal to
the function field `K(X) = X.functionField`. This is Hartshorne II.6's
"regular in codimension one" property combined with the regular-local-ring-of-dim-1
$\Leftrightarrow$ DVR equivalence (Atiyah–Macdonald 9.2; Stacks `00PD`).

Blueprint pin: `lem:smooth_codim_one_dvr` (Hartshorne II.6 p. 130). -/

/-! ### Stacks 00TT scaffolding (Lane M↓ iter-191 first scaffold)

The Mathlib gap "smooth over `\bar k` ⟹ stalk is a regular local ring"
(Stacks tag `00TT`) is structured here as a four-stage pipeline:

* **Stage 1** — smooth ⟹ flat at every stalk (Mathlib instance
  `AlgebraicGeometry.instFlatOfSmooth` + `Flat.stalkMap`).
* **Stage 2** — smooth at a point ⟹ exists a standard smooth presentation
  on an affine neighbourhood (Stacks tag `00T7`, packaged in Mathlib at
  `AlgebraicGeometry.Smooth.exists_isStandardSmooth`).
* **Stage 3** — the polynomial generators of the standard smooth
  presentation form a regular sequence after localising at any prime
  (Stacks `02JK`/`07BV`; Mathlib gap as of `b80f227`).
* **Stage 4** — a Noetherian local ring whose maximal ideal is generated
  by a regular sequence of length equal to its Krull dimension is a
  regular local ring (`IsRegularLocalRing.of_regularSequence`; Stacks
  `00OE`/Matsumura 19.2; Mathlib gap as of `b80f227`).

Stages 1-2 are landed axiom-clean as named helpers below. Stages 3-4 were
historically a single scoped `sorry` inside the main theorem
`isRegularLocalRing_stalk_of_smooth`; that theorem is now **fully proved**
(no `sorry`) via the Serre-free arbitrary-prime route of
`Albanese/SmoothPrimeRegularity.lean` (conormal identity + Kähler-trdeg
identification + polynomial-ring trdeg–height inequality), which needs
neither Stacks `00OF` nor the `02JK`/`00OE` regular-sequence chain. -/

/-- **Stage 1 (Stacks 00TT, smooth ⟹ flat at stalk).** For a smooth
morphism `X.hom : X.left ⟶ Spec (.of k̄)` with `k̄` algebraically closed,
the induced ring map on stalks at every point `z : X.left` is flat. This
is the smooth ⟹ flat instance applied through the stalk-map flatness
characterisation `AlgebraicGeometry.Flat.iff_flat_stalkMap`.

Axiom-clean: composes the smooth ⟹ flat instance with the stalk-map
flatness lemma. No Mathlib gap. -/
private theorem stalkMap_flat_of_smooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom]
    (z : X.left) :
    ((X.hom.stalkMap z).hom).Flat :=
  AlgebraicGeometry.Flat.stalkMap X.hom z

/-- **Stage 2 (Stacks 00T7, smooth ⟹ standard smooth presentation at a
point).** For a smooth morphism `X.hom : X.left ⟶ Spec (.of k̄)`, every
point `z : X.left` admits affine open neighbourhoods `U ⊆ Spec (.of k̄)`,
`V ⊆ X.left` with `z ∈ V` and `V ⊆ X.hom ⁻¹' U` such that the induced
ring map `(X.hom.appLE U V e).hom` is `IsStandardSmooth`.

Axiom-clean: re-exports `AlgebraicGeometry.Smooth.exists_isStandardSmooth`
(the scheme-level packaging of Stacks tag `00T7`) at the project's
`Over (Spec (.of k̄))` calling convention. -/
private theorem exists_isStandardSmooth_at_of_smooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom]
    (z : X.left) :
    ∃ (U : (Spec (.of kbar)).Opens) (_ : IsAffineOpen U)
      (V : X.left.Opens) (_ : IsAffineOpen V)
      (_hzV : z ∈ V) (e : V ≤ X.hom ⁻¹ᵁ U),
      (X.hom.appLE U V e).hom.IsStandardSmooth :=
  AlgebraicGeometry.Smooth.exists_isStandardSmooth X.hom z

/-- **Stage 3 (Stacks 00TT, scheme-to-algebra bridge for the standard smooth
presentation).** Iter-192 axiom-clean intermediate helper: combines Stage 2's
existence-of-standard-smooth-presentation output with the `RingHom`-to-`Algebra`
bridge `RingHom.IsStandardSmooth.toAlgebra`, plus the affine-open stalk
localisation `IsAffineOpen.isLocalization_stalk`. Returns the full algebra-side
package needed by Stages 4-5 of the regularity proof: an affine neighbourhood
`V ∋ z`, an `Algebra Γ(Spec _, U) Γ(X.left, V)` instance under which
`Γ(X.left, V)` is `Algebra.IsStandardSmooth` over `Γ(Spec _, U)`, plus the
`IsLocalization.AtPrime` witness identifying the stalk at `z` with the
localisation of `Γ(X.left, V)` at the prime ideal of `z`.

Axiom-clean: composition of `exists_isStandardSmooth_at_of_smooth` +
`RingHom.IsStandardSmooth.toAlgebra` + `IsAffineOpen.isLocalization_stalk`.

This is the iter-192 Lane M↓ HARD BAR new axiom-clean helper: it packages the
"smooth ⟹ stalk is localisation of a standard-smooth Γ(Spec, U)-algebra"
content as a standalone declaration that downstream Stages 4-5 (the genuine
Stacks 02JK + 00OE Mathlib-gap chain) can consume directly. -/
private theorem exists_algebra_isStandardSmooth_section_stalk_isLocalization_of_smooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom]
    (z : X.left) :
    ∃ (U : (Spec (.of kbar)).Opens) (_hU : IsAffineOpen U)
      (V : X.left.Opens) (hV : IsAffineOpen V)
      (hzV : z ∈ V) (_e : V ≤ X.hom ⁻¹ᵁ U)
      (alg : Algebra Γ(Spec (.of kbar), U) Γ(X.left, V)),
      @Algebra.IsStandardSmooth _ _ _ _ alg ∧
      letI := TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨z, hzV⟩
      IsLocalization.AtPrime
        (X.left.presheaf.stalk z) (hV.primeIdealOf ⟨z, hzV⟩).asIdeal := by
  obtain ⟨U, hU, V, hV, hzV, e, hStdSmooth⟩ :=
    exists_isStandardSmooth_at_of_smooth X z
  refine ⟨U, hU, V, hV, hzV, e, (X.hom.appLE U V e).hom.toAlgebra,
    hStdSmooth.toAlgebra, ?_⟩
  -- Localisation witness: the affine-open stalk is `Aₚ` for `p = primeIdealOf z`.
  letI := TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨z, hzV⟩
  exact hV.isLocalization_stalk ⟨z, hzV⟩

/-- **Stage 4 (Stacks 00T7(2), Kähler-differentials freeness).** Iter-192
axiom-clean intermediate helper: given an algebra-level
`Algebra.IsStandardSmooth R S` instance (typically arising from
`Stage 3 = exists_algebra_isStandardSmooth_section_stalk_isLocalization_of_smooth`),
the module of Kähler differentials `Ω[S⁄R]` is `Module.Free` over `S`. The
basis is the `{d sᵢ}ᵢ` family witnessed by
`Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential`.

Axiom-clean: re-export of `Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential`
+ `Module.Free.of_basis`. -/
private theorem module_free_kaehlerDifferential_of_isStandardSmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmooth R S] :
    Module.Free S (Ω[S⁄R]) := by
  obtain ⟨_, _, b, _⟩ :=
    (Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential
      (R := R) (S := S)).mp ‹_›
  exact Module.Free.of_basis b

/-- **Stage 5a (Stacks 02JK, freeness transports through localisation, algebra-side).**
Iter-193 Lane M↓ axiom-clean substrate helper: for an `R`-algebra `S` whose Kähler
differentials `Ω[S⁄R]` are `S`-free (e.g.\ when `S` is `R`-standard smooth via
`module_free_kaehlerDifferential_of_isStandardSmooth`), the localisation `Sₘ` at any
submonoid `M ⊆ S` has Kähler differentials `Ω[Sₘ⁄R]` which are `Sₘ`-free.

Axiom-clean: composes `KaehlerDifferential.isLocalizedModule_map` (Mathlib re-export)
with `Module.free_of_isLocalizedModule`. This is the substantive localisation-of-freeness
step that Stage 5 of the smooth ⟹ regular pipeline uses; extracted as a named helper
here so the main proof body of `isRegularLocalRing_stalk_of_smooth` reads as a clean
chain of named lemmas rather than an inline `IsLocalizedModule` + `Module.free_of_*`
maneuver. -/
private theorem module_free_kaehlerDifferential_localization
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S] [Algebra R S]
    [Module.Free S (Ω[S⁄R])]
    (M : Submonoid S)
    (Sₘ : Type u) [CommRing Sₘ] [Algebra R Sₘ] [Algebra S Sₘ]
    [IsScalarTower R S Sₘ] [IsLocalization M Sₘ] :
    Module.Free Sₘ (Ω[Sₘ⁄R]) := by
  haveI : IsLocalizedModule M (KaehlerDifferential.map R R S Sₘ) :=
    KaehlerDifferential.isLocalizedModule_map R S Sₘ M
  exact Module.free_of_isLocalizedModule (R := S) (Rₛ := Sₘ) (S := M)
    (M := Ω[S⁄R]) (Mₛ := Ω[Sₘ⁄R])
    (KaehlerDifferential.map R R S Sₘ)

/-- **Stage 5b (Stacks 02JK + 00T7, rank computation through localisation, algebra-side).**
Iter-193 Lane M↓ axiom-clean substrate helper: for an `R`-algebra `S` that is
`IsStandardSmoothOfRelativeDimension n` over `R` and a localisation `Sₘ` at any
submonoid `M` (with `Sₘ` non-trivial), the `Sₘ`-rank of `Ω[Sₘ⁄R]` equals `n`. This
upgrades Stage 5a's freeness conclusion with a *specific* rank.

Axiom-clean: composes `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
(Mathlib, gives `rank S Ω[S⁄R] = n`) with `Module.lift_rank_of_isLocalizedModule_of_free`
(Mathlib, transports module rank through `IsLocalizedModule`). The combination
provides the rank of the stalk-side Kähler differentials, which is one of the two
ingredients of the regularity conclusion at the stalk (the other ingredient is the
Stacks 00OE smooth-algebra dimension formula, still a Mathlib gap). -/
private theorem rank_kaehlerDifferential_localization_eq_relativeDimension
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S] [Nontrivial S] [Algebra R S]
    (n : ℕ) [hS : Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (M : Submonoid S)
    (Sₘ : Type u) [CommRing Sₘ] [Nontrivial Sₘ]
    [Algebra R Sₘ] [Algebra S Sₘ]
    [IsScalarTower R S Sₘ] [IsLocalization M Sₘ] :
    Module.rank Sₘ (Ω[Sₘ⁄R]) = n := by
  haveI : Algebra.IsStandardSmooth R S := hS.isStandardSmooth
  haveI : Module.Free S (Ω[S⁄R]) := Algebra.IsStandardSmooth.free_kaehlerDifferential
  haveI : IsLocalizedModule M (KaehlerDifferential.map R R S Sₘ) :=
    KaehlerDifferential.isLocalizedModule_map R S Sₘ M
  have hrank :
      Cardinal.lift.{u, u} (Module.rank Sₘ (Ω[Sₘ⁄R])) =
      Cardinal.lift.{u, u} (Module.rank S (Ω[S⁄R])) :=
    Module.lift_rank_of_isLocalizedModule_of_free Sₘ M
      (KaehlerDifferential.map R R S Sₘ)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
        (S := S) n] at hrank
  simpa using hrank

/-- **Stage 6.B substrate (Stacks 02JK, RHS of the conormal iso).** Iter-198
Lane COE axiom-clean substrate helper: under the Stage 5a + 5b hypotheses
(`Ω[Sₘ⁄R]` is `Sₘ`-free with `Sₘ`-rank `n`), the residue-field base-change
`κ(mₘ) ⊗_{Sₘ} Ω[Sₘ⁄R]` has `κ(mₘ)`-dimension `n`. This is the *right-hand
side* of the Stacks-02JK cotangent iso
`κ(mₘ) ⊗_{Sₘ} Ω[Sₘ⁄R] ≃ mₘ/mₘ²` (the iso itself is the missing Mathlib
bridge for sub-lemma 6.B); combined with the bridge it gives
`Module.finrank κ (CotangentSpace Sₘ) = n`, the cotangent input of the
regularity criterion `IsRegularLocalRing.iff_finrank_cotangentSpace`.

Axiom-clean: composes `Module.finrank_baseChange` (Mathlib re-export,
`LinearAlgebra/Dimension/Constructions.lean`) with the cardinal-to-natural
cast `Module.finrank_eq_of_rank_eq`. Consumes no Mathlib gap.

The hypothesis pattern (free + rank = n) is exactly the conclusion of
Stages 5a + 5b applied to the stalk of a smooth scheme; the helper is
phrased independently of `IsStandardSmoothOfRelativeDimension` because the
stalk-side localisation is not preserved by that class (Mathlib commit
`b80f227` only provides `localization_away` which collapses to rel-dim 0).
-/
private theorem finrank_residueField_tensor_kaehlerDifferential_of_free_rank_eq
    {R : Type u} [CommRing R]
    {Sₘ : Type u} [CommRing Sₘ] [IsLocalRing Sₘ] [Algebra R Sₘ]
    [Module.Free Sₘ (Ω[Sₘ⁄R])] (n : ℕ) (hrank : Module.rank Sₘ (Ω[Sₘ⁄R]) = n) :
    Module.finrank (IsLocalRing.ResidueField Sₘ)
      (TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) (Ω[Sₘ⁄R])) = n := by
  rw [Module.finrank_baseChange]
  exact Module.finrank_eq_of_rank_eq hrank

/-- **Stage 6.B substrate (Stacks 02JK, LHS-RHS bridge): formally-smooth residue
gives the cotangent iso.** Iter-199 Lane COE axiom-clean closed-point-style
helper: assuming the source ring `Sₘ` is formally smooth over `R`, its residue
field `κ = ResidueField Sₘ` is formally smooth over `R`, and `Ω[κ⁄R]` is
subsingleton (the three hypotheses combine to model the closed-point case of
Stacks 02JK over an algebraically closed base, where `κ = R` makes both FS
and `Ω[κ⁄R] = 0` automatic), the canonical Mathlib map
`KaehlerDifferential.kerCotangentToTensor R Sₘ κ`
is an `Sₘ`-linear equivalence between
`(maximalIdeal Sₘ).Cotangent` (the `Sₘ`-side packaging of `m/m²`)
and `κ ⊗_Sₘ Ω[Sₘ⁄R]` (the residue-field base-change of the Kähler
differentials).

This is the closed-point case of the Stacks-02JK cotangent ↔ Kähler iso
(sub-gap (ii.A) of the Stage 6 chain in `isRegularLocalRing_stalk_of_smooth`).
The proof is the 3-step recipe from `analogies/coe-stacks02jk.md`:

* **Step 1** — retraction → injection via
  `Algebra.FormallySmooth.iff_split_injection`: under
  `FormallySmooth R κ` and surjectivity of `Sₘ → κ`, the conormal map
  `kerCotangentToTensor R Sₘ κ` admits a left-inverse `l`, hence is injective.
* **Step 2** — `Ω[κ⁄R] = 0` + exactness → surjection: combining
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` with
  `Subsingleton (Ω[κ⁄R])` gives that every element of the tensor space lies
  in the kernel of `mapBaseChange`, hence in the range of `kerCotangentToTensor`.
* **Step 3** — bijective → iso: package as `LinearEquiv.ofBijective`.

The `kerCotangentToTensor` map's domain is
`(RingHom.ker (algebraMap Sₘ κ)).Cotangent`, which equals
`(IsLocalRing.maximalIdeal Sₘ).Cotangent = IsLocalRing.CotangentSpace Sₘ` since
`κ = Sₘ / maximalIdeal Sₘ`; the equivalence is therefore the
Stacks 02JK closed-point cotangent iso
`m/m² ≃ₗ[Sₘ] κ ⊗_Sₘ Ω[Sₘ⁄R]`.

Axiom-clean: composes
`Algebra.FormallySmooth.iff_split_injection` (Mathlib;
`Mathlib/RingTheory/Smooth/Basic.lean`),
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` (Mathlib;
`Mathlib/RingTheory/Kaehler/Basic.lean`), and `LinearEquiv.ofBijective`. -/
noncomputable def cotangent_iso_residue_tensor_kaehler_of_formallySmooth_residue
    {R Sₘ : Type*} [CommRing R] [CommRing Sₘ] [IsLocalRing Sₘ] [Algebra R Sₘ]
    [Algebra.FormallySmooth R Sₘ]
    [Algebra.FormallySmooth R (IsLocalRing.ResidueField Sₘ)]
    [Subsingleton (Ω[IsLocalRing.ResidueField Sₘ⁄R])] :
    (RingHom.ker (algebraMap Sₘ (IsLocalRing.ResidueField Sₘ))).Cotangent ≃ₗ[Sₘ]
      TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) Ω[Sₘ⁄R] := by
  -- Surjectivity of `algebraMap Sₘ κ` is the residue surjection.
  have hSurj : Function.Surjective
      (algebraMap Sₘ (IsLocalRing.ResidueField Sₘ)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  -- Step 1: retraction → injection via `iff_split_injection`.
  have hInj : Function.Injective
      (KaehlerDifferential.kerCotangentToTensor R Sₘ (IsLocalRing.ResidueField Sₘ)) := by
    obtain ⟨l, hl⟩ :=
      (Algebra.FormallySmooth.iff_split_injection
        (R := R) (P := Sₘ) (A := IsLocalRing.ResidueField Sₘ) hSurj).mp ‹_›
    refine Function.LeftInverse.injective (g := l) (fun x => ?_)
    have h := LinearMap.congr_fun hl x
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    exact h
  -- Step 2: `Ω[κ⁄R] = 0` + exactness → surjection.
  have hExact :=
    KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R Sₘ
      (IsLocalRing.ResidueField Sₘ) hSurj
  have hSurjMap :
      Function.Surjective
        (KaehlerDifferential.kerCotangentToTensor R Sₘ
          (IsLocalRing.ResidueField Sₘ)) := by
    intro x
    have h0 :
        KaehlerDifferential.mapBaseChange R Sₘ
          (IsLocalRing.ResidueField Sₘ) x = 0 :=
      Subsingleton.elim _ _
    exact (hExact x).mp h0
  -- Step 3: bijective → linear equivalence.
  exact LinearEquiv.ofBijective _ ⟨hInj, hSurjMap⟩

/-- **Stage 6.B substrate (iter-199), maximal-ideal-domain repackaging.** The
same Stacks-02JK closed-point cotangent iso as
`cotangent_iso_residue_tensor_kaehler_of_formallySmooth_residue` above, but
restated with `(IsLocalRing.maximalIdeal Sₘ).Cotangent` (the canonical
`Sₘ/m = κ`-module side of `IsLocalRing.CotangentSpace Sₘ`) as the domain
rather than `(RingHom.ker (algebraMap Sₘ κ)).Cotangent`. The two coincide
through `IsLocalRing.ResidueField.algebraMap_eq + IsLocalRing.ker_residue`,
but the maximal-ideal form is the one Mathlib pre-equips with the κ-module
instance via `IsLocalRing.instModuleResidueFieldCotangentSpace`, so this
repackaging is what downstream κ-finrank computations want to consume.

Axiom-clean: `rw`-transports the iso above along the ideal equality. -/
noncomputable def cotangent_iso_maximalIdeal_residue_tensor_kaehler_of_formallySmooth_residue
    {R Sₘ : Type*} [CommRing R] [CommRing Sₘ] [IsLocalRing Sₘ] [Algebra R Sₘ]
    [Algebra.FormallySmooth R Sₘ]
    [Algebra.FormallySmooth R (IsLocalRing.ResidueField Sₘ)]
    [Subsingleton (Ω[IsLocalRing.ResidueField Sₘ⁄R])] :
    (IsLocalRing.maximalIdeal Sₘ).Cotangent ≃ₗ[Sₘ]
      TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) Ω[Sₘ⁄R] := by
  have hker : RingHom.ker (algebraMap Sₘ (IsLocalRing.ResidueField Sₘ)) =
      IsLocalRing.maximalIdeal Sₘ := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  rw [← hker]
  exact cotangent_iso_residue_tensor_kaehler_of_formallySmooth_residue

/-- **Stage 6.B substrate (iter-199), κ-finrank conclusion.** Assemble the
maximal-ideal-side cotangent iso of
`cotangent_iso_maximalIdeal_residue_tensor_kaehler_of_formallySmooth_residue`
with the 6.B-RHS substrate
`finrank_residueField_tensor_kaehlerDifferential_of_free_rank_eq` to compute
the κ-finrank of `IsLocalRing.CotangentSpace Sₘ` (= `m/m²`) explicitly.

Under the closed-point-style hypothesis pattern (`Sₘ` formally smooth over
`R`, residue field `κ` formally smooth over `R`, `Ω[κ⁄R]` subsingleton),
combined with `Module.Free Sₘ Ω[Sₘ⁄R]` of `Sₘ`-rank `n` (the conclusion of
Stages 5a + 5b applied to a standard-smooth localisation), the cotangent
space `m/m²` has `κ`-finrank equal to `n`.

This is the precise conclusion the consumer
`isRegularLocalRing_stalk_of_smooth` needs: combined with the still-open
Stacks-00OE Krull-dim formula (sub-gap (ii.B)) it discharges the regularity
criterion `IsRegularLocalRing.iff_finrank_cotangentSpace`. Sub-gap (ii.A)
(this lemma) is now axiom-clean; sub-gap (ii.B) remains the residual gap.

Axiom-clean: composes the Sₘ-linear iso with `LinearEquiv.extendScalarsOfSurjective`
(promotion to κ-linear via the residue surjection), `LinearEquiv.finrank_eq`,
and the 6.B-RHS substrate `finrank_baseChange + finrank_eq_of_rank_eq`. -/
private theorem finrank_cotangentSpace_of_formallySmooth_residue
    {R Sₘ : Type u} [CommRing R] [CommRing Sₘ] [IsLocalRing Sₘ]
    [Algebra R Sₘ]
    [Algebra.FormallySmooth R Sₘ]
    [Algebra.FormallySmooth R (IsLocalRing.ResidueField Sₘ)]
    [Subsingleton (Ω[IsLocalRing.ResidueField Sₘ⁄R])]
    [Module.Free Sₘ (Ω[Sₘ⁄R])]
    (n : ℕ) (hrank : Module.rank Sₘ (Ω[Sₘ⁄R]) = n) :
    Module.finrank (IsLocalRing.ResidueField Sₘ)
      (IsLocalRing.CotangentSpace Sₘ) = n := by
  -- 6.B-RHS substrate: finrank κ (κ ⊗_Sₘ Ω[Sₘ⁄R]) = n.
  have hRHS :
      Module.finrank (IsLocalRing.ResidueField Sₘ)
        (TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) (Ω[Sₘ⁄R])) = n :=
    finrank_residueField_tensor_kaehlerDifferential_of_free_rank_eq n hrank
  -- Sₘ-linear iso (maximalIdeal form).
  have hiso :
      (IsLocalRing.maximalIdeal Sₘ).Cotangent ≃ₗ[Sₘ]
        TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) (Ω[Sₘ⁄R]) :=
    cotangent_iso_maximalIdeal_residue_tensor_kaehler_of_formallySmooth_residue
  -- Promote to κ-linear via the residue surjection.
  have hSurj : Function.Surjective
      (algebraMap Sₘ (IsLocalRing.ResidueField Sₘ)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  have hisoκ :
      (IsLocalRing.maximalIdeal Sₘ).Cotangent ≃ₗ[IsLocalRing.ResidueField Sₘ]
        TensorProduct Sₘ (IsLocalRing.ResidueField Sₘ) (Ω[Sₘ⁄R]) :=
    LinearEquiv.extendScalarsOfSurjective hSurj hiso
  rw [hisoκ.finrank_eq, hRHS]

/-- **Stage 6.B substrate (iter-199), bundled bijective-residue-map form.**
Closed-point-friendly bundled variant of
`finrank_cotangentSpace_of_formallySmooth_residue` that replaces the three
typeclass hypotheses `Algebra.FormallySmooth R (ResidueField Sₘ)` and
`Subsingleton (Ω[ResidueField Sₘ⁄R])` with the single hypothesis that
`algebraMap R (ResidueField Sₘ)` is bijective. This is the precise hypothesis
the closed-point case of Stacks 02JK consumes: at a `k̄`-rational closed
point of a smooth `k̄`-algebra, the residue map `k̄ → κ` is the identity
(Nullstellensatz), hence bijective.

The proof:

* `RingHom.FormallySmooth.of_bijective` + `RingHom.formallySmooth_algebraMap`
  upgrade `Bijective` to `Algebra.FormallySmooth R (ResidueField Sₘ)`.
* `KaehlerDifferential.subsingleton_of_surjective` deduces
  `Subsingleton (Ω[ResidueField Sₘ⁄R])` from the surjectivity half of
  bijectivity.
* Then apply the typeclass-hypothesis form
  `finrank_cotangentSpace_of_formallySmooth_residue`.

Axiom-clean: composes Mathlib bridges with the iter-199 helper above. -/
private theorem finrank_cotangentSpace_of_bijective_algebraMap_residue
    {R Sₘ : Type u} [CommRing R] [CommRing Sₘ] [IsLocalRing Sₘ]
    [Algebra R Sₘ]
    [Algebra.FormallySmooth R Sₘ]
    [Module.Free Sₘ (Ω[Sₘ⁄R])]
    (hbij : Function.Bijective (algebraMap R (IsLocalRing.ResidueField Sₘ)))
    (n : ℕ) (hrank : Module.rank Sₘ (Ω[Sₘ⁄R]) = n) :
    Module.finrank (IsLocalRing.ResidueField Sₘ)
      (IsLocalRing.CotangentSpace Sₘ) = n := by
  haveI : Algebra.FormallySmooth R (IsLocalRing.ResidueField Sₘ) :=
    RingHom.formallySmooth_algebraMap.mp
      (RingHom.FormallySmooth.of_bijective hbij)
  haveI : Subsingleton (Ω[IsLocalRing.ResidueField Sₘ⁄R]) :=
    KaehlerDifferential.subsingleton_of_surjective R _ hbij.surjective
  exact finrank_cotangentSpace_of_formallySmooth_residue n hrank

/-! ### Stacks-00OE Krull-dimension bridge

The smooth-algebra Krull-dimension formula at closed points (Stacks 00OE) is
provided by `AlgebraicJacobian.Albanese.StandardSmoothDimension`
(`MvPolynomial.height_eq_natCard_of_isMaximal` +
`Algebra.IsStandardSmoothOfRelativeDimension.natCast_le_height_of_isMaximal` +
`le_ringKrullDim_of_isLocalization_atPrime`), which replaced an earlier
in-file regular-sequence-witness chain (deleted as dead code). Only the
localization/height translator below remains here. -/

/-- **Stacks 00OE localization/height bridge.** Ergonomic re-export of
`IsLocalization.AtPrime.ringKrullDim_eq_height`: for a prime ideal `m ⊂ R` and
a localization `A = R_m`, `ringKrullDim A = m.height`. This is the boundary
translator between `Scheme.ringKrullDim_stalk_eq_coheight` (the iter-183
CoheightBridge bridge, phrased in `ringKrullDim`) and the
`StandardSmoothDimension` height arithmetic (phrased in `Ideal.height`).

Axiom-clean: 1-line re-export. -/
private theorem ringKrullDim_localization_eq_height_atPrime
    {R : Type*} [CommRing R] (m : Ideal R) [m.IsPrime]
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A m] :
    ringKrullDim A = m.height :=
  IsLocalization.AtPrime.ringKrullDim_eq_height m A

/-- **Stage 6 sub-gap (i) resolution (iter-198).** Axiom-clean substrate helper:
every `Algebra.IsStandardSmooth R S` instance can be promoted to
`Algebra.IsStandardSmoothOfRelativeDimension n R S` for some specific `n : ℕ`
(extracted from the underlying submersive presentation via
`Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension`).

This closes the iter-193 "sub-gap (i): relative-dimension determination"
identified in the docstring of `isRegularLocalRing_stalk_of_smooth` below.
The remaining Stage 6 gap is solely (ii) the Stacks-00OE smooth-algebra
Krull-dimension formula plus the Stacks-02JK cotangent-Kähler bridge over a
field.

Axiom-clean: a 4-line unpacking of `Algebra.IsStandardSmooth.out` via
`Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension`. No
Mathlib gap; the only reason this was a sub-gap iter-191--194 was an
overconservative read of `IsStandardSmooth.relativeDimension`'s
`Classical.choice` apparatus. -/
private theorem exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [hS : Algebra.IsStandardSmooth R S] :
    ∃ n : ℕ, Algebra.IsStandardSmoothOfRelativeDimension n R S := by
  obtain ⟨iota, sigma, hσ, hι, ⟨P⟩⟩ := hS.out
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

/-! ## §3.B. Project-local Mathlib supplement — Stage 6 scheme-to-algebra bridges (iter-202)

Lane COE Step B substrate: four axiom-clean scheme-to-algebra bridges feeding the
eventual closure of `isRegularLocalRing_stalk_of_smooth` (the L1061 Stacks-00TT
regularity gap). They are deliberately decoupled from Step A1 (the Matsumura
Jacobian-regular-sequence witness, gated on the iter-203 `AuslanderBuchsbaum`
public promotions) so they land independently this iter.

* **B.a** (`exists_submersivePresentation_of_isStandardSmoothOfRelativeDimension`):
  extract the explicit `Algebra.SubmersivePresentation` with `P.dimension = n`
  from `Algebra.IsStandardSmoothOfRelativeDimension n R S` (the relative-dimension
  packaging produced by the iter-198 sub-gap (i) discharger
  `exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth`).
* **B.b** (`isLocalization_atPrime_stalk_of_affineOpen`): the affine-open
  stalk-localisation `IsLocalization.AtPrime (stalk z) (primeIdealOf z)`, decoupled
  from standard-smoothness, as a named reusable substrate lemma.
* **B.c** (`open_eq_top_of_subsingleton` + `gammaSpecField_ringEquiv`): on a scheme
  whose carrier is a subsingleton (e.g.\ `Spec (.of k̄)` for a field `k̄`), every
  nonempty open is `⊤`; hence the sections of `Spec (.of k̄)` over any nonempty
  open form a ring isomorphic to `k̄`. This is the `Γ(Spec (.of k̄), U) = k̄`
  definitional bridge of the COE recipe, giving the algebraically-closed base ring
  of the standard-smooth presentation a clean `k̄`-identification.

`isLocalization_atPrime_stalk_of_affineOpen` / `gammaSpecField_ringEquiv` are
exposed (non-`private`) since they are generic Mathlib-shaped facts a future
in-file or cross-file consumer may want; the rest are `private` helpers. -/

/-- **Lane COE Step B.a (iter-202).** Extract the explicit
`Algebra.SubmersivePresentation` underlying an
`Algebra.IsStandardSmoothOfRelativeDimension n R S` instance, together with the
witness `P.dimension = n`. This is a forward-ergonomics re-export of the
`Algebra.IsStandardSmoothOfRelativeDimension.out` field, giving Step B.d direct
access to the submersive presentation `P` (whose relations are the input to the
iter-203 Step A1 Jacobian-regular-sequence witness). Axiom-clean: 1-line
re-export of the structure field. -/
private theorem exists_submersivePresentation_of_isStandardSmoothOfRelativeDimension
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ} [h : Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ (ix sx : Type), ∃ (_ : Finite sx) (_ : Finite ix),
      ∃ P : Algebra.SubmersivePresentation R S ix sx, P.dimension = n :=
  h.out

/-- **Lane COE Step B.b (iter-202).** The affine-open stalk localisation: for an
affine open `V ∋ z` of a scheme `X`, the stalk `X.presheaf.stalk z` is the
localisation of the section ring `Γ(X, V)` at the prime ideal `primeIdealOf z`.
Re-export of `IsAffineOpen.isLocalization_stalk`, decoupled here from
standard-smoothness so downstream regularity computations (Step B.d) can name the
`IsLocalization.AtPrime` instance without re-deriving the Stage-3 algebra package.
Axiom-clean: 1-line re-export. -/
theorem isLocalization_atPrime_stalk_of_affineOpen
    {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V) (z : X) (hzV : z ∈ V) :
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzV⟩
    IsLocalization.AtPrime (X.presheaf.stalk z) (hV.primeIdealOf ⟨z, hzV⟩).asIdeal :=
  hV.isLocalization_stalk ⟨z, hzV⟩

/-- **Lane COE Step B.c helper (iter-202).** On a scheme whose underlying carrier
is a subsingleton (the topological space has at most one point — e.g.\
`Spec (.of k̄)` for a field `k̄`, which has a unique point by
`PrimeSpectrum.instUnique`), every nonempty open subset equals `⊤`. Axiom-clean:
the unique-point argument via `Subsingleton.elim`. -/
private lemma open_eq_top_of_subsingleton {X : Scheme.{u}} [Subsingleton X]
    (U : X.Opens) (hU : Nonempty U) : U = ⊤ := by
  obtain ⟨⟨x, hx⟩⟩ := hU
  ext y
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  rwa [Subsingleton.elim y x]

/-- **Lane COE Step B.c (iter-202).** The `Γ(Spec (.of k̄), U) = k̄` bridge: for a
field `k̄` and any nonempty open `U` of `Spec (.of k̄)`, the section ring over `U`
is ring-isomorphic to `k̄`. Since `Spec (.of k̄)` has a subsingleton carrier
(`PrimeSpectrum.instUnique`), `U = ⊤` and the sections collapse to the global
sections `Γ(Spec (.of k̄), ⊤) ≅ k̄` (`Scheme.ΓSpecIso`). This supplies the
algebraically-closed base ring of the standard-smooth presentation
(`R = Γ(Spec (.of k̄), U)`) with a clean `k̄`-identification — the geometric input
to the closed-point residue-field bridge `finrank_cotangentSpace_of_bijective_algebraMap_residue`.
Axiom-clean: `subst` of `open_eq_top_of_subsingleton` + `Scheme.ΓSpecIso`. -/
noncomputable def gammaSpecField_ringEquiv (kbar : Type u) [Field kbar]
    (U : (Spec (.of kbar)).Opens) (hU : Nonempty U) :
    Γ(Spec (.of kbar), U) ≃+* kbar := by
  have h : U = ⊤ := open_eq_top_of_subsingleton U hU
  subst h
  exact (Scheme.ΓSpecIso (.of kbar)).commRingCatIsoToRingEquiv

/-- **Lane COE Step B.d — Stacks `00TT` at a rational closed point, algebra
level (this iter).** For a standard-smooth algebra `S` over a field `k`, a
maximal ideal `m ⊆ S` whose induced residue map `k → κ(m)` is bijective (the
`k`-rational-point condition, automatic over an algebraically closed field by
the Nullstellensatz), the localisation `Sₘ` is a regular local ring.

This *closes sub-gap (ii.B) at closed points*: the proof combines
* the iter-199 sub-gap (ii.A) cotangent computation
  `finrank_cotangentSpace_of_bijective_algebraMap_residue`
  (`finrank κ (m/m²) = n`, from formal smoothness + free Kähler differentials
  of rank `n`), with
* the new `StandardSmoothDimension.lean` dimension lower bound
  `Algebra.IsStandardSmoothOfRelativeDimension.le_ringKrullDim_of_isLocalization_atPrime`
  (`n ≤ ringKrullDim Sₘ`, via the polynomial-ring height computation and
  Krull's height theorem — no transcendence-degree theory needed), through
* the generic glue `IsRegularLocalRing.of_finrank_cotangentSpace_le_ringKrullDim`
  (a Noetherian local ring with `dim_κ m/m² ≤ ringKrullDim` is regular).

The consumer `isRegularLocalRing_stalk_of_smooth` quantifies over *all*
points `z`; the non-closed points (where the residue field is a
transcendental extension of `k̄` and the bijectivity hypothesis fails) are
now handled by the Serre-free arbitrary-prime theorem of
`Albanese/SmoothPrimeRegularity.lean`, so the whole pipeline is `sorry`-free
without Stacks `00OF`. This closed-point form is retained as the input to
Step B.e (`isReduced_of_isStandardSmooth_of_isAlgClosed`). Axiom-clean. -/
theorem isRegularLocalRing_localization_of_isStandardSmooth_of_bijective_residue
    {k : Type u} [Field k]
    {S : Type u} [CommRing S] [Nontrivial S] [Algebra k S]
    [Algebra.IsStandardSmooth k S]
    (m : Ideal S) (hm : m.IsMaximal)
    (Sₘ : Type u) [CommRing Sₘ] [IsLocalRing Sₘ] [Algebra k Sₘ] [Algebra S Sₘ]
    [IsScalarTower k S Sₘ] [IsLocalization.AtPrime Sₘ m]
    (hbij : Function.Bijective (algebraMap k (IsLocalRing.ResidueField Sₘ))) :
    IsRegularLocalRing Sₘ := by
  haveI := hm.isPrime
  -- Noetherian structure: standard-smooth ⟹ finite presentation ⟹ Noetherian
  -- over the base field; localisation preserves Noetherianness.
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  haveI : IsNoetherianRing Sₘ := IsLocalization.isNoetherianRing m.primeCompl Sₘ ‹_›
  -- Extract the relative dimension n.
  obtain ⟨n, hn⟩ :=
    exists_isStandardSmoothOfRelativeDimension_of_isStandardSmooth (R := k) (S := S)
  haveI := hn
  -- Kähler package at the localisation (Stages 4, 5a, 5b).
  haveI : Module.Free S (Ω[S⁄k]) := module_free_kaehlerDifferential_of_isStandardSmooth
  haveI : Module.Free Sₘ (Ω[Sₘ⁄k]) :=
    module_free_kaehlerDifferential_localization m.primeCompl Sₘ
  have hrank : Module.rank Sₘ (Ω[Sₘ⁄k]) = n :=
    rank_kaehlerDifferential_localization_eq_relativeDimension n m.primeCompl Sₘ
  -- Formal smoothness of the localisation over k.
  haveI : Algebra.FormallySmooth S Sₘ := Algebra.FormallySmooth.of_isLocalization m.primeCompl
  haveI : Algebra.FormallySmooth k Sₘ := Algebra.FormallySmooth.comp k S Sₘ
  -- (ii.A): cotangent finrank = n at the k-rational closed point.
  have hcot := finrank_cotangentSpace_of_bijective_algebraMap_residue hbij n hrank
  -- (ii.B): dimension lower bound n ≤ dim Sₘ.
  have hdim :=
    Algebra.IsStandardSmoothOfRelativeDimension.le_ringKrullDim_of_isLocalization_atPrime
      (k := k) n m hm Sₘ
  exact IsRegularLocalRing.of_finrank_cotangentSpace_le_ringKrullDim
    (by rw [hcot]; exact_mod_cast hdim)

/-- **Lane COE Step B.d′ — Stacks `00TT` at closed points over an algebraically
closed field, unconditional form.** Over an algebraically closed base field the
`k`-rationality hypothesis of Step B.d is automatic: for any maximal ideal
`m ⊆ S` of the standard-smooth algebra `S`, the residue field `S ⧸ m` is a
finite (Zariski's lemma, `finite_of_finite_type_of_isJacobsonRing`) hence
algebraic extension of `k`, so `k → κ(m)` is bijective
(`IsAlgClosed.algebraMap_bijective_of_isIntegral` composed with
`Ideal.bijective_algebraMap_quotient_residueField`). Hence the local ring of a
standard-smooth `k̄`-algebra at **every** closed point is regular. Stated for
the model localisation `Localization.AtPrime m`; transport to an abstract
localisation (e.g. a scheme stalk) via `IsRegularLocalRing.of_ringEquiv` along
`IsLocalization.algEquiv`. Axiom-clean. -/
theorem isRegularLocalRing_localizationAtPrime_of_isStandardSmooth_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {S : Type u} [CommRing S] [Nontrivial S] [Algebra k S]
    [Algebra.IsStandardSmooth k S]
    (m : Ideal S) (hm : m.IsMaximal) :
    IsRegularLocalRing (Localization.AtPrime m) := by
  haveI := hm.isPrime
  refine isRegularLocalRing_localization_of_isStandardSmooth_of_bijective_residue
    (k := k) m hm (Localization.AtPrime m) ?_
  -- Zariski's lemma: the residue field `S ⧸ m` is module-finite over `k`.
  -- (The `Field` instance must be installed FIRST so all subsequent instance
  -- searches on `S ⧸ m` share its semiring key.)
  letI := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (S ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  haveI : Module.Finite k (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
  haveI : Algebra.IsIntegral k (S ⧸ m) := Algebra.IsIntegral.of_finite k (S ⧸ m)
  -- `k → S ⧸ m` is bijective since `k` is algebraically closed.
  have h1 : Function.Bijective (algebraMap k (S ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  -- `S ⧸ m → κ(m)` is bijective since `m` is maximal.
  have h2 := m.bijective_algebraMap_quotient_residueField
  rw [show algebraMap k (IsLocalRing.ResidueField (Localization.AtPrime m))
      = (algebraMap (S ⧸ m) m.ResidueField).comp (algebraMap k (S ⧸ m)) from
    IsScalarTower.algebraMap_eq k (S ⧸ m) m.ResidueField]
  exact h2.comp h1

/-- **Lane COE Step B.e — standard-smooth algebras over an algebraically closed
field are reduced (Stacks `033B`/`00TT` corollary).** For a standard-smooth
algebra `S` over an algebraically closed field `k`, the ring `S` is reduced.

Route: reducedness is checked at localisations at maximal ideals
(`isReduced_ofLocalizationMaximal`); each localisation `Sₘ` is a regular local
ring by the Step B.d′ closed-point theorem
(`isRegularLocalRing_localizationAtPrime_of_isStandardSmooth_of_isAlgClosed`),
regular local rings are domains
(`RingTheory.CohenMacaulay.isDomain_of_regularLocal`, the project-local
Stacks `00NP` from `AuslanderBuchsbaum.lean`), and domains are reduced.
The trivial-ring case is reduced vacuously. Axiom-clean. -/
theorem isReduced_of_isStandardSmooth_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (S : Type u) [CommRing S] [Algebra k S]
    [Algebra.IsStandardSmooth k S] :
    _root_.IsReduced S := by
  cases subsingleton_or_nontrivial S with
  | inl _ => exact ⟨fun x _ => Subsingleton.elim x 0⟩
  | inr _ =>
    refine isReduced_ofLocalizationMaximal S (fun m hm => ?_)
    haveI := hm.isPrime
    haveI : IsRegularLocalRing (Localization.AtPrime m) :=
      isRegularLocalRing_localizationAtPrime_of_isStandardSmooth_of_isAlgClosed
        (k := k) m hm
    haveI : IsDomain (Localization.AtPrime m) :=
      RingTheory.CohenMacaulay.isDomain_of_regularLocal _
    infer_instance

/-- **Stacks `056S`/`033B` over an algebraically closed field: a scheme smooth
over `Spec k̄` is reduced.** This discharges the former Mathlib-gap helper
`isReduced_of_smooth_over_field` in `Thm32RationalMapExtension.lean` (the
`IsReduced A.left` input to `av_isIntegral_of_smooth_geomIrred`).

Route: reducedness is stalk-local (`isReduced_of_isReduced_stalk`). At each
point `z`, Stage 2 (`exists_isStandardSmooth_at_of_smooth`) produces an affine
chart `V ∋ z` over an affine open `U ⊆ Spec k̄` with
`Γ(X.left, V)` standard-smooth over `Γ(Spec k̄, U)`; the base identification
`Γ(Spec k̄, U) ≃+* k̄` (`gammaSpecField_ringEquiv`, `U` is nonempty since it
contains the image of `z`) transports standard-smoothness to a `k̄`-algebra
structure (`RingHom.isStandardSmooth_respectsIso`), Step B.e above gives
`IsReduced Γ(X.left, V)`, and the stalk — the localisation of `Γ(X.left, V)`
at the prime of `z` (`IsAffineOpen.isLocalization_stalk`) — is reduced by
`isReduced_localizationPreserves`.

Reducedness only needs the maximal-ideal localisations of the chart ring, so the
closed-point theorem B.d′ suffices at EVERY point `z`. Axiom-clean.

**Two corrections to this paragraph, 2026-07-30 (`ajc-p4`).**  It used to open
"Unlike the still-open regularity keystone `isRegularLocalRing_stalk_of_smooth`
(blocked on Stacks `00OF` at non-closed points)".  That keystone is **not** open
and is **not** blocked on `00OF`: it is proved above via
`isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField`
(`Albanese/SmoothPrimeRegularity.lean`), whose whole point is avoiding `00OF`,
and its own docstring says so.  Second, the contrast drawn here is backwards as
a guide to which statement is cheaper in the field: the regularity route widens
to a **perfect** base field unchanged, while THIS statement's route does not,
because Step B.e (`isReduced_of_isStandardSmooth_of_isAlgClosed`) is the
closed-point argument.  The perfect-field reducedness statement therefore takes a
different route — regular local ⇒ domain ⇒ reduced at each stalk — and is
`Scheme.isReduced_of_smooth_perfectField` in `Albanese/CodimOnePerfectField.lean`,
together with the rest of the Milne 3.1 chain over a perfect field. -/
theorem isReduced_of_smooth_of_isAlgClosed
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom] :
    IsReduced X.left := by
  haveI hstalk : ∀ z : X.left.toPresheafedSpace,
      _root_.IsReduced (X.left.presheaf.stalk z) := by
    intro z
    -- Stage 2: standard-smooth chart at z, RingHom form.
    obtain ⟨U, hU, V, hV, hzV, e, hSS⟩ := exists_isStandardSmooth_at_of_smooth X z
    -- Base identification: U contains the image of z, so Γ(Spec k̄, U) ≃+* k̄.
    let ε : kbar ≃+* Γ(Spec (.of kbar), U) :=
      (gammaSpecField_ringEquiv kbar U ⟨⟨_, e hzV⟩⟩).symm
    -- Transport standard-smoothness along the base iso.
    have hSS' : ((X.hom.appLE U V e).hom.comp ε.toRingHom).IsStandardSmooth :=
      RingHom.isStandardSmooth_respectsIso.2 _ ε hSS
    letI : Algebra kbar Γ(X.left, V) :=
      ((X.hom.appLE U V e).hom.comp ε.toRingHom).toAlgebra
    haveI : Algebra.IsStandardSmooth kbar Γ(X.left, V) := hSS'.toAlgebra
    -- Sections over V are reduced (Step B.e).
    haveI hSred : _root_.IsReduced Γ(X.left, V) :=
      isReduced_of_isStandardSmooth_of_isAlgClosed kbar Γ(X.left, V)
    -- The stalk is a localisation of Γ(X.left, V); reducedness localises.
    letI : Algebra Γ(X.left, V) (X.left.presheaf.stalk z) :=
      TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨z, hzV⟩
    haveI : IsLocalization.AtPrime (X.left.presheaf.stalk z)
        (hV.primeIdealOf ⟨z, hzV⟩).asIdeal := hV.isLocalization_stalk ⟨z, hzV⟩
    exact isReduced_localizationPreserves
      (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl (X.left.presheaf.stalk z) hSred
  exact isReduced_of_isReduced_stalk X.left

/-- **Integrality of the self-product `X ×_{k̄} X`.** For a smooth, geometrically
irreducible, integral scheme `X` over an algebraically closed field `k̄`, the self
fibre product `X ×_{k̄} X` is integral: it is reduced because it is smooth over the
algebraically closed field (`isReduced_of_smooth_of_isAlgClosed` on the composite
structure map `pr₁ ≫ X.hom`) and irreducible because `X.hom` is geometrically
irreducible and universally open (`GeometricallyIrreducible.irreducibleSpace`,
base change of geometric irreducibility along the open projection).

This discharges the `[IsIntegral (pullback X.hom X.hom)]` hypothesis of
`AlgebraicGeometry.Scheme.RationalMap.differenceRationalMap` (Milne Lemma 3.3,
Sub-step 1, `Albanese/DifferenceMap.lean`), and supplies the integral-surface input
to the pole-purity engine of Sub-step 4 (`Albanese/PolePurity.lean`). Axiom-clean. -/
theorem isIntegral_pullback_self
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsIntegral X.left] :
    IsIntegral (pullback X.hom X.hom) := by
  -- The composite structure map `X ×_{k̄} X → Spec k̄` is smooth (`smooth_comp` of
  -- the base-change-smooth projection with `X.hom`); package it as an `Over` object.
  haveI hsm : Smooth (Over.mk (pullback.fst X.hom X.hom ≫ X.hom)).hom := by
    change Smooth (pullback.fst X.hom X.hom ≫ X.hom)
    infer_instance
  haveI hred : IsReduced (pullback X.hom X.hom) :=
    isReduced_of_smooth_of_isAlgClosed (Over.mk (pullback.fst X.hom X.hom ≫ X.hom))
  -- Irreducibility of `X ×_{k̄} X` from geometric irreducibility of `X.hom` (the
  -- projection is universally open). Drive synthesis through the `Scheme`-typed
  -- application so the `Scheme → Type` coercion on the pullback is inserted (a bare
  -- `IrreducibleSpace (pullback …)` mis-resolves `pullback` in the `Type` category).
  haveI : UniversallyOpen X.hom := inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced (pullback X.hom X.hom)

/-! ## §3.C. Project-local Mathlib supplement

### Matsumura regular-sequence bridge (iter-203, Step A1)

Lane COE Step A1 substrate (Matsumura *Commutative Ring Theory* Thm 14.2 /
Stacks 00NQ). The goal of this section is the criterion: on a regular local
Noetherian ring `(A, 𝔪)`, a finite sequence `f₁,…,f_c ∈ 𝔪` whose images in the
cotangent space `𝔪/𝔪²` are `κ`-linearly independent forms a
`RingTheory.Sequence.IsRegular` sequence.

The induction is on the length `c`, peeling the head `f₁`. The mathematical
peeling step uses `RingTheory.Sequence.IsRegular.cons'`, whose tail lives over
the *module* quotient `QuotSMulTop f₁ A = A ⧸ (f₁ • ⊤)`. The two bridges below
convert that module-quotient bookkeeping into the *ring* quotient
`A ⧸ Ideal.span {f₁}` (over which the induction hypothesis is naturally
phrased): `quotSMulTop_quotientRing_linearEquiv` is the canonical
`(A ⧸ span{f₁})`-linear identification `QuotSMulTop f₁ A ≃ₗ A ⧸ span{f₁}`, and
`isRegular_cons_of_quotient_ring` is the resulting clean cons rule.

These are project-local because Mathlib ships only the `QuotSMulTop`-flavoured
`IsRegular.cons'`; the ring-quotient repackaging is what makes a downstream
ring-theoretic induction (the Matsumura criterion) ergonomic. -/

/-- **Step A1 bridge (iter-203).** The canonical `(A ⧸ span{r})`-linear
equivalence between the module quotient `QuotSMulTop r A = A ⧸ (r • ⊤)` and the
ring quotient `A ⧸ span{r}`. Built by composing Mathlib's
`QuotSMulTop.equivQuotTensor` (`QuotSMulTop r A ≃ₗ[A] (A⧸span{r}) ⊗[A] A`) with
`TensorProduct.rid` and then promoting the resulting `A`-linear equivalence to
an `(A⧸span{r})`-linear one via `LinearEquiv.extendScalarsOfSurjective` along the
surjective quotient map. Axiom-clean. -/
private noncomputable def quotSMulTop_quotientRing_linearEquiv
    {A : Type u} [CommRing A] (r : A) :
    QuotSMulTop r A ≃ₗ[A ⧸ Ideal.span {r}] (A ⧸ Ideal.span {r}) :=
  LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    ((QuotSMulTop.equivQuotTensor r A) ≪≫ₗ (TensorProduct.rid A (A ⧸ Ideal.span {r})))

/-- **Step A1 bridge (iter-203).** Ring-quotient cons rule for regular
sequences: given `IsSMulRegular A r` and a regular sequence over the ring
quotient `A ⧸ span{r}` on the images of `rs`, the list `r :: rs` is a regular
sequence over `A`. This is the ergonomic ring-quotient form of Mathlib's
`RingTheory.Sequence.IsRegular.cons'` (whose tail lives over the module quotient
`QuotSMulTop r A`), transported across `quotSMulTop_quotientRing_linearEquiv` via
`LinearEquiv.isRegular_congr`. Axiom-clean. -/
private theorem isRegular_cons_of_quotient_ring
    {A : Type u} [CommRing A] {r : A} {rs : List A}
    (h1 : IsSMulRegular A r)
    (h2 : RingTheory.Sequence.IsRegular (A ⧸ Ideal.span {r})
            (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    RingTheory.Sequence.IsRegular A (r :: rs) := by
  apply RingTheory.Sequence.IsRegular.cons' h1
  exact ((quotSMulTop_quotientRing_linearEquiv r).symm.isRegular_congr _).mp h2

set_option maxHeartbeats 1600000 in
-- The cotangent-map kernel computation + the hand-rolled `linearIndependent_iff`
-- argument are heartbeat-heavy; the default budget is insufficient.
/-- **Step A1 cotangent linear-independence descent (iter-203).** The inductive
descent step of the Matsumura criterion: if the cotangent classes of a sequence
`f₀, f₁, …, f_m ∈ 𝔪` are `κ(A)`-linearly independent, then the cotangent classes
of the *tail* `f₁, …, f_m`, pushed into the quotient `A' = A ⧸ span{f₀}`, are
`κ(A')`-linearly independent in `𝔪'/𝔪'²`.

This is the genuine mathematical content of the descent (the part the iter-203
blueprint recipe flagged as a `LinearIndependent.map`/`.image` step). The proof
constructs the `A`-linear cotangent map `π : 𝔪.Cotangent →ₗ[A] 𝔪'.Cotangent`
(Mathlib's `Ideal.mapCotangent` for the quotient algebra `A → A'`), shows it is
surjective with kernel `A ∙ (𝔪.toCotangent f₀)` (via
`Ideal.mapCotangent_ker_of_surjective`, using `span{f₀} ⊓ 𝔪 = span{f₀}`), and
then runs the kernel-disjointness/linear-independence argument by hand through
`Fintype.linearIndependent_iff`: a `κ(A')`-relation on the tail images lifts to
an `A`-relation `∑ aᵢ • π(vᵢ₊₁) = 0`, hence `∑ aᵢ • vᵢ₊₁ ∈ ker π = A ∙ v₀`, so
reducing modulo `𝔪` and applying the full `κ(A)`-independence forces every
`residue (aᵢ) = 0`, whence every original `κ(A')`-coefficient vanishes (the
residue fields are matched through `algebraMap A A'`, no explicit residue-field
isomorphism is needed).

Project-local because Mathlib ships `Ideal.mapCotangent` and its kernel/surjectivity
lemmas but not this regular-local descent packaging. Axiom-clean. -/
private theorem matsumura_descent_cotangent
    {A : Type u} [CommRing A] [IsLocalRing A]
    (m : ℕ) (rs : Fin (m + 1) → A) (hmem : ∀ i, rs i ∈ IsLocalRing.maximalIdeal A)
    [IsLocalRing (A ⧸ Ideal.span ({rs 0} : Set A))]
    (hlin : LinearIndependent (IsLocalRing.ResidueField A)
       (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨rs i, hmem i⟩))
    (hg'mem : ∀ i : Fin m, (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)) (rs i.succ))
       ∈ IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A))) :
    LinearIndependent (IsLocalRing.ResidueField (A ⧸ Ideal.span ({rs 0} : Set A)))
      (fun i : Fin m => (IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A))).toCotangent
        ⟨Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)) (rs i.succ), hg'mem i⟩) := by
  set x := rs 0 with hxdef
  have hxmem : x ∈ IsLocalRing.maximalIdeal A := hmem 0
  set B := A ⧸ Ideal.span ({x} : Set A) with hB
  have hsurj : Function.Surjective (algebraMap A B) := Ideal.Quotient.mk_surjective
  have halg : algebraMap A B = Ideal.Quotient.mk (Ideal.span ({x} : Set A)) :=
    Ideal.Quotient.algebraMap_eq _
  have hkerm : RingHom.ker (algebraMap A B) = Ideal.span ({x} : Set A) := by
    rw [halg]; exact Ideal.mk_ker
  have hcomap : Ideal.comap (algebraMap A B) (IsLocalRing.maximalIdeal B)
      = IsLocalRing.maximalIdeal A :=
    (IsLocalRing.isMaximal_iff A).mp (Ideal.comap_isMaximal_of_surjective _ hsurj)
  have heq : Ideal.comap (algebraMap A B) (IsLocalRing.maximalIdeal B)
      = RingHom.ker (algebraMap A B) ⊔ IsLocalRing.maximalIdeal A := by
    rw [hcomap, hkerm, sup_eq_right.mpr]; rwa [Ideal.span_le, Set.singleton_subset_iff]
  have hle : IsLocalRing.maximalIdeal A
      ≤ Ideal.comap (Algebra.ofId A B) (IsLocalRing.maximalIdeal B) := hcomap.ge
  set π := (IsLocalRing.maximalIdeal A).mapCotangent (IsLocalRing.maximalIdeal B)
    (Algebra.ofId A B) hle with hπdef
  have hπker := Ideal.mapCotangent_ker_of_surjective
    (I := IsLocalRing.maximalIdeal B) (J := IsLocalRing.maximalIdeal A) hsurj heq
  have hxsq : Ideal.span ({x} : Set A) ⊓ IsLocalRing.maximalIdeal A = Ideal.span ({x} : Set A) := by
    rw [inf_eq_left, Ideal.span_le, Set.singleton_subset_iff]; exact hxmem
  have hcomapsub : Submodule.comap (Submodule.subtype (IsLocalRing.maximalIdeal A))
      (Ideal.span ({x} : Set A))
      = Submodule.span A {(⟨x, hxmem⟩ : IsLocalRing.maximalIdeal A)} := by
    apply le_antisymm
    · rintro ⟨a, ha⟩ hain
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hain
      rw [Ideal.mem_span_singleton'] at hain
      obtain ⟨r, rfl⟩ := hain
      rw [Submodule.mem_span_singleton]; exact ⟨r, by ext; simp⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      simp only [SetLike.mem_coe, Submodule.mem_comap, Submodule.coe_subtype]
      exact Ideal.mem_span_singleton_self x
  have hkerπ : LinearMap.ker π
      = Submodule.span A {(IsLocalRing.maximalIdeal A).toCotangent ⟨x, hxmem⟩} := by
    rw [hπdef, hπker, hkerm, hxsq, hcomapsub, Submodule.map_span]; congr 1; simp
  set v : Fin (m + 1) → IsLocalRing.CotangentSpace A :=
    fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨rs i, hmem i⟩ with hvdef
  have hF1 : ∀ i : Fin m, π (v i.succ) = (IsLocalRing.maximalIdeal B).toCotangent
      ⟨Ideal.Quotient.mk (Ideal.span ({x} : Set A)) (rs i.succ), hg'mem i⟩ := by
    intro i; rw [hvdef, hπdef, Ideal.mapCotangent_toCotangent]; congr 1
  rw [show (fun i : Fin m => (IsLocalRing.maximalIdeal B).toCotangent
      ⟨Ideal.Quotient.mk (Ideal.span ({x} : Set A)) (rs i.succ), hg'mem i⟩)
      = (fun i => π (v i.succ)) from by funext i; rw [hF1]]
  have e1 : ∀ (r : A) (y : IsLocalRing.CotangentSpace A),
      r • y = (IsLocalRing.residue A r) • y := fun r y => by
    rw [← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField A) r y]; rfl
  have e1B : ∀ (r : B) (y : IsLocalRing.CotangentSpace B),
      r • y = (IsLocalRing.residue B r) • y := fun r y => by
    rw [← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField B) r y]; rfl
  have hρsurj : Function.Surjective (fun a : A => IsLocalRing.residue B (algebraMap A B a)) :=
    (IsLocalRing.residue_surjective).comp hsurj
  rw [Fintype.linearIndependent_iff]
  intro g hg
  choose a ha using fun i => hρsurj (g i)
  have hai : ∀ i, IsLocalRing.residue B (algebraMap A B (a i)) = g i := ha
  have hstep : ∀ i : Fin m, g i • π (v i.succ) = a i • π (v i.succ) := by
    intro i
    rw [← hai i, ← e1B (algebraMap A B (a i)) (π (v i.succ)),
        IsScalarTower.algebraMap_smul B (a i) (π (v i.succ))]
  have hsumeq : ∑ i, g i • π (v i.succ) = π (∑ i, a i • v i.succ) := by
    rw [map_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [hstep i, map_smul])
  rw [hsumeq] at hg
  have hmemker : (∑ i, a i • v i.succ) ∈ LinearMap.ker π := hg
  rw [hkerπ, Submodule.mem_span_singleton] at hmemker
  obtain ⟨b, hb⟩ := hmemker
  have hκ : (IsLocalRing.residue A b) • v 0 = ∑ i, (IsLocalRing.residue A (a i)) • v i.succ := by
    rw [← e1 b (v 0), hb]; exact Finset.sum_congr rfl (fun i _ => e1 (a i) (v i.succ))
  have hzero : ∑ j, (Fin.cons (IsLocalRing.residue A b) (fun i => -(IsLocalRing.residue A (a i))) :
      Fin (m + 1) → IsLocalRing.ResidueField A) j • v j = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, neg_smul]
    rw [hκ, ← Finset.sum_add_distrib]; simp
  have hall := Fintype.linearIndependent_iff.mp hlin _ hzero
  intro i
  have hd : IsLocalRing.residue A (a i) = 0 := by
    have h := hall i.succ; rw [Fin.cons_succ] at h; exact neg_eq_zero.mp h
  have hai_mem : a i ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.residue_eq_zero_iff (a i)).mp hd
  rw [← hai i]
  change IsLocalRing.residue B (algebraMap A B (a i)) = 0
  rw [IsLocalRing.residue_eq_zero_iff]
  have hcm : a i ∈ Ideal.comap (algebraMap A B) (IsLocalRing.maximalIdeal B) := by
    rw [hcomap]; exact hai_mem
  exact Ideal.mem_comap.mp hcm

/-- **Step A1 — Matsumura's regular-sequence criterion (iter-203, Lane COE).**
On a regular local Noetherian ring `(A, 𝔪)`, a finite sequence `f₁, …, f_c ∈ 𝔪`
whose images in the cotangent space `𝔪/𝔪²` are `κ(A)`-linearly independent forms
a `RingTheory.Sequence.IsRegular` sequence.

This is Matsumura, *Commutative Ring Theory*, Thm 14.2 (cf. Stacks tag `00NQ`):
linearly independent elements of `𝔪/𝔪²` in a regular local ring form a regular
sequence (indeed they extend to a regular system of parameters). The proof is
the iter-203 blueprint recipe `\subsec:stage6_iib_substrate_iter200`, Step A1:
induction on the length `c` (here `n`), peeling the head `f₁` via
`isRegular_cons_of_quotient_ring`. At each step the head is a non-zero-divisor
(`A` is a domain by `RingTheory.CohenMacaulay.isDomain_of_regularLocal`, and
`f₁ ≠ 0` since `f₁ ∉ 𝔪²`), the quotient `A ⧸ span{f₁}` is again regular local
(`RingTheory.CohenMacaulay.regularLocal_quotient_isRegularLocal_of_notMemSq`),
and the tail's cotangent classes stay `κ`-linearly independent in the quotient
(`matsumura_descent_cotangent`). The two
`RingTheory.CohenMacaulay.*` inputs were promoted to public in iter-202.

Project-local because Mathlib at commit `b80f227` ships neither this criterion
nor the regular-local⟹domain / regular-local-quotient facts it consumes.
Axiom-clean. -/
private theorem matsumura_isRegular_of_linearIndependent_cotangent
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (n : ℕ) (rs : Fin n → A) (hrs_mem : ∀ i, rs i ∈ IsLocalRing.maximalIdeal A)
    (h_lin : LinearIndependent (IsLocalRing.ResidueField A)
               (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨rs i, hrs_mem i⟩)) :
    RingTheory.Sequence.IsRegular A (List.ofFn rs) := by
  suffices H : ∀ (n : ℕ) (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [IsRegularLocalRing A] (rs : Fin n → A)
      (hrs_mem : ∀ i, rs i ∈ IsLocalRing.maximalIdeal A),
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun i => (IsLocalRing.maximalIdeal A).toCotangent ⟨rs i, hrs_mem i⟩) →
      RingTheory.Sequence.IsRegular A (List.ofFn rs) from H n A rs hrs_mem h_lin
  clear h_lin hrs_mem rs n
  intro n
  induction n with
  | zero =>
    intro A _ _ _ _ rs _ _
    rw [List.ofFn_zero]; exact RingTheory.Sequence.IsRegular.nil A A
  | succ m ih =>
    intro A _ _ _ _ rs hmem hlin
    have hxmem : rs 0 ∈ IsLocalRing.maximalIdeal A := hmem 0
    have hxne0 : (IsLocalRing.maximalIdeal A).toCotangent ⟨rs 0, hxmem⟩ ≠ 0 := hlin.ne_zero 0
    have hxnotsq : rs 0 ∉ IsLocalRing.maximalIdeal A ^ 2 := fun hsq =>
      hxne0 ((Ideal.toCotangent_eq_zero _ ⟨rs 0, hxmem⟩).mpr hsq)
    have hspan_pos : ∃ k, (IsLocalRing.maximalIdeal A).spanFinrank = k + 1 := by
      rcases Nat.eq_zero_or_pos ((IsLocalRing.maximalIdeal A).spanFinrank) with h0 | hpos
      · exfalso
        have hfg : (IsLocalRing.maximalIdeal A).FG := Ideal.fg_of_isNoetherianRing _
        have hbot : IsLocalRing.maximalIdeal A = ⊥ :=
          (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp h0
        apply hxnotsq
        have hb : rs 0 ∈ (⊥ : Ideal A) := hbot ▸ hxmem
        rw [Submodule.mem_bot] at hb; rw [hb]; exact Ideal.zero_mem _
      · exact ⟨(IsLocalRing.maximalIdeal A).spanFinrank - 1, by omega⟩
    obtain ⟨k, hk⟩ := hspan_pos
    obtain ⟨hNT, hLR, hRLR, _hdim_quot⟩ :=
      RingTheory.CohenMacaulay.regularLocal_quotient_isRegularLocal_of_notMemSq
        hk (rs 0) hxmem hxnotsq
    haveI : Nontrivial (A ⧸ Ideal.span ({rs 0} : Set A)) := hNT
    haveI : IsLocalRing (A ⧸ Ideal.span ({rs 0} : Set A)) := hLR
    haveI : IsRegularLocalRing (A ⧸ Ideal.span ({rs 0} : Set A)) := hRLR
    haveI : IsNoetherianRing (A ⧸ Ideal.span ({rs 0} : Set A)) := inferInstance
    have hg_mem : ∀ i : Fin m, (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)) (rs i.succ))
        ∈ IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A)) := by
      intro i
      have hmax : (Ideal.comap (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)))
          (IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A)))).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      have hc : Ideal.comap (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)))
          (IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A)))
          = IsLocalRing.maximalIdeal A := (IsLocalRing.isMaximal_iff A).mp hmax
      have hin : rs i.succ ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)))
          (IsLocalRing.maximalIdeal (A ⧸ Ideal.span ({rs 0} : Set A))) := by
        rw [hc]; exact hmem i.succ
      exact Ideal.mem_comap.mp hin
    have hlin' := matsumura_descent_cotangent m rs hmem hlin hg_mem
    have hih := ih (A ⧸ Ideal.span ({rs 0} : Set A))
      (fun i => Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)) (rs i.succ)) hg_mem hlin'
    haveI : IsDomain A := RingTheory.CohenMacaulay.isDomain_of_regularLocal A
    have hxne0' : rs 0 ≠ 0 := fun h => hxnotsq (by rw [h]; exact Ideal.zero_mem _)
    have h1 : IsSMulRegular A (rs 0) := IsSMulRegular.of_ne_zero hxne0'
    rw [List.ofFn_succ]
    apply isRegular_cons_of_quotient_ring h1
    have hmapeq : (List.ofFn (fun i : Fin m => rs i.succ)).map
        (Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)))
        = List.ofFn (fun i => Ideal.Quotient.mk (Ideal.span ({rs 0} : Set A)) (rs i.succ)) := by
      rw [List.map_ofFn]; rfl
    rw [hmapeq]; exact hih

/-- **Stacks `00TT`, Jacobian-criterion direction (regularity conclusion).**
For a smooth integral variety `X` over an algebraically closed field `k̄`, the
stalk of `X` at **every** point (closed or not) is a regular local ring.

Proof: Stage 2 (`exists_isStandardSmooth_at_of_smooth`) produces an affine
chart `V ∋ z` whose section ring `Γ(X, V)` is standard-smooth over
`Γ(Spec k̄, U) ≃ k̄` (base identification `gammaSpecField_ringEquiv`,
transported by `RingHom.isStandardSmooth_respectsIso`); the stalk is the
localisation of `Γ(X, V)` at the prime of `z` (`IsAffineOpen.isLocalization_stalk`),
and the Serre-free Stacks-00TT theorem at arbitrary primes
`isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField`
(`Albanese/SmoothPrimeRegularity.lean`; conormal identity + Kähler-trdeg
identification + the polynomial-ring trdeg–height inequality) applies since
`k̄` is perfect.

**History.** This statement was the Stage-6 keystone gap of the codim-1
extension pipeline: the closed-point case was closed in `StandardSmoothDimension.lean`
(iter-199/ii.B) via `isRegularLocalRing_localizationAtPrime_of_isStandardSmooth_of_isAlgClosed`
(§3.B above), while the non-closed-point case was long believed to require
Stacks `00OF` (localisation of regular local rings, Serre's homological
characterisation — still absent from Mathlib v4.31). The
`SmoothPrimeRegularity.lean` route avoids `00OF` entirely; the previous
6-stage in-body scaffolding (flat stalks, Kähler freeness/rank at the stalk,
cotangent computation at rational points) survives as §3.A/§3.B helpers used
by the closed-point corollaries and `isReduced_of_smooth_of_isAlgClosed`.

Blueprint reference: `\cref{lem:smooth_to_regular_local_ring}` in
`blueprint/src/chapters/Albanese_CodimOneExtension.tex` (also Stacks
\href{https://stacks.math.columbia.edu/tag/00TT}{tag 00TT}). -/
theorem isRegularLocalRing_stalk_of_smooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    (z : X.left) :
    IsRegularLocalRing (X.left.presheaf.stalk z) := by
  -- Stage 2 chart: a standard-smooth section ring on an affine chart `V ∋ z`.
  obtain ⟨U, hU, V, hV, hzV, e, hSS⟩ := exists_isStandardSmooth_at_of_smooth X z
  -- Base identification `Γ(Spec k̄, U) ≃+* k̄` (U is nonempty: it contains the
  -- image of z).
  let ε : kbar ≃+* Γ(Spec (.of kbar), U) :=
    (gammaSpecField_ringEquiv kbar U ⟨⟨_, e hzV⟩⟩).symm
  have hSS' : ((X.hom.appLE U V e).hom.comp ε.toRingHom).IsStandardSmooth :=
    RingHom.isStandardSmooth_respectsIso.2 _ ε hSS
  letI : Algebra kbar Γ(X.left, V) :=
    ((X.hom.appLE U V e).hom.comp ε.toRingHom).toAlgebra
  haveI : Algebra.IsStandardSmooth kbar Γ(X.left, V) := hSS'.toAlgebra
  -- The stalk as the localisation of the chart ring at the prime of `z`.
  letI : Algebra Γ(X.left, V) (X.left.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨z, hzV⟩
  haveI hLoc : IsLocalization.AtPrime (X.left.presheaf.stalk z)
      (hV.primeIdealOf ⟨z, hzV⟩).asIdeal :=
    isLocalization_atPrime_stalk_of_affineOpen hV z hzV
  letI : Algebra kbar (X.left.presheaf.stalk z) :=
    ((algebraMap Γ(X.left, V) (X.left.presheaf.stalk z)).comp
      (algebraMap kbar Γ(X.left, V))).toAlgebra
  haveI : IsScalarTower kbar Γ(X.left, V) (X.left.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
  haveI : Nontrivial Γ(X.left, V) :=
    AlgebraicGeometry.Scheme.component_nontrivial X.left V
  -- Conclude by the Serre-free Stacks-00TT theorem at arbitrary primes.
  exact isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField
    (k := kbar) (hV.primeIdealOf ⟨z, hzV⟩).asIdeal
    (hV.primeIdealOf ⟨z, hzV⟩).isPrime (X.left.presheaf.stalk z)

/-- **Helper for `localRing_dvr_of_codim_one`.** On a smooth integral variety
over an algebraically closed field, the stalk at a codimension-`1` point has a
*principal nonzero* maximal ideal. Encodes the substantive geometric content
of "regular in codimension one": smoothness ⟹ `IsRegularLocalRing` at the
stalk (Stacks `00PD`/`00TT`), and a Noetherian regular local ring with
`ringKrullDim = 1` has principal nonzero maximal ideal (Stacks `02IZ`),
via the cotangent-space `finrank = 1` characterisation.

**Iter-187 Lane M↓ refactor.** The previous body bundled both Mathlib gaps —
smooth ⟹ regular (Stacks 00TT) and codim-1 ⟹ Krull-dim-1 — into an inline
`hreg_dim` conjunction whose first conjunct was a bare `sorry`. The Krull-dim
half has been closed axiom-clean since iter-184 via
`Scheme.ringKrullDim_stalk_eq_coheight` (the iter-183 `CoheightBridge.lean`
bridge); the iter-187 refactor isolated the then-open Stacks-00TT gap as the
named helper `isRegularLocalRing_stalk_of_smooth` above, which is now fully
proved (via `Albanese/SmoothPrimeRegularity.lean`). The whole chain is
therefore **axiom-clean** — no residual gap. -/
private theorem smooth_codim_one_maximalIdeal_isPrincipal_and_ne_bot
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    (z : X.left) (_hz : Order.coheight z = 1) :
    Submodule.IsPrincipal (IsLocalRing.maximalIdeal (X.left.presheaf.stalk z)) ∧
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk z) ≠ ⊥ := by
  -- Set up Noetherian structure on the stalk (needed for the cotangent-space API):
  -- `LocallyOfFiniteType X.hom` lifts the automatic `IsLocallyNoetherian (Spec k̄)`
  -- through to `IsLocallyNoetherian X.left`, from which the stalk picks up
  -- `IsNoetherianRing` (Mathlib instance).
  haveI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  -- Regularity half: the named helper above (`isRegularLocalRing_stalk_of_smooth`,
  -- Stacks 00TT at every point — sorry-free via SmoothPrimeRegularity.lean).
  have hreg : IsRegularLocalRing (X.left.presheaf.stalk z) :=
    isRegularLocalRing_stalk_of_smooth X z
  -- Krull-dim half: closes via the iter-183 axiom-clean CoheightBridge
  -- equality + the codim-1 witness `_hz`.
  have hdim : ringKrullDim (X.left.presheaf.stalk z) = 1 := by
    rw [Scheme.ringKrullDim_stalk_eq_coheight]
    exact_mod_cast _hz
  -- From regularity + dim = 1, the cotangent space has `finrank = 1`
  -- (Mathlib `IsRegularLocalRing.iff_finrank_cotangentSpace`).
  have hfin :
      Module.finrank
        (IsLocalRing.ResidueField (X.left.presheaf.stalk z))
        (IsLocalRing.CotangentSpace (X.left.presheaf.stalk z)) = 1 := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hreg
    rw [hdim] at h
    exact_mod_cast h
  -- Principal maximal ideal: `finrank ≤ 1 ↔ IsPrincipal maximalIdeal`
  -- (Mathlib `IsLocalRing.finrank_cotangentSpace_le_one_iff`).
  have hprin : Submodule.IsPrincipal
      (IsLocalRing.maximalIdeal (X.left.presheaf.stalk z)) :=
    IsLocalRing.finrank_cotangentSpace_le_one_iff.mp hfin.le
  -- `maximalIdeal ≠ ⊥`: equivalent to "not a field" by Mathlib
  -- `IsLocalRing.isField_iff_maximalIdeal_eq`, and a field has Krull dim 0,
  -- contradicting `hdim : ringKrullDim = 1` via `ringKrullDim_eq_zero_of_isField`.
  have hne : IsLocalRing.maximalIdeal (X.left.presheaf.stalk z) ≠ ⊥ := by
    intro hbot
    have hF : IsField (X.left.presheaf.stalk z) :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
    have h0 : ringKrullDim (X.left.presheaf.stalk z) = 0 :=
      ringKrullDim_eq_zero_of_isField hF
    -- Contradiction: `1 = 0` in `WithBot ℕ∞`.
    rw [hdim] at h0
    exact_mod_cast h0
  exact ⟨hprin, hne⟩

/-- **Smooth + codim-1 ⇒ DVR.** For a nonsingular integral variety `X` over
an algebraically closed field `k̄` and a point `η : X.left` with
`Order.coheight η = 1`, the stalk `X.left.presheaf.stalk η` is a discrete
valuation ring (with fraction field the function field `K(X)`).

The proof reduces to "regular local ring of Krull dimension `1` is a DVR"
(Mathlib `IsDiscreteValuationRing.isDiscreteValuationRing_iff` or analogous)
plus the smooth-variety fact that every local ring at a codim-1 point is
regular of dimension `1`. The geometric step is packaged in the private helper
`smooth_codim_one_maximalIdeal_isPrincipal_and_ne_bot`; the rest assembles the
DVR instance via `IsDiscreteValuationRing.TFAE`.

Blueprint reference: `lem:smooth_codim_one_dvr` (Hartshorne II.6 p. 130;
Stacks `00PD` for the regular-of-dim-1 ⇔ DVR equivalence). -/
theorem localRing_dvr_of_codim_one
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    (z : X.left) (_hz : Order.coheight z = 1) :
    IsDiscreteValuationRing (X.left.presheaf.stalk z) := by
  -- Set up Noetherian structure on the stalk:
  -- `LocallyOfFiniteType X.hom` lifts the (automatic) `IsLocallyNoetherian (Spec k̄)`
  -- to `IsLocallyNoetherian X.left`, from which the stalk inherits
  -- `IsNoetherianRing` (Mathlib instance). The stalk of an integral scheme is
  -- a domain (Mathlib instance), and stalks of schemes are always local (Mathlib
  -- instance); these are picked up automatically by typeclass search.
  haveI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  -- Extract the principal+nonzero-maximal-ideal helper (the Mathlib-gap content).
  obtain ⟨hprin, hne⟩ :=
    smooth_codim_one_maximalIdeal_isPrincipal_and_ne_bot X z _hz
  -- The stalk is a local Noetherian domain with principal maximal ideal:
  -- promote `IsPrincipal (maximalIdeal)` to a `IsPrincipalIdealRing` instance
  -- and conclude DVR via `IsDiscreteValuationRing.mk`.
  -- The TFAE entry "principal maximal ideal ⇔ DVR" handles the conversion
  -- once we know `¬ IsField` (which follows from `maximalIdeal ≠ ⊥`).
  have hfield : ¬ IsField (X.left.presheaf.stalk z) := by
    intro hF
    exact hne ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)
  have tfae := IsDiscreteValuationRing.TFAE (X.left.presheaf.stalk z) hfield
  -- TFAE entry index 4 is `Submodule.IsPrincipal (IsLocalRing.maximalIdeal R)`.
  exact ((tfae.out 0 4).mpr hprin)

namespace RationalMap

/-! ## §4. Milne Theorem 3.1 — codim-≥2 indeterminacy, and extension from ∅

A rational map from a nonsingular variety to a complete variety has
indeterminacy locus of codimension `≥ 2`
(`indeterminacy_codimGe2_of_smooth_of_complete`, = Milne 3.1; equivalently
`CodimOneFree f`, `codimOneFree_of_smooth_of_complete`). Separately, a
rational map (from any reduced scheme to any separated scheme) with *empty*
indeterminacy locus is uniquely represented by a regular morphism
(`existsUnique_hom_of_indeterminacyLocus_eq_empty`). Milne 3.2 combines the
two through Lemma 3.3, which forces `Z(f) = ∅` for group-variety targets.

NOTE: the former `extend_of_codimOneFree_of_smooth` ("CodimOneFree alone ⇒
extension, complete target") was removed in run-0006 T6 session 0015 — its
statement was false (counterexample `ℙ² ⇢ ℙ¹`; see the docstring of
`existsUnique_hom_of_indeterminacyLocus_eq_empty`), so its `sorry` was
unclosable.

Blueprint pins: `thm:indeterminacy_codimGe2`, `cor:codim_one_free`,
`thm:codim_one_extension` (Milne §I.3 Theorem 3.1 p. 16). -/

/-- Glue helper: the function-field morphism of a partial map factors through
the `Spec`-of-stalk morphism at any point of its domain. Both sides are
`(fromSpecStalkOfMem) ≫ g.hom` for the domain open; the factorization is the
open-immersion cancellation of Mathlib's
`SpecMap_stalkSpecializes_fromSpecStalk` along `g.domain.ι`. -/
private lemma fromFunctionField_factor
    {X Y : Scheme.{u}} [IrreducibleSpace X] (g : X.PartialMap Y) {x : X}
    (hx : x ∈ g.domain) :
    g.fromFunctionField =
      Spec.map (X.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes trivial)) ≫
        g.fromSpecStalkOfMem hx := by
  dsimp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem]
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono g.domain.ι, Category.assoc, Opens.fromSpecStalkOfMem_ι,
    Opens.fromSpecStalkOfMem_ι, SpecMap_stalkSpecializes_fromSpecStalk]

set_option backward.isDefEq.respectTransparency false in
/-- **Milne Theorem 3.1, codim-≥2 conclusion (unbundled).** For a rational map
`f : X ⇢ Y` of varieties over `k̄` (the `hf` hypothesis is the "over `k̄`"
condition: `f` composed with `Y`'s structure morphism is `X`'s structure
morphism, as rational maps) with `X` nonsingular and `Y` complete, every
point of the indeterminacy locus has coheight (codimension) at least `2`.

This *is* Milne Theorem 3.1 (the theorem asserts exactly the codim-≥2
property of the indeterminacy locus — not an everywhere-extension, which
for general complete targets is false; see
`existsUnique_hom_of_indeterminacyLocus_eq_empty` below).
`av_indeterminacyLocus_eq_empty` in `Thm32RationalMapExtension.lean`
combines this conclusion with Milne Lemma 3.3's pure-codim-1 disjunct to
force the locus empty for abelian-variety targets.

**Proved (run-0006 T6, second session).** Proof: let `z ∈ Z(f)` with
`coheight z ≤ 1`. If `coheight z = 0` then `z` is the generic point (maximal
in the specialisation preorder of the irreducible sober space `X`), which
lies in the dense open `f.domain` — contradiction. If `coheight z = 1`, the
stalk `O_{X,z}` is a DVR (`localRing_dvr_of_codim_one`, sorry-free via
`SmoothPrimeRegularity.lean`) with fraction field `K(X)`
(Mathlib `IsFractionRing (stalk z) functionField` for integral schemes), so
`Spec K(X) ⟶ Y` (`f.fromFunctionField`) together with
`Spec O_{X,z} ⟶ Spec k̄` forms a `ValuativeCommSq` over `Y.hom` — the
square commutes by `hf` pushed to the function field. Properness of `Y.hom`
supplies a lift `L : Spec O_{X,z} ⟶ Y` (Mathlib
`IsProper.eq_valuativeCriterion`), which spreads out to a partial map
defined at `z` (Mathlib `PartialMap.ofFromSpecStalk`, using germ-injectivity
of integral schemes); its rational class is `f` by comparison at the
function field (`RationalMap.eq_of_fromFunctionField_eq` + the
`fromFunctionField_factor` glue above), so `z ∈ f.domain` — contradiction.

The over-`k̄` hypothesis `hf` is necessary: the valuative square's base
compatibility identifies the `k̄`-structure on `K(X)` induced by `f` with
the one induced by `X`, which can fail for abstract-scheme rational maps.
This matches Milne's setting (rational maps of varieties *over* `k`).

**The `[IsAlgClosed kbar]` binder, by contrast, is NOT necessary** (`ajc-p4`,
2026-07-30, measured rather than argued).  Nothing in this proof consumes it: the
coheight-`0` branch is topology of an irreducible sober space and the
coheight-`1` branch is the valuative criterion at the DVR stalk.  It enters only
through `localRing_dvr_of_codim_one` → `isRegularLocalRing_stalk_of_smooth`,
whose delegate asks for a **perfect** field.  The same proof body, with
`[PerfectField k]`, is
`Scheme.RationalMap.indeterminacy_codimGe2_of_smooth_of_complete_perfectField`
in `Albanese/CodimOnePerfectField.lean`, so this theorem also holds over `ℚ`,
every number field and every `𝔽_q`.  Do not price a transport of this statement
off the binder written here.  (What does not widen is Milne **3.3** — see that
file's §2.) -/
theorem indeterminacy_codimGe2_of_smooth_of_complete
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {Y : Over (Spec (.of kbar))}
    [IsProper Y.hom] [GeometricallyIrreducible Y.hom]
    [IsIntegral Y.left] [IsReduced Y.left]
    (f : X.left.RationalMap Y.left)
    (hf : f.compHom Y.hom = X.hom.toRationalMap) :
    ∀ z ∈ indeterminacyLocus f, 2 ≤ Order.coheight z := by
  intro z hz
  have hzdom : z ∉ f.domain := hz
  by_contra hlt
  have hle : Order.coheight z ≤ 1 := by
    have h2 : Order.coheight z < 2 := not_le.mp hlt
    rwa [ENat.lt_two_iff] at h2
  -- The generic point of X.
  have hspec : genericPoint X.left ⤳ z :=
    (genericPoint_spec X.left).specializes trivial
  -- Over-ness at the function-field level.
  have hff : f.fromFunctionField ≫ Y.hom
      = X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom := by
    obtain ⟨g0, rfl⟩ := f.exists_rep
    have h1' : (g0.compHom Y.hom).toRationalMap
        = X.hom.toPartialMap.toRationalMap := by
      rw [RationalMap.compHom_toRationalMap]; exact hf
    have h2 := congrArg RationalMap.fromFunctionField h1'
    rw [RationalMap.fromFunctionField_toRationalMap,
      RationalMap.fromFunctionField_toRationalMap] at h2
    simpa using h2
  rcases hle.lt_or_eq with h0 | h1
  · -- coheight 0: `z` is the generic point, which lies in the dense open domain.
    rw [Order.lt_one_iff] at h0
    have hmax : IsMax z := Order.coheight_eq_zero.mp h0
    have hzeq : z = genericPoint X.left :=
      ((show z ⤳ genericPoint X.left from hmax hspec).antisymm hspec).eq
    obtain ⟨w, hw⟩ := f.dense_domain.nonempty
    exact hzdom (hzeq ▸ (genericPoint_specializes w).mem_open f.domain.2 hw)
  · -- coheight 1: valuative criterion at the DVR stalk.
    haveI hDVR : IsDiscreteValuationRing (X.left.presheaf.stalk z) :=
      localRing_dvr_of_codim_one z h1
    haveI : ValuationRing (X.left.presheaf.stalk z) := inferInstance
    -- The valuative criterion for the proper structure morphism of Y.
    have hVC : ValuativeCriterion Y.hom := by
      have hP : IsProper Y.hom := inferInstance
      rw [IsProper.eq_valuativeCriterion] at hP
      exact hP.1.1.1
    -- The valuative commutative square. Note `algebraMap (stalk z) K(X)` is
    -- definitionally the stalk-specialization map (`stalkFunctionFieldAlgebra`).
    have hcommSq : CommSq f.fromFunctionField
        (Spec.map (CommRingCat.ofHom
          (algebraMap (X.left.presheaf.stalk z) X.left.functionField)))
        Y.hom (X.left.fromSpecStalk z ≫ X.hom) := ⟨by
      rw [hff, ← Category.assoc]
      congr 1
      exact (SpecMap_stalkSpecializes_fromSpecStalk hspec).symm⟩
    -- Materialise the instance fields outside the structure literal (inside it
    -- the stalk term is unfolded past `Scheme.presheaf`, so the keyed
    -- instances no longer fire). Plain `have`/`let` (NOT `haveI`/`letI`): an
    -- opaque local `Field` instance would poison the `Semiring`-path defeq.
    have hdom : IsDomain (X.left.presheaf.stalk z) := inferInstance
    have hvr : ValuationRing (X.left.presheaf.stalk z) := inferInstance
    let hfld : Field X.left.functionField := inferInstance
    have hfr : IsFractionRing (X.left.presheaf.stalk z) X.left.functionField :=
      inferInstance
    obtain ⟨hlift⟩ := hVC
      { R := X.left.presheaf.stalk z
        commRing := inferInstance
        domain := hdom
        valuationRing := hvr
        K := X.left.functionField
        field := hfld
        algebra := stalkFunctionFieldAlgebra X.left z
        isFractionRing := hfr
        i₁ := f.fromFunctionField
        i₂ := X.left.fromSpecStalk z ≫ X.hom
        commSq := hcommSq }
    obtain ⟨L₀, hfacl₀, hfacr₀⟩ := hlift.default
    -- Retype the lift through the (definitional) `CommRingCat.of ↥R = R` and
    -- `algebraMap = stalkSpecializes` identifications.
    let L : Spec (X.left.presheaf.stalk z) ⟶ Y.left := L₀
    have hfacl : Spec.map (X.left.presheaf.stalkSpecializes hspec) ≫ L
        = f.fromFunctionField := hfacl₀
    have hfacr : L ≫ Y.hom = X.left.fromSpecStalk z ≫ X.hom := hfacr₀
    -- Spread the lift out to a partial map defined at z.
    let g : X.left.PartialMap Y.left :=
      PartialMap.ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hzg : z ∈ g.domain :=
      PartialMap.mem_domain_ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hgL : g.fromSpecStalkOfMem hzg = L :=
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hgen : g.toRationalMap = f := by
      refine RationalMap.eq_of_fromFunctionField_eq _ _ ?_
      rw [RationalMap.fromFunctionField_toRationalMap,
        fromFunctionField_factor g hzg, hgL]
      exact hfacl
    exact hzdom (RationalMap.mem_domain.mpr ⟨g, hzg, hgen⟩)

/-- **Milne Theorem 3.1, `CodimOneFree` phrasing.** A rational map of
`k̄`-varieties from a nonsingular variety to a complete variety is
codim-1-indeterminacy-free: every codim-1 point of `X` lies in the domain
of definition. Immediate from the codim-≥2 conclusion
`indeterminacy_codimGe2_of_smooth_of_complete`.

Blueprint reference: `cor:codim_one_free` (Milne, *Abelian Varieties*,
Theorem 3.1, §I.3, p. 16, the "equivalently" clause). -/
theorem codimOneFree_of_smooth_of_complete
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {Y : Over (Spec (.of kbar))}
    [IsProper Y.hom] [GeometricallyIrreducible Y.hom]
    [IsIntegral Y.left] [IsReduced Y.left]
    (f : X.left.RationalMap Y.left)
    (hf : f.compHom Y.hom = X.hom.toRationalMap) :
    CodimOneFree f := by
  intro x hx
  by_contra hnotin
  have h2 := indeterminacy_codimGe2_of_smooth_of_complete f hf x hnotin
  rw [hx] at h2
  norm_num at h2

/-- The maximal representative `RationalMap.toPartialMap` of a rational map
is defined exactly on `f.domain` (definitional; recorded as a `simp` lemma so
rewrites can cross the `toPartialMap` boundary). -/
@[simp]
theorem toPartialMap_domain {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (f : X.RationalMap Y) : f.toPartialMap.domain = f.domain := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms from a reduced scheme to a separated scheme are determined by
their rational-map class: if `g₁.toRationalMap = g₂.toRationalMap` then
`g₁ = g₂`. This is the reduced-and-separated agreement principle
(`AlgebraicGeometry.ext_of_isDominant`) routed through the `PartialMap`
equivalence: the two morphisms agree on a common dense open. -/
theorem hom_ext_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced X]
    [Y.IsSeparated] {g₁ g₂ : X ⟶ Y}
    (e : g₁.toRationalMap = g₂.toRationalMap) : g₁ = g₂ := by
  obtain ⟨W, hW, hle₁, hle₂, he⟩ := PartialMap.toRationalMap_eq_iff.mp e
  haveI : IsDominant W.ι := Opens.isDominant_ι hW
  exact ext_of_isDominant W.ι (by simpa [Scheme.Hom.toPartialMap] using he)

set_option backward.isDefEq.respectTransparency false in
/-- **Extension of a rational map with empty indeterminacy locus.** If the
indeterminacy locus of a rational map `f : X ⇢ Y` from a reduced scheme to a
separated scheme is empty, then `f` is (uniquely) represented by a regular
morphism `g : X ⟶ Y`.

This is the honest "extension" content of the Milne §I.3 chain: once
`Z(f) = ∅` — which for an abelian-variety target follows from combining
Milne Lemma 3.3 (`indeterminacy_pure_codim_one_into_grpScheme`) with the
codim-≥2 conclusion of Milne Theorem 3.1
(`indeterminacy_codimGe2_of_smooth_of_complete`) — the maximal representative
`f.toPartialMap` is defined on all of `X`, and its composite with the
isomorphism `X ≅ (⊤ : X.Opens)` is the required morphism. Uniqueness is the
reduced-and-separated agreement principle (`hom_ext_of_toRationalMap_eq`).

**Statement-correction note (run-0006 T6, session 0015).** This lemma
*replaces* the former `extend_of_codimOneFree_of_smooth`, whose statement —
"`CodimOneFree f` alone implies a regular extension, for an arbitrary
complete target" — was **false as stated**: the projection `ℙ² ⇢ ℙ¹` away
from a point satisfies every hypothesis (smooth integral source, complete
smooth integral target, indeterminacy a single codim-2 closed point, hence
`CodimOneFree`), yet admits no regular extension (any extension `g` would
force `⊤ = g.toPartialMap.domain ≤ f.domain` via
`PartialMap.le_domain_toRationalMap`, but `f.domain = ℙ² ∖ {pt}`). Milne 3.1
asserts only the codim-≥2 conclusion; the everywhere-extension in Milne 3.2
needs the *group-variety* input of Lemma 3.3 to force `Z(f) = ∅` first.

Blueprint reference: `thm:codim_one_extension`. -/
theorem existsUnique_hom_of_indeterminacyLocus_eq_empty
    {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (f : X.RationalMap Y) (h : indeterminacyLocus f = ∅) :
    ∃! (g : X ⟶ Y), g.toRationalMap = f := by
  -- The domain of definition is all of `X`.
  have hdom : f.toPartialMap.domain = ⊤ := by
    rw [toPartialMap_domain, ← TopologicalSpace.Opens.coe_inj,
      TopologicalSpace.Opens.coe_top, ← Set.compl_empty_iff]
    exact h
  -- The candidate morphism: transport the maximal representative along
  -- `X ≅ ⊤ ≅ f.toPartialMap.domain`.
  have hwit : (X.topIso.inv ≫ X.homOfLE hdom.ge
      ≫ f.toPartialMap.hom).toRationalMap = f := by
    conv_rhs => rw [← f.toRationalMap_toPartialMap]
    refine PartialMap.toRationalMap_eq_iff.mpr ?_
    refine ⟨⊤, by rw [TopologicalSpace.Opens.coe_top]; exact dense_univ,
      le_top, hdom.ge, ?_⟩
    simp only [PartialMap.restrict_hom, Scheme.Hom.toPartialMap,
      Scheme.topIso_hom, Scheme.ι_toIso_inv_assoc,
      Scheme.homOfLE_homOfLE_assoc]
  exact ⟨_, hwit, fun g hg => hom_ext_of_toRationalMap_eq (hg.trans hwit.symm)⟩

/-! ## §5. Milne Lemma 3.3 — pure-codim-1 indeterminacy into a group variety

A rational map from a nonsingular variety to a group variety has its
indeterminacy locus either empty or of pure codimension `1`. Combined with
`thm:indeterminacy_codimGe2`'s codim-≥2 conclusion, this forces the locus
to be empty when the target is an abelian variety, at which point
`existsUnique_hom_of_indeterminacyLocus_eq_empty` extends.

**The theorem now lives in `Albanese/Milne33.lean`** as
`indeterminacy_pure_codim_one_into_grpScheme`, where it is **proved** (no
`sorry`). It was stated here without proof until run 0069; the proof needs the
difference-map / pole-purity / Hauptidealsatz-transport layers
(`Albanese/Milne33{Rows,Diagonal,RowSection,Pullback,CMEquidim,KernelGen,
TransportLocal,Transport}.lean`), which import *this* file, so the theorem
cannot be stated here without a cycle. Consumers import
`Albanese/Milne33.lean`; the only one is `av_indeterminacyLocus_eq_empty` in
`Albanese/Thm32RationalMapExtension.lean`.

Blueprint pin: `lem:milne_codim1_indeterminacy` (Milne §I.3 Lemma 3.3 p. 17). -/
/-! ## §6. Definedness at a prime-divisor generic point

A truthful, lightweight reformulation of definedness at a prime-divisor
generic point: `f` is defined at `W.point` iff `f` admits a `PartialMap`
representative whose domain contains `W.point`. This is a definitional
re-shuffle of `Mathlib.AlgebraicGeometry.Scheme.RationalMap.mem_domain`
swapping the order of the two conjuncts under the existential for downstream
ergonomics (so the `toRationalMap = f` conjunct lands first, the way later
witnesses are constructed in this project).

### Status note (iter-179 Lane D, Path D2)

The blueprint pin `thm:weil_divisor_obstruction` (Hartshorne II.6
pp. 130–131) calls for the genuinely substantive statement

> `f` is defined at `W.point` iff every regular function on every affine
> open `V ⊆ Y` around `f(W.point)` pulls back to an element of
> `O_{X,W.point}` ⊂ `K(X)` of `ord_W`-value `≥ 0`,

which requires the pullback machinery
`Scheme.RationalMap → K(Y) → K(X)` and the project's existing
`Scheme.RationalMap.order : X.functionField → ℤ` valuation from
`RiemannRoch/WeilDivisor.lean`. The Lean-level construction of the
`RationalMap`-to-function-field ring map is **not** shipped by Mathlib
at commit `b80f227`, and building it inside this file would constitute
a substantive new sub-build (cf. `analogies/relative-spec-encoding.md`
on the pullback of a sheaf-of-algebras along a morphism).

iter-178's `extend_iff_order_nonneg` claimed the substantive statement
in its docstring but only proved this reshuffle; the lemma's name and
documentation are corrected here (auditor 178B's Path D2 honest fallback)
to match the proven content. The `[Ring.KrullDimLE 1]` and
`[IsLocallyNoetherian X.left]` typeclass binders that the substantive
statement would have required are dropped along with the renaming, since
the reshuffle does not use them. The substantive statement is deferred to
a future lemma (working title: `extend_iff_pullback_order_nonneg`) once
the pullback machinery lands.

Blueprint reference (in its current weakened form): a definitional unfold
of `Mathlib.AlgebraicGeometry.Scheme.RationalMap.mem_domain`. -/

end RationalMap

end Scheme

end AlgebraicGeometry
