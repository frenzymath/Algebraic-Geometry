/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Albanese.DifferenceMap
import AlgebraicJacobian.Albanese.PolePurity
import AlgebraicJacobian.Albanese.CoheightBridge

/-!
# Self-contained substeps of Milne Lemma 3.3

This leaf assembles two of the still-open point-set/ring-theoretic substeps of
Milne's *Abelian Varieties* §I.3 Lemma 3.3
(`AlgebraicGeometry.Scheme.RationalMap.indeterminacy_pure_codim_one_into_grpScheme`,
`Albanese/CodimOneExtension.lean`) as standalone, fully-proved lemmas.

## Substep 2, topological existence half (`[2-topo-a]`)

Milne: *"if `Φ` is defined at `(x, x)`, then it is defined on an open
neighbourhood of `(x, x)`; ... there is an open `U` such that `Φ` is defined on
`{x} × U`. After possibly replacing `U` by a smaller open subset, `φ` will be
defined on `U`. For `u ∈ U`, the formula `φ(x) = Φ(x, u)·φ(u)` defines `φ` at
`x`."*

The topological content is: on the smooth self-product `X ×_{k̄} X`, the fibre
`pr₁⁻¹{x}` of the (geometrically irreducible, open) first projection is
irreducible; hence any two open subsets meeting the fibre meet it *together*.
Applied to `V = Dom(Φ)` (which meets the fibre at the diagonal point over `x`)
and `pr₂⁻¹(Dom f)` (which meets the fibre by surjectivity of `pr₂` on the
fibre, a point over `(x, u)` for any `u ∈ Dom f`), this produces a single point
`p` of the fibre with `pr₁ p = x`, `p ∈ Dom(Φ)` and `pr₂ p ∈ Dom(f)` — the
witness `u = pr₂ p` of Milne's argument.

Main result: `AlgebraicGeometry.exists_snd_mem_of_fst_eq_of_mem`
(and its difference-map corollary
`AlgebraicGeometry.Scheme.RationalMap.exists_mem_domain_precomp_fst_of_differenceRationalMap`).

## Substep 4b, Krull-Hauptidealsatz transport (`[4b]`)

Milne uses that the pole divisor of `f = Φ*(g)` on `X × X` meets the diagonal
`Δ ≅ X` in *pure codimension one* — Krull's Hauptidealsatz applied to a local
equation of `div(f)_∞` restricted to `Δ`. The ring-theoretic heart is Krull's
principal-ideal theorem: in a Noetherian domain, a nonzero non-unit lies in a
height-one prime below any prime containing it.

Main results: `Ideal.exists_height_one_prime_mem_le` (ring core) and
`AlgebraicGeometry.Scheme.exists_specializes_coheight_eq_one_of_mem_maximalIdeal`
(scheme wrapper: a regular function vanishing at a point of a smooth variety
still vanishes at a coheight-one generisation).

Blueprint reference: `lem:milne_codim1_indeterminacy` (Milne, *Abelian
Varieties*, §I.3 p. 17).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-! ## §1. Substep 2, topological existence half `[2-topo-a]` -/

/-- **Milne Lemma 3.3, Substep 2 topological half (`[2-topo-a]`), abstract form.**

On the smooth self-product `X ×_{k̄} X` of a geometrically irreducible variety,
let `V` be any open set meeting the fibre `pr₁⁻¹{x}` (via a point `p₀` with
`pr₁ p₀ = x`, `p₀ ∈ V`) and let `D` be any *dense* open of `X`. Then there is a
point `p` of the fibre with `pr₁ p = x`, `p ∈ V`, and `pr₂ p ∈ D`.

This is the point-set core of Milne's slice argument: with `V = Dom(Φ)` (met at
the diagonal point `(x, x) ∈ Dom(Φ)`) and `D = Dom(f)`, it produces Milne's
`u := pr₂ p ∈ Dom(f)` with `(x, u) ∈ Dom(Φ)`. The proof combines:
* irreducibility of the fibre `pr₁⁻¹{x}` (geometric irreducibility of `X.hom`,
  `Scheme.Hom.isIrreducible_preimage`, since `pr₁ = pullback.fst` is
  geometrically irreducible and open);
* surjectivity of `pr₂` onto `X` *along the fibre*, via a scheme-theoretic point
  over `(x, u)` for any chosen `u ∈ D` (`Scheme.Pullback.exists_preimage_pullback`,
  using that the base `Spec k̄` is a single point). -/
theorem exists_snd_mem_of_fst_eq_of_mem
    {kbar : Type u} [Field kbar]
    (X : Over (Spec (.of kbar))) [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (V : (pullback X.hom X.hom).Opens) (D : X.left.Opens)
    (hD : Dense (D : Set X.left))
    (x : X.left) (p₀ : ↥(pullback X.hom X.hom))
    (hfst : (pullback.fst X.hom X.hom).base p₀ = x) (hp₀V : p₀ ∈ V) :
    ∃ p : ↥(pullback X.hom X.hom),
      (pullback.fst X.hom X.hom).base p = x ∧ p ∈ V ∧
      (pullback.snd X.hom X.hom).base p ∈ D := by
  -- The fibre `pr₁⁻¹{x}` is irreducible.
  have hopen : IsOpenMap (pullback.fst X.hom X.hom).base := isOpenMap_pullback_fst_self X
  have hirr : IsIrreducible ((pullback.fst X.hom X.hom).base ⁻¹' {x}) :=
    (pullback.fst X.hom X.hom).isIrreducible_preimage hopen isIrreducible_singleton
  -- `V` meets the fibre (at `p₀`).
  have hAne : (((pullback.fst X.hom X.hom).base ⁻¹' {x}) ∩ (V : Set _)).Nonempty :=
    ⟨p₀, hfst, hp₀V⟩
  -- `pr₂⁻¹(D)` meets the fibre: pick `u ∈ D` and a point over `(x, u)`.
  haveI : Nonempty X.left := ⟨x⟩
  obtain ⟨u, huD⟩ := hD.nonempty
  obtain ⟨q, hq1, hq2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := X.hom) x u
      (Subsingleton.elim _ _)
  have hBne :
      (((pullback.fst X.hom X.hom).base ⁻¹' {x}) ∩
        ((pullback.snd X.hom X.hom).base ⁻¹' (D : Set _))).Nonempty :=
    ⟨q, hq1, by rw [Set.mem_preimage, hq2]; exact huD⟩
  -- Preirreducibility: the two opens meet the fibre simultaneously.
  obtain ⟨p, hpfib, hpV, hpD⟩ :=
    hirr.2 (V : Set _) ((pullback.snd X.hom X.hom).base ⁻¹' (D : Set _))
      V.isOpen (D.isOpen.preimage (pullback.snd X.hom X.hom).continuous) hAne hBne
  exact ⟨p, hpfib, hpV, hpD⟩

/-- **Milne Lemma 3.3, Substep 2 topological half (`[2-topo-a]`), difference-map
form.** If Milne's difference map `Φ = differenceRationalMap f hover` is defined
at a point `p₀` of `X ×_{k̄} X` lying over `x` (i.e. `pr₁ p₀ = x` — think
`p₀ = (x, x)`), then there is a point `p` over `x` at which the *precomposition*
`f ∘ pr₁` is defined.

This packages the slice step of Milne's converse: choosing `u := pr₂ p ∈ Dom(f)`
with `(x, u) ∈ Dom(Φ)` (via `exists_snd_mem_of_fst_eq_of_mem`), the reconstruction
`f(x) = Φ(x, u)·f(u)` (`le_domain_precomp_fst_of_difference`) makes `f ∘ pr₁`
defined at that point. The remaining step to conclude `x ∈ Dom(f)` is the
smooth-descent reflection `Dom(f ∘ pr₁) ≤ pr₁⁻¹(Dom f)` (`[2-topo-b]`), which is
*not* proved here. -/
theorem Scheme.RationalMap.exists_mem_domain_precomp_fst_of_differenceRationalMap
    {kbar : Type u} [Field kbar]
    {X G : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [GrpObj G] [LocallyOfFiniteType G.hom]
    [IsIntegral (pullback X.hom X.hom)] [IsReduced X.left] [G.left.IsSeparated]
    (f : X.left.RationalMap G.left)
    (hover : f.compHom G.hom = X.hom.toRationalMap)
    (x : X.left) (p₀ : ↥(pullback X.hom X.hom))
    (hfst : (pullback.fst X.hom X.hom).base p₀ = x)
    (hp₀ : p₀ ∈ (Scheme.RationalMap.differenceRationalMap f hover).domain) :
    ∃ p : ↥(pullback X.hom X.hom),
      (pullback.fst X.hom X.hom).base p = x ∧
      p ∈ (f.precomp (pullback.fst X.hom X.hom) (isOpenMap_pullback_fst_self X)).domain := by
  obtain ⟨p, hpfst, hpV, hpD⟩ :=
    exists_snd_mem_of_fst_eq_of_mem X
      (Scheme.RationalMap.differenceRationalMap f hover).domain f.domain f.dense_domain
      x p₀ hfst hp₀
  refine ⟨p, hpfst, ?_⟩
  exact Scheme.RationalMap.le_domain_precomp_fst_of_difference f hover ⟨hpV, hpD⟩

end AlgebraicGeometry

/-! ## §2. Substep 4b, Krull-Hauptidealsatz transport `[4b]` (ring core) -/

/-- **Krull's Hauptidealsatz transport (`[4b]` ring core).** In a Noetherian
domain `R`, a nonzero element `t` contained in a prime `p` lies in a prime `q`
of *height exactly one* below `p`.

This is the ring-theoretic heart of Milne Lemma 3.3 Substep 4b: a local equation
`t = b|_Δ` of the pole divisor `div(f)_∞` restricted to the diagonal `Δ ≅ X` is a
nonzero (`Δ ⊄ div(f)_∞`) non-unit (`δ(x₀) ∈ div(f)_∞`) of the local ring at
`x₀`; Krull's principal-ideal theorem forces its vanishing locus to be pure
codimension one, producing the codim-1 point `z` of `X` inside `Z(f)`.

The bound `q.height ≤ 1` is Krull's Hauptidealsatz
(`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`); the reverse
`1 ≤ q.height` holds since `t ∈ q`, `t ≠ 0`, so `q ≠ ⊥` (in a domain, `⊥` is the
unique height-zero prime). -/
theorem Ideal.exists_height_one_prime_mem_le
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {t : R} (ht0 : t ≠ 0) {p : Ideal R} [p.IsPrime] (htp : t ∈ p) :
    ∃ q : Ideal R, q.IsPrime ∧ q.height = 1 ∧ q ≤ p ∧ t ∈ q := by
  -- `span{t} ≤ p`; pick a minimal prime `q` of `span{t}` below `p`.
  have hspan_le : Ideal.span ({t} : Set R) ≤ p := by
    rw [Ideal.span_singleton_le_iff_mem]; exact htp
  obtain ⟨q, hqmin, hqle⟩ := Ideal.exists_minimalPrimes_le hspan_le
  have hqprime : q.IsPrime := hqmin.1.1
  have htq : t ∈ q := hqmin.1.2 (Ideal.mem_span_singleton_self t)
  have hq_ne_bot : q ≠ ⊥ := fun h => ht0 (by simpa [h, Ideal.mem_bot] using htq)
  refine ⟨q, hqprime, le_antisymm ?_ ?_, hqle, htq⟩
  · -- Krull's Hauptidealsatz: a minimal prime over a principal ideal has height ≤ 1.
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hqmin
  · -- `1 ≤ height q` since `q ≠ ⊥` in a domain.
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff]
    intro hmin
    exact hq_ne_bot (le_bot_iff.mp (hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le))


/-! ## §3. Substep 4b, Krull-Hauptidealsatz transport `[4b]` (scheme wrapper) -/

namespace AlgebraicGeometry

/-- On an irreducible scheme, a function-field element regular at a point `P` is
regular at every generisation `z ⤳ P`: the germ pullback factors through the
specialisation map `𝒪_{X,P} ⟶ 𝒪_{X,z}`. -/
lemma range_algebraMap_stalk_le_of_specializes
    {X : Scheme.{u}} [IrreducibleSpace X] {z P : X} (h : z ⤳ P) :
    (algebraMap (X.presheaf.stalk P) X.functionField).range ≤
      (algebraMap (X.presheaf.stalk z) X.functionField).range := by
  rintro t ⟨s, rfl⟩
  refine ⟨(X.presheaf.stalkSpecializes h).hom s, ?_⟩
  simp only [RingHom.algebraMap_toAlgebra]
  rw [← CommRingCat.comp_apply, X.presheaf.stalkSpecializes_comp]

/-- **Milne Lemma 3.3, Substep 4b (scheme wrapper).** On a locally Noetherian
integral scheme with regular stalks (e.g. `X` smooth over a field), a
function-field element `t` that is *regular and vanishing* at a point `P` — i.e.
`t = algebraMap s` for some `s` in the maximal ideal of `𝒪_{X,P}` — with `t ≠ 0`,
is *still regular and vanishing* at some coheight-one generisation `z ⤳ P`.

Geometrically: the zero locus of a regular function is pure codimension one. This
is the honest transport step of Substep 4b: with `t = b|_Δ` a local equation of
`div(f)_∞` restricted to the diagonal `Δ ≅ X` (nonzero since `Δ ⊄ div(f)_∞`,
vanishing at `x₀` since `δ(x₀) ∈ div(f)_∞`), it produces the coheight-1 point `z`
of `X` with `x₀ ∈ closure{z}` at which `b|_Δ` still vanishes.

Proof by reduction to pole-divisor purity
(`Scheme.exists_specializes_coheight_eq_one_of_notMem_stalk_range`) applied to the
reciprocal `t⁻¹`: `s ∈ 𝔪_P` non-unit with `t ≠ 0` makes `t⁻¹` non-regular at `P`;
regularity of `t` propagates to the generisation `z`
(`range_algebraMap_stalk_le_of_specializes`), and non-regularity of `t⁻¹` at `z`
forces the lift `s'` into `𝔪_z`. -/
theorem Scheme.exists_specializes_coheight_eq_one_of_mem_maximalIdeal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (P : X) (s : X.presheaf.stalk P)
    (hs_ne : algebraMap (X.presheaf.stalk P) X.functionField s ≠ 0)
    (hs_mem : s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk P)) :
    ∃ z : X, z ⤳ P ∧ Order.coheight z = 1 ∧
      ∃ s' : X.presheaf.stalk z,
        algebraMap (X.presheaf.stalk z) X.functionField s' =
          algebraMap (X.presheaf.stalk P) X.functionField s ∧
        s' ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
  set t := algebraMap (X.presheaf.stalk P) X.functionField s with ht
  -- (A) `t⁻¹` is not regular at `P`: else `1 - u·s ↦ 0` for a unit `1 - u·s`.
  have hpole : t⁻¹ ∉ (algebraMap (X.presheaf.stalk P) X.functionField).range := by
    rintro ⟨u, hu⟩
    have hus_mem : u * s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk P) :=
      Ideal.mul_mem_left _ u hs_mem
    have hunit : IsUnit (1 - u * s) := by
      refine IsLocalRing.notMem_maximalIdeal.mp (fun hmem => ?_)
      have h1 : (1 : X.presheaf.stalk P) ∈ IsLocalRing.maximalIdeal _ := by
        have h := Ideal.add_mem _ hmem hus_mem
        rwa [sub_add_cancel] at h
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        ((Ideal.eq_top_iff_one _).mpr h1)
    have himg : algebraMap (X.presheaf.stalk P) X.functionField (1 - u * s) = 0 := by
      rw [map_sub, map_one, map_mul, hu, ← ht, inv_mul_cancel₀ hs_ne, sub_self]
    exact not_isUnit_zero (himg ▸ hunit.map (algebraMap (X.presheaf.stalk P) X.functionField))
  -- (B) Pole-divisor purity for `t⁻¹`.
  obtain ⟨z, hz_spec, hz_coht, hz_pole⟩ :=
    Scheme.exists_specializes_coheight_eq_one_of_notMem_stalk_range X hreg P t⁻¹ hpole
  -- (C) `t` remains regular at the generisation `z`.
  obtain ⟨s', hs'⟩ := range_algebraMap_stalk_le_of_specializes hz_spec ⟨s, rfl⟩
  refine ⟨z, hz_spec, hz_coht, s', hs', ?_⟩
  -- (D) `s' ∈ 𝔪_z`: else `s'` is a unit and `t⁻¹` would be regular at `z`.
  by_contra hs'not
  have hunit : IsUnit s' := IsLocalRing.notMem_maximalIdeal.mp hs'not
  have hs't : algebraMap (X.presheaf.stalk z) X.functionField s' = t := hs'.trans ht.symm
  refine hz_pole ⟨↑hunit.unit⁻¹, ?_⟩
  have hmulz : s' * (↑hunit.unit⁻¹ : X.presheaf.stalk z) = 1 := by
    have h := Units.mul_inv hunit.unit
    rwa [hunit.unit_spec] at h
  have hone : algebraMap (X.presheaf.stalk z) X.functionField (↑hunit.unit⁻¹) * t = 1 := by
    rw [← hs't, ← map_mul, mul_comm, hmulz, map_one]
  exact eq_inv_of_mul_eq_one_left hone

end AlgebraicGeometry
