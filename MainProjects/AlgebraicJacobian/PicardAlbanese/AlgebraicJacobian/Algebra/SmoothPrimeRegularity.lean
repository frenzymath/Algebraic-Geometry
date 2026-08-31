/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Algebra.StandardSmoothDimension
import AlgebraicJacobian.Algebra.SmoothPrimeRegularityStep

/-!
# Regularity of standard-smooth algebras at all primes (Stacks 00TT, Serre-free route)

This file closes the "non-closed point" gap of the smooth ⟹ regular pipeline
(Stacks tag `00TT`) **without** Stacks `00OF` (localisations of regular local
rings are regular, via Serre's homological characterisation — absent from
Mathlib at the pinned version). Instead of localising a closed-point
regularity witness, we prove regularity at an arbitrary prime `q` of a
standard-smooth algebra `S` over a *perfect* field `k` directly, via the
conormal sequence and the transcendence-degree/height inequality of
`Algebra/SmoothPrimeRegularityStep.lean` (Lemmas A/B there). Ported from the
Albanese layer of the previous Algebraic-Jacobian tree (identical toolchain
and mathlib pin, split at the source's own section seams),
re-kernel-verified here.

* `Algebra.rank_kaehlerDifferential_eq_trdeg` (**Lemma C**): for an
  essentially-finite-type field extension `K` of a perfect field `k`,
  `rank_K Ω[K⁄k] = trdeg k K`. Choose a separating transcendence basis `s`
  (`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`); over the
  rational-function subfield `F = k(s)` the extension is formally étale, so
  `Ω[K⁄k] ≃ K ⊗_F Ω[F⁄k]`, and `Ω[F⁄k]` is the localised module of
  `Ω[k[s]⁄k]`, free with basis `{d xᵢ}`.
* `finrank_cotangentSpace_add_finrank_kaehler_residueField` (**Lemma D**): the
  conormal (Stacks `00RU`) dimension count at an arbitrary prime: for a local
  algebra `Sₘ` formally smooth over `R` with formally smooth residue field
  `κ` and `Ω[Sₘ⁄R]` free of rank `n`,
  `dim_κ (m/m²) + dim_κ Ω[κ⁄R] = n`. The retraction from
  `FormallySmooth R κ` makes the conormal map `m/m² → κ ⊗ Ω[Sₘ⁄R]`
  (split) injective, the cokernel is `Ω[κ⁄R]` by exactness
  (`exact_kerCotangentToTensor_mapBaseChange`) plus surjectivity of
  `mapBaseChange`, and rank–nullity gives the identity.
* `isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField`
  (**Theorem**, Stacks `00TT` at every prime): combining B, C, D: at any
  prime `q` of a standard-smooth `k`-algebra (`k` perfect, e.g. algebraically
  closed), any localisation `S_q` is a regular local ring. Indeed
  `dim_κ (m/m²) = n - dim_κ Ω[κ⁄k] = n - trdeg k κ ≤ ht q = dim S_q`, and a
  Noetherian local ring with `dim_κ m/m² ≤ dim` is regular
  (`IsRegularLocalRing.of_finrank_cotangentSpace_le_ringKrullDim` from
  `Algebra/StandardSmoothDimension.lean`).

The downstream consumer is the codim-1 extension layer (Stage 6 of the
`Albanese/CodimOneExtension.lean` pipeline), which instantiates the theorem at
the stalk of a smooth variety over an algebraically closed field.
-/

set_option autoImplicit false

universe u v

set_option maxSynthPendingDepth 3

open Ideal

section LemmaC

/-! ### Lemma C: Kähler rank equals transcendence degree over a perfect field -/

open KaehlerDifferential Cardinal Module

/-- Ω-rank is invariant under `k`-algebra isomorphisms: transport along the
formally étale algebra structure induced by the isomorphism, then apply the
étale base-change identification of Kähler differentials. -/
private lemma rank_kaehlerDifferential_eq_of_algEquiv
    {k : Type u} [CommRing k] {B C : Type u} [Field B] [Field C]
    [Algebra k B] [Algebra k C] (e : B ≃ₐ[k] C) :
    Module.rank B (Ω[B⁄k]) = Module.rank C (Ω[C⁄k]) := by
  letI : Algebra B C := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower k B C := IsScalarTower.of_algebraMap_eq fun x =>
    (e.commutes x).symm
  haveI : Algebra.FormallyEtale B C := by
    have e' : B ≃ₐ[B] C := AlgEquiv.ofBijective (Algebra.ofId B C) e.bijective
    exact Algebra.FormallyEtale.of_equiv e'
  rw [← (tensorKaehlerEquivOfFormallyEtale k B C).rank_eq, Module.rank_baseChange,
    Cardinal.lift_id]

/-- **Lemma C: the Kähler rank of an essentially-finite-type field extension
of a perfect field equals its transcendence degree.** Choose a separating
transcendence basis `s` (`PerfectField` +
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`); the extension
`K / k(s)` is separable algebraic hence formally étale, so
`Ω[K⁄k] ≃ K ⊗_{k(s)} Ω[k(s)⁄k]`, and `Ω[k(s)⁄k]` is the localisation of the
free module `Ω[k[s]⁄k]` with basis `{d xᵢ : i ∈ s}`. -/
theorem Algebra.rank_kaehlerDifferential_eq_trdeg
    (k K : Type u) [Field k] [PerfectField k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    Module.rank K (Ω[K⁄k]) = Algebra.trdeg k K := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  set F : IntermediateField k K := IntermediateField.adjoin k (s : Set K) with hFdef
  haveI : Algebra.IsSeparable F K := H
  haveI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  -- Step 1: étale base change along `F ⊆ K`.
  have h1 : Module.rank K (Ω[K⁄k]) = Module.rank F (Ω[F⁄k]) := by
    rw [← (tensorKaehlerEquivOfFormallyEtale k F K).rank_eq, Module.rank_baseChange,
      Cardinal.lift_id]
  -- Step 2: `F ≃ₐ[k] Frac k[s]` via the transcendence basis.
  have hrange : Set.range ((↑) : {x // x ∈ s} → K) = (s : Set K) := Subtype.range_coe
  have e : FractionRing (MvPolynomial {x // x ∈ s} k) ≃ₐ[k] F := by
    rw [hFdef, ← hrange]
    exact hs.1.aevalEquivField
  have h2 : Module.rank F (Ω[F⁄k]) =
      Module.rank (FractionRing (MvPolynomial {x // x ∈ s} k))
        (Ω[FractionRing (MvPolynomial {x // x ∈ s} k)⁄k]) :=
    (rank_kaehlerDifferential_eq_of_algEquiv e).symm
  -- Step 3: `Ω` of the fraction field of the polynomial ring is free of rank `#s`.
  have h3 : Module.rank (FractionRing (MvPolynomial {x // x ∈ s} k))
      (Ω[FractionRing (MvPolynomial {x // x ∈ s} k)⁄k]) = #{x // x ∈ s} := by
    haveI : IsLocalizedModule (nonZeroDivisors (MvPolynomial {x // x ∈ s} k))
        (map k k (MvPolynomial {x // x ∈ s} k)
          (FractionRing (MvPolynomial {x // x ∈ s} k))) :=
      isLocalizedModule_map k (MvPolynomial {x // x ∈ s} k)
        (FractionRing (MvPolynomial {x // x ∈ s} k))
        (nonZeroDivisors (MvPolynomial {x // x ∈ s} k))
    have b : Basis {x // x ∈ s} (FractionRing (MvPolynomial {x // x ∈ s} k))
        (Ω[FractionRing (MvPolynomial {x // x ∈ s} k)⁄k]) :=
      (mvPolynomialBasis k {x // x ∈ s}).ofIsLocalizedModule
        (FractionRing (MvPolynomial {x // x ∈ s} k))
        (nonZeroDivisors (MvPolynomial {x // x ∈ s} k))
        (map k k (MvPolynomial {x // x ∈ s} k)
          (FractionRing (MvPolynomial {x // x ∈ s} k)))
    exact (b.mk_eq_rank'').symm
  -- Step 4: `#s = trdeg k K` since `s` is a transcendence basis.
  have h4 : (#{x // x ∈ s} : Cardinal) = Algebra.trdeg k K := hs.cardinalMk_eq_trdeg
  rw [h1, h2, h3, h4]

end LemmaC

section LemmaD

/-! ### Lemma D: the conormal dimension identity -/

open KaehlerDifferential IsLocalRing

/-- **Lemma D: the conormal (Stacks 00RU) dimension identity at an arbitrary
prime.** For a local algebra `Sₘ` formally smooth over `R`, with residue field
`κ` also formally smooth over `R` (automatic over a perfect base field) and
Kähler differentials free of rank `n`,

`dim_κ (m/m²) + dim_κ Ω[κ⁄R] = n.`

Proof: the conormal map `m/m² → κ ⊗ Ω[Sₘ⁄R]` is (split) injective by
`Algebra.FormallySmooth.iff_split_injection` (using `FormallySmooth R κ`), its
cokernel is `Ω[κ⁄R]` by `exact_kerCotangentToTensor_mapBaseChange` plus
surjectivity of `mapBaseChange`, and the middle term has dimension `n`;
rank–nullity gives the identity. This generalises the closed-point
computation (which additionally assumed `Subsingleton Ω[κ⁄R]`). -/
theorem finrank_cotangentSpace_add_finrank_kaehler_residueField
    {R Sₘ : Type u} [CommRing R] [CommRing Sₘ] [IsLocalRing Sₘ]
    [Algebra R Sₘ] [Algebra.FormallySmooth R Sₘ]
    [Algebra.FormallySmooth R (ResidueField Sₘ)]
    [Module.Free Sₘ (Ω[Sₘ⁄R])]
    (n : ℕ) (hrank : Module.rank Sₘ (Ω[Sₘ⁄R]) = n) :
    Module.finrank (ResidueField Sₘ) (CotangentSpace Sₘ)
      + Module.finrank (ResidueField Sₘ) (Ω[ResidueField Sₘ⁄R]) = n := by
  have hSurj : Function.Surjective (algebraMap Sₘ (ResidueField Sₘ)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  have hker : RingHom.ker (algebraMap Sₘ (ResidueField Sₘ)) = maximalIdeal Sₘ := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  -- Step 1: the Sₘ-linear conormal map out of the maximal-ideal cotangent,
  -- injective with range the kernel of `mapBaseChange`.
  obtain ⟨f, hfinj, hfrange⟩ :
      ∃ f : (maximalIdeal Sₘ).Cotangent →ₗ[Sₘ]
          TensorProduct Sₘ (ResidueField Sₘ) (Ω[Sₘ⁄R]),
        Function.Injective f ∧
          ∀ x, x ∈ LinearMap.ker (mapBaseChange R Sₘ (ResidueField Sₘ)) ↔
            x ∈ Set.range f := by
    rw [← hker]
    refine ⟨kerCotangentToTensor R Sₘ (ResidueField Sₘ), ?_, ?_⟩
    · obtain ⟨l, hl⟩ :=
        (Algebra.FormallySmooth.iff_split_injection
          (R := R) (P := Sₘ) (A := ResidueField Sₘ) hSurj).mp ‹_›
      refine Function.LeftInverse.injective (g := l) fun x => ?_
      have h := LinearMap.congr_fun hl x
      simp only [LinearMap.coe_comp, Function.comp_apply] at h
      exact h
    · intro x
      have h := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R Sₘ
        (ResidueField Sₘ) hSurj x
      rw [LinearMap.mem_ker]
      exact h
  -- Step 2: promote to κ-linear and identify `CotangentSpace` with the kernel.
  set f' : CotangentSpace Sₘ →ₗ[ResidueField Sₘ]
      TensorProduct Sₘ (ResidueField Sₘ) (Ω[Sₘ⁄R]) :=
    f.extendScalarsOfSurjective hSurj with hf'def
  have hf'app : ∀ x, f' x = f x := fun x => rfl
  have hf'inj : Function.Injective f' := fun a b hab => hfinj (by
    rw [← hf'app, ← hf'app]; exact hab)
  have hrangeEq : LinearMap.range f'
      = LinearMap.ker (mapBaseChange R Sₘ (ResidueField Sₘ)) := by
    ext x
    rw [LinearMap.mem_range, hfrange x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hf'app y).symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hf'app]; exact hy⟩
  -- Step 3: finite-dimensionality of the middle term, of dimension `n`.
  haveI : Module.Finite Sₘ (Ω[Sₘ⁄R]) := by
    rw [← Module.rank_lt_aleph0_iff, hrank]
    exact Cardinal.natCast_lt_aleph0
  have hmid : Module.finrank (ResidueField Sₘ)
      (TensorProduct Sₘ (ResidueField Sₘ) (Ω[Sₘ⁄R])) = n := by
    rw [Module.finrank_baseChange]
    exact Module.finrank_eq_of_rank_eq hrank
  -- Step 4: rank–nullity for `mapBaseChange`.
  have hgsurj : Function.Surjective (mapBaseChange R Sₘ (ResidueField Sₘ)) :=
    KaehlerDifferential.mapBaseChange_surjective R Sₘ (ResidueField Sₘ) hSurj
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (mapBaseChange R Sₘ (ResidueField Sₘ))
  rw [LinearMap.range_eq_top.mpr hgsurj, finrank_top] at hrn
  have hkerfin : Module.finrank (ResidueField Sₘ)
      (LinearMap.ker (mapBaseChange R Sₘ (ResidueField Sₘ)))
      = Module.finrank (ResidueField Sₘ) (CotangentSpace Sₘ) := by
    rw [← hrangeEq]
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofInjective f' hf'inj)).symm
  rw [hkerfin, hmid] at hrn
  omega

end LemmaD

section Main

/-! ### The main theorem: Stacks 00TT at every prime, Serre-free -/

open KaehlerDifferential IsLocalRing

/-- **Stacks `00TT` at an arbitrary prime over a perfect field (algebra form,
Serre-free).** For a standard-smooth algebra `S` over a perfect field `k`
(e.g. an algebraically closed field), any localisation of `S` at any prime
ideal `q` is a regular local ring. This includes the non-closed points that
the closed-point route cannot reach, and requires neither Stacks `00OF`
(localisation of regular local rings) nor Serre's homological criterion:
the cotangent dimension is computed directly by the conormal identity
(Lemma D), the Kähler–trdeg identification at the residue field (Lemma C),
and the trdeg–height inequality (Lemmas A/B of
`Algebra/SmoothPrimeRegularityStep.lean`). -/
theorem isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField
    {k : Type u} [Field k] [PerfectField k]
    {S : Type u} [CommRing S] [Nontrivial S] [Algebra k S]
    [Algebra.IsStandardSmooth k S]
    (q : Ideal S) (hq : q.IsPrime)
    (Sq : Type u) [CommRing Sq] [IsLocalRing Sq] [Algebra k Sq] [Algebra S Sq]
    [IsScalarTower k S Sq] [IsLocalization.AtPrime Sq q] :
    IsRegularLocalRing Sq := by
  haveI := hq
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  haveI : IsNoetherianRing Sq := IsLocalization.isNoetherianRing q.primeCompl Sq ‹_›
  obtain ⟨n, hn⟩ : ∃ n, Algebra.IsStandardSmoothOfRelativeDimension n k S := by
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := (inferInstance : Algebra.IsStandardSmooth k S).out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  haveI := hn
  -- Kähler package at the localisation (free of rank `n`).
  haveI : Module.Free S (Ω[S⁄k]) := Algebra.IsStandardSmooth.free_kaehlerDifferential
  haveI : IsLocalizedModule q.primeCompl (KaehlerDifferential.map k k S Sq) :=
    KaehlerDifferential.isLocalizedModule_map k S Sq q.primeCompl
  haveI : Module.Free Sq (Ω[Sq⁄k]) :=
    Module.free_of_isLocalizedModule (R := S) (Rₛ := Sq) (S := q.primeCompl)
      (M := Ω[S⁄k]) (Mₛ := Ω[Sq⁄k]) (KaehlerDifferential.map k k S Sq)
  have hrank : Module.rank Sq (Ω[Sq⁄k]) = n := by
    have h := Module.lift_rank_of_isLocalizedModule_of_free Sq q.primeCompl
      (KaehlerDifferential.map k k S Sq)
    rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (S := S) n] at h
    simpa using h
  -- Formal smoothness of `Sq` and of its residue field over `k`.
  haveI : Algebra.FormallySmooth S Sq := Algebra.FormallySmooth.of_isLocalization q.primeCompl
  haveI : Algebra.FormallySmooth k Sq := Algebra.FormallySmooth.comp k S Sq
  haveI : Algebra.EssFiniteType k S := Algebra.EssFiniteType.of_finiteType k S
  haveI : Algebra.EssFiniteType S Sq := Algebra.EssFiniteType.of_isLocalization Sq q.primeCompl
  haveI : Algebra.EssFiniteType k Sq := Algebra.EssFiniteType.comp k S Sq
  have hResSurj : Function.Surjective (algebraMap Sq (ResidueField Sq)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  haveI : Algebra.FiniteType Sq (ResidueField Sq) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId Sq (ResidueField Sq)) hResSurj
  haveI : Algebra.EssFiniteType Sq (ResidueField Sq) :=
    Algebra.EssFiniteType.of_finiteType Sq (ResidueField Sq)
  haveI : Algebra.EssFiniteType k (ResidueField Sq) :=
    Algebra.EssFiniteType.comp k Sq (ResidueField Sq)
  -- (the `Algebra.FormallySmooth.of_perfectField` low-priority instance)
  haveI : Algebra.FormallySmooth k (ResidueField Sq) := inferInstance
  -- Lemma D: the conormal dimension identity at `Sq`.
  have hD := finrank_cotangentSpace_add_finrank_kaehler_residueField
    (R := k) (Sₘ := Sq) n hrank
  -- Lemma B: the trdeg–height inequality at `q`.
  obtain ⟨d, hd, hB⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_le_trdeg_and_natCast_le_height_add
      (k := k) n q hq
  -- trdeg monotonicity from `S ⧸ q` into the residue field.
  have hmono : Algebra.trdeg k (S ⧸ q) ≤ Algebra.trdeg k (ResidueField Sq) := by
    set φ : S →ₐ[k] ResidueField Sq :=
      (IsScalarTower.toAlgHom k Sq (ResidueField Sq)).comp
        (IsScalarTower.toAlgHom k S Sq) with hφdef
    have hφmem : ∀ a : S, φ a = 0 ↔ a ∈ q := by
      intro a
      simp only [hφdef, AlgHom.coe_comp, Function.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
      exact IsLocalization.AtPrime.to_map_mem_maximal_iff Sq q a
    have hφker : ∀ a ∈ q, φ a = 0 := fun a ha => (hφmem a).mpr ha
    have hinj : Function.Injective (Ideal.Quotient.liftₐ q φ hφker) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (hφmem r).mp hx
    exact trdeg_le_of_injective _ hinj
  -- Lemma C at the residue field.
  have hC : Module.rank (ResidueField Sq) (Ω[ResidueField Sq⁄k]) =
      Algebra.trdeg k (ResidueField Sq) :=
    Algebra.rank_kaehlerDifferential_eq_trdeg k (ResidueField Sq)
  -- Ω[κ⁄k] is finite-dimensional (surjective image of the f.d. middle term).
  haveI : Module.Finite Sq (Ω[Sq⁄k]) := by
    rw [← Module.rank_lt_aleph0_iff, hrank]
    exact Cardinal.natCast_lt_aleph0
  haveI : Module.Finite (ResidueField Sq) (Ω[ResidueField Sq⁄k]) :=
    Module.Finite.of_surjective (mapBaseChange k Sq (ResidueField Sq))
      (KaehlerDifferential.mapBaseChange_surjective k Sq (ResidueField Sq) hResSurj)
  -- `d ≤ dim_κ Ω[κ⁄k]`.
  have hdfin : (d : ℕ∞) ≤
      (Module.finrank (ResidueField Sq) (Ω[ResidueField Sq⁄k]) : ℕ∞) := by
    have hcard : (d : Cardinal) ≤
        Module.rank (ResidueField Sq) (Ω[ResidueField Sq⁄k]) := by
      rw [hC]
      exact le_trans hd hmono
    rw [← Module.finrank_eq_rank] at hcard
    exact_mod_cast hcard
  -- Conclude via the cotangent criterion.
  apply IsRegularLocalRing.of_finrank_cotangentSpace_le_ringKrullDim
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q Sq]
  have hfinal : (Module.finrank (ResidueField Sq) (CotangentSpace Sq) : ℕ∞) ≤ q.height := by
    refine (ENat.add_le_add_iff_right
      (k := (Module.finrank (ResidueField Sq) (Ω[ResidueField Sq⁄k]) : ℕ∞))
      (by simp)).mp ?_
    calc (Module.finrank (ResidueField Sq) (CotangentSpace Sq) : ℕ∞)
        + (Module.finrank (ResidueField Sq) (Ω[ResidueField Sq⁄k]) : ℕ∞)
        = (n : ℕ∞) := by exact_mod_cast hD
      _ ≤ q.height + d := hB
      _ ≤ q.height + (Module.finrank (ResidueField Sq) (Ω[ResidueField Sq⁄k]) : ℕ∞) := by
          gcongr
  exact_mod_cast hfinal

end Main
