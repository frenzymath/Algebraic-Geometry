/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.PolePurityLocal
import AlgebraicJacobian.Algebra.CoheightBridge

/-!
# Pole-divisor purity on a locally Noetherian integral scheme with regular stalks

This file proves the **purity of the polar locus** of a function-field element:
on a locally Noetherian integral scheme `X` all of whose stalks are regular
local rings (e.g. a scheme smooth over a field, via
`isRegularLocalRing_stalk_of_smooth`), an element `h ∈ K(X)` that is *not*
regular at a point `P` (i.e. `h` is not in the image of `𝒪_{X,P} → K(X)`)
fails to be regular already at some *codimension-one* generisation `z ⤳ P`:

* `AlgebraicGeometry.Scheme.exists_specializes_coheight_eq_one_of_notMem_stalk_range`.

This is the scheme-level "pole divisors are pure codimension 1" input to
Milne's *Abelian Varieties* §I.3 Lemma 3.3 (Substep 4 of the plan recorded at
`indeterminacy_pure_codim_one_into_grpScheme` in the codim-one extension leg):
the polar locus of each pulled-back regular function on the smooth variety
`X × X` is pure codim 1 through every of its points, in exactly the
"specialises from a coheight-1 point of the locus" form needed by the
Lemma 3.3 disjunct.

## Route

The ring-theoretic core (`exists_height_one_prime_colon_le` — the elementary,
Serre- and UFD-free replacement of "principal ideals are unmixed in a normal
domain") lives in `Albanese/PolePurityLocal.lean`; see its module docstring
for the four-step chain. This file adds the remaining two layers:

5. **Fraction-field membership as a colon condition**
   (`div_mem_range_algebraMap_iff`): over a localization `S = R_𝔮` inside
   `K = Frac R`, the fraction `a / b` is regular at `𝔮` — lies in the image
   of `S → K` — iff the denominator ideal `((b) : a)` is *not* contained in
   `𝔮`.
6. **Scheme wrapper**: choose an affine open `U ∋ P`, identify
   `𝒪_{X,P} = Γ(U)_𝔭` and `K(X) = Frac Γ(U)`, translate "regular at a
   point" via step 5, run the main ring theorem, and convert the height-1
   prime back into a point `z ⤳ P` with `Order.coheight z = 1` via
   `IsAffineOpen.fromSpec` and the project's coheight bridge
   (`ringKrullDim_stalk_eq_coheight` in `Algebra/CoheightBridge.lean`).

Blueprint reference: `lem:pole_divisor_purity` (feeding
`lem:milne_codim1_indeterminacy`; Milne, *Abelian Varieties*, §I.3 p. 17,
and Hartshorne, *Algebraic Geometry*, II.6.3A / AG 9.2 for the classical
normality route this replaces).
-/

set_option autoImplicit false

universe u

open IsLocalRing

/-! ## §5. Fraction-field membership as a colon condition -/

/-- Over a localization `S = R_𝔮` sitting inside the fraction field `K` of a
domain `R`, the fraction `a / b` (with `b ≠ 0`) lies in the image of `S → K`
iff the denominator ideal `((b) : a)` is *not* contained in `𝔮`. -/
private lemma div_mem_range_algebraMap_iff
    {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K]
    (S : Type*) [CommRing S] [Algebra R S] [Algebra S K] [IsScalarTower R S K]
    {q : Ideal R} [hq : q.IsPrime] [IsLocalization.AtPrime S q]
    {a b : R} (hb : b ≠ 0) :
    algebraMap R K a / algebraMap R K b ∈ (algebraMap S K).range ↔
      ¬ ((Ideal.span ({b} : Set R)).colon {a} ≤ q) := by
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hbK : algebraMap R K b ≠ 0 := fun h => hb (hinjK (by simpa using h))
  constructor
  · rintro ⟨g, hg⟩ hcolon
    obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.mk'_surjective q.primeCompl g
    replace hcs : IsLocalization.mk' S c s = g := hcs
    -- push `mk'_spec` down to `K` along the scalar tower.
    have hspec : algebraMap S K g * algebraMap R K (s : R) = algebraMap R K c := by
      have h0 : IsLocalization.mk' S c s * algebraMap R S (s : R) = algebraMap R S c :=
        IsLocalization.mk'_spec S c s
      have h1 := congrArg (algebraMap S K) h0
      rw [map_mul, hcs] at h1
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    -- `g * b = a` in `K`.
    have hg' : algebraMap S K g * algebraMap R K b = algebraMap R K a := by
      rw [hg, div_mul_cancel₀ _ hbK]
    -- `s * a = b * c` in `R`.
    have hKey : algebraMap R K ((s : R) * a) = algebraMap R K (b * c) := by
      rw [map_mul, map_mul, ← hg', ← hspec]
      ring
    have hcross : (s : R) * a = b * c := hinjK hKey
    have hsColon : (s : R) ∈ (Ideal.span ({b} : Set R)).colon {a} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      exact Ideal.mem_span_singleton.mpr ⟨c, hcross⟩
    exact s.2 (hcolon hsColon)
  · intro hnot
    obtain ⟨s, hsColon, hsq⟩ := SetLike.not_le_iff_exists.mp hnot
    have hs0 : s ≠ 0 := fun h => hsq (h ▸ q.zero_mem)
    have hsa : s • a ∈ Ideal.span ({b} : Set R) := Submodule.mem_colon_singleton.mp hsColon
    rw [smul_eq_mul] at hsa
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hsa
    have hsq' : s ∈ q.primeCompl := hsq
    refine ⟨IsLocalization.mk' S c ⟨s, hsq'⟩, ?_⟩
    have hspec : algebraMap S K (IsLocalization.mk' S c ⟨s, hsq'⟩)
        * algebraMap R K s = algebraMap R K c := by
      have h0 : IsLocalization.mk' S c ⟨s, hsq'⟩ * algebraMap R S s = algebraMap R S c :=
        IsLocalization.mk'_spec S c ⟨s, hsq'⟩
      have h1 := congrArg (algebraMap S K) h0
      rw [map_mul] at h1
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    have hsK : algebraMap R K s ≠ 0 := fun h => hs0 (hinjK (by simpa using h))
    have hcb : c * b = a * s := by
      rw [mul_comm c b, ← hc]
      exact mul_comm _ _
    rw [eq_div_iff hbK]
    apply mul_right_cancel₀ hsK
    calc algebraMap S K (IsLocalization.mk' S c ⟨s, hsq'⟩) * algebraMap R K b
          * algebraMap R K s
        = (algebraMap S K (IsLocalization.mk' S c ⟨s, hsq'⟩) * algebraMap R K s)
          * algebraMap R K b := by ring
      _ = algebraMap R K c * algebraMap R K b := by rw [hspec]
      _ = algebraMap R K (c * b) := by rw [map_mul]
      _ = algebraMap R K (a * s) := by rw [hcb]
      _ = algebraMap R K a * algebraMap R K s := by rw [map_mul]

/-! ## §6. The scheme-level pole-divisor purity theorem -/

namespace AlgebraicGeometry

open TopologicalSpace

/-- **Pole-divisor purity.** Let `X` be a locally Noetherian integral scheme
all of whose stalks are regular local rings (e.g. `X` smooth over a field).
If `h ∈ K(X)` is not regular at a point `P` — i.e. `h` does not lie in the
image of `𝒪_{X,P} → K(X)` — then `h` is already non-regular at some
codimension-one point `z` specialising to `P`:

`∃ z, z ⤳ P ∧ coheight z = 1 ∧ h ∉ im (𝒪_{X,z} → K(X))`.

In particular the polar locus `{x | h ∉ im (𝒪_{X,x} → K(X))}` of a
function-field element is of *pure codimension one* in the "every point
specialises from a coheight-one point of the locus" sense — exactly the shape
of the Milne Lemma 3.3 disjunct (`indeterminacy_pure_codim_one_into_grpScheme`
in the codim-one extension leg).

Blueprint reference: `lem:pole_divisor_purity` (Hartshorne II.6.3A;
Milne, *Abelian Varieties*, §I.3 p. 17). -/
theorem Scheme.exists_specializes_coheight_eq_one_of_notMem_stalk_range
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (P : X) (h : X.functionField)
    (hP : h ∉ (algebraMap (X.presheaf.stalk P) X.functionField).range) :
    ∃ z : X, z ⤳ P ∧ Order.coheight z = 1 ∧
      h ∉ (algebraMap (X.presheaf.stalk z) X.functionField).range := by
  -- Choose an affine chart `U ∋ P` and set `R := Γ(X, U)`.
  obtain ⟨U, hU, hPU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := P) (U := ⊤) (by trivial)
  haveI : Nonempty U := ⟨⟨P, hPU⟩⟩
  haveI hNoeth : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI hFR : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  -- The stalk at `P` as the localization of `R` at `𝔭`.
  set p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨P, hPU⟩ with hp_def
  letI : Algebra Γ(X, U) (X.presheaf.stalk P) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPU⟩
  haveI hlocP : IsLocalization.AtPrime (X.presheaf.stalk P) p.asIdeal :=
    hU.isLocalization_stalk ⟨P, hPU⟩
  haveI := functionField_isScalarTower X U ⟨P, hPU⟩
  -- Write `h = a / b` as a fraction of sections over `U`.
  obtain ⟨⟨a, b⟩, hmk⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Γ(X, U)) h
  replace hmk : IsLocalization.mk' X.functionField a b = h := hmk
  have hb0 : (b : Γ(X, U)) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hdiv : h = algebraMap Γ(X, U) X.functionField a
      / algebraMap Γ(X, U) X.functionField b := by
    rw [← hmk, IsFractionRing.mk'_eq_div]
  -- Non-regularity at `P` says the denominator ideal sits inside `𝔭`.
  have hle : (Ideal.span ({(b : Γ(X, U))} : Set Γ(X, U))).colon {a} ≤ p.asIdeal := by
    have hnn := (div_mem_range_algebraMap_iff (K := X.functionField)
      (X.presheaf.stalk P) (q := p.asIdeal) hb0).not.mp (hdiv ▸ hP)
    exact not_not.mp hnn
  -- Every localization of `R` at a prime is regular: transport stalk
  -- regularity along the chart.
  have hregR : ∀ (q : Ideal Γ(X, U)) [q.IsPrime],
      IsRegularLocalRing (Localization.AtPrime q) := by
    intro q hq
    have hzU' : hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)) ∈ U := by
      have h1 : hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U))
          ∈ Set.range hU.fromSpec.base := ⟨⟨q, hq⟩, rfl⟩
      rw [hU.range_fromSpec] at h1
      exact h1
    letI : Algebra Γ(X, U)
        (X.presheaf.stalk (hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)))) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hzU'⟩
    haveI hlocz : IsLocalization.AtPrime
        (X.presheaf.stalk (hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)))) q :=
      hU.isLocalization_stalk' ⟨q, hq⟩ hzU'
    haveI := hreg (hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U)))
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl
        (X.presheaf.stalk (hU.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U))))
        (Localization.AtPrime q)).toRingEquiv
  -- Main ring theorem: a height-one prime `𝔮 ≤ 𝔭` containing the
  -- denominator ideal.
  obtain ⟨q, hqprime, hqht, hqle, hqcolon⟩ :=
    exists_height_one_prime_colon_le hregR hb0 (p := p.asIdeal) hle
  haveI := hqprime
  -- The corresponding point `z ∈ U ⊆ X`.
  have hzU : hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)) ∈ U := by
    have h1 : hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U))
        ∈ Set.range hU.fromSpec.base := ⟨⟨q, hqprime⟩, rfl⟩
    rw [hU.range_fromSpec] at h1
    exact h1
  letI : Algebra Γ(X, U)
      (X.presheaf.stalk (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)))) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hzU⟩
  haveI hlocz : IsLocalization.AtPrime
      (X.presheaf.stalk (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)))) q :=
    hU.isLocalization_stalk' ⟨q, hqprime⟩ hzU
  haveI := functionField_isScalarTower X U ⟨_, hzU⟩
  refine ⟨hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)), ?_, ?_, ?_⟩
  · -- `z ⤳ P` from `𝔮 ≤ 𝔭` via the chart.
    have hle' : (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)) ≤ p := hqle
    have hspec2 : (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)) ⤳ p :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hle'
    have hmap := hspec2.map hU.fromSpec.continuous
    have hPeq : hU.fromSpec p = P := by
      rw [hp_def]
      exact hU.fromSpec_primeIdealOf ⟨P, hPU⟩
    rwa [hPeq] at hmap
  · -- `coheight z = 1` via the coheight–Krull-dimension bridge.
    have hbridge := AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_coheight X
      (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U)))
    have hdim : ringKrullDim
        (X.presheaf.stalk (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U))))
        = ((1 : ℕ∞) : WithBot ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q
        (X.presheaf.stalk (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U))))]
      exact_mod_cast hqht
    rw [hbridge] at hdim
    exact_mod_cast hdim
  · -- non-regularity at `z` from `((b) : a) ≤ 𝔮`.
    rw [hdiv]
    rw [div_mem_range_algebraMap_iff (K := X.functionField)
      (X.presheaf.stalk (hU.fromSpec (⟨q, hqprime⟩ : PrimeSpectrum Γ(X, U))))
      (q := q) hb0]
    exact fun hn => hn hqcolon

end AlgebraicGeometry
