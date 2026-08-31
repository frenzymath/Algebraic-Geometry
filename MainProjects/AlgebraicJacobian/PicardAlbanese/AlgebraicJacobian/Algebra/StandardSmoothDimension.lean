/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Krull dimension at maximal ideals of standard-smooth algebras (Stacks 00OE substrate)

This file provides the dimension side of the smooth ⟹ regular pipeline
(Stacks tag `00OE`, the smooth-algebra Krull-dimension formula), in the
closed-point form the pipeline consumes: for a standard-smooth algebra `S` of
relative dimension `n` over a field `k` and a *maximal* ideal `m ⊆ S`, the
localisation `Sₘ` has Krull dimension (at least, hence — combined with the
cotangent bound — exactly) `n`. Ported from the Albanese layer of the previous
Algebraic-Jacobian tree (identical toolchain and mathlib pin),
re-kernel-verified here.

No transcendence-degree theory is needed: the pinned Mathlib toolbox
(`Polynomial.height_eq_height_add_one`, Krull's height theorem in the form
`Ideal.height_le_height_add_spanFinrank_of_le`, and the
`MvPolynomial.isJacobsonRing` instance) supports a direct height computation:

* `MvPolynomial.height_eq_natCard_of_isMaximal`: every maximal ideal of
  `MvPolynomial ι k` (finitely many variables over a field) has height
  `Nat.card ι`. Induction over `ι` via `Finite.induction_empty_option`; the
  induction step contracts a maximal ideal of `R[X]` to a maximal ideal of `R`
  (Jacobson) and applies `Polynomial.height_eq_height_add_one`.
* `Algebra.IsStandardSmoothOfRelativeDimension.natCast_le_height_of_isMaximal`:
  the **lower bound** `n ≤ ht m` for a maximal ideal `m` of a standard-smooth
  `k`-algebra of relative dimension `n`. Writing `S = P.Ring ⧸ ker` for a
  submersive presentation `P` with `#ι` generators and `#σ` relations
  (`n = #ι - #σ`), the pullback `M ⊆ P.Ring` of `m` is maximal of height `#ι`,
  and Krull's height theorem bounds `ht M ≤ ht m + #σ`.
* `Algebra.IsStandardSmoothOfRelativeDimension.le_ringKrullDim_of_isLocalization_atPrime`:
  the same lower bound for `ringKrullDim Sₘ` at the localisation.
* `IsRegularLocalRing.of_finrank_cotangentSpace_le_ringKrullDim`: the generic
  regularity glue — a Noetherian local ring whose cotangent-space dimension is
  bounded by its Krull dimension is regular (the reverse inequality is
  automatic).

The downstream consumers are the smooth ⟹ regular results: the arbitrary-prime
theorem of `Algebra/SmoothPrimeRegularity.lean` (Serre-free Stacks `00TT`)
combines the last lemma with the trdeg–height inequality, and the codim-1
extension layer instantiates it at stalks of smooth varieties.
-/

set_option autoImplicit false

universe u v

open Ideal

section MvPolynomialHeight

/-- **Maximal ideals of finite-variable polynomial rings over a field have full
height.** For a field `k`, a finite index type `ι` and a maximal ideal
`M ⊆ k[Xᵢ : i ∈ ι]`, the height of `M` is `Nat.card ι`.

Induction over `ι` via `Finite.induction_empty_option`: the base case is the
field `k` itself (Krull dimension `0`), and the induction step writes
`MvPolynomial (Option α) k ≃+* (MvPolynomial α k)[X]`, contracts the maximal
ideal along `C` (maximal again, since `MvPolynomial α k` is Jacobson), and
applies `Polynomial.height_eq_height_add_one`. -/
theorem MvPolynomial.height_eq_natCard_of_isMaximal
    {k : Type u} [Field k] {ι : Type v} [Finite ι]
    (M : Ideal (MvPolynomial ι k)) (hM : M.IsMaximal) :
    M.height = Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e IH =>
    haveI := hM
    have h1 := IH (M.comap (MvPolynomial.renameEquiv k e).toRingEquiv)
      (Ideal.comap_isMaximal_of_equiv _)
    rw [RingEquiv.height_comap] at h1
    rw [h1, Nat.card_congr e]
  | h_empty =>
    have hdim : ringKrullDim (MvPolynomial PEmpty.{v + 1} k) = 0 := by
      rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.isEmptyRingEquiv k PEmpty)]
      exact ringKrullDim_eq_zero_of_field k
    have hle : (M.height : WithBot ℕ∞) ≤ 0 :=
      hdim ▸ Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    have hz : M.height = 0 := le_antisymm (by exact_mod_cast hle) (by simp)
    simp [hz]
  | h_option IH =>
    rename_i α _
    haveI := hM
    set ψ := (MvPolynomial.optionEquivLeft k α).toRingEquiv with hψ
    set P' : Ideal (Polynomial (MvPolynomial α k)) := M.map ψ with hP'
    haveI hP'max : P'.IsMaximal := Ideal.map_isMaximal_of_equiv ψ
    set p : Ideal (MvPolynomial α k) := P'.comap (Polynomial.C) with hpdef
    haveI hpmax : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P'
    haveI : P'.LiesOver p := ⟨by rw [hpdef, Ideal.under_def, Polynomial.algebraMap_eq]⟩
    have hht : P'.height = p.height + 1 := Polynomial.height_eq_height_add_one p P'
    have hIH : p.height = Nat.card α := IH p hpmax
    have hMP' : M.height = P'.height := (RingEquiv.height_map ψ M).symm
    have hcard : Nat.card (Option α) = Nat.card α + 1 := by
      simp [Nat.card_eq_fintype_card]
    rw [hMP', hht, hIH, hcard]
    push_cast
    ring

end MvPolynomialHeight

section StandardSmoothLowerBound

namespace Algebra.IsStandardSmoothOfRelativeDimension

/-- **Stacks 00OE lower bound (closed-point form).** For a standard-smooth
algebra `S` of relative dimension `n` over a field `k` and a maximal ideal
`m ⊆ S`, the height of `m` is at least `n`.

Proof: extract a submersive presentation `P` (with `#ι` generators, `#σ`
relations, `n = #ι - #σ`). The pullback `M` of `m` to the polynomial ring
`P.Ring` is maximal of height `#ι`
(`MvPolynomial.height_eq_natCard_of_isMaximal`), contains the kernel of the
presentation (generated by the `#σ` relations), and Krull's height theorem
(`Ideal.height_le_height_add_spanFinrank_of_le`) gives
`#ι = ht M ≤ ht m + #σ`, whence `n ≤ ht m`. -/
theorem natCast_le_height_of_isMaximal
    {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S] (n : ℕ)
    [H : Algebra.IsStandardSmoothOfRelativeDimension n k S]
    (m : Ideal S) (hm : m.IsMaximal) : (n : ℕ∞) ≤ m.height := by
  obtain ⟨ι, σ, hσ, hι, P, hPdim⟩ := H.out
  haveI := hm
  have hsurj : Function.Surjective (algebraMap P.Ring S) := P.algebraMap_surjective
  set M : Ideal P.Ring := m.comap (algebraMap P.Ring S) with hMdef
  haveI hM : M.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  -- full height of the pullback in the polynomial ring
  have hMheight : M.height = Nat.card ι := MvPolynomial.height_eq_natCard_of_isMaximal M hM
  -- the presentation kernel sits inside the pullback
  have hker_le : RingHom.ker (algebraMap P.Ring S) ≤ M := fun x hx => by
    rw [hMdef, Ideal.mem_comap, RingHom.mem_ker.mp hx]
    exact m.zero_mem
  -- Krull's height theorem
  have hbound := Ideal.height_le_height_add_spanFinrank_of_le hker_le
  -- identify the quotient-side prime with `m` (first isomorphism theorem)
  set e := (algebraMap P.Ring S : P.Ring →+* S).quotientKerEquivOfSurjective hsurj with hedef
  have hMcomap : M = Ideal.comap (Ideal.Quotient.mk (RingHom.ker (algebraMap P.Ring S)))
      (Ideal.comap e m) := by
    ext x
    simp only [hMdef, Ideal.mem_comap]
    rw [hedef, RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hqheight : (M.map (Ideal.Quotient.mk (RingHom.ker (algebraMap P.Ring S)))).height
      = m.height := by
    rw [hMcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
      RingEquiv.height_comap]
  -- the kernel is generated by the `#σ` relations
  have hker_span : RingHom.ker (algebraMap P.Ring S) = Ideal.span (Set.range P.relation) :=
    P.span_range_relation_eq_ker.symm
  have hfr : (RingHom.ker (algebraMap P.Ring S)).spanFinrank ≤ Nat.card σ := by
    rw [hker_span]
    refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)) ?_
    calc (Set.range P.relation).ncard
        = (P.relation '' Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set σ).ncard := Set.ncard_image_le Set.finite_univ
      _ = Nat.card σ := Set.ncard_univ σ
  -- cardinal bookkeeping: `n + #σ = #ι`
  have hcards : n + Nat.card σ = Nat.card ι := by
    have hle : Nat.card σ ≤ Nat.card ι := Nat.card_le_card_of_injective P.map P.map_inj
    have hdim : Nat.card ι - Nat.card σ = n := hPdim
    omega
  -- combine
  have h1 : (Nat.card ι : ℕ∞) ≤ m.height + Nat.card σ := by
    calc (Nat.card ι : ℕ∞) = M.height := hMheight.symm
      _ ≤ (M.map (Ideal.Quotient.mk (RingHom.ker (algebraMap P.Ring S)))).height
          + (RingHom.ker (algebraMap P.Ring S)).spanFinrank := hbound
      _ ≤ m.height + Nat.card σ := by
          rw [hqheight]
          have hfr' : ((RingHom.ker (algebraMap P.Ring S)).spanFinrank : ℕ∞)
              ≤ (Nat.card σ : ℕ∞) := by exact_mod_cast hfr
          exact add_le_add le_rfl hfr'
  rw [← hcards] at h1
  push_cast at h1
  exact (ENat.add_le_add_iff_right (by simp)).mp h1

/-- **Stacks 00OE lower bound, localised form.** For a standard-smooth algebra
`S` of relative dimension `n` over a field `k`, a maximal ideal `m ⊆ S` and a
localisation `Sₘ` of `S` at `m`, the Krull dimension of `Sₘ` is at least `n`. -/
theorem le_ringKrullDim_of_isLocalization_atPrime
    {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k S]
    (m : Ideal S) (hm : m.IsMaximal)
    (Sₘ : Type u) [CommRing Sₘ] [Algebra S Sₘ] [IsLocalization.AtPrime Sₘ m] :
    (n : WithBot ℕ∞) ≤ ringKrullDim Sₘ := by
  haveI := hm.isPrime
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m Sₘ]
  exact_mod_cast natCast_le_height_of_isMaximal (k := k) n m hm

end Algebra.IsStandardSmoothOfRelativeDimension

end StandardSmoothLowerBound

section RegularityGlue

/-- **Regularity from the cotangent upper bound.** A Noetherian local ring whose
cotangent-space dimension is bounded above by its Krull dimension is a regular
local ring (the reverse inequality `dim ≤ dim_κ m/m²` holds in any Noetherian
local ring, via `ringKrullDim_le_spanFinrank_maximalIdeal`). This is the glue
between the cotangent computation and the dimension lower bound in the
smooth ⟹ regular pipeline. -/
theorem IsRegularLocalRing.of_finrank_cotangentSpace_le_ringKrullDim
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h : (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) : WithBot ℕ∞)
      ≤ ringKrullDim A) : IsRegularLocalRing A := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rwa [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]

end RegularityGlue
