/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# The trdeg–height inequality for standard-smooth algebras (Stacks 00TT substrate, part 1)

This file is the first half of the Serre-free Stacks `00TT` route (regularity
of standard-smooth algebras at **all** primes): the pure height/transcendence
combinatorics. Ported from the Albanese layer of the previous
Algebraic-Jacobian tree (identical toolchain and mathlib pin, split at the
source's own section seams), re-kernel-verified here. The Kähler/conormal half
and the capstone theorem live in `Algebra/SmoothPrimeRegularity.lean`.

* `Polynomial.step_height_trdeg_of_isPrime` (**step lemma**): for a prime
  `P ⊆ R[X]` over `p = P ∩ R` (`R` Noetherian), either `ht p + 1 ≤ ht P` and
  `trdeg k (R⧸p) ≤ trdeg k (R[X]⧸P)`, or `ht P = ht p` and
  `trdeg k (R⧸p) + 1 ≤ trdeg k (R[X]⧸P)`. The height identity is Stacks
  `00ON` (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`; `R[X]` is
  free, hence flat, hence going-down over `R`), and the fiber prime in
  `R[X]/pR[X] ≅ (R⧸p)[X]` is either `⊥` (the residue algebra gains a
  transcendental element) or nonzero (height `≥ 1`).
* `MvPolynomial.exists_le_trdeg_and_natCard_le_height_add` (**Lemma A**): for
  any prime `P` of `k[xᵢ : i ∈ ι]` (`ι` finite) there is `d : ℕ` with
  `d ≤ trdeg k (k[xᵢ] ⧸ P)` and `#ι ≤ ht P + d`. Induction on `ι` via the
  step lemma. No Noether normalisation is needed.
* `Algebra.IsStandardSmoothOfRelativeDimension.exists_le_trdeg_and_natCast_le_height_add`
  (**Lemma B**): the transfer to a standard-smooth algebra `S` of relative
  dimension `n`: for any prime `q ⊆ S` there is `d : ℕ` with
  `d ≤ trdeg k (S ⧸ q)` and `n ≤ ht q + d`. Same pullback pattern as the
  closed-point `natCast_le_height_of_isMaximal` in
  `Algebra/StandardSmoothDimension.lean` (Krull's height theorem bounds the
  height defect by the number of relations of a submersive presentation).
-/

set_option autoImplicit false

universe u v

set_option maxSynthPendingDepth 3

open Ideal

section TrdegHelpers

variable {k : Type u} [Field k]

/-- Adjoining a polynomial variable to a domain raises the transcendence degree
by (at least) one: `trdeg k A + 1 ≤ trdeg k A[X]`. Superadditivity of `trdeg`
in the tower `k → A → A[X]` plus `trdeg A A[X] = 1`. -/
private lemma trdeg_add_one_le_trdeg_polynomial
    (A : Type v) [CommRing A] [IsDomain A] [Algebra k A] :
    Algebra.trdeg k A + 1 ≤ Algebra.trdeg k (Polynomial A) := by
  haveI : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  haveI : FaithfulSMul A (Polynomial A) :=
    (faithfulSMul_iff_algebraMap_injective A (Polynomial A)).mpr
      Polynomial.C_injective
  have h := trdeg_add_le (R := k) (S := A) (A := Polynomial A)
  rwa [Polynomial.trdeg_of_isDomain] at h

/-- If a prime `Q ⊆ A[X]` contracts to `⊥` in `A`, the residue algebra
`A[X] ⧸ Q` contains (a copy of) `A`; hence `trdeg k A ≤ trdeg k (A[X] ⧸ Q)`. -/
private lemma trdeg_le_trdeg_polynomial_quotient
    (A : Type v) [CommRing A] [Algebra k A]
    (Q : Ideal (Polynomial A)) (hQA : Q.comap (algebraMap A (Polynomial A)) = ⊥) :
    Algebra.trdeg k A ≤ Algebra.trdeg k (Polynomial A ⧸ Q) := by
  refine trdeg_le_of_injective
    ((Ideal.Quotient.mkₐ k Q).comp (IsScalarTower.toAlgHom k A (Polynomial A))) ?_
  rw [injective_iff_map_eq_zero]
  intro a ha
  simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    IsScalarTower.coe_toAlgHom', Ideal.Quotient.eq_zero_iff_mem] at ha
  have h1 : a ∈ Q.comap (algebraMap A (Polynomial A)) := ha
  rw [hQA] at h1
  simpa using h1

/-- Quotienting by `⊥` does not lower the transcendence degree (one inequality
suffices downstream). -/
private lemma trdeg_le_trdeg_quotient_bot
    (B : Type v) [CommRing B] [Algebra k B] :
    Algebra.trdeg k B ≤ Algebra.trdeg k (B ⧸ (⊥ : Ideal B)) := by
  refine trdeg_le_of_injective (Ideal.Quotient.mkₐ k ⊥) ?_
  rw [injective_iff_map_eq_zero]
  intro b hb
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hb
  simpa using hb

/-- Transcendence degree is monotone along `k`-algebra isomorphisms (one
inequality suffices downstream). -/
private lemma trdeg_le_of_algEquiv
    {B C : Type v} [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]
    (g : B ≃ₐ[k] C) : Algebra.trdeg k B ≤ Algebra.trdeg k C :=
  trdeg_le_of_injective g.toAlgHom g.injective

/-- The quotient by the (membership-described) preimage of an ideal embeds into
the quotient by the ideal, so transcendence degrees compare. Stated with an
explicit membership equivalence to avoid comparing coercion paths. -/
private lemma trdeg_quotient_le_of_forall_mem_iff
    {B C : Type v} [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]
    (g : B →ₐ[k] C) (P : Ideal C) (P₀ : Ideal B)
    (hmem : ∀ a : B, a ∈ P₀ ↔ g a ∈ P) :
    Algebra.trdeg k (B ⧸ P₀) ≤ Algebra.trdeg k (C ⧸ P) := by
  set φ : B →ₐ[k] C ⧸ P := (Ideal.Quotient.mkₐ k P).comp g with hφdef
  have hφmem : ∀ a : B, φ a = 0 ↔ a ∈ P₀ := by
    intro a
    rw [hφdef]
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact (hmem a).symm
  refine trdeg_le_of_injective (Ideal.Quotient.liftₐ P₀ φ
    (fun a ha => (hφmem a).mpr ha)) ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (hφmem b).mp hx

end TrdegHelpers

section PolynomialStep

/-! ### The one-variable step of Lemma A -/

variable {k : Type u} [Field k] {R : Type v} [CommRing R] [IsNoetherianRing R]
  [Algebra k R]

/-- **One-variable step for the trdeg–height inequality.** For a prime
`P ⊆ R[X]` lying over `p = P ∩ R` in a Noetherian ring `R`, either the height
jumps (`ht p + 1 ≤ ht P`) while the residue algebra still contains `R⧸p`, or
the height is preserved (`ht P = ht p`) and the residue algebra gains a
transcendental element (`trdeg + 1`). Stacks `00ON` supplies
`ht P = ht p + ht P̄` for the fiber prime `P̄` of `R[X]/pR[X] ≅ (R⧸p)[X]`;
the two cases are `P̄ ≠ ⊥` (then `ht P̄ ≥ 1`) and `P̄ = ⊥` (then
`R[X]⧸P ≅ (R⧸p)[X]`). -/
theorem Polynomial.step_height_trdeg_of_isPrime
    (P : Ideal (Polynomial R)) (hP : P.IsPrime) :
    ((P.comap (algebraMap R (Polynomial R))).height + 1 ≤ P.height ∧
      Algebra.trdeg k (R ⧸ P.comap (algebraMap R (Polynomial R))) ≤
        Algebra.trdeg k (Polynomial R ⧸ P)) ∨
    (P.height = (P.comap (algebraMap R (Polynomial R))).height ∧
      Algebra.trdeg k (R ⧸ P.comap (algebraMap R (Polynomial R))) + 1 ≤
        Algebra.trdeg k (Polynomial R ⧸ P)) := by
  haveI := hP
  set p : Ideal R := P.comap (algebraMap R (Polynomial R)) with hpdef
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ P
  haveI : P.LiesOver p := ⟨rfl⟩
  -- Stacks 00ON (going-down for the flat extension `R → R[X]`).
  haveI : Module.Flat R (Polynomial R) := Module.Flat.of_free
  have h00 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  -- Notation for the fiber.
  set pX : Ideal (Polynomial R) := p.map (algebraMap R (Polynomial R)) with hpXdef
  have hker_le : pX ≤ P := Ideal.map_le_iff_le_comap.mpr le_rfl
  set Pbar : Ideal (Polynomial R ⧸ pX) := P.map (Ideal.Quotient.mk pX) with hPbardef
  haveI hPbarPrime : Pbar.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  set A := R ⧸ p with hAdef
  haveI : IsDomain A := Ideal.Quotient.isDomain p
  -- The fiber ring identification `A[X] ≃+* R[X] ⧸ pR[X]`.
  have hCeq : p.map (Polynomial.C (R := R)) = pX := by
    rw [hpXdef, Polynomial.algebraMap_eq]
  set e2 : Polynomial A ≃+* (Polynomial R ⧸ pX) :=
    p.polynomialQuotientEquivQuotientPolynomial.trans (Ideal.quotEquivOfEq hCeq)
    with he2def
  have hcomm : ∀ r : R, e2 (Polynomial.C (Ideal.Quotient.mk p r)) =
      Ideal.Quotient.mk pX (Polynomial.C r) := by
    intro r
    have hs := Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk p (Polynomial.C r)
    rw [Polynomial.map_C] at hs
    have hfwd : p.polynomialQuotientEquivQuotientPolynomial
        (Polynomial.C (Ideal.Quotient.mk p r)) =
        Ideal.Quotient.mk _ (Polynomial.C r) := by
      rw [← hs, RingEquiv.apply_symm_apply]
    rw [he2def, RingEquiv.coe_trans, Function.comp_apply, hfwd, Ideal.quotEquivOfEq_mk]
  -- The fiber prime `Q ⊆ A[X]` and its basic properties.
  set Q : Ideal (Polynomial A) := Pbar.comap e2 with hQdef
  haveI hQPrime : Q.IsPrime := Ideal.comap_isPrime _ Pbar
  have hQheight : Q.height = Pbar.height := RingEquiv.height_comap e2 Pbar
  have hQmap : Pbar = Q.map (e2 : Polynomial A →+* (Polynomial R ⧸ pX)) := by
    have hcoe : Q = Pbar.comap (e2 : Polynomial A →+* (Polynomial R ⧸ pX)) :=
      Ideal.ext fun x => Iff.rfl
    rw [hcoe, Ideal.map_comap_of_surjective
      (e2 : Polynomial A →+* (Polynomial R ⧸ pX)) e2.surjective]
  -- Membership translation between `Q` and `P`.
  have hmem : ∀ r : R, Polynomial.C (Ideal.Quotient.mk p r) ∈ Q ↔ Polynomial.C r ∈ P := by
    intro r
    rw [hQdef, Ideal.mem_comap, hcomm, hPbardef, Ideal.mem_quotient_iff_mem hker_le]
  -- The contraction of `Q` to `A` is trivial.
  have hQA : Q.comap (algebraMap A (Polynomial A)) = ⊥ := by
    ext a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.mem_comap, Polynomial.algebraMap_eq, Submodule.mem_bot, hmem r,
      Ideal.Quotient.eq_zero_iff_mem]
    change Polynomial.C r ∈ P ↔ r ∈ p
    rw [hpdef, Ideal.mem_comap, Polynomial.algebraMap_eq]
  -- The `k`-algebra upgrade of `e2`.
  have he2c : ∀ c : k, e2 (algebraMap k (Polynomial A) c) =
      algebraMap k (Polynomial R ⧸ pX) c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k A (Polynomial A), Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply k R A, Ideal.Quotient.algebraMap_eq, hcomm,
      IsScalarTower.algebraMap_apply k (Polynomial R) (Polynomial R ⧸ pX),
      Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_apply k R (Polynomial R),
      Polynomial.algebraMap_eq]
  set e2alg : Polynomial A ≃ₐ[k] (Polynomial R ⧸ pX) := AlgEquiv.ofRingEquiv he2c
    with he2algdef
  -- The `k`-algebra identification of the residue algebras.
  have hQmapAlg : Pbar = Q.map (e2alg : Polynomial A →+* (Polynomial R ⧸ pX)) := by
    rw [hQmap]
    congr 1
  have gQuot : (Polynomial A ⧸ Q) ≃ₐ[k] (Polynomial R ⧸ P) := by
    refine (Ideal.quotientEquivAlg Q Pbar e2alg hQmapAlg).trans ?_
    refine AlgEquiv.ofRingEquiv (f := DoubleQuot.quotQuotEquivQuotOfLE hker_le) ?_
    intro c
    have hL : algebraMap k ((Polynomial R ⧸ pX) ⧸ Pbar) c =
        Ideal.Quotient.mk Pbar (Ideal.Quotient.mk pX (algebraMap k (Polynomial R) c)) := by
      rw [IsScalarTower.algebraMap_apply k (Polynomial R ⧸ pX)
          ((Polynomial R ⧸ pX) ⧸ Pbar),
        Ideal.Quotient.algebraMap_eq,
        IsScalarTower.algebraMap_apply k (Polynomial R) (Polynomial R ⧸ pX),
        Ideal.Quotient.algebraMap_eq]
    have hR : algebraMap k (Polynomial R ⧸ P) c =
        Ideal.Quotient.mk P (algebraMap k (Polynomial R) c) := by
      rw [IsScalarTower.algebraMap_apply k (Polynomial R) (Polynomial R ⧸ P),
        Ideal.Quotient.algebraMap_eq]
    rw [hL, hR]
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk (algebraMap k (Polynomial R) c) hker_le
  -- Case split on the fiber prime.
  by_cases hQ : Q = ⊥
  · -- Fiber prime trivial: heights agree, transcendence degree gains one.
    right
    have hPbarBot : Pbar = ⊥ := by rw [hQmap, hQ, Ideal.map_bot]
    haveI : Nontrivial (Polynomial R ⧸ pX) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (fun htop => hP.ne_top (top_le_iff.mp (htop ▸ hker_le)))
    constructor
    · rw [h00, hPbarBot, Ideal.height_bot, add_zero]
    · calc Algebra.trdeg k A + 1
          ≤ Algebra.trdeg k (Polynomial A) := trdeg_add_one_le_trdeg_polynomial A
        _ ≤ Algebra.trdeg k (Polynomial A ⧸ Q) := by
            rw [hQ]; exact trdeg_le_trdeg_quotient_bot _
        _ ≤ Algebra.trdeg k (Polynomial R ⧸ P) := trdeg_le_of_algEquiv gQuot
  · -- Fiber prime nontrivial: the height jumps by at least one.
    left
    have h1Q : 1 ≤ Q.height := by
      haveI : (⊥ : Ideal (Polynomial A)).IsPrime := Ideal.isPrime_bot
      have hlt : (⊥ : Ideal (Polynomial A)) < Q := bot_lt_iff_ne_bot.mpr hQ
      have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rwa [Ideal.height_bot, zero_add] at h
    constructor
    · rw [h00]
      gcongr
      exact le_trans h1Q (le_of_eq hQheight)
    · calc Algebra.trdeg k A
          ≤ Algebra.trdeg k (Polynomial A ⧸ Q) :=
            trdeg_le_trdeg_polynomial_quotient A Q hQA
        _ ≤ Algebra.trdeg k (Polynomial R ⧸ P) := trdeg_le_of_algEquiv gQuot

end PolynomialStep

section LemmaA

/-! ### Lemma A: the trdeg–height inequality at primes of polynomial rings -/

/-- **Lemma A (trdeg–height inequality in finite polynomial rings).** For a
field `k`, a finite index type `ι` and a prime ideal `P ⊆ k[xᵢ : i ∈ ι]`,
there is a natural number `d` with `d ≤ trdeg k (k[xᵢ] ⧸ P)` and
`#ι ≤ ht P + d`. (Classically `d` is the transcendence degree of the residue
field and both inequalities are equalities; the one-sided witness form is all
the regularity pipeline needs, and keeps the induction free of fraction
fields.) Induction on `ι` via `Finite.induction_empty_option` and the
one-variable step lemma `Polynomial.step_height_trdeg_of_isPrime`. -/
theorem MvPolynomial.exists_le_trdeg_and_natCard_le_height_add
    {k : Type u} [Field k] {ι : Type v} [Finite ι]
    (P : Ideal (MvPolynomial ι k)) (hP : P.IsPrime) :
    ∃ d : ℕ, (d : Cardinal) ≤ Algebra.trdeg k (MvPolynomial ι k ⧸ P) ∧
      (Nat.card ι : ℕ∞) ≤ P.height + d := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e IH =>
    haveI := hP
    set ψ := MvPolynomial.renameEquiv k e with hψdef
    set P₀ := P.comap ψ.toRingEquiv with hP₀def
    haveI hP₀p : P₀.IsPrime := Ideal.comap_isPrime _ P
    obtain ⟨d, hd, hht⟩ := IH P₀ hP₀p
    refine ⟨d, ?_, ?_⟩
    · refine le_trans hd (trdeg_quotient_le_of_forall_mem_iff ψ.toAlgHom P P₀ ?_)
      intro a
      rw [hP₀def, Ideal.mem_comap]
      exact Iff.rfl
    · have hh : P₀.height = P.height := by
        rw [hP₀def]
        exact RingEquiv.height_comap ψ.toRingEquiv P
      rw [← Nat.card_congr e]
      rwa [hh] at hht
  | h_empty =>
    exact ⟨0, by simp, by simp⟩
  | h_option IH =>
    rename_i α _
    haveI := hP
    set ψ : MvPolynomial (Option α) k ≃ₐ[k] Polynomial (MvPolynomial α k) :=
      MvPolynomial.optionEquivLeft k α with hψdef
    set P' : Ideal (Polynomial (MvPolynomial α k)) := P.comap ψ.symm.toRingEquiv
      with hP'def
    haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ P
    have hPheight : P'.height = P.height := by
      rw [hP'def]
      exact RingEquiv.height_comap ψ.symm.toRingEquiv P
    have htr : Algebra.trdeg k (Polynomial (MvPolynomial α k) ⧸ P') ≤
        Algebra.trdeg k (MvPolynomial (Option α) k ⧸ P) := by
      refine trdeg_quotient_le_of_forall_mem_iff ψ.symm.toAlgHom P P' ?_
      intro a
      rw [hP'def, Ideal.mem_comap]
      exact Iff.rfl
    set p : Ideal (MvPolynomial α k) :=
      P'.comap (algebraMap (MvPolynomial α k) (Polynomial (MvPolynomial α k))) with hpdef
    haveI hpp : p.IsPrime := Ideal.comap_isPrime _ P'
    obtain ⟨d, hd, hht⟩ := IH p hpp
    have hstep := Polynomial.step_height_trdeg_of_isPrime (k := k) P' hP'p
    have hcard : (Nat.card (Option α) : ℕ∞) = (Nat.card α : ℕ∞) + 1 := by
      rw [Finite.card_option]
      push_cast
      rfl
    rcases hstep with ⟨hh, ht⟩ | ⟨hh, ht⟩
    · -- Height jumped: keep the same witness `d`.
      refine ⟨d, ?_, ?_⟩
      · exact le_trans (le_trans hd ht) htr
      · rw [hcard]
        calc (Nat.card α : ℕ∞) + 1 ≤ (p.height + d) + 1 := by gcongr
          _ = (p.height + 1) + d := by
              rw [add_assoc, add_comm (d : ℕ∞) 1, ← add_assoc]
          _ ≤ P'.height + d := by gcongr
          _ = P.height + d := by rw [hPheight]
    · -- Transcendence degree jumped: use `d + 1`.
      refine ⟨d + 1, ?_, ?_⟩
      · push_cast
        refine le_trans ?_ (le_trans ht htr)
        gcongr
      · rw [hcard]
        push_cast
        calc (Nat.card α : ℕ∞) + 1 ≤ (p.height + d) + 1 := by gcongr
          _ = p.height + ((d : ℕ∞) + 1) := by rw [add_assoc]
          _ = P.height + ((d : ℕ∞) + 1) := by rw [← hPheight, hh]

end LemmaA

section LemmaB

/-! ### Lemma B: transfer to standard-smooth algebras -/

/-- **Lemma B (trdeg–height inequality for standard-smooth algebras).** For a
standard-smooth algebra `S` of relative dimension `n` over a field `k` and a
prime ideal `q ⊆ S`, there is `d : ℕ` with `d ≤ trdeg k (S ⧸ q)` and
`n ≤ ht q + d`. Pull `q` back along a submersive presentation
`P.Ring = k[xᵢ] ↠ S`, apply Lemma A to the pullback and Krull's height
theorem (`Ideal.height_le_height_add_spanFinrank_of_le`) to descend, exactly
as in the closed-point lemma `natCast_le_height_of_isMaximal` of
`Algebra/StandardSmoothDimension.lean`. -/
theorem Algebra.IsStandardSmoothOfRelativeDimension.exists_le_trdeg_and_natCast_le_height_add
    {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S] (n : ℕ)
    [H : Algebra.IsStandardSmoothOfRelativeDimension n k S]
    (q : Ideal S) (hq : q.IsPrime) :
    ∃ d : ℕ, (d : Cardinal) ≤ Algebra.trdeg k (S ⧸ q) ∧ (n : ℕ∞) ≤ q.height + d := by
  obtain ⟨ι, σ, hσ, hι, P, hPdim⟩ := H.out
  haveI := hq
  have hsurj : Function.Surjective (algebraMap P.Ring S) := P.algebraMap_surjective
  set M : Ideal P.Ring := q.comap (algebraMap P.Ring S) with hMdef
  haveI hM : M.IsPrime := Ideal.comap_isPrime _ q
  obtain ⟨d, hd, hA⟩ := MvPolynomial.exists_le_trdeg_and_natCard_le_height_add M hM
  refine ⟨d, ?_, ?_⟩
  · -- Transport trdeg along the induced embedding `P.Ring ⧸ M →ₐ[k] S ⧸ q`.
    set φ : P.Ring →ₐ[k] S ⧸ q :=
      (Ideal.Quotient.mkₐ k q).comp (IsScalarTower.toAlgHom k P.Ring S) with hφdef
    have hφker : ∀ a ∈ M, φ a = 0 := by
      intro a ha
      simp only [hφdef, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        IsScalarTower.coe_toAlgHom', Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    have hφqinj : Function.Injective (Ideal.Quotient.liftₐ M φ hφker) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk] at hx
      have h2 : φ r = 0 := hx
      rw [hφdef] at h2
      simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        IsScalarTower.coe_toAlgHom', Ideal.Quotient.eq_zero_iff_mem] at h2
      rw [Ideal.Quotient.eq_zero_iff_mem, hMdef]
      exact Ideal.mem_comap.mpr h2
    exact le_trans hd (trdeg_le_of_injective _ hφqinj)
  · -- Height bookkeeping (mirror of the closed-point proof).
    have hker_le : RingHom.ker (algebraMap P.Ring S) ≤ M := fun x hx => by
      rw [hMdef, Ideal.mem_comap, RingHom.mem_ker.mp hx]
      exact q.zero_mem
    have hbound := Ideal.height_le_height_add_spanFinrank_of_le hker_le
    set e := (algebraMap P.Ring S : P.Ring →+* S).quotientKerEquivOfSurjective hsurj
      with hedef
    have hMcomap : M = Ideal.comap (Ideal.Quotient.mk (RingHom.ker (algebraMap P.Ring S)))
        (Ideal.comap e q) := by
      ext x
      simp only [hMdef, Ideal.mem_comap]
      rw [hedef, RingHom.quotientKerEquivOfSurjective_apply_mk]
    have hqheight : (M.map (Ideal.Quotient.mk (RingHom.ker (algebraMap P.Ring S)))).height
        = q.height := by
      rw [hMcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        RingEquiv.height_comap]
    have hker_span : RingHom.ker (algebraMap P.Ring S) = Ideal.span (Set.range P.relation) :=
      P.span_range_relation_eq_ker.symm
    have hfr : (RingHom.ker (algebraMap P.Ring S)).spanFinrank ≤ Nat.card σ := by
      rw [hker_span]
      refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)) ?_
      calc (Set.range P.relation).ncard
          = (P.relation '' Set.univ).ncard := by rw [Set.image_univ]
        _ ≤ (Set.univ : Set σ).ncard := Set.ncard_image_le Set.finite_univ
        _ = Nat.card σ := Set.ncard_univ σ
    have hcards : n + Nat.card σ = Nat.card ι := by
      have hle : Nat.card σ ≤ Nat.card ι := Nat.card_le_card_of_injective P.map P.map_inj
      have hdim : Nat.card ι - Nat.card σ = n := hPdim
      omega
    have h1 : (Nat.card ι : ℕ∞) ≤ (q.height + d) + Nat.card σ := by
      calc (Nat.card ι : ℕ∞) ≤ M.height + d := hA
        _ ≤ ((M.map (Ideal.Quotient.mk (RingHom.ker (algebraMap P.Ring S)))).height
            + (RingHom.ker (algebraMap P.Ring S)).spanFinrank) + d := by gcongr
        _ ≤ (q.height + Nat.card σ) + d := by
            rw [hqheight]
            have hfr' : ((RingHom.ker (algebraMap P.Ring S)).spanFinrank : ℕ∞)
                ≤ (Nat.card σ : ℕ∞) := by exact_mod_cast hfr
            gcongr
        _ = (q.height + d) + Nat.card σ := by
            rw [add_assoc, add_comm (Nat.card σ : ℕ∞) (d : ℕ∞), ← add_assoc]
    rw [← hcards] at h1
    push_cast at h1
    exact (ENat.add_le_add_iff_right (by simp)).mp h1

end LemmaB
