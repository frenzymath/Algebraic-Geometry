/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorDatumRankOne
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Localization.BaseChange

/-!
# DAT-C C4 — the canonical-section normalization mono (N4/N5 + the local-basis companion)
(`informal/w4-datc-worksheet.md` §2 (N4)/(N5), GAP-3 companion)

This file provides the module-theoretic heart of the canonical-section normalization —
the deferred GAP-3 **Nakayama companion** (I-0253): a *given* fibrewise-nonzero element of
a rank-`1` finite projective module is a **Zariski-local basis** (the converse direction
of N3's generator production) — together with the DAT-A class law N4 for arbitrary
fibrewise-regular sections of the divisor datum.

* `Module.exists_notMem_bijective_toSpanSingleton` — **the Nakayama companion** (GAP-3
  companion, deferred from C2/I-0253): for a finite projective `B`-module `Q` of
  stalk-rank `1` at `p` and an element `q` nonzero in the fibre `Q ⊗ κ(p)`, there is a
  basic open `D(f) ∋ p` on which `x ↦ x • q` is a **bijection** `B_f → Q_f`, i.e. `q`
  is a local basis of `Q`.  Route: over the local ring `Rₚ` the localized module `Qₚ` is
  free of rank `1`; the fibre nonzeroness pins the basis coordinate of `q` to a unit, so
  `q` spans `Qₚ`; `PicardGroup`'s `bijective_of_surjective` (invertible target) upgrades
  spanning to bijectivity, and `Module.FinitePresentation.exists_notMem_bijective` spreads
  the stalk bijection to a basic open.
* `Module.exists_notMem_smul_eq_of_tmul_ne_zero` — **the local-rescaling corollary** (the
  N5 engine input): a second element `q'` lies in the `B_f`-span of the local basis `q`,
  so `q' = a • q` in `Q_f` for a scalar `a`.

Consumers: N5 (the relative uniqueness / mono engine) and the §3.2 chart mono
consume the local basis to rescale the two canonical sections by a unit
(the I-0231-safe route: invertibility of `H⁰`, never "fibrewise ⟹ relative").
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open scoped TensorProduct

namespace Module

variable {B : Type u} [CommRing B] {Q : Type u} [AddCommGroup Q] [Module B Q]

/-- **The Nakayama companion — a fibrewise-nonzero element is a Zariski-local basis**
(worksheet GAP-3 companion, deferred from C2/I-0253): for a finite projective `B`-module
`Q` of stalk-rank exactly `1` at the prime `p`, an element `q : Q` whose image in the
fibre `Q ⊗ κ(p)` is nonzero generates `Q` freely on a basic open `D(f) ∋ p`: the map
`x ↦ x • q` is a bijection `B_f → Q_f`.

Over the local ring `Rₚ` the localized module `Qₚ` is free of rank `1`, so `q`'s basis
coordinate `c` satisfies: if `c` were a non-unit it would lie in the maximal ideal, hence
`q` would vanish in the fibre `κ(p) ⊗ Qₚ ≅ Q ⊗ κ(p)`, contradicting `hq`. Thus `c` is a
unit and `q` spans `Qₚ`; `Module.Invertible`'s `bijective_of_surjective` promotes spanning
to a bijection, and the isomorphism spreads to a basic open. -/
theorem exists_notMem_bijective_toSpanSingleton
    [Module.Finite B Q] [Module.Projective B Q] (p : PrimeSpectrum B)
    (hrank : Module.rankAtStalk Q p = 1) (q : Q)
    (hq : (q ⊗ₜ[B] (1 : p.asIdeal.ResidueField) : Q ⊗[B] p.asIdeal.ResidueField) ≠ 0) :
    ∃ f : B, f ∉ p.asIdeal ∧ Function.Bijective
      (LocalizedModule.map (Submonoid.powers f) (LinearMap.toSpanSingleton B Q q)) := by
  classical
  haveI : Module.FinitePresentation B Q := Module.finitePresentation_of_projective B Q
  set Rₚ := Localization.AtPrime p.asIdeal with hRₚ
  set Qₚ := LocalizedModule p.asIdeal.primeCompl Q with hQₚ
  set mkq : Qₚ := LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q q with hmkq
  -- `Qₚ` is finite, flat and hence free of rank `1` over the local ring `Rₚ`
  haveI : Module.Free Rₚ Qₚ := Module.free_of_flat_of_isLocalRing
  have hrank1 : Module.finrank Rₚ Qₚ = 1 := hrank
  -- a basis of the free rank-`1` module, and the coordinate of `mkq`
  set b : Module.Basis Unit Rₚ Qₚ := Module.basisUnique Unit hrank1 with hb
  set c : Rₚ := b.repr mkq default with hc
  have hmkq_eq : mkq = c • b default := by
    have hsum := b.sum_repr mkq
    rw [Fintype.sum_unique, ← hc] at hsum
    exact hsum.symm
  -- `c` is a unit: otherwise `mkq` vanishes in the fibre, contradicting `hq`
  have hcunit : IsUnit c := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hcmem
    -- the fibre map `κ ⊗[Rₚ] Qₚ → κ ⊗[B] Q` sends `1 ⊗ mkq` to `1 ⊗ q`, injectively
    set κ := p.asIdeal.ResidueField with hκ
    set η : Qₚ ≃ₗ[Rₚ] Rₚ ⊗[B] Q := LocalizedModule.equivTensorProduct p.asIdeal.primeCompl Q
      with hη
    set ε : κ ⊗[Rₚ] Qₚ →ₗ[Rₚ] κ ⊗[B] Q :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange B Rₚ κ κ Q).toLinearMap.restrictScalars Rₚ
        ∘ₗ (η.lTensor κ).toLinearMap with hε
    have hηmkq : η mkq = (1 : Rₚ) ⊗ₜ[B] q := by
      rw [hη, hmkq, LocalizedModule.mkLinearMap_apply,
        LocalizedModule.equivTensorProduct_apply_mk, Localization.mk_one]
    have hεval : ε ((1 : κ) ⊗ₜ[Rₚ] mkq) = (1 : κ) ⊗ₜ[B] q := by
      simp only [hε, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
        LinearEquiv.lTensor_tmul, hηmkq,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    -- but `1 ⊗ mkq = 0` since `c ∈ maximalIdeal` kills the residue
    have hcres : c • (1 : κ) = 0 := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
      exact (IsLocalRing.residue_eq_zero_iff c).mpr hcmem
    have hzero : (1 : κ) ⊗ₜ[Rₚ] mkq = 0 := by
      rw [hmkq_eq, ← TensorProduct.smul_tmul, hcres, TensorProduct.zero_tmul]
    -- transport the vanishing to `Q ⊗ κ`, contradicting `hq`
    have h1q : (1 : κ) ⊗ₜ[B] q = 0 := by rw [← hεval, hzero, map_zero]
    exact hq (by
      rw [show (q ⊗ₜ[B] (1 : κ) : Q ⊗[B] κ)
          = TensorProduct.comm B κ Q ((1 : κ) ⊗ₜ[B] q) from rfl, h1q, map_zero])
  -- `mkq` spans `Qₚ` (unit multiple of a basis element), so `toSpanSingleton` is surjective
  haveI hinv : Module.Invertible Rₚ Qₚ :=
    Module.Invertible.congr ((Module.nonempty_linearEquiv_of_finrank_eq_one hrank1).some)
  have hspanmkq : Submodule.span Rₚ {mkq} = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← b.span_eq, Set.range_unique, Submodule.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe]
    refine Submodule.mem_span_singleton.mpr ⟨(hcunit.unit⁻¹ : Rₚˣ).val, ?_⟩
    rw [hmkq_eq, smul_smul, hcunit.val_inv_mul, one_smul]
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton Rₚ Qₚ mkq) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton]; exact hspanmkq
  have hbijR : Function.Bijective (LinearMap.toSpanSingleton Rₚ Qₚ mkq) :=
    Module.Invertible.bijective_of_surjective hsurj
  -- identify the stalk of `toSpanSingleton` with `toSpanSingleton` over `Rₚ`
  have hmapeq : IsLocalizedModule.map p.asIdeal.primeCompl (Algebra.linearMap B Rₚ)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q) (LinearMap.toSpanSingleton B Q q)
      = (LinearMap.toSpanSingleton Rₚ Qₚ mkq).restrictScalars B := by
    refine IsLocalizedModule.ext p.asIdeal.primeCompl (Algebra.linearMap B Rₚ)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q)) ?_
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, IsLocalizedModule.map_apply]
    simp only [LinearMap.toSpanSingleton_apply, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply, map_smul, ← hmkq]
    exact algebra_compatible_smul Rₚ x mkq
  have hstalk : Function.Bijective (IsLocalizedModule.map p.asIdeal.primeCompl
      (Algebra.linearMap B Rₚ) (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q)
      (LinearMap.toSpanSingleton B Q q)) := by
    rw [hmapeq]; exact hbijR
  exact Module.FinitePresentation.exists_notMem_bijective (LinearMap.toSpanSingleton B Q q)
    p.asIdeal (Algebra.linearMap B Rₚ)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q) hstalk

/-- A fibrewise-nonzero element of a finite projective module of constant stalk rank one
is a global basis.  The local basis neighbourhoods supplied by
`exists_notMem_bijective_toSpanSingleton` cover `Spec B`: if their generators failed to
span the unit ideal, a maximal ideal containing that span would contain the generator
chosen at its own prime.  Bijectivity then descends from this standard-open cover. -/
theorem bijective_toSpanSingleton_of_forall_tmul_ne_zero
    [Module.Finite B Q] [Module.Projective B Q]
    (hrank : ∀ p : PrimeSpectrum B, Module.rankAtStalk Q p = 1)
    (q : Q)
    (hq : ∀ p : PrimeSpectrum B,
      (q ⊗ₜ[B] (1 : p.asIdeal.ResidueField) :
        Q ⊗[B] p.asIdeal.ResidueField) ≠ 0) :
    Function.Bijective (LinearMap.toSpanSingleton B Q q) := by
  classical
  let f : PrimeSpectrum B → B := fun p ↦
    (exists_notMem_bijective_toSpanSingleton p (hrank p) q (hq p)).choose
  have hf (p : PrimeSpectrum B) : f p ∉ p.asIdeal :=
    (exists_notMem_bijective_toSpanSingleton p (hrank p) q (hq p)).choose_spec.1
  have hbij (p : PrimeSpectrum B) : Function.Bijective
      (LocalizedModule.map (Submonoid.powers (f p))
        (LinearMap.toSpanSingleton B Q q)) :=
    (exists_notMem_bijective_toSpanSingleton p (hrank p) q (hq p)).choose_spec.2
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum B := ⟨m, hm.isPrime⟩
    exact hf p (hle (Ideal.subset_span (Set.mem_range_self p)))
  refine bijective_of_localized_span (Set.range f) hspan
    (LinearMap.toSpanSingleton B Q q) ?_
  rintro ⟨r, p, rfl⟩
  exact hbij p

/-- Two fibrewise-nonzero elements of a finite projective module of constant stalk rank
one differ by a unique unit.  This is the choice-independence form consumed by the
rank-one divisor construction. -/
theorem existsUnique_unit_smul_of_forall_tmul_ne_zero
    [Module.Finite B Q] [Module.Projective B Q]
    (hrank : ∀ p : PrimeSpectrum B, Module.rankAtStalk Q p = 1)
    (q q' : Q)
    (hq : ∀ p : PrimeSpectrum B,
      (q ⊗ₜ[B] (1 : p.asIdeal.ResidueField) :
        Q ⊗[B] p.asIdeal.ResidueField) ≠ 0)
    (hq' : ∀ p : PrimeSpectrum B,
      (q' ⊗ₜ[B] (1 : p.asIdeal.ResidueField) :
        Q ⊗[B] p.asIdeal.ResidueField) ≠ 0) :
    ∃! u : Bˣ, q' = (u : B) • q := by
  let e : B ≃ₗ[B] Q := LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton B Q q)
    (bijective_toSpanSingleton_of_forall_tmul_ne_zero hrank q hq)
  let a : B := e.symm q'
  have ha : q' = a • q := by
    rw [← LinearMap.toSpanSingleton_apply]
    exact (e.apply_symm_apply q').symm
  have hqbij := bijective_toSpanSingleton_of_forall_tmul_ne_zero hrank q hq
  have hq'bij := bijective_toSpanSingleton_of_forall_tmul_ne_zero hrank q' hq'
  obtain ⟨b, hb⟩ := hq'bij.2 q
  have hab : a * b = 1 := by
    apply hqbij.1
    rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply, one_smul]
    rw [mul_comm, mul_smul, ← ha, ← LinearMap.toSpanSingleton_apply]
    exact hb
  let u : Bˣ := ⟨a, b, hab, by rw [mul_comm, hab]⟩
  refine ⟨u, ha, fun v hv ↦ ?_⟩
  apply Units.ext
  apply hqbij.1
  simpa only [LinearMap.toSpanSingleton_apply] using hv.symm.trans ha

/-- **The local-rescaling corollary** (the N5 engine input): with `q` a local basis at
`p` (rank `1`, fibrewise nonzero), any second element `q'` lies in the `B_f`-span of `q`,
so `q'` equals `a • q` in the away localization `Q_f` for a scalar `a : Localization.Away f`.
This is the mechanism by which two fibrewise-nonzero sections of an invertible `H⁰` differ,
Zariski-locally, by a scalar rescaling — and, when `q'` is itself fibrewise nonzero, by a
**unit** rescaling (a `DivEq` move). -/
theorem exists_notMem_smul_eq_of_tmul_ne_zero
    [Module.Finite B Q] [Module.Projective B Q] (p : PrimeSpectrum B)
    (hrank : Module.rankAtStalk Q p = 1) (q q' : Q)
    (hq : (q ⊗ₜ[B] (1 : p.asIdeal.ResidueField) : Q ⊗[B] p.asIdeal.ResidueField) ≠ 0) :
    ∃ f : B, f ∉ p.asIdeal ∧ ∃ a : Localization.Away f,
      (LocalizedModule.mk q' 1 : LocalizedModule.Away f Q) = a • LocalizedModule.mk q 1 := by
  obtain ⟨f, hf, hbij⟩ := exists_notMem_bijective_toSpanSingleton p hrank q hq
  obtain ⟨y, hy⟩ := hbij.surjective (LocalizedModule.mk q' 1)
  induction y using LocalizedModule.induction_on with
  | h r s =>
    refine ⟨f, hf, Localization.mk r s, ?_⟩
    rw [← hy, LocalizedModule.mk_smul_mk, mul_one, LocalizedModule.map_mk,
      LinearMap.toSpanSingleton_apply]

end Module

namespace AlgebraicGeometry

open CategoryTheory Opposite AlgebraicJacobian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {S : Type u} [CommRing S] [Algebra k S]
variable {π : C.left ⟶ P1 k} [IsFinite π] {n : ℕ}

/-! ## (N4) — sections cut divisors of the family's class -/

/-- **(N4) Sections cut divisors — DAT-A consumed on the nose** (worksheet §2 (N4)): for a
certified divisor family `G` over the Noetherian test `S` and ANY fibrewise-regular global
section `s` of the divisor datum `D_G := G.adaptation.divisorDatum`, the `LocalEquations`
family cut by `s` (`sectionLocalEquationsOfFibrewiseRegular`) has Čech Picard class exactly
`G.eqns.picClass` — the DAT-A class law composed with the divisor-datum class law
`cechPicClass_divisorDatum` (C0). Any two fibrewise-regular sections therefore cut families
of the *same* class; the finer `DivEq` refinement is N5. -/
theorem CertifiedDivisorFamily.picClass_sectionLocalEquationsOfFibrewiseRegular
    [IsNoetherianRing S] (G : CertifiedDivisorFamily C S π n)
    (s : ↥(gluedSubmodule S G.adaptation.divisorDatum.pieces
      G.adaptation.divisorDatum.unit ⊤))
    (hfib : ∀ (j : G.adaptation.divisorDatum.index) (p : PrimeSpectrum S), Function.Injective
      ((Scheme.mulSectionEnd S (G.adaptation.divisorDatum.component s j)).rTensor
        p.asIdeal.ResidueField)) :
    (G.adaptation.divisorDatum.sectionLocalEquationsOfFibrewiseRegular s hfib).picClass
      = G.eqns.picClass := by
  rw [G.adaptation.divisorDatum.sectionLocalEquationsOfFibrewiseRegular_picClass s hfib,
    G.adaptation.cechPicClass_divisorDatum]

end AlgebraicGeometry
