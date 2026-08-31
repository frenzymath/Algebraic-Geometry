/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.LocalEquationsPullback
import AlgebraicJacobian.RiemannRoch.DegreeBaseChange
import AlgebraicJacobian.RiemannRoch.DegreePullbackDictionary
import AlgebraicJacobian.Cohomology.Finiteness

/-!
# EV-3: the fiber sum `Σ e·f = n` under a finite morphism (E-v campaign, Lane B)

For a finite morphism `f : X ⟶ Y` of curve bundles over a field `K` (compatible with the
structure morphisms, generic point to generic point), this file proves the fiber-sum
identity **EV-3** of the E-v campaign (`informal/w7-ev-worksheet.md` §2):

**`sum_ordZ_residueDeg_of_isFinite`**: for a chart `V ∋ η_Y` carrying a section `t` of
order `1` at a single closed point `y` (a tracked uniformizer) and a finite set `S`
exhausting the non-unit locus of the pulled section `f^♯ t`,

`∑_{z ∈ S} ord_z(f^♯ g) · [κ(z) : K] = [K(X) : K(Y)] · [κ(y) : K]`.

Pinned route: `(t) = p_y` in the Dedekind chart (the order-1 hypothesis pins the
factorization), hence `(f^♯ t) = p_y · Γ(X, f ⁻¹ᵁ V)`; each `S`-term is
`e·f · [κ(y) : K]` by the chart dictionary (`toAdd_ordZ_eq_count_factors`, the
ramification bridges `ramificationIdx_eq_ramificationIdx'`/`inertiaDeg_eq_inertiaDeg'`
and the residue tower `K → Γ(Y,V)/p_y → Γ(X,f⁻¹ᵁV)/q_z` through the
`appLE_overAlgebraMap` seam); the reindex `S ↔ p_y.primesOver` is a
`Finset.sum_bij_ne_zero` (the SB-3b skeleton), and the mathlib gift
`Ideal.sum_ramification_inertia_eq_finrank` plus EV-2
(`RiemannRoch/DegreePullbackDictionary.lean`) close the sum.

All `f`-dependent algebra structures are the named towers of the dictionary file
(R-EV-1 discipline).  The ladder assembly EV-4 consuming this keystone is
`RiemannRoch/DegreePullback.lean` (the file split is the ratified `> 500L` clause).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open UniqueFactorizationMonoid

namespace AlgebraicGeometry

attribute [local instance] Scheme.overSectionsAlgebra Scheme.residueFieldOverModule

/-! ## EV-3: the fiber sum `Σ e·f = n`, in chart form -/

section FiberSum

variable (K : Type u) [Field K] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))] [IsIntegral Y]

/-- **EV-3, the fiber-degree identity of the E-v campaign** (`w7-ev-worksheet.md` §2,
the (†)-mirror): let `f : X ⟶ Y` be a finite morphism of curve bundles over `K`
(compatible with the structure morphisms, generic point to generic point), `V ∋ η_Y` an
affine chart carrying a section `t` whose germ at `η` underlies the unit `g : K(Y)ˣ`,
with `ord_y(g) = 1` at a closed point `y ∈ V` and `t` a unit at every other closed point
of `V`; let `S` be a finite set of closed points of `f ⁻¹ᵁ V` outside which the pulled
section `f^♯ t` is a unit.  Then

`∑_{z ∈ S} ord_z(f^♯ g) · [κ(z) : K] = [K(X) : K(Y)] · [κ(y) : K]`.

The hypotheses force `S` to exhaust the fiber of `y` up to order-zero terms; each term
is `e_z · f_z · [κ(y) : K]`, and `Σ e·f = [K(X) : K(Y)]` by
`Ideal.sum_ramification_inertia_eq_finrank` + EV-2. -/
theorem sum_ordZ_residueDeg_of_isFinite (f : X ⟶ Y) [IsFinite f]
    (hcomp : f ≫ (Y ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K))
    (hf : f.base (genericPoint X) = genericPoint Y)
    {V : Y.Opens} (hV : IsAffineOpen V) (hη : genericPoint Y ∈ V)
    {t : Γ(Y, V)} (g : Y.functionFieldˣ)
    (hg : (g : Y.functionField) = (Y.presheaf.germ V (genericPoint Y) hη).hom t)
    {y : Y} (hyg : y ≠ genericPoint Y) (hyV : y ∈ V)
    (hordy : Scheme.ordZ (Y ↘ Spec (CommRingCat.of K)) hyg g
      = Multiplicative.ofAdd (1 : ℤ))
    (hunit : ∀ (z : Y) (hz : z ∈ V), z ≠ y →
      IsUnit ((Y.presheaf.germ V z hz).hom t))
    (S : Finset {z : X // z ≠ genericPoint X})
    (hSV : ∀ p ∈ S, p.1 ∈ f ⁻¹ᵁ V)
    (hout : ∀ (z : X) (hz : z ∈ f ⁻¹ᵁ V) (hzg : z ≠ genericPoint X),
      (⟨z, hzg⟩ : {z : X // z ≠ genericPoint X}) ∉ S →
        IsUnit ((X.presheaf.germ (f ⁻¹ᵁ V) z hz).hom
          ((f.appLE V (f ⁻¹ᵁ V) le_rfl).hom t))) :
    letI := f.functionFieldAlgebra hf
    ∑ p ∈ S, Multiplicative.toAdd
        (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2 (f.functionFieldMapUnits hf g))
        * (X.residueDeg K p.1 : ℤ)
      = (Module.finrank Y.functionField X.functionField : ℤ)
        * (Y.residueDeg K y : ℤ) := by
  classical
  letI := f.functionFieldAlgebra hf
  letI := f.pullbackSectionsAlgebra V
  -- chart setup
  have hηW : genericPoint X ∈ f ⁻¹ᵁ V := by
    change f.base (genericPoint X) ∈ V
    rw [hf]
    exact hη
  haveI : Nonempty V := ⟨⟨_, hη⟩⟩
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨_, hηW⟩⟩
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  haveI hDedY : IsDedekindDomain Γ(Y, V) := isDedekindDomain_section K hV hη
  haveI hDedX : IsDedekindDomain Γ(X, f ⁻¹ᵁ V) := isDedekindDomain_section K hW hηW
  haveI := f.moduleFinite_pullbackSections hV
  haveI := f.faithfulSMul_pullbackSections hf hη
  -- the `K`-structure tower through the pulled chart (the `appLE_overAlgebraMap` seam)
  haveI : IsScalarTower K Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (f.appLE_overAlgebraMap hcomp (le_rfl : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V) c).symm
  -- the pulled section and its unit
  have happ : f.appLE V (f ⁻¹ᵁ V) le_rfl = f.app V := Scheme.Hom.appLE_eq_app f
  set t' : Γ(X, f ⁻¹ᵁ V) := (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom t with ht'def
  set g' : X.functionFieldˣ := f.functionFieldMapUnits hf g with hg'def
  have hg₂ : (g' : X.functionField)
      = (X.presheaf.germ (f ⁻¹ᵁ V) (genericPoint X) hηW).hom t' := by
    rw [hg'def, Scheme.Hom.coe_functionFieldMapUnits, hg,
      f.functionFieldMap_germ hf V hη hηW t, ht'def, happ]
  have ht0 : t ≠ 0 := fun h0 => g.ne_zero (by rw [hg, h0, map_zero])
  have ht'0 : t' ≠ 0 := fun h0 => g'.ne_zero (by rw [hg₂, h0, map_zero])
  -- the tracked prime downstairs
  set py : Ideal Γ(Y, V) := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal with hpydef
  have hpy0 : py ≠ ⊥ := hV.primeIdealOf_ne_bot hyV hyg
  haveI hpyp : py.IsPrime := (hV.primeIdealOf ⟨y, hyV⟩).isPrime
  haveI hpym : py.IsMaximal := hpyp.isMaximal hpy0
  -- (i) the tracked section cuts out exactly the tracked prime
  have hcount1 : Multiset.count py (factors (Ideal.span {t})) = 1 := by
    have h := toAdd_ordZ_eq_count_factors K hV hη hyV hyg ht0 g hg
    rw [hordy, toAdd_ofAdd] at h
    exact_mod_cast h.symm
  have hall : ∀ P ∈ factors (Ideal.span {t}), P = py := by
    intro P hP
    obtain ⟨hPp, hP0, htP⟩ := prime_factor_span t (Multiset.mem_toFinset.mpr hP)
    haveI := hPp
    have hzV : hV.fromSpec.base ⟨P, hPp⟩ ∈ V := hV.fromSpec_base_mem _
    have hq : hV.primeIdealOf ⟨hV.fromSpec.base ⟨P, hPp⟩, hzV⟩ = ⟨P, hPp⟩ :=
      hV.primeIdealOf_fromSpec_base _
    by_cases hzy : hV.fromSpec.base ⟨P, hPp⟩ = y
    · have hsub : (⟨hV.fromSpec.base ⟨P, hPp⟩, hzV⟩ : V) = ⟨y, hyV⟩ := Subtype.ext hzy
      calc P = (hV.primeIdealOf ⟨hV.fromSpec.base ⟨P, hPp⟩, hzV⟩).asIdeal :=
            (congrArg PrimeSpectrum.asIdeal hq).symm
        _ = py := by rw [hsub]
    · exfalso
      have hmem' : t ∈ (hV.primeIdealOf ⟨hV.fromSpec.base ⟨P, hPp⟩, hzV⟩).asIdeal := by
        rw [congrArg PrimeSpectrum.asIdeal hq]
        exact htP
      exact (not_isUnit_germ_iff_mem hV hzV t).mpr hmem' (hunit _ hzV hzy)
  have hrepl := Multiset.eq_replicate_of_mem hall
  have hcard : Multiset.card (factors (Ideal.span {t})) = 1 := by
    have h2 : Multiset.count py (Multiset.replicate
        (Multiset.card (factors (Ideal.span {t}))) py) = 1 := by
      rw [← hrepl]
      exact hcount1
    rwa [Multiset.count_replicate_self] at h2
  have hspan : Ideal.span {t} = py := by
    have hsne : Ideal.span {t} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using ht0
    have hassoc := factors_prod hsne
    rw [hrepl, hcard, Multiset.replicate_one, Multiset.prod_singleton] at hassoc
    exact (associated_iff_eq.mp hassoc).symm
  -- (ii) the pulled section cuts out the pulled ideal
  have hmapspan : Ideal.span {t'} = Ideal.map (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) py := by
    rw [← hspan, Ideal.map_span, Set.image_singleton]
    rfl
  have hmap0 : Ideal.map (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) py ≠ ⊥ := by
    rw [← hmapspan]
    simpa [Ideal.span_singleton_eq_bot] using ht'0
  -- the lying-over certificate at a vanishing point of `f^♯ t`
  have hLies : ∀ (Q : Ideal Γ(X, f ⁻¹ᵁ V)), Q.IsPrime → t' ∈ Q → Q.LiesOver py := by
    intro Q hQp htQ
    have hle : Ideal.map (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) py ≤ Q := by
      rw [← hmapspan, Ideal.span_le, Set.singleton_subset_iff]
      exact htQ
    have hle' : py ≤ Q.comap (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) :=
      Ideal.map_le_iff_le_comap.mp hle
    have hne : Q.comap (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) ≠ ⊤ :=
      Ideal.comap_ne_top _ hQp.ne_top
    exact ⟨hpym.eq_of_le hne hle'⟩
  -- non-unit points of `f^♯ t` in `S` lie in the support
  have hmemQ : ∀ (p : {z : X // z ≠ genericPoint X}) (hp : p ∈ S),
      Multiplicative.toAdd
        (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2 g') ≠ 0 →
      t' ∈ (hW.primeIdealOf ⟨p.1, hSV p hp⟩).asIdeal := by
    intro p hp hne
    refine (not_isUnit_germ_iff_mem hW (hSV p hp) t').mp fun hu => ?_
    exact hne (toAdd_ordZ_eq_zero_of_isUnit_germ K hηW (hSV p hp) p.2 g' hg₂ hu)
  -- the order/ramification dictionary at a point over `y`
  have hcnt : ∀ (z : X) (hzW : z ∈ f ⁻¹ᵁ V) (hzg : z ≠ genericPoint X),
      ((hW.primeIdealOf ⟨z, hzW⟩).asIdeal).LiesOver py →
      Multiplicative.toAdd (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hzg g')
        = ((hW.primeIdealOf ⟨z, hzW⟩).asIdeal.ramificationIdx' Γ(Y, V) : ℤ) := by
    intro z hzW hzg hLO
    haveI := hLO
    haveI hQp : ((hW.primeIdealOf ⟨z, hzW⟩).asIdeal).IsPrime :=
      (hW.primeIdealOf ⟨z, hzW⟩).isPrime
    have hQ0 : (hW.primeIdealOf ⟨z, hzW⟩).asIdeal ≠ ⊥ := hW.primeIdealOf_ne_bot hzW hzg
    have h1 : Multiset.count ((hW.primeIdealOf ⟨z, hzW⟩).asIdeal)
        (factors (Ideal.span {t'}))
        = Ideal.ramificationIdx py (hW.primeIdealOf ⟨z, hzW⟩).asIdeal := by
      rw [hmapspan]
      exact (Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count hmap0 hQp hQ0).symm
    have h2 : Ideal.ramificationIdx py (hW.primeIdealOf ⟨z, hzW⟩).asIdeal
        = (hW.primeIdealOf ⟨z, hzW⟩).asIdeal.ramificationIdx' Γ(Y, V) :=
      Ideal.ramificationIdx_eq_ramificationIdx' py _ hpy0
    rw [toAdd_ordZ_eq_count_factors K hW hηW hzW hzg ht'0 g' hg₂, h1, h2]
  -- the residue tower at a point over `y`
  have hres : ∀ (z : X) (hzW : z ∈ f ⁻¹ᵁ V) (hzg : z ≠ genericPoint X),
      ((hW.primeIdealOf ⟨z, hzW⟩).asIdeal).LiesOver py →
      X.residueDeg K z
        = (hW.primeIdealOf ⟨z, hzW⟩).asIdeal.inertiaDeg' Γ(Y, V)
          * Y.residueDeg K y := by
    intro z hzW hzg hLO
    haveI := hLO
    haveI hQp : ((hW.primeIdealOf ⟨z, hzW⟩).asIdeal).IsPrime :=
      (hW.primeIdealOf ⟨z, hzW⟩).isPrime
    have hQ0 : (hW.primeIdealOf ⟨z, hzW⟩).asIdeal ≠ ⊥ := hW.primeIdealOf_ne_bot hzW hzg
    haveI hQm : ((hW.primeIdealOf ⟨z, hzW⟩).asIdeal).IsMaximal := hQp.isMaximal hQ0
    letI : Field (Γ(Y, V) ⧸ py) := Ideal.Quotient.field py
    have h1 : X.residueDeg K z
        = Module.finrank K (Γ(X, f ⁻¹ᵁ V) ⧸ (hW.primeIdealOf ⟨z, hzW⟩).asIdeal) :=
      (finrank_quotient_primeIdealOf K hW hzW hzg).symm
    have h2 : Y.residueDeg K y = Module.finrank K (Γ(Y, V) ⧸ py) :=
      (finrank_quotient_primeIdealOf K hV hyV hyg).symm
    have h3 := Module.finrank_mul_finrank K (Γ(Y, V) ⧸ py)
      (Γ(X, f ⁻¹ᵁ V) ⧸ (hW.primeIdealOf ⟨z, hzW⟩).asIdeal)
    have h4 : Ideal.inertiaDeg py (hW.primeIdealOf ⟨z, hzW⟩).asIdeal
        = Module.finrank (Γ(Y, V) ⧸ py)
            (Γ(X, f ⁻¹ᵁ V) ⧸ (hW.primeIdealOf ⟨z, hzW⟩).asIdeal) :=
      Ideal.inertiaDeg_algebraMap py _
    have h5 : Ideal.inertiaDeg py (hW.primeIdealOf ⟨z, hzW⟩).asIdeal
        = (hW.primeIdealOf ⟨z, hzW⟩).asIdeal.inertiaDeg' Γ(Y, V) :=
      Ideal.inertiaDeg_eq_inertiaDeg' py _
    rw [h1, ← h3, ← h2, ← h4, h5, Nat.mul_comm]
  -- the gift: `Σ e·f = finrank` over the primes over `p_y`
  haveI : Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := inferInstance
  have hgift := Ideal.sum_ramification_inertia_eq_finrank py Γ(X, f ⁻¹ᵁ V)
  -- EV-2: the chart rank is the function-field degree
  have hEV2 : Module.finrank Y.functionField X.functionField
      = Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
    f.finrank_functionField_eq_finrank_pullbackSections hf hV hη
  -- the reindex `S ↔ primesOver` and the close
  calc ∑ p ∈ S, Multiplicative.toAdd
        (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2 g')
        * (X.residueDeg K p.1 : ℤ)
      = ∑ q : py.primesOver Γ(X, f ⁻¹ᵁ V),
          ((q.1.ramificationIdx' Γ(Y, V) * q.1.inertiaDeg' Γ(Y, V) : ℕ) : ℤ)
            * (Y.residueDeg K y : ℤ) := by
        refine Finset.sum_bij_ne_zero
          (i := fun p hp hne => ⟨(hW.primeIdealOf ⟨p.1, hSV p hp⟩).asIdeal,
            (hW.primeIdealOf ⟨p.1, hSV p hp⟩).isPrime,
            hLies _ (hW.primeIdealOf ⟨p.1, hSV p hp⟩).isPrime
              (hmemQ p hp (left_ne_zero_of_mul hne))⟩)
          ?_ ?_ ?_ ?_
        · -- membership
          intro p h₁ h₂
          exact Finset.mem_univ _
        · -- injectivity
          intro p₁ h₁₁ h₁₂ p₂ h₂₁ h₂₂ heq
          have hids : (hW.primeIdealOf ⟨p₁.1, hSV p₁ h₁₁⟩).asIdeal
              = (hW.primeIdealOf ⟨p₂.1, hSV p₂ h₂₁⟩).asIdeal :=
            congrArg Subtype.val heq
          have h1 := hW.fromSpec_primeIdealOf ⟨p₁.1, hSV p₁ h₁₁⟩
          have h2 := hW.fromSpec_primeIdealOf ⟨p₂.1, hSV p₂ h₂₁⟩
          refine Subtype.ext ?_
          rw [← h1, ← h2]
          exact congrArg hW.fromSpec.base (PrimeSpectrum.ext hids)
        · -- surjectivity: every prime over `p_y` comes from a point of `S`
          intro q _ hqne
          obtain ⟨Q, hQmem⟩ := q
          have hQp : Q.IsPrime := hQmem.1
          haveI hQlies : Q.LiesOver py := hQmem.2
          haveI := hQp
          have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpy0 Q
          have hzW : hW.fromSpec.base ⟨Q, hQp⟩ ∈ f ⁻¹ᵁ V := hW.fromSpec_base_mem _
          have hzg : hW.fromSpec.base ⟨Q, hQp⟩ ≠ genericPoint X :=
            hW.fromSpec_base_ne_genericPoint hQ0
          have hq : hW.primeIdealOf ⟨hW.fromSpec.base ⟨Q, hQp⟩, hzW⟩ = ⟨Q, hQp⟩ :=
            hW.primeIdealOf_fromSpec_base _
          have htQ : t' ∈ Q := by
            have hle : Ideal.map (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) py ≤ Q := by
              rw [Ideal.over_def Q py]
              exact Ideal.map_comap_le
            rw [← hmapspan] at hle
            exact hle (Ideal.mem_span_singleton_self t')
          have hnu : ¬ IsUnit ((X.presheaf.germ (f ⁻¹ᵁ V)
              (hW.fromSpec.base ⟨Q, hQp⟩) hzW).hom t') := by
            refine (not_isUnit_germ_iff_mem hW hzW t').mpr ?_
            rw [congrArg PrimeSpectrum.asIdeal hq]
            exact htQ
          have hzS : (⟨hW.fromSpec.base ⟨Q, hQp⟩, hzg⟩ :
              {z : X // z ≠ genericPoint X}) ∈ S := by
            by_contra hn
            exact hnu (hout _ hzW hzg hn)
          have hLO' : ((hW.primeIdealOf ⟨hW.fromSpec.base ⟨Q, hQp⟩, hzW⟩).asIdeal).LiesOver
              py := by
            rw [congrArg PrimeSpectrum.asIdeal hq]
            exact hQlies
          refine ⟨⟨hW.fromSpec.base ⟨Q, hQp⟩, hzg⟩, hzS, ?_, ?_⟩
          · -- the term at the point is nonzero
            have hcz := hcnt _ hzW hzg hLO'
            have hpos : (hW.primeIdealOf
                ⟨hW.fromSpec.base ⟨Q, hQp⟩, hzW⟩).asIdeal.ramificationIdx' Γ(Y, V) ≠ 0 := by
              haveI := hLO'
              exact (Ideal.ramificationIdx'_pos _ Γ(Y, V)).ne'
            refine mul_ne_zero ?_ ?_
            · rw [hcz]
              exact_mod_cast hpos
            · exact_mod_cast (Scheme.residueDeg_pos hzg).ne'
          · -- the produced point maps back to `q`
            exact Subtype.ext (congrArg PrimeSpectrum.asIdeal hq)
        · -- values: each term is `e·f · [κ(y) : K]`
          intro p h₁ h₂
          have hLO : ((hW.primeIdealOf ⟨p.1, hSV p h₁⟩).asIdeal).LiesOver py :=
            hLies _ (hW.primeIdealOf ⟨p.1, hSV p h₁⟩).isPrime
              (hmemQ p h₁ (left_ne_zero_of_mul h₂))
          -- strip the subtype packaging (whose membership proof depends on `h₂`)
          change Multiplicative.toAdd
              (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2 g')
              * (X.residueDeg K p.1 : ℤ)
            = (((hW.primeIdealOf ⟨p.1, hSV p h₁⟩).asIdeal.ramificationIdx' Γ(Y, V)
                * (hW.primeIdealOf ⟨p.1, hSV p h₁⟩).asIdeal.inertiaDeg' Γ(Y, V) : ℕ) : ℤ)
              * (Y.residueDeg K y : ℤ)
          rw [hcnt p.1 (hSV p h₁) p.2 hLO, hres p.1 (hSV p h₁) p.2 hLO]
          push_cast
          ring
    _ = ((∑ q : py.primesOver Γ(X, f ⁻¹ᵁ V),
          q.1.ramificationIdx' Γ(Y, V) * q.1.inertiaDeg' Γ(Y, V) : ℕ) : ℤ)
            * (Y.residueDeg K y : ℤ) := by
        rw [← Finset.sum_mul]
        push_cast
        rfl
    _ = (Module.finrank Y.functionField X.functionField : ℤ)
        * (Y.residueDeg K y : ℤ) := by
        rw [hgift, ← hEV2]

end FiberSum

end AlgebraicGeometry
