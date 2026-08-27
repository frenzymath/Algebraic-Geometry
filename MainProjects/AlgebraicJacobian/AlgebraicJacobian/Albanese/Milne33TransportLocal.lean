/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import AlgebraicJacobian.Albanese.AuslanderBuchsbaum
import AlgebraicJacobian.Albanese.Milne33CMEquidim
import AlgebraicJacobian.Albanese.Milne33KernelGen

/-!
# Milne Lemma 3.3, transport helpers: coheight strictness, the Krull count, the
generic-value bridge, Jacobson density on locally closed sets

Support layer for the 4b-transport (`Albanese/Milne33Transport.lean`) and the
final assembly (`Albanese/Milne33.lean`), per `informal/m33-spec.md` (D5/D6).

* `AlgebraicGeometry.Scheme.coheight_add_one_le_of_specializes` — coheight
  strict monotonicity along a non-trivial specialisation of scheme points
  (`a ⤳ b`, `a ≠ b` gives `coheight a + 1 ≤ coheight b`), and the corollary
  `one_le_coheight_of_ne_genericPoint`.
* `RingTheory.CohenMacaulay.ringKrullDim_le_length_add_one_of_forall_le_isPrime`
  — **the Krull codimension count** of spec D5(c): in a Cohen–Macaulay local
  ring, if the only prime containing `ofList xs ⊔ J` (with `J` a height-one
  prime) is the maximal ideal, then `dim R ≤ |xs| + 1`. Combines Krull's
  height theorem (`ringKrullDim_le_ringKrullDim_quotient_add_encard` in
  `R ⧸ J`) with the landed (K)-at-height-one
  (`ringKrullDim_quotient_add_one_of_height_eq_one`).
* `AlgebraicGeometry.Scheme.PartialMap.hom_base_genericPoint` — the
  **generic-value bridge**: the function-field morphism of `g.toRationalMap`
  sends the closed point of `Spec K(Y)` to the value of `g` at the generic
  point. Anchors the substep-3 germ pullback at the unit point through
  `toPartialMap_hom_base_specializes_unit` (spec D4/D5(d)).
* `AlgebraicGeometry.exists_isClosed_singleton_mem_of_isLocallyClosed` —
  Jacobson density of closed points in nonempty **locally closed** subsets
  (the D6 component-selection form of the landed open-set version).

Blueprint reference: `lem:milne_codim1_indeterminacy` (Milne, *Abelian
Varieties*, §I.3 Lemma 3.3, pp. 17–18; `abelian-varieties:page-0023/0024`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

/-! ## §1. Coheight strictness along specialisations of scheme points -/

/-- **Coheight strictness.** A non-trivial specialisation `a ⤳ b` of points of
a scheme drops the coheight: `coheight a + 1 ≤ coheight b`. (On the
specialisation preorder of the carrier, `a` is strictly above `b`.) -/
lemma Scheme.coheight_add_one_le_of_specializes {Y : Scheme.{u}} {a b : ↥Y}
    (h : a ⤳ b) (hne : a ≠ b) :
    Order.coheight a + 1 ≤ Order.coheight b := by
  refine Order.coheight_add_one_le (lt_of_le_not_ge (show b ≤ a from h) ?_)
  intro hba
  exact hne (h.antisymm hba).eq

/-- On an irreducible sober scheme, every point other than the generic point
has coheight at least one. -/
lemma Scheme.one_le_coheight_of_ne_genericPoint {Y : Scheme.{u}}
    [IrreducibleSpace ↥Y] {z : ↥Y} (hz : z ≠ genericPoint ↥Y) :
    1 ≤ Order.coheight z := by
  have h := Scheme.coheight_add_one_le_of_specializes
    (genericPoint_specializes z) (fun h' => hz h'.symm)
  exact le_trans le_add_self h

end AlgebraicGeometry

/-! ## §2. The Krull codimension count -/

namespace RingTheory.CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- If every prime of `R` containing `I` is the maximal ideal, then the
quotient `R ⧸ I` has Krull dimension at most `0`. -/
private lemma ringKrullDim_quotient_le_zero_of_forall_le_isPrime
    {I : Ideal R}
    (huniq : ∀ r : Ideal R, r.IsPrime → I ≤ r → r = IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ I) ≤ 0 := by
  rw [ringKrullDim_le_iff_height_le]
  intro P hP
  -- `I` is contained in the contraction of every ideal of the quotient.
  have hIle : ∀ Q : Ideal (R ⧸ I), I ≤ Ideal.comap (Ideal.Quotient.mk I) Q := by
    intro Q x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Q.zero_mem
  -- Every prime of the quotient pulls back to the maximal ideal, so any two
  -- primes agree; hence `P` is minimal and has height `0`.
  have hkey : ∀ Q : Ideal (R ⧸ I), Q.IsPrime → Q = P := by
    intro Q hQ
    have hQ' : Ideal.comap (Ideal.Quotient.mk I) Q = IsLocalRing.maximalIdeal R :=
      huniq _ (hQ.comap _) (hIle Q)
    have hP' : Ideal.comap (Ideal.Quotient.mk I) P = IsLocalRing.maximalIdeal R :=
      huniq _ (hP.comap _) (hIle P)
    calc Q = Ideal.map (Ideal.Quotient.mk I) (Ideal.comap (Ideal.Quotient.mk I) Q) :=
          (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q).symm
      _ = Ideal.map (Ideal.Quotient.mk I) (Ideal.comap (Ideal.Quotient.mk I) P) := by
          rw [hQ', hP']
      _ = P := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P
  have hmin : P ∈ minimalPrimes (R ⧸ I) :=
    ⟨⟨hP, bot_le⟩, fun {Q} hQ _ => le_of_eq (hkey Q hQ.1).symm⟩
  rw [Ideal.height_eq_zero_iff.mpr hmin]
  exact le_rfl

/-- **The Krull codimension count (Milne 3.3, spec D5(c)).** Let `R` be a
Cohen–Macaulay Noetherian local ring, `J` a prime of height one, and `xs` a
list such that the only prime containing `Ideal.ofList xs ⊔ J` is the maximal
ideal. Then `dim R ≤ |xs| + 1`.

Proof: (K) at height one gives `dim (R ⧸ J) + 1 = dim R`; in `R ⧸ J` the
images of `xs` generate an ideal whose only containing prime is the maximal
ideal, so Krull's height theorem
(`ringKrullDim_le_ringKrullDim_quotient_add_encard`) bounds
`dim (R ⧸ J) ≤ 0 + |xs|`. -/
theorem ringKrullDim_le_length_add_one_of_forall_le_isPrime
    [CohenMacaulay R] {J : Ideal R} [J.IsPrime] (hJ : J.height = 1)
    (xs : List R)
    (hle : Ideal.ofList xs ⊔ J ≤ IsLocalRing.maximalIdeal R)
    (huniq : ∀ r : Ideal R, r.IsPrime → Ideal.ofList xs ⊔ J ≤ r →
      r = IsLocalRing.maximalIdeal R) :
    ringKrullDim R ≤ (xs.length : WithBot ℕ∞) + 1 := by
  -- The quotient `C := R ⧸ J` is local with maximal ideal the image of `𝔪`.
  haveI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hmax : Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal R)
      = IsLocalRing.maximalIdeal (R ⧸ J) :=
    map_maximalIdeal_eq_of_surjective _ Ideal.Quotient.mk_surjective
  -- The image generating set.
  set s : Set (R ⧸ J) := Ideal.Quotient.mk J '' {a | a ∈ xs} with hsdef
  -- It lies in the Jacobson radical (= the maximal ideal).
  have hsjac : s ⊆ Ring.jacobson (R ⧸ J) := by
    rintro _ ⟨a, ha, rfl⟩
    have ha𝔪 : a ∈ IsLocalRing.maximalIdeal R :=
      hle (le_sup_left (α := Ideal R) (Ideal.subset_span ha))
    have h1 : Ideal.Quotient.mk J a ∈ IsLocalRing.maximalIdeal (R ⧸ J) :=
      hmax ▸ Ideal.mem_map_of_mem _ ha𝔪
    rwa [← Ideal.jacobson_bot,
      IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (R ⧸ J)) bot_ne_top]
  -- Krull's height theorem in `R ⧸ J`.
  have hkrull := ringKrullDim_le_ringKrullDim_quotient_add_encard s hsjac
  -- The double quotient has dimension at most `0`.
  have hzero : ringKrullDim ((R ⧸ J) ⧸ Ideal.span s) ≤ 0 := by
    refine ringKrullDim_quotient_le_zero_of_forall_le_isPrime (fun r hr hler => ?_)
    -- Pull the prime `r` of `R ⧸ J` back to `R`: it contains `ofList xs ⊔ J`.
    haveI hrp : (Ideal.comap (Ideal.Quotient.mk J) r).IsPrime := hr.comap _
    have hcontain : Ideal.ofList xs ⊔ J ≤ Ideal.comap (Ideal.Quotient.mk J) r := by
      refine sup_le ?_ ?_
      · rw [Ideal.ofList, Ideal.span_le]
        intro a ha
        rw [SetLike.mem_coe, Ideal.mem_comap]
        exact hler (Ideal.subset_span ⟨a, ha, rfl⟩)
      · intro j hj
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hj]
        exact r.zero_mem
    have h𝔪 := huniq _ hrp hcontain
    calc r = Ideal.map (Ideal.Quotient.mk J) (Ideal.comap (Ideal.Quotient.mk J) r) :=
          (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective r).symm
      _ = Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal R) := by rw [h𝔪]
      _ = IsLocalRing.maximalIdeal (R ⧸ J) := hmax
  -- The cardinality of the image set is at most the list length.
  have hcard : s.encard ≤ (xs.length : ℕ∞) := by
    classical
    calc s.encard ≤ ({a | a ∈ xs} : Set R).encard := Set.encard_image_le _ _
      _ = (xs.toFinset : Set R).encard := by rw [List.coe_toFinset]
      _ = (xs.toFinset.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
      _ ≤ (xs.length : ℕ∞) := by exact_mod_cast xs.toFinset_card_le
  -- Assemble: `dim R = dim (R ⧸ J) + 1 ≤ (0 + |xs|) + 1`.
  have hK := ringKrullDim_quotient_add_one_of_height_eq_one (R := R) (p := J) hJ
  calc ringKrullDim R = ringKrullDim (R ⧸ J) + 1 := hK.symm
    _ ≤ (ringKrullDim ((R ⧸ J) ⧸ Ideal.span s) + s.encard) + 1 := by gcongr
    _ ≤ (0 + (xs.length : WithBot ℕ∞)) + 1 := by
        gcongr
        exact_mod_cast hcard
    _ = (xs.length : WithBot ℕ∞) + 1 := by rw [zero_add]

end RingTheory.CohenMacaulay

namespace AlgebraicGeometry

/-! ## §3. The generic-value bridge -/

/-- **The generic-value bridge.** For a partial map `g : Y ⤏ Z` out of an
integral scheme defined at the generic point, the function-field morphism of
`g.toRationalMap` sends the closed point of `Spec K(Y)` to the value of `g`
at the generic point. This identifies the anchor `γ = Φ(η_Y)` of the
substep-3 germ pullback with the pointwise value of the maximal
representative (spec D4/D5(d)). -/
lemma Scheme.PartialMap.hom_base_genericPoint
    {Y Z : Scheme.{u}} [IsIntegral Y] (g : Y.PartialMap Z)
    (hη : genericPoint ↥Y ∈ g.domain) :
    g.toRationalMap.fromFunctionField (closedPoint Y.functionField)
      = g.hom.base ⟨genericPoint ↥Y, hη⟩ := by
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
  have hcomp : g.fromFunctionField
      = g.domain.fromSpecStalkOfMem (genericPoint ↥Y) hη ≫ g.hom := rfl
  rw [hcomp, Scheme.Hom.comp_apply]
  congr 1
  -- The stalk-to-domain morphism sends the closed point to `⟨η, hη⟩`.
  apply g.domain.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact Scheme.fromSpecStalk_closedPoint

/-! ## §3½. The transported codimension count -/

end AlgebraicGeometry

namespace RingTheory.CohenMacaulay

/-- **The transported codimension count (Milne 3.3, spec D5(c) assembled).**
Let `R` be a (chart) ring, `𝔡 𝔮 𝔯 : Ideal R` with `𝔮` prime of height one and
`𝔯` minimal over `𝔡 ⊔ 𝔮`; let `B'` be the localization of `R` at `𝔯` and
`φ : B' →+* A'` a surjection of regular local rings that kills the image of
`𝔡`. Then `dim A' ≤ 1`.

Route: the kernel-generation theorem
(`exists_ofList_eq_ker_length_add_ringKrullDim`) writes `ker φ` as
`Ideal.ofList xs` with `|xs| + dim A' = dim B'`; the prime `𝔮` transports to a
height-one prime `J'` of `B'` (`IsLocalization.height_map_of_disjoint`);
minimality of `𝔯` forces the maximal ideal of `B'` to be the *only* prime over
`ofList xs ⊔ J'` (contract to `R` and use the localization prime
correspondence); the Krull codimension count
(`ringKrullDim_le_length_add_one_of_forall_le_isPrime`) bounds
`dim B' ≤ |xs| + 1`, and cancellation of the finite `|xs|` gives the claim. -/
theorem ringKrullDim_le_one_of_minimalPrimes_of_surjective
    {R : Type u} [CommRing R] {𝔡 𝔮 𝔯 : Ideal R} [𝔮.IsPrime] [𝔯.IsPrime]
    (h𝔮ht : 𝔮.height = 1) (h𝔯min : 𝔯 ∈ (𝔡 ⊔ 𝔮).minimalPrimes)
    {B' A' : Type u} [CommRing B'] [CommRing A'] [Algebra R B']
    [IsLocalization.AtPrime B' 𝔯] [IsRegularLocalRing B'] [IsRegularLocalRing A']
    (φ : B' →+* A') (hφ : Function.Surjective φ)
    (h𝔡 : ∀ d ∈ 𝔡, φ (algebraMap R B' d) = 0) :
    ringKrullDim A' ≤ 1 := by
  -- Kernel generation at `φ`.
  obtain ⟨xs, hxsker, hxslen⟩ := exists_ofList_eq_ker_length_add_ringKrullDim φ hφ
  -- The transported height-one prime `J' := 𝔮 B'`.
  set J' : Ideal B' := 𝔮.map (algebraMap R B') with hJ'def
  have h𝔮𝔯 : 𝔮 ≤ 𝔯 := le_trans le_sup_right h𝔯min.1.2
  have hdisj : Disjoint (𝔯.primeCompl : Set R) (𝔮 : Set R) :=
    Set.disjoint_left.mpr fun {a} ha ha𝔮 => ha (h𝔮𝔯 ha𝔮)
  haveI hJ'pr : J'.IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime (q := 𝔯) h𝔮𝔯
  have hJ'ht : J'.height = 1 := by
    rw [hJ'def, IsLocalization.height_map_of_disjoint 𝔯.primeCompl 𝔮 hdisj, h𝔮ht]
  -- The contraction identities.
  have hunder : (IsLocalRing.maximalIdeal B').comap (algebraMap R B') = 𝔯 :=
    IsLocalization.AtPrime.under_maximalIdeal (R := R) (S := B') (I := 𝔯)
  have h𝔯max : 𝔯.map (algebraMap R B') = IsLocalRing.maximalIdeal B' := by
    conv_lhs => rw [← hunder]
    exact IsLocalization.map_under 𝔯.primeCompl B' (IsLocalRing.maximalIdeal B')
  -- `ofList xs ⊔ J' ≤ 𝔪`.
  have hle : Ideal.ofList xs ⊔ J' ≤ IsLocalRing.maximalIdeal B' := by
    refine sup_le ?_ ?_
    · rw [hxsker]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
    · rw [hJ'def, ← h𝔯max]
      exact Ideal.map_mono h𝔮𝔯
  -- The maximal ideal is the only prime over `ofList xs ⊔ J'`.
  have huniq : ∀ r : Ideal B', r.IsPrime → Ideal.ofList xs ⊔ J' ≤ r →
      r = IsLocalRing.maximalIdeal B' := by
    intro r hr hler
    have h𝔰pr : (r.comap (algebraMap R B')).IsPrime := hr.comap _
    have h𝔡𝔰 : 𝔡 ≤ r.comap (algebraMap R B') := by
      intro d hd
      rw [Ideal.mem_comap]
      have hmem : algebraMap R B' d ∈ RingHom.ker φ := h𝔡 d hd
      rw [← hxsker] at hmem
      exact le_trans le_sup_left hler hmem
    have h𝔮𝔰 : 𝔮 ≤ r.comap (algebraMap R B') :=
      le_trans Ideal.le_comap_map (Ideal.comap_mono (le_trans le_sup_right hler))
    have h𝔰𝔯 : r.comap (algebraMap R B') ≤ 𝔯 := by
      calc r.comap (algebraMap R B')
          ≤ (IsLocalRing.maximalIdeal B').comap (algebraMap R B') :=
            Ideal.comap_mono (IsLocalRing.le_maximalIdeal hr.ne_top)
        _ = 𝔯 := hunder
    have h𝔰eq : r.comap (algebraMap R B') = 𝔯 :=
      le_antisymm h𝔰𝔯 (h𝔯min.2 ⟨h𝔰pr, sup_le h𝔡𝔰 h𝔮𝔰⟩ h𝔰𝔯)
    calc r = (r.comap (algebraMap R B')).map (algebraMap R B') :=
          (IsLocalization.map_under 𝔯.primeCompl B' r).symm
      _ = 𝔯.map (algebraMap R B') := by rw [h𝔰eq]
      _ = IsLocalRing.maximalIdeal B' := h𝔯max
  -- The Krull codimension count, then cancellation of the finite `|xs|`.
  have hcount := ringKrullDim_le_length_add_one_of_forall_le_isPrime
    (R := B') (J := J') hJ'ht xs hle huniq
  rw [← hxslen] at hcount
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A')] at hcount ⊢
  have hnat : xs.length + (IsLocalRing.maximalIdeal A').spanFinrank
      ≤ xs.length + 1 := by exact_mod_cast hcount
  have hle1 : (IsLocalRing.maximalIdeal A').spanFinrank ≤ 1 :=
    Nat.le_of_add_le_add_left hnat
  exact_mod_cast hle1

end RingTheory.CohenMacaulay

namespace AlgebraicGeometry

/-! ## §4. Jacobson density on locally closed subsets -/

/-- **Jacobson density of closed points, locally closed form.** Every nonempty
locally closed subset of a scheme locally of finite type over a field contains
a point that is closed in the ambient scheme. Generalises the landed open-set
version (`exists_isClosed_singleton_mem_of_isOpen`); used by the D6 component
selection. -/
lemma exists_isClosed_singleton_mem_of_isLocallyClosed
    {kbar : Type u} [Field kbar] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of kbar)) [LocallyOfFiniteType g]
    {O : Set ↥Z} (hO : IsLocallyClosed O) (hne : O.Nonempty) :
    ∃ u ∈ O, IsClosed ({u} : Set ↥Z) := by
  have hJ : JacobsonSpace ↥Z := LocallyOfFiniteType.jacobsonSpace g
  by_contra hc
  push Not at hc
  have hemp : O ∩ closedPoints ↥Z = ∅ := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun h1 h2 => hc v h1 h2
  have h := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := ↥Z) hO
  rw [hemp, closure_empty] at h
  obtain ⟨x, hx⟩ := hne
  have hx' : x ∈ closure O := subset_closure hx
  rw [← h] at hx'
  simp at hx'

end AlgebraicGeometry
