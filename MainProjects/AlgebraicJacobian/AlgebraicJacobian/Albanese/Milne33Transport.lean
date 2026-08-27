/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import AlgebraicJacobian.Albanese.Milne33TransportLocal
import AlgebraicJacobian.Albanese.Milne33Substeps
import AlgebraicJacobian.Albanese.Milne33RowSection
import AlgebraicJacobian.Albanese.Milne33Pullback
import AlgebraicJacobian.Albanese.CodimOneExtension

/-!
# Milne Lemma 3.3, substep 4b-transport: the codimension-one point of the
indeterminacy locus

Per `informal/m33-spec.md` (D5). Main results:

* `AlgebraicGeometry.Scheme.exists_base_eq_fromSpec_of_ker_app_le` — chart
  image-point production for a closed immersion `g : X ⟶ Y`: a prime of an
  affine chart ring `Γ(Y, U)` containing `ker (g.app U)` is the image of a
  point of `X` (D5(b), "`z̃ = δ(z)`").
* `AlgebraicGeometry.Scheme.exists_specializes_ringKrullDim_stalk_le_one_of_notMem_stalk_range`
  — the **transport kernel** (Milne-context-free): on an integral scheme `Y`
  with regular stalks, given a closed immersion `g : X ⟶ Y`, a point
  `x₀ : X`, and a coheight-one pole `w ⤳ g(x₀)` of `h ∈ K(Y)`, there is
  `z ⤳ x₀` with `dim 𝒪_{X,z} ≤ 1` such that `h` still has a pole at `g(z)`
  (D5(b)+(c): minimal prime of `𝔡 ⊔ 𝔮_w` in the chart, kernel generation of
  the diagonal ideal, the transported Krull count).
* `AlgebraicGeometry.Scheme.RationalMap.exists_notMem_domain_specializes_coheight_eq_one`
  — **the 4b-transport (D5 assembled)**: for the difference map
  `Φ := differenceRationalMap f hover` on `Y := X ×_{k̄} X` and a closed point
  `x₀ ∉ dom f`, there is a point `z ∉ dom f` with `z ⤳ x₀` and
  `coheight z = 1`. Front end: substep 2-hard contrapositive
  (`mem_domain_of_selfDiag_mem_domain`) and the pole-existence corollary of
  substep 3 (`exists_germ_stalkPullback_notMem_range_of_notMem_domain`); back
  end: 3-easy (`germ_stalkPullback_mem_range_of_mem_domain`) plus diagonal
  triviality (`toPartialMap_hom_base_selfDiag_eq`) to place `z` in the
  indeterminacy locus, and the coheight pincer
  (`one_le_coheight_of_ne_genericPoint`) to nail `coheight z = 1`.

Blueprint reference: `lem:milne_codim1_indeterminacy` (Milne, *Abelian
Varieties*, §I.3 Lemma 3.3, pp. 17–18; `abelian-varieties:page-0023/0024`).
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

/-! ## §1. Chart image points of a closed immersion -/

/-- **Chart image-point production.** For a closed immersion `g : X ⟶ Y`, an
affine open `U ⊆ Y`, and a prime `𝔯` of `Γ(Y, U)` containing the kernel of the
section map `g.app U`, the chart point of `𝔯` lies in the image of `g`.
(D5(b): the minimal prime over the diagonal ideal plus the pole prime is a
point *of the diagonal*.) -/
lemma Scheme.exists_base_eq_fromSpec_of_ker_app_le
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsClosedImmersion g]
    {U : Y.Opens} (hU : IsAffineOpen U) (𝔯 : PrimeSpectrum Γ(Y, U))
    (hker : RingHom.ker (g.app U).hom ≤ 𝔯.asIdeal) :
    ∃ z : X, g.base z = hU.fromSpec 𝔯 := by
  have hW : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  haveI h𝔷 : (𝔯.asIdeal.map (g.app U).hom).IsPrime :=
    Ideal.map_isPrime_of_surjective (g.app_surjective U hU) hker
  set p𝔷 : PrimeSpectrum Γ(X, g ⁻¹ᵁ U) := ⟨𝔯.asIdeal.map (g.app U).hom, h𝔷⟩
    with hp𝔷def
  refine ⟨hW.fromSpec p𝔷, ?_⟩
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec g hU hW le_rfl
  calc g.base (hW.fromSpec p𝔷)
      = (hW.fromSpec ≫ g).base p𝔷 := rfl
    _ = (Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl) ≫ hU.fromSpec).base p𝔷 := by
        rw [hsq]
    _ = hU.fromSpec.base ((Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl)).base p𝔷) := rfl
    _ = hU.fromSpec 𝔯 := by
        congr 1
        rw [Scheme.Hom.appLE_eq_app]
        change PrimeSpectrum.comap (g.app U).hom p𝔷 = 𝔯
        refine PrimeSpectrum.ext ?_
        change Ideal.comap (g.app U).hom (𝔯.asIdeal.map (g.app U).hom) = 𝔯.asIdeal
        rw [Ideal.comap_map_of_surjective _ (g.app_surjective U hU)]
        exact sup_eq_left.mpr hker

/-! ## §2. The transport kernel -/

/-- **The 4b-transport kernel (Milne 3.3, D5(b)+(c), Milne-context-free).**
Let `Y` be an integral scheme with regular stalks, `g : X ⟶ Y` a closed
immersion with `X` having regular stalks, `x₀ : X`, and let `h ∈ K(Y)` have a
pole at a coheight-one point `w ⤳ g(x₀)`. Then some `z ⤳ x₀` with
`dim 𝒪_{X,z} ≤ 1` still carries the pole: `h ∉ im (𝒪_{Y,g(z)} → K(Y))`.

Route: chart `U ∋ g(x₀)` with ring `R`; `𝔡 := ker (Γ(U) → 𝒪_{X,x₀})` (the
diagonal ideal), `𝔮 :=` the prime of `w`; a minimal prime `𝔯` of `𝔡 ⊔ 𝔮`
inside the prime of `g(x₀)` is a point `g(z)` of the image (§1), and the
transported codimension count
(`RingTheory.CohenMacaulay.ringKrullDim_le_one_of_minimalPrimes_of_surjective`)
applied to the stalk surjection `𝒪_{Y,g(z)} ↠ 𝒪_{X,z}` bounds
`dim 𝒪_{X,z} ≤ 1`. -/
theorem Scheme.exists_specializes_ringKrullDim_stalk_le_one_of_notMem_stalk_range
    {X Y : Scheme.{u}} [IsIntegral Y] (g : X ⟶ Y) [IsClosedImmersion g]
    (hregX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hregY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (x₀ : X) {w : Y} (hw : w ⤳ g.base x₀) (hcw : Order.coheight w = 1)
    {h : Y.functionField}
    (hh : h ∉ (algebraMap (Y.presheaf.stalk w) Y.functionField).range) :
    ∃ z : X, z ⤳ x₀ ∧ ringKrullDim (X.presheaf.stalk z) ≤ 1 ∧
      h ∉ (algebraMap (Y.presheaf.stalk (g.base z)) Y.functionField).range := by
  -- §a. The chart at `P := g x₀`.
  obtain ⟨U, hU, hPU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := g.base x₀) (U := ⊤)
      (by trivial)
  have hwU : w ∈ U := hw.mem_open U.isOpen hPU
  have hx₀W : x₀ ∈ g ⁻¹ᵁ U := hPU
  set 𝔭 : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨g.base x₀, hPU⟩ with h𝔭def
  set 𝔮 : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨w, hwU⟩ with h𝔮def
  -- §b. The diagonal ideal `𝔡` of the chart.
  set 𝔡 : Ideal Γ(Y, U) :=
    RingHom.ker ((g.app U ≫ X.presheaf.germ (g ⁻¹ᵁ U) x₀ hx₀W).hom) with h𝔡def
  have h𝔡mem : ∀ d : Γ(Y, U), d ∈ 𝔡 ↔
      X.presheaf.germ (g ⁻¹ᵁ U) x₀ hx₀W ((g.app U) d) = 0 := by
    intro d
    rw [h𝔡def, RingHom.mem_ker, CommRingCat.comp_apply]
  -- `𝔡 ≤ 𝔭`: a section invertible at `P` cannot have zero germ at `x₀`.
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk (g.base x₀)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨g.base x₀, hPU⟩
  haveI hlocP : IsLocalization.AtPrime (Y.presheaf.stalk (g.base x₀)) 𝔭.asIdeal :=
    hU.isLocalization_stalk ⟨g.base x₀, hPU⟩
  have h𝔡𝔭 : 𝔡 ≤ 𝔭.asIdeal := by
    intro d hd
    by_contra hd𝔭
    have hunit : IsUnit (algebraMap Γ(Y, U) (Y.presheaf.stalk (g.base x₀)) d) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (Y.presheaf.stalk (g.base x₀)) 𝔭.asIdeal d).mpr hd𝔭
    have hzero : g.stalkMap x₀ (algebraMap Γ(Y, U) (Y.presheaf.stalk (g.base x₀)) d)
        = 0 := by
      change g.stalkMap x₀ (Y.presheaf.germ U (g.base x₀) hPU d) = 0
      rw [Scheme.Hom.germ_stalkMap_apply]
      exact (h𝔡mem d).mp hd
    have : IsUnit ((0 : X.presheaf.stalk x₀)) := by
      rw [← hzero]
      exact hunit.map (g.stalkMap x₀).hom
    exact not_isUnit_zero this
  -- `𝔮 ≤ 𝔭` from `w ⤳ P` through the chart.
  have hfrom𝔮 : hU.fromSpec 𝔮 = w := hU.fromSpec_primeIdealOf ⟨w, hwU⟩
  have hfrom𝔭 : hU.fromSpec 𝔭 = g.base x₀ := hU.fromSpec_primeIdealOf ⟨g.base x₀, hPU⟩
  have hind : Topology.IsInducing hU.fromSpec.base :=
    hU.fromSpec.isOpenEmbedding.toIsInducing
  have h𝔮𝔭 : 𝔮.asIdeal ≤ 𝔭.asIdeal := by
    have : 𝔮 ⤳ 𝔭 := by
      refine hind.specializes_iff.mp ?_
      rw [hfrom𝔮, hfrom𝔭]
      exact hw
    exact (PrimeSpectrum.le_iff_specializes 𝔮 𝔭).mpr this
  -- §c. A minimal prime `𝔯` of `𝔡 ⊔ 𝔮` inside `𝔭`, and its chart point.
  obtain ⟨𝔯, h𝔯min, h𝔯𝔭⟩ :=
    Ideal.exists_minimalPrimes_le (sup_le h𝔡𝔭 h𝔮𝔭)
  haveI h𝔯pr : 𝔯.IsPrime := h𝔯min.1.1
  set 𝔯pt : PrimeSpectrum Γ(Y, U) := ⟨𝔯, h𝔯pr⟩ with h𝔯ptdef
  have h𝔮𝔯 : 𝔮.asIdeal ≤ 𝔯 := le_trans le_sup_right h𝔯min.1.2
  have h𝔡𝔯 : 𝔡 ≤ 𝔯 := le_trans le_sup_left h𝔯min.1.2
  -- Its chart point is in the image of `g`.
  have hkerapp : RingHom.ker (g.app U).hom ≤ 𝔯 := by
    refine le_trans ?_ h𝔡𝔯
    intro u hu
    rw [h𝔡mem]
    rw [RingHom.mem_ker] at hu
    change X.presheaf.germ (g ⁻¹ᵁ U) x₀ hx₀W ((g.app U).hom u) = 0
    rw [hu, map_zero]
  obtain ⟨z, hgz⟩ := Scheme.exists_base_eq_fromSpec_of_ker_app_le g hU 𝔯pt hkerapp
  -- §d. Specialisation bookkeeping.
  have hztUmem : hU.fromSpec 𝔯pt ∈ U := by
    have h1 : hU.fromSpec 𝔯pt ∈ Set.range hU.fromSpec.base := ⟨𝔯pt, rfl⟩
    rwa [hU.range_fromSpec] at h1
  have hztP : hU.fromSpec 𝔯pt ⤳ g.base x₀ := by
    have hsp : 𝔯pt ⤳ 𝔭 := (PrimeSpectrum.le_iff_specializes 𝔯pt 𝔭).mp h𝔯𝔭
    have := hsp.map hU.fromSpec.continuous
    rwa [hfrom𝔭] at this
  have hwzt : w ⤳ hU.fromSpec 𝔯pt := by
    have hsp : 𝔮 ⤳ 𝔯pt := (PrimeSpectrum.le_iff_specializes 𝔮 𝔯pt).mp h𝔮𝔯
    have := hsp.map hU.fromSpec.continuous
    rwa [hfrom𝔮] at this
  have hzx₀ : z ⤳ x₀ := by
    have hind' : Topology.IsInducing g.base := g.isClosedEmbedding.toIsInducing
    rw [← hind'.specializes_iff]
    show g.base z ⤳ g.base x₀
    rw [hgz]
    exact hztP
  refine ⟨z, hzx₀, ?_, ?_⟩
  · -- §e. The transported codimension count at `𝒪_{Y,g(z)} ↠ 𝒪_{X,z}`.
    -- Chart structure at `z̃ := g z`.
    letI : Algebra Γ(Y, U) (Y.presheaf.stalk (hU.fromSpec 𝔯pt)) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨_, hztUmem⟩
    haveI hloczt : IsLocalization.AtPrime (Y.presheaf.stalk (hU.fromSpec 𝔯pt)) 𝔯 :=
      hU.isLocalization_stalk' 𝔯pt hztUmem
    haveI hregzt : IsRegularLocalRing (Y.presheaf.stalk (hU.fromSpec 𝔯pt)) :=
      hregY _
    haveI hregz : IsRegularLocalRing (X.presheaf.stalk z) := hregX z
    haveI h𝔮pr : 𝔮.asIdeal.IsPrime := 𝔮.2
    -- `𝔮` has height one (coheight bridge at `w`).
    letI : Algebra Γ(Y, U) (Y.presheaf.stalk w) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨w, hwU⟩
    haveI hlocw : IsLocalization.AtPrime (Y.presheaf.stalk w) 𝔮.asIdeal :=
      hU.isLocalization_stalk ⟨w, hwU⟩
    have h𝔮ht : 𝔮.asIdeal.height = 1 := by
      have hb := Scheme.ringKrullDim_stalk_eq_coheight Y w
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮.asIdeal
        (Y.presheaf.stalk w), hcw] at hb
      exact_mod_cast hb
    -- The stalk surjection, re-anchored at the chart point.
    set ψ : Y.presheaf.stalk (hU.fromSpec 𝔯pt) ≅ Y.presheaf.stalk (g.base z) :=
      Y.presheaf.stalkCongr (Inseparable.of_eq hgz.symm) with hψdef
    set φ : Y.presheaf.stalk (hU.fromSpec 𝔯pt) ⟶ X.presheaf.stalk z :=
      ψ.hom ≫ g.stalkMap z with hφdef
    have hφsurj : Function.Surjective φ.hom := by
      have h1 : Function.Surjective (g.stalkMap z) := g.stalkMap_surjective z
      have h2 : Function.Surjective ψ.hom :=
        (ConcreteCategory.bijective_of_isIso ψ.hom).2
      rw [hφdef]
      intro a
      obtain ⟨b, hb⟩ := h1 a
      obtain ⟨c, hc⟩ := h2 b
      exact ⟨c, by rw [CommRingCat.comp_apply, hc, hb]⟩
    -- `φ` kills `𝔡`.
    have hztUmem2 : g.base z ∈ U := by rw [hgz]; exact hztUmem
    have h𝔡kill : ∀ d ∈ 𝔡, φ.hom (algebraMap Γ(Y, U)
        (Y.presheaf.stalk (hU.fromSpec 𝔯pt)) d) = 0 := by
      intro d hd
      change φ (Y.presheaf.germ U (hU.fromSpec 𝔯pt) hztUmem d) = 0
      rw [hφdef, CommRingCat.comp_apply]
      have hψgerm : ψ.hom (Y.presheaf.germ U (hU.fromSpec 𝔯pt) hztUmem d)
          = Y.presheaf.germ U (g.base z) hztUmem2 d := by
        rw [hψdef, TopCat.Presheaf.stalkCongr_hom,
          TopCat.Presheaf.germ_stalkSpecializes_apply]
      rw [hψgerm, Scheme.Hom.germ_stalkMap_apply]
      -- the germ of `g.app U d` at `z` factors through the vanishing germ at `x₀`
      have hspec := TopCat.Presheaf.germ_stalkSpecializes_apply
        X.presheaf (U := g ⁻¹ᵁ U) hx₀W hzx₀ ((g.app U) d)
      rw [← hspec, (h𝔡mem d).mp hd, map_zero]
    -- Conclude with the transported codimension count.
    exact RingTheory.CohenMacaulay.ringKrullDim_le_one_of_minimalPrimes_of_surjective
      (𝔡 := 𝔡) (𝔮 := 𝔮.asIdeal) (𝔯 := 𝔯) h𝔮ht h𝔯min φ.hom hφsurj h𝔡kill
  · -- §f. The pole survives at `g z`.
    have hztrange : h ∉ (algebraMap (Y.presheaf.stalk (hU.fromSpec 𝔯pt))
        Y.functionField).range :=
      fun hmem => hh (range_algebraMap_stalk_le_of_specializes hwzt hmem)
    rw [← hgz] at hztrange
    exact hztrange

/-! ## §3. The 4b-transport, assembled (D5) -/

namespace Scheme.RationalMap

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
variable {X G : Over (Spec (.of kbar))}
  [Smooth X.hom] [GrpObj G] [LocallyOfFiniteType G.hom] [LocallyOfFiniteType X.hom]

/-- **Milne Lemma 3.3, substep 4b-transport (spec D5).** Let `f : X ⇢ G` be a
rational map over `k̄` from a smooth irreducible variety to a group variety,
compatible with the structure maps. If a *closed* point `x₀` is outside the
domain of `f`, then some point `z` outside the domain with `coheight z = 1`
specialises to it.

Front end: `x₀ ∉ dom f` forces `δ(x₀) ∉ dom Φ` for the difference map `Φ` on
`Y := X ×_{k̄} X` (substep 2-hard, contrapositive), so some coheight-one
`w ⤳ δ(x₀)` carries a pole of a pulled-back regular function `h` (substep 3 +
pole purity). The transport kernel moves the pole to `δ(z)` for some `z ⤳ x₀`
with `dim 𝒪_{X,z} ≤ 1`. Back end: if `f` were defined at `z` then `Φ` would
be defined at `δ(z)` with value the unit (2-easy + diagonal triviality), and
`h` would be regular at `δ(z)` (3-easy) — contradiction. Finally `z ≠ η_X`
(the generic point is in `dom f`), so `coheight z = 1` by the pincer. -/
theorem exists_notMem_domain_specializes_coheight_eq_one
    (f : X.left.RationalMap G.left) (hover : f.compHom G.hom = X.hom.toRationalMap)
    [GeometricallyIrreducible X.hom] [IsSeparated X.hom]
    [IsIntegral X.left] [IsReduced X.left] [IrreducibleSpace ↥X.left]
    [G.left.IsSeparated] [IsSeparated G.hom]
    (x₀ : ↥X.left) (hx₀ : IsClosed ({x₀} : Set ↥X.left)) (hx₀f : x₀ ∉ f.domain) :
    ∃ z : ↥X.left, z ∉ f.domain ∧ z ⤳ x₀ ∧ Order.coheight z = 1 := by
  -- §0. Instance pack for the self-product `Y := X ×_{k̄} X`.
  haveI hYint : IsIntegral (pullback X.hom X.hom) := isIntegral_pullback_self X
  haveI hYnoeth : IsLocallyNoetherian (pullback X.hom X.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst X.hom X.hom ≫ X.hom)
  haveI : Smooth (Over.mk (pullback.fst X.hom X.hom ≫ X.hom)).hom := by
    change Smooth (pullback.fst X.hom X.hom ≫ X.hom); infer_instance
  haveI : GeometricallyIrreducible (Over.mk (pullback.fst X.hom X.hom ≫ X.hom)).hom := by
    change GeometricallyIrreducible (pullback.fst X.hom X.hom ≫ X.hom)
    exact GeometricallyIrreducible.comp _ _
  haveI : IsSeparated (Over.mk (pullback.fst X.hom X.hom ≫ X.hom)).hom := by
    change IsSeparated (pullback.fst X.hom X.hom ≫ X.hom); infer_instance
  haveI : LocallyOfFiniteType (Over.mk (pullback.fst X.hom X.hom ≫ X.hom)).hom := by
    change LocallyOfFiniteType (pullback.fst X.hom X.hom ≫ X.hom); infer_instance
  haveI : IsIntegral (Over.mk (pullback.fst X.hom X.hom ≫ X.hom)).left := hYint
  have hregY : ∀ y : ↥(pullback X.hom X.hom),
      IsRegularLocalRing ((pullback X.hom X.hom).presheaf.stalk y) := fun y =>
    isRegularLocalRing_stalk_of_smooth (Over.mk (pullback.fst X.hom X.hom ≫ X.hom)) y
  have hregX : ∀ x : ↥X.left, IsRegularLocalRing (X.left.presheaf.stalk x) := fun x =>
    isRegularLocalRing_stalk_of_smooth X x
  haveI : IsClosedImmersion (selfDiag X) :=
    IsSeparated.isClosedImmersion_diagonal (f := X.hom)
  -- §1. `P := δ(x₀)` is outside the domain of `Φ` (substep 2-hard).
  have hP : (selfDiag X).base x₀ ∉ (differenceRationalMap f hover).domain :=
    fun hmem => hx₀f (mem_domain_of_selfDiag_mem_domain f hover x₀ hx₀ hmem)
  -- §2. The generic points lie in the domains.
  have hηX : genericPoint ↥X.left ∈ f.toPartialMap.domain :=
    (genericPoint_specializes _).mem_open f.toPartialMap.domain.2
      f.toPartialMap.dense_domain.nonempty.choose_spec
  have hηY : genericPoint ↥(pullback X.hom X.hom)
      ∈ (differenceRationalMap f hover).toPartialMap.domain :=
    (genericPoint_specializes _).mem_open
      (differenceRationalMap f hover).toPartialMap.domain.2
      (differenceRationalMap f hover).toPartialMap.dense_domain.nonempty.choose_spec
  -- §3. The affine window `V` at the unit point.
  haveI : Subsingleton ↥(Spec (.of kbar)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum kbar))
  obtain ⟨V, hV, heV, -⟩ := exists_isAffineOpen_mem_and_subset (X := G.left)
    (x := (grpObjUnitPoint G).base (X.hom.base x₀)) (U := ⊤) (by trivial)
  have hγeq : (differenceRationalMap f hover).fromFunctionField
        (closedPoint (pullback X.hom X.hom).functionField)
      = (differenceRationalMap f hover).toPartialMap.hom.base ⟨genericPoint _, hηY⟩ := by
    have hb := Scheme.PartialMap.hom_base_genericPoint
      (differenceRationalMap f hover).toPartialMap hηY
    rwa [Scheme.RationalMap.toRationalMap_toPartialMap] at hb
  have hγe : (differenceRationalMap f hover).fromFunctionField
        (closedPoint (pullback X.hom X.hom).functionField)
      ⤳ (grpObjUnitPoint G).base (X.hom.base x₀) := by
    rw [hγeq]
    have hspec := toPartialMap_hom_base_specializes_unit f hover
      (genericPoint ↥X.left) hηX (genericPoint ↥(pullback X.hom X.hom)) hηY
      (genericPoint_specializes _)
    have hpt : X.hom.base (genericPoint ↥X.left) = X.hom.base x₀ :=
      Subsingleton.elim _ _
    rwa [hpt] at hspec
  have hγV : (differenceRationalMap f hover).fromFunctionField
      (closedPoint (pullback X.hom X.hom).functionField) ∈ V :=
    hγe.mem_open V.isOpen heV
  -- §4. `Φ` is over `k̄` in the `fromFunctionField` form.
  have hFover : (differenceRationalMap f hover).fromFunctionField ≫ G.hom
      = (pullback X.hom X.hom).fromSpecStalk (genericPoint ↥(pullback X.hom X.hom))
        ≫ (pullback.fst X.hom X.hom ≫ X.hom) := by
    have h1 : (differenceRationalMap f hover).fromFunctionField
        = (differenceRationalMap f hover).toPartialMap.fromFunctionField := by
      conv_lhs => rw [← Scheme.RationalMap.toRationalMap_toPartialMap
        (differenceRationalMap f hover)]
      rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
    have h2 : (differenceRationalMap f hover).toPartialMap.fromFunctionField
        = (differenceRationalMap f hover).toPartialMap.domain.fromSpecStalkOfMem
            (genericPoint ↥(pullback X.hom X.hom)) hηY
          ≫ (differenceRationalMap f hover).toPartialMap.hom := rfl
    rw [h1, h2, Category.assoc, diff_toPartialMap_hom_comp_hom f hover,
      ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  -- §5. The pole of substep 3 + pole purity, then the transport kernel.
  obtain ⟨s, w, hwspec, hcw, hh⟩ :=
    exists_germ_stalkPullback_notMem_range_of_notMem_domain hregY
      (pullback.fst X.hom X.hom ≫ X.hom) G.hom (differenceRationalMap f hover)
      hFover hV hγV ((selfDiag X).base x₀) hP
  obtain ⟨z, hzx₀, hdim, hhz⟩ :=
    Scheme.exists_specializes_ringKrullDim_stalk_le_one_of_notMem_stalk_range
      (selfDiag X) hregX hregY x₀ hwspec hcw hh
  -- §6. `z` is outside the domain of `f` (2-easy + diagonal triviality + 3-easy).
  have hzf : z ∉ f.domain := by
    intro hzf
    have hδz : (selfDiag X).base z
        ∈ (differenceRationalMap f hover).toPartialMap.domain :=
      selfDiag_base_mem_domain f hover z hzf
    have hQV : (differenceRationalMap f hover).toPartialMap.hom.base
        ⟨(selfDiag X).base z, hδz⟩ ∈ V := by
      rw [toPartialMap_hom_base_selfDiag_eq f hover z hzf hδz]
      have hpt : X.hom.base z = X.hom.base x₀ := Subsingleton.elim _ _
      rw [hpt]
      exact heV
    exact hhz (germ_stalkPullback_mem_range_of_mem_domain
      (differenceRationalMap f hover) hV hγV
      (differenceRationalMap f hover).toPartialMap
      (Scheme.RationalMap.toRationalMap_toPartialMap _) hδz hQV s)
  -- §7. The coheight pincer.
  have hne : z ≠ genericPoint ↥X.left := fun he => hzf (by rw [he]; exact hηX)
  have hcoh : Order.coheight z = 1 := by
    have hb := Scheme.ringKrullDim_stalk_eq_coheight X.left z
    rw [hb] at hdim
    have h1 : Order.coheight z ≤ 1 := by exact_mod_cast hdim
    exact le_antisymm h1 (Scheme.one_le_coheight_of_ne_genericPoint hne)
  exact ⟨z, hzf, hzx₀, hcoh⟩

end Scheme.RationalMap

end AlgebraicGeometry
