/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeKeyChart
import AlgebraicJacobian.Picard.DivSchemeFamilyUniv

/-!
# The atlas factorization of `DivScheme g` (DDR-9.F1)

`informal/w4-ddr9-worksheet.md` §3.3: the chart atlas of the glued carve locus, and the
factorization of an arbitrary test morphism through it.

* `AlgebraicGeometry.carveLocusToCarveScheme` (campaign `divCarveChartToDivScheme`): each
  chart-wise carve locus `Z(♦)_{I,J} = Spec R_Z` maps to the glued locus over the pair
  chart — the factor of `carveLocusToGrPair` through the closed immersion `carveSchemeι`,
  with defining triangle `carveLocusToCarveScheme_carveSchemeι`
  (campaign `divCarveChartToDivScheme_divSchemeι`).  The kill law feeding the factoring
  criterion is the quotient self-kill (`Ideal.mk_ker`; equivalently
  `divCarveIdeal_le_ker_of_tower` at the chart ring itself).
* **Keystone** (`carveScheme_exists_chartFactor`; campaign
  `divScheme_exists_chartFactor`): every morphism `v : overSpec k S ⟶ carveSchemeOver`
  factors, on a finite spanning family of basic localizations of `S`, through some
  `carveLocusToCarveScheme i j` along a `k`-algebra map
  `ω : R_{I,J} ⧸ I_♦ →ₐ[k] Localization.Away (f t)`.  Route: pull the pair-chart atlas
  (`grPairCover` conjugated by `grPairPatchIso`) back along `u := v.left ≫ carveSchemeι`,
  refine by basic opens of `Spec S` (quasi-compactness), extract the chart map by
  `IsOpenImmersion.lift` + `Spec.preimage`, read its `k`-structure off the chart structure
  triangle (`pairChartMap_grPairStructMap`), kill the chart carve ideal by
  `carveIdealSheaf_le_ker_of_factors` + KeyChart
  (`carveIdealSheaf_ideal_pairChartOpen`) through the chart-sections workhorse, and
  descend through `Ideal.Quotient.liftₐ`.
-/

set_option autoImplicit false

universe u

open TensorProduct CategoryTheory

namespace AlgebraicGeometry

open Grassmannian

section Generic

variable (k : Type u) [Field k] (g r₁ r₂ : ℕ)
variable {ι : Type u} (μ : ι → ((Fin r₁ → k) →ₗ[k] (Fin r₂ → k)))

/-! ## The chart atlas of the glued carve locus -/

/-- **The chart atlas of `Z(♦)`**: the chart-wise carve locus
`Z(♦)_{I,J} = Spec (R_{I,J} ⧸ I_♦)` maps to the glued carve locus — the factor of
`carveLocusToGrPair` through the closed immersion `carveSchemeι`, given by the DDR-1
factoring criterion at the quotient presentation (which kills `I_♦` by `Ideal.mk_ker`).
The defining triangle is `carveLocusToCarveScheme_carveSchemeι`. -/
noncomputable def carveLocusToCarveScheme
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    Spec (CommRingCat.of (PairChartRing k g r₁ g r₂ i j ⧸ carveIdeal k g r₁ r₂ μ i j))
      ⟶ carveScheme k g r₁ r₂ μ :=
  (carveScheme_exists_factor_of_le_ker k g r₁ r₂ μ i j
    (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j)) Ideal.mk_ker.ge).choose

/-- **The defining triangle of the chart atlas**: through the closed immersion, the chart
map of `Z(♦)_{I,J}` is the quotient presentation followed by the pair chart (that is,
`carveLocusToGrPair i j`). -/
theorem carveLocusToCarveScheme_carveSchemeι
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    carveLocusToCarveScheme k g r₁ r₂ μ i j ≫ carveSchemeι k g r₁ r₂ μ
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j)))
        ≫ pairChartMap k g r₁ g r₂ i j :=
  (carveScheme_exists_factor_of_le_ker k g r₁ r₂ μ i j
    (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j)) Ideal.mk_ker.ge).choose_spec

/-! ## The per-point chart selection -/

/-- Every point of the Grassmannian pair lies in the range of a pair chart (the
`grPairCover` patches conjugated by `grPairPatchIso`). -/
private lemma exists_mem_range_pairChartMap (y : grPair k g r₁ g r₂) :
    ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J),
      y ∈ Set.range (pairChartMap k g r₁ g r₂ i j) := by
  obtain ⟨c, z, hz⟩ := (grPairCover k g r₁ g r₂).exists_eq y
  refine ⟨c.1, c.2, (grPairPatchIso k g r₁ g r₂ c.1 c.2).hom z, ?_⟩
  have h1 : (grPairPatchIso k g r₁ g r₂ c.1 c.2).hom ≫ pairChartMap k g r₁ g r₂ c.1 c.2
      = (grPairCover k g r₁ g r₂).f c :=
    Iso.hom_inv_id_assoc (grPairPatchIso k g r₁ g r₂ c.1 c.2)
      ((grPairCover k g r₁ g r₂).f c)
  calc pairChartMap k g r₁ g r₂ c.1 c.2 ((grPairPatchIso k g r₁ g r₂ c.1 c.2).hom z)
      = ((grPairPatchIso k g r₁ g r₂ c.1 c.2).hom ≫ pairChartMap k g r₁ g r₂ c.1 c.2) z :=
        (Scheme.Hom.comp_apply _ _ z).symm
    _ = (grPairCover k g r₁ g r₂).f c z := congrArg (fun m => m z) h1
    _ = y := hz

/-- **The basic-open chart selection**: around every point of an affine test of `grPair`
there is a basic open whose points all land in the range of one pair chart. -/
private lemma exists_basicOpen_range_pairChartMap {S : Type u} [CommRing S]
    (u : Spec (CommRingCat.of S) ⟶ grPair k g r₁ g r₂) (p : PrimeSpectrum S) :
    ∃ (x : S) (i : (glueData k g r₁).J) (j : (glueData k g r₂).J),
      p ∈ PrimeSpectrum.basicOpen x ∧
      ∀ q : PrimeSpectrum S, x ∉ q.asIdeal
        → u q ∈ Set.range (pairChartMap k g r₁ g r₂ i j) := by
  obtain ⟨i, j, hij⟩ := exists_mem_range_pairChartMap k g r₁ r₂ (u p)
  have hro : IsOpen (Set.range (pairChartMap k g r₁ g r₂ i j)) :=
    (pairChartMap k g r₁ g r₂ i j).isOpenEmbedding.isOpen_range
  have hopen : IsOpen
      (u ⁻¹' Set.range (pairChartMap k g r₁ g r₂ i j) : Set (PrimeSpectrum S)) :=
    hro.preimage u.continuous
  obtain ⟨V, ⟨x, rfl⟩, hpV, hVsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ (u ⁻¹' Set.range (pairChartMap k g r₁ g r₂ i j) : Set (PrimeSpectrum S))
        from hij)
      hopen
  exact ⟨x, i, j, hpV, fun q hq => hVsub ((PrimeSpectrum.mem_basicOpen x q).mpr hq)⟩

/-! ## The per-piece factorization -/

/-- **The quotient descent**: a chart map killing the chart carve ideal and presenting the
localized test descends to the chart atlas of `Z(♦)` through `Ideal.Quotient.liftₐ`. -/
private theorem descend_chartFactor {S : Type u} [CommRing S] [Algebra k S]
    (vv : Spec (CommRingCat.of S) ⟶ carveScheme k g r₁ r₂ μ) (x : S)
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away x)
    (hkill : ∀ c ∈ carveIdeal k g r₁ r₂ μ i j, w c = 0)
    (hfac : Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
      = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
        ≫ vv ≫ carveSchemeι k g r₁ r₂ μ) :
    ∃ ω : (PairChartRing k g r₁ g r₂ i j ⧸ carveIdeal k g r₁ r₂ μ i j)
        →ₐ[k] Localization.Away x,
      Spec.map (CommRingCat.ofHom ω.toRingHom) ≫ carveLocusToCarveScheme k g r₁ r₂ μ i j
        = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x))) ≫ vv := by
  refine ⟨Ideal.Quotient.liftₐ (carveIdeal k g r₁ r₂ μ i j) w hkill, ?_⟩
  refine carveScheme_hom_ext k g r₁ r₂ μ _ _ ?_
  have hcomp : CommRingCat.ofHom (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j))
      ≫ CommRingCat.ofHom
        (Ideal.Quotient.liftₐ (carveIdeal k g r₁ r₂ μ i j) w hkill).toRingHom
      = CommRingCat.ofHom w.toRingHom :=
    (CommRingCat.ofHom_comp _ _).symm.trans (congrArg CommRingCat.ofHom
      (congrArg AlgHom.toRingHom
        (Ideal.Quotient.liftₐ_comp (carveIdeal k g r₁ r₂ μ i j) w hkill)))
  calc (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.liftₐ (carveIdeal k g r₁ r₂ μ i j) w hkill).toRingHom)
        ≫ carveLocusToCarveScheme k g r₁ r₂ μ i j) ≫ carveSchemeι k g r₁ r₂ μ
      = Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.liftₐ (carveIdeal k g r₁ r₂ μ i j) w hkill).toRingHom)
        ≫ carveLocusToCarveScheme k g r₁ r₂ μ i j ≫ carveSchemeι k g r₁ r₂ μ :=
        Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.liftₐ (carveIdeal k g r₁ r₂ μ i j) w hkill).toRingHom)
        ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j)))
        ≫ pairChartMap k g r₁ g r₂ i j :=
        congrArg (Spec.map _ ≫ ·) (carveLocusToCarveScheme_carveSchemeι k g r₁ r₂ μ i j)
    _ = (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.liftₐ (carveIdeal k g r₁ r₂ μ i j) w hkill).toRingHom)
        ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j))))
        ≫ pairChartMap k g r₁ g r₂ i j := (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j :=
        congrArg (· ≫ pairChartMap k g r₁ g r₂ i j)
          ((Spec.map_comp _ _).symm.trans (congrArg Spec.map hcomp))
    _ = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
        ≫ vv ≫ carveSchemeι k g r₁ r₂ μ := hfac
    _ = (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x))) ≫ vv)
        ≫ carveSchemeι k g r₁ r₂ μ := (Category.assoc _ _ _).symm

/-- **The per-piece chart factor**: on a basic localization whose points all land in the
range of the pair chart `(I, J)`, the test morphism factors through the chart atlas of
`Z(♦)` along a `k`-algebra map out of the chart ring `R_{I,J} ⧸ I_♦`. -/
private theorem chartFactor_piece {S : Type u} [CommRing S] [Algebra k S]
    (vv : Spec (CommRingCat.of S) ⟶ carveScheme k g r₁ r₂ μ)
    (hstruct : vv ≫ carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂
      = Spec.map (CommRingCat.ofHom (algebraMap k S)))
    (x : S) (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (hx : ∀ q : PrimeSpectrum S, x ∉ q.asIdeal
      → (vv ≫ carveSchemeι k g r₁ r₂ μ) q
          ∈ Set.range (pairChartMap k g r₁ g r₂ i j)) :
    ∃ ω : (PairChartRing k g r₁ g r₂ i j ⧸ carveIdeal k g r₁ r₂ μ i j)
        →ₐ[k] Localization.Away x,
      Spec.map (CommRingCat.ofHom ω.toRingHom) ≫ carveLocusToCarveScheme k g r₁ r₂ μ i j
        = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x))) ≫ vv := by
  -- the localized test lands in the pair chart
  have hrange : Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
        ≫ vv ≫ carveSchemeι k g r₁ r₂ μ)
      ⊆ Set.range (pairChartMap k g r₁ g r₂ i j) := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    refine hx ((Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))) z) ?_
    intro hmem
    exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem (Ideal.mem_comap.mp hmem)
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x))
  -- the chart presentation of the localized test
  obtain ⟨w', hw'⟩ : ∃ w' : CommRingCat.of (PairChartRing k g r₁ g r₂ i j)
        ⟶ CommRingCat.of (Localization.Away x),
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
          ≫ vv ≫ carveSchemeι k g r₁ r₂ μ
        = Spec.map w' ≫ pairChartMap k g r₁ g r₂ i j :=
    ⟨Spec.preimage (IsOpenImmersion.lift (pairChartMap k g r₁ g r₂ i j)
        (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
          ≫ vv ≫ carveSchemeι k g r₁ r₂ μ) hrange), by
      rw [Spec.map_preimage]
      exact (IsOpenImmersion.lift_fac _ _ hrange).symm⟩
  -- the chart map is a `k`-algebra map (the chart structure triangle)
  have hkalg : CommRingCat.ofHom (algebraMap k (PairChartRing k g r₁ g r₂ i j)) ≫ w'
      = CommRingCat.ofHom (algebraMap k (Localization.Away x)) := by
    apply Spec.map_injective
    calc Spec.map (CommRingCat.ofHom (algebraMap k (PairChartRing k g r₁ g r₂ i j)) ≫ w')
        = Spec.map w'
          ≫ (pairChartMap k g r₁ g r₂ i j ≫ grPairStructMap k g r₁ g r₂) :=
          (Spec.map_comp _ _).trans (congrArg (Spec.map w' ≫ ·)
            (pairChartMap_grPairStructMap k g r₁ g r₂ i j).symm)
      _ = (Spec.map w' ≫ pairChartMap k g r₁ g r₂ i j) ≫ grPairStructMap k g r₁ g r₂ :=
          (Category.assoc _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
            ≫ vv ≫ carveSchemeι k g r₁ r₂ μ) ≫ grPairStructMap k g r₁ g r₂ :=
          congrArg (· ≫ grPairStructMap k g r₁ g r₂) hw'.symm
      _ = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
            ≫ vv ≫ carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂ :=
          (Category.assoc _ _ _).trans (congrArg (Spec.map _ ≫ ·) (Category.assoc _ _ _))
      _ = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
            ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)) :=
          congrArg (Spec.map _ ≫ ·) hstruct
      _ = Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away x))) := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq k S (Localization.Away x)]
  have hcommutes : ∀ c : k, w'.hom (algebraMap k (PairChartRing k g r₁ g r₂ i j) c)
      = algebraMap k (Localization.Away x) c := fun c =>
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hkalg) c
  -- the chart map kills the chart carve ideal (KeyChart + the sections workhorse)
  have hkill : ∀ c ∈ carveIdeal k g r₁ r₂ μ i j, w'.hom c = 0 := by
    intro c hc
    have hs : (pairChartΓ k g r₁ g r₂ i j).hom
        ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c) = c :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (IsIso.inv_hom_id (pairChartΓ k g r₁ g r₂ i j))) c
    -- the section over the chart open lies in the carve ideal sheaf (KeyChart)
    have hmem1 : (inv (pairChartΓ k g r₁ g r₂ i j)).hom c
        ∈ (carveIdealSheaf k g r₁ r₂ μ).ideal (pairChartOpen k g r₁ g r₂ i j) :=
      (carveIdealSheaf_ideal_pairChartOpen k g r₁ r₂ μ i j).ge
        (Ideal.mem_comap.mpr (hs.symm ▸ hc))
    -- so the test kills it as a section
    have happ : ((vv ≫ carveSchemeι k g r₁ r₂ μ).app
        (pairChartOpen k g r₁ g r₂ i j).1).hom
        ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c) = 0 :=
      RingHom.mem_ker.mp (Scheme.Hom.ideal_ker_le (vv ≫ carveSchemeι k g r₁ r₂ μ)
        (pairChartOpen k g r₁ g r₂ i j)
        (carveIdealSheaf_le_ker_of_factors k g r₁ r₂ μ
          (vv ≫ carveSchemeι k g r₁ r₂ μ) vv rfl
          (pairChartOpen k g r₁ g r₂ i j) hmem1))
    -- localize the kill through `appLE`
    have hsplit : (vv ≫ carveSchemeι k g r₁ r₂ μ).appLE
          (pairChartOpen k g r₁ g r₂ i j).1
          ((vv ≫ carveSchemeι k g r₁ r₂ μ) ⁻¹ᵁ (pairChartOpen k g r₁ g r₂ i j).1) le_rfl
        ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))).appLE
          ((vv ≫ carveSchemeι k g r₁ r₂ μ) ⁻¹ᵁ (pairChartOpen k g r₁ g r₂ i j).1) ⊤
          (top_le_preimage_pairChartOpen_of_factor k g r₁ g r₂ i j w' hw')
      = (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
          ≫ vv ≫ carveSchemeι k g r₁ r₂ μ).appLE (pairChartOpen k g r₁ g r₂ i j).1 ⊤
          (top_le_preimage_pairChartOpen_of_factor k g r₁ g r₂ i j w' hw') :=
      Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have h1 : ((Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
          ≫ vv ≫ carveSchemeι k g r₁ r₂ μ).appLE (pairChartOpen k g r₁ g r₂ i j).1 ⊤
          (top_le_preimage_pairChartOpen_of_factor k g r₁ g r₂ i j w' hw')).hom
        ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c)
        = ((Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))).appLE
            ((vv ≫ carveSchemeι k g r₁ r₂ μ) ⁻¹ᵁ (pairChartOpen k g r₁ g r₂ i j).1) ⊤
            (top_le_preimage_pairChartOpen_of_factor k g r₁ g r₂ i j w' hw')).hom
          (((vv ≫ carveSchemeι k g r₁ r₂ μ).appLE (pairChartOpen k g r₁ g r₂ i j).1
              ((vv ≫ carveSchemeι k g r₁ r₂ μ) ⁻¹ᵁ (pairChartOpen k g r₁ g r₂ i j).1)
              le_rfl).hom ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c)) :=
      (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsplit)
        ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c)).symm
    have h2 : (((vv ≫ carveSchemeι k g r₁ r₂ μ).appLE (pairChartOpen k g r₁ g r₂ i j).1
          ((vv ≫ carveSchemeι k g r₁ r₂ μ) ⁻¹ᵁ (pairChartOpen k g r₁ g r₂ i j).1)
          le_rfl).hom ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c))
        = ((vv ≫ carveSchemeι k g r₁ r₂ μ).app (pairChartOpen k g r₁ g r₂ i j).1).hom
            ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (Scheme.Hom.appLE_eq_app (vv ≫ carveSchemeι k g r₁ r₂ μ)))
        ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c)
    have h0 : ((Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
          ≫ vv ≫ carveSchemeι k g r₁ r₂ μ).appLE (pairChartOpen k g r₁ g r₂ i j).1 ⊤
          (top_le_preimage_pairChartOpen_of_factor k g r₁ g r₂ i j w' hw')).hom
        ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c) = 0 :=
      h1.trans ((DFunLike.congr_arg
        ((Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))).appLE
          ((vv ≫ carveSchemeι k g r₁ r₂ μ) ⁻¹ᵁ (pairChartOpen k g r₁ g r₂ i j).1) ⊤
          (top_le_preimage_pairChartOpen_of_factor k g r₁ g r₂ i j w' hw')).hom
        (h2.trans happ)).trans (map_zero _))
    -- read the kill through the chart-sections workhorse
    have hW := ΓSpecIso_hom_appLE_of_eq_specMap_pairChartMap k g r₁ g r₂ i j w' hw'
      (top_le_preimage_pairChartOpen_of_factor k g r₁ g r₂ i j w' hw')
      ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c)
    have h4 : w'.hom ((pairChartΓ k g r₁ g r₂ i j).hom
        ((inv (pairChartΓ k g r₁ g r₂ i j)).hom c)) = 0 :=
      hW.symm.trans ((DFunLike.congr_arg
        (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away x))).hom.hom h0).trans
        (map_zero _))
    exact (DFunLike.congr_arg w'.hom hs).symm.trans h4
  -- descend to the chart atlas
  exact descend_chartFactor k g r₁ r₂ μ vv x i j
    { toRingHom := w'.hom, commutes' := hcommutes } hkill hw'.symm

/-! ## The keystone: the atlas factorization of an arbitrary test morphism -/

/-- **The atlas factorization** (`informal/w4-ddr9-worksheet.md` §3.3): every morphism
`v : overSpec k S ⟶ carveSchemeOver` factors, over a finite spanning family of basic
localizations of `S`, through the chart atlas of `Z(♦)` along `k`-algebra maps
`ω : R_{I,J} ⧸ I_♦ →ₐ[k] Localization.Away (f t)` out of the chart rings. -/
theorem carveScheme_exists_chartFactor (S : Type u) [CommRing S] [Algebra k S]
    (v : overSpec k S ⟶ carveSchemeOver k g r₁ r₂ μ) :
    ∃ (m : ℕ) (f : Fin m → S), Ideal.span (Set.range f) = ⊤ ∧
      ∀ t : Fin m, ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
        (ω : (PairChartRing k g r₁ g r₂ i j ⧸ carveIdeal k g r₁ r₂ μ i j)
          →ₐ[k] Localization.Away (f t)),
        Spec.map (CommRingCat.ofHom ω.toRingHom)
            ≫ carveLocusToCarveScheme k g r₁ r₂ μ i j
          = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t))))
            ≫ v.left := by
  have hstruct : v.left ≫ carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂
      = Spec.map (CommRingCat.ofHom (algebraMap k S)) := Over.w v
  choose F I J hmem hsub using fun p : PrimeSpectrum S =>
    exists_basicOpen_range_pairChartMap k g r₁ r₂
      (v.left ≫ carveSchemeι k g r₁ r₂ μ) p
  obtain ⟨tset, htset⟩ := isCompact_univ.elim_finite_subcover
    (fun p : PrimeSpectrum S => (PrimeSpectrum.basicOpen (F p) : Set (PrimeSpectrum S)))
    (fun p => (PrimeSpectrum.basicOpen (F p)).2)
    (fun p _ => Set.mem_iUnion.mpr ⟨p, hmem p⟩)
  refine ⟨tset.card, fun n => F (tset.equivFin.symm n).1, ?_, fun t => ?_⟩
  · -- the selected elements span the unit ideal
    refine PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp ?_
    rw [PrimeSpectrum.zeroLocus_span]
    refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp (htset (Set.mem_univ p))
    exact (PrimeSpectrum.mem_basicOpen (F q) p).mp hpq
      ((PrimeSpectrum.mem_zeroLocus p _).mp hp
        (Set.mem_range.mpr ⟨tset.equivFin ⟨q, hq⟩,
          congrArg F (congrArg Subtype.val (tset.equivFin.symm_apply_apply ⟨q, hq⟩))⟩))
  · -- the per-piece factorization at the selected basic open
    obtain ⟨ω, hω⟩ := chartFactor_piece k g r₁ r₂ μ v.left hstruct
      (F (tset.equivFin.symm t).1) (I (tset.equivFin.symm t).1) (J (tset.equivFin.symm t).1)
      (hsub (tset.equivFin.symm t).1)
    exact ⟨I (tset.equivFin.symm t).1, J (tset.equivFin.symm t).1, ω, hω⟩

end Generic

/-! ## The campaign spellings (the DAT-D windows) -/

section Curve

open Scheme

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable (A B : X.CurveDivisor) (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
variable (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤))

/-- **The chart atlas of `DivScheme g`** (`informal/w4-ddr9-worksheet.md` §3.3): each
`Z(♦)`-chart `Spec R_Z` maps to `DivScheme g`, factoring the chart presentation through
`divSchemeι`.  The kill law is `divCarveIdeal_le_ker_of_tower` at the chart ring itself
(spelled `Ideal.mk_ker`). -/
noncomputable def divCarveChartToDivScheme
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    Spec (CommRingCat.of (DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j))
      ⟶ DivScheme k A B g r₁ r₂ b₁ b₂ :=
  carveLocusToCarveScheme k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂) i j

/-- **The defining triangle of the `DivScheme` chart atlas**: through the closed immersion
`divSchemeι`, the chart map of `Spec R_Z` is `Spec` of the quotient presentation
`divCarveChartMk` followed by the pair chart. -/
theorem divCarveChartToDivScheme_divSchemeι
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    divCarveChartToDivScheme k A B g r₁ r₂ b₁ b₂ i j ≫ divSchemeι k A B g r₁ r₂ b₁ b₂
      = Spec.map (CommRingCat.ofHom (divCarveChartMk k A B g r₁ r₂ b₁ b₂ i j).toRingHom)
        ≫ pairChartMap k g r₁ g r₂ i j :=
  carveLocusToCarveScheme_carveSchemeι k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂) i j

/-- **The atlas factorization of `DivScheme g`** (`informal/w4-ddr9-worksheet.md` §3.3,
the DDR-9.F1 keystone): every test morphism `v : overSpec k S ⟶ divSchemeOver` factors,
over a finite spanning family of basic localizations of `S`, through some chart
`divCarveChartToDivScheme i j` along a `k`-algebra map
`ω : R_Z →ₐ[k] Localization.Away (f t)` out of the `Z(♦)`-chart ring. -/
theorem divScheme_exists_chartFactor (S : Type u) [CommRing S] [Algebra k S]
    (v : overSpec k S ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂) :
    ∃ (m : ℕ) (f : Fin m → S), Ideal.span (Set.range f) = ⊤ ∧
      ∀ t : Fin m, ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
        (ω : DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j →ₐ[k] Localization.Away (f t)),
        Spec.map (CommRingCat.ofHom ω.toRingHom)
            ≫ divCarveChartToDivScheme k A B g r₁ r₂ b₁ b₂ i j
          = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t))))
            ≫ v.left :=
  carveScheme_exists_chartFactor k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂) S v

end Curve

end AlgebraicGeometry
